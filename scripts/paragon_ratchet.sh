#!/usr/bin/env bash
# Paragon quality ratchet (roadmap "paragon standard", QUALITY leg).
#
# Measures four code-quality debt metrics across crates/ and enforces
# shrink-only against the committed baseline data/paragon_ratchet.json
# (mirrors data/unchecked_decl_ratchet.json):
#
#   (a) files_over_1000         .rs files longer than 1000 lines (OWNER RULING 2026-08-24: threshold raised 500 -> 1000; the goal is organization, not taxing proof text — was the 500-line rust_excellence figure)
#   (b) unwrap_expect_production .unwrap()/.expect( in non-test production code
#   (c) bare_pub_non_lib        bare `pub fn/struct/enum` outside lib.rs
#   (d) allow_dead_code_sites   whole-module dead-code inner attributes in src/
#
# Usage:
#   scripts/paragon_ratchet.sh            # recompute, FAIL if any total grew
#   scripts/paragon_ratchet.sh --update   # rewrite baseline (intentional ratchet-down)
#
# A DEBT (the baseline's "debt" key) is growth someone else caused, owned and
# expiring, CAPPED at what was measured: {"owner", "expires" (YYYY-MM-DD, at
# most 180 days out), "measured" (the reason), "ceilings" {total: ceiling}}.
# While it runs, a total may reach its ceiling and no further; past its expiry
# it caps nothing; once every total is back at its baseline it FAILS until
# deleted, so it cannot outlive the growth it names. It replaces the pre-push
# hook's WAIVED row for this leg, which passed whatever the leg measured
# (verifier land-clean-r1: a new unwrap in clean-elab landed under it), and
# scripts/check_hook_coverage.py refuses that row. The decision is self-tested
# on every run (PARAGON_RATCHET_SELFTEST).
#
# Heuristics are documented in the generated JSON ("heuristics" key) and in
# the python core below. Exclusions: */target/*, crates/clean-kernel/src/env/
# (another lane owns its content; excluded so this ratchet never pressures
# edits there).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

MODE="check"
[[ "${1:-}" == "--update" ]] && MODE="update"

PARAGON_RATCHET_MODE="$MODE" python3 - <<'EOF'
import json
import os
import re
import sys
from functools import lru_cache
from datetime import date, timedelta
from pathlib import Path

DATA_FILE = Path("data/paragon_ratchet.json")
MODE = os.environ.get("PARAGON_RATCHET_MODE", "check")

# ---------------------------------------------------------------------------
# File discovery
# ---------------------------------------------------------------------------
# Scope: all .rs files under crates/<crate>/, excluding target/ build output
# and crates/clean-kernel/src/env/ (owned by another lane; never measured so
# this ratchet can never pressure edits there).
KERNEL_ENV = Path("crates/clean-kernel/src/env")


# ONE `git ls-files` for the whole run, and ONE read per file. The scanner used
# to walk the tree four times (discover, the cfg(test)-root scan, the metric
# loop, and a re-read of every parent mod.rs inside is_cfg_test_module_file);
# every consumer below now shares these two structures instead.
def _tracked_rs() -> list[str]:
    import subprocess

    return subprocess.run(
        ["git", "ls-files", "crates/*.rs", "crates/**/*.rs"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()


TRACKED = _tracked_rs()
TRACKED_PATHS = {Path(name) for name in TRACKED}
_TEXT: dict[Path, str] = {}


def text_of(path: Path) -> str:
    """Cached file read. Untracked parents still fall back to disk, so the
    test-path heuristic below sees exactly what it saw when it read directly."""
    cached = _TEXT.get(path)
    if cached is None:
        cached = path.read_text(encoding="utf-8", errors="replace")
        _TEXT[path] = cached
    return cached


def discover() -> dict[str, list[Path]]:
    by_crate: dict[str, list[Path]] = {}
    for path in sorted(TRACKED_PATHS):
        parts = path.parts
        if "target" in parts:
            continue
        if path.is_relative_to(KERNEL_ENV):
            continue
        crate = parts[1]
        by_crate.setdefault(crate, []).append(path)
    return by_crate


# ---------------------------------------------------------------------------
# Test-region heuristic (documented in JSON "heuristics")
# ---------------------------------------------------------------------------
# A line is "test code" if it sits inside a #[cfg(test)]-gated item: when a
# #[cfg(test)] / #[cfg(all(test, ...))] attribute is seen, the next item is
# skipped — a braced block is skipped to its matching close brace (naive
# brace counting after stripping string literals and // comments), a
# semicolon-terminated item is skipped as one line. This catches the
# standard `#[cfg(test)] mod tests { ... }` layout and cfg(test) functions.
# Files under tests/, benches/, examples/ directories are excluded from the
# production metrics wholesale (they only count for file length).
STRING_RE = re.compile(r'"(?:\\.|[^"\\])*"')
CHAR_RE = re.compile(r"'(?:\\.|[^'\\])'")
CFG_TEST_RE = re.compile(r"#\[cfg\((?:all\()?test\b")
BARE_PUB_RE = re.compile(
    r'^\s*pub\s+(?:async\s+|const\s+|unsafe\s+|extern\s+"[^"]*"\s+)*(?:fn|struct|enum)\b'
)
ALLOW_DEAD_RE = re.compile(r"#!\[[^\]]*\ballow\([^)]*\bdead_code\b")
CFG_TEST_MOD_RE = re.compile(
    r'#\[cfg\(test\)\]\s*'
    r'(?:#\[path\s*=\s*"([^"]+)"\]\s*)?'
    r'mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;'
)


def discover_cfg_test_module_roots() -> tuple[Path, ...]:
    """Resolve files/directories imported only through `#[cfg(test)] mod`."""
    tracked_paths = TRACKED_PATHS
    roots: set[Path] = set()
    for declaring_file in sorted(tracked_paths):
        text = text_of(declaring_file)
        for explicit_path, module_name in CFG_TEST_MOD_RE.findall(text):
            if explicit_path:
                candidates = [declaring_file.parent / explicit_path]
            else:
                module_dir = (
                    declaring_file.parent
                    if declaring_file.name in {"lib.rs", "main.rs", "mod.rs"}
                    else declaring_file.with_suffix("")
                )
                candidates = [
                    module_dir / f"{module_name}.rs",
                    module_dir / module_name / "mod.rs",
                ]
            for candidate in candidates:
                if candidate not in tracked_paths:
                    continue
                roots.add(candidate)
                roots.add(
                    candidate.parent
                    if candidate.name == "mod.rs"
                    else candidate.with_suffix("")
                )
                break
    return tuple(sorted(roots))


CFG_TEST_MODULE_ROOTS = discover_cfg_test_module_roots()
# `path.is_relative_to(root)` for every root was 8.03M Path comparisons -- 33.5s
# of a 39s run, and the reason this leg cost a minute. A path is relative to
# some root exactly when one of its OWN ancestors (or itself) IS a root, and a
# path has ~6 ancestors against 2,176 roots. Same predicate, set-sized.
CFG_TEST_MODULE_ROOT_SET = frozenset(CFG_TEST_MODULE_ROOTS)


def strip_code(line: str) -> str:
    """Remove string/char literals and // comments for brace/pattern scanning."""
    line = STRING_RE.sub('""', line)
    line = CHAR_RE.sub("' '", line)
    idx = line.find("//")
    if idx != -1:
        line = line[:idx]
    return line


def production_lines(text: str):
    """Yield (raw_line, stripped_line) for lines outside #[cfg(test)] items."""
    pending_cfg_test = False
    skip_depth = None  # brace depth at which a skipped block ends
    depth = 0
    for raw in text.splitlines():
        code = strip_code(raw)
        opens, closes = code.count("{"), code.count("}")
        if skip_depth is not None:
            depth += opens - closes
            if depth <= skip_depth:
                skip_depth = None
            continue
        if pending_cfg_test:
            if "{" in code:
                pending_cfg_test = False
                skip_depth = depth
                depth += opens - closes
                if depth <= skip_depth:
                    skip_depth = None
                continue
            if code.strip().endswith(";"):
                pending_cfg_test = False
                continue
            # attribute lines / blank lines between #[cfg(test)] and the item
            if CFG_TEST_RE.search(code) or code.strip().startswith("#[") or not code.strip():
                continue
            pending_cfg_test = False  # malformed; fail open (count the line)
        if CFG_TEST_RE.search(code):
            pending_cfg_test = True
            continue
        depth += opens - closes
        yield raw, code


@lru_cache(maxsize=None)
def is_cfg_test_module_file(path: Path) -> bool:
    """Return whether a sibling module file is declared behind `cfg(test)`."""
    module_name = path.stem
    parent_sources = [
        path.parent / "mod.rs",
        path.parent / "lib.rs",
        path.parent / "main.rs",
        path.parent.with_suffix(".rs"),
    ]
    declaration = re.compile(rf"\bmod\s+{re.escape(module_name)}\s*;")
    for parent in dict.fromkeys(parent_sources):
        if parent == path or (parent not in TRACKED_PATHS and not parent.is_file()):
            continue
        pending_cfg_test = False
        for raw in text_of(parent).splitlines():
            code = strip_code(raw).strip()
            if CFG_TEST_RE.search(code):
                pending_cfg_test = True
                continue
            if not pending_cfg_test:
                continue
            if not code or code.startswith("#["):
                continue
            if declaration.search(code):
                return True
            pending_cfg_test = False
    return False


@lru_cache(maxsize=None)
def is_test_path(path: Path) -> bool:
    if any(p in ("tests", "benches", "examples") for p in path.parts):
        return True
    # Two complementary cfg(test)-module detectors, unioned: the root scan
    # resolves `#[path = "..."]` declarations and whole module DIRECTORIES,
    # the parent walk catches declarations separated from `#[cfg(test)]` by
    # intervening attribute lines. Either match means test-only code.
    if not CFG_TEST_MODULE_ROOT_SET.isdisjoint(path.parents):
        return True
    if path in CFG_TEST_MODULE_ROOT_SET:
        return True
    if is_cfg_test_module_file(path):
        return True
    # Sibling test FILES and DIRECTORIES carry no #[cfg(test)] marker inside
    # themselves but are compiled only via `#[cfg(test)] mod tests*;` in the
    # parent (repo conventions: tests.rs, *_tests.rs (incl. numbered *_tests2.rs),
    # tests_*.rs files and
    # tests_*/ directories — every tests_*/ dir in the workspace was verified
    # cfg(test)-gated when this rule landed; see data/paragon_ratchet.json).
    if any(p.startswith("tests_") for p in path.parts[:-1]):
        return True
    n = path.name
    # tests.rs / foo_tests.rs / tests_foo.rs PLUS numbered or suffixed split
    # variants (foo_tests2.rs, tests3.rs, foo_tests_binding.rs): a split test
    # file named *_tests2.rs or *_tests_<suffix>.rs is still test code, not
    # production. The old bare `_tests.rs` suffix check mis-counted those as
    # production, inflating the metrics. The trailing `(?:_[a-z0-9]+)?` accepts
    # a descriptive split suffix after `tests` (e.g. closure_load_v3_tests
    # split into _tests.rs + _tests_binding.rs, mathverse_integration_tests
    # split into _tests.rs + _tests_extra.rs) — both verified #[cfg(test)]-gated
    # `#[path]`/`mod` submodules when this rule landed.
    return (
        bool(re.search(r"(?:^|_)tests\d*(?:_[a-z0-9]+)?\.rs$", n))
        or n.startswith("tests_")
    )


# ---------------------------------------------------------------------------
# Metrics
# ---------------------------------------------------------------------------
def measure():
    crates: dict[str, dict[str, int]] = {}
    offenders: list[dict] = []
    for crate, files in discover().items():
        m = {
            "files_over_1000": 0,
            "unwrap_expect_production": 0,
            "bare_pub_non_lib": 0,
            "allow_dead_code_sites": 0,
        }
        for path in files:
            text = text_of(path)
            n_lines = text.count("\n") + (1 if text and not text.endswith("\n") else 0)
            if n_lines > 1000:
                m["files_over_1000"] += 1
                offenders.append({"path": str(path), "lines": n_lines})
            if is_test_path(path) or "src" not in path.parts:
                continue  # production metrics: src/ only
            for raw, code in production_lines(text):
                m["unwrap_expect_production"] += code.count(".unwrap()")
                m["unwrap_expect_production"] += code.count(".expect(")
                if path.name != "lib.rs" and BARE_PUB_RE.match(code):
                    m["bare_pub_non_lib"] += 1
                if ALLOW_DEAD_RE.search(code):
                    m["allow_dead_code_sites"] += 1
        crates[crate] = m
    totals = {
        k: sum(c[k] for c in crates.values())
        for k in (
            "files_over_1000",
            "unwrap_expect_production",
            "bare_pub_non_lib",
            "allow_dead_code_sites",
        )
    }
    offenders.sort(key=lambda o: (-o["lines"], o["path"]))
    return crates, totals, offenders[:20]


crates, totals, worst = measure()

HEURISTICS = {
    "scope": "all .rs files under crates/<crate>/; excludes */target/* and crates/clean-kernel/src/env/ (another lane owns its content)",
    "files_over_1000": "every in-scope .rs file with >1000 lines (src, tests, benches, examples) — owner ruling 2026-08-24 raised the organizational threshold from the rust_excellence 500 figure",
    "unwrap_expect_production": "occurrences of `.unwrap()` and `.expect(` in src/ files only (tests/, benches/, examples/ dirs, files/directories resolved from direct #[cfg(test)] mod declarations including #[path=\"...\"], sibling modules declared behind #[cfg(test)], sibling test files tests.rs/*_tests.rs/tests_*.rs, and sibling test dirs tests_*/ excluded), skipping #[cfg(test)]-gated inline items via a naive brace-depth scanner (string literals and // comments stripped first) and skipping comment text; string contents containing the patterns are not detected — grep heuristic, not a parse",
    "bare_pub_non_lib": "lines in src/ non-lib.rs files (same test-skip heuristic) matching `pub [async|const|unsafe|extern] fn|struct|enum` — bare pub, not pub(crate)/pub(super); proxy for pub(crate) discipline",
    "allow_dead_code_sites": "inner-attribute lines in src/ files that allow dead_code directly or through cfg_attr (whole-file/module suppressions)",
}

if MODE == "update":
    previous = (
        json.loads(DATA_FILE.read_text(encoding="utf-8"))
        if DATA_FILE.exists()
        else {}
    )
    doc = {
        "note": "Paragon quality ratchet (rust_excellence.md enforced as ratchets, not advice). Shrink-only: scripts/paragon_ratchet.sh fails if any total increases; rerun with --update only for intentional ratchet-downs.",
        "cfg_test_module_correction": "2026-07-23: production metrics now resolve direct #[cfg(test)] mod declarations, excluding their external module files and descendants. The prior scanner counted test-only files with names such as lean4_features.rs as production debt.",
        "heuristics": HEURISTICS,
        "totals": totals,
        "crates": crates,
        "worst_offenders_over_1000": worst,
        "generated_by": "scripts/paragon_ratchet.sh --update",
        "last_updated": date.today().isoformat(),
    }
    # Carry forward every narrative key the baseline already had that this
    # generator does not itself produce. `--update` used to preserve exactly
    # one hand-written key by name, so the REASONING a lane recorded for a
    # legitimate baseline bump ("these four pubs are structurally required, and
    # here is why each one is") was silently erased by the next lane's refresh.
    # A ratchet whose justifications evaporate is a ratchet whose numbers
    # nobody can audit, so the rule is now the general one: generated keys are
    # rewritten, everything else survives.
    for key, value in previous.items():
        if key not in doc:
            doc[key] = value
    DATA_FILE.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    print(f"paragon ratchet: baseline written to {DATA_FILE}")
    for k, v in totals.items():
        print(f"  {k}: {v}")
    sys.exit(0)

ISO_DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def debt_problems(debt, base_totals, today):
    """Why a baseline's debt is malformed, or []: an owned, expiring, capped
    account, each ceiling above its baseline (at it, it caps nothing)."""
    if not isinstance(debt, dict):
        return ["the debt is not an object"]
    problems = []
    owner = debt.get("owner")
    if not isinstance(owner, str) or owner.strip() in ("", "-"):
        problems.append("the debt names no owner -- an unowned debt is how growth becomes permanent")
    expires = debt.get("expires")
    if not isinstance(expires, str) or not ISO_DATE.match(expires):
        problems.append(f"the debt's expiry {expires!r} is not YYYY-MM-DD")
    else:
        horizon = (date.fromisoformat(today) + timedelta(days=180)).isoformat()
        if expires > horizon:
            problems.append(f"the debt expires {expires}, beyond the 180-day horizon ({horizon})")
    if not isinstance(debt.get("measured"), str) or not debt["measured"].strip():
        problems.append("the debt records no measurement")
    ceilings = debt.get("ceilings")
    if not isinstance(ceilings, dict) or not ceilings:
        problems.append("the debt caps no total")
    else:
        for k, ceiling in ceilings.items():
            base = base_totals.get(k)
            if base is None:
                problems.append(f"the debt caps {k!r}, which the baseline has no total for")
            elif not isinstance(ceiling, int) or ceiling <= base:
                problems.append(f"the debt's ceiling {ceiling!r} for {k} is not above its baseline {base}")
    return problems


def decide(totals, base_totals, debt, today):
    """(failed, lines, grew): each total against its baseline, or, while an
    owned debt runs, against the ceiling it caps that total at."""
    lines, grew, failed = [], [], False
    ceilings = {}
    if debt is not None:
        problems = debt_problems(debt, base_totals, today)
        if problems:
            return True, [f"FAIL — {p}" for p in problems], grew
        if debt["expires"] < today:
            lines.append(f"debt EXPIRED on {debt['expires']} (owner {debt['owner']}): it caps nothing")
        else:
            ceilings = debt["ceilings"]
    for k, cur in totals.items():
        base = base_totals.get(k)
        if base is None:
            lines.append(f"FAIL — baseline missing total '{k}'; run --update")
            failed = True
            continue
        delta = cur - base
        if delta <= 0:
            lines.append(f"  OK  {k}: baseline={base} current={cur} ({delta:+d})")
        elif k in ceilings and cur <= ceilings[k]:
            lines.append(
                f"  DEBT {k}: baseline={base} current={cur} ({delta:+d}), within the ceiling "
                f"{ceilings[k]} owned by {debt['owner']} until {debt['expires']}"
            )
        else:
            cap = f", past the debt's ceiling {ceilings[k]}" if k in ceilings else ""
            lines.append(f"  GREW {k}: baseline={base} current={cur} ({delta:+d}){cap}")
            grew.append(k)
            failed = True
    if debt is not None and all(totals[k] <= base_totals.get(k, 0) for k in totals):
        lines.append(
            "FAIL — the debt is paid (every total is at or below its baseline): delete the "
            f"\"debt\" key from {DATA_FILE}"
        )
        failed = True
    return failed, lines, grew


def selftest():
    """The decision, over made-up totals: every way a debt must fail fails."""
    base = {"a": 10, "b": 5}
    today = "2026-09-29"
    debt = {"owner": "lane-x", "expires": "2026-10-06", "measured": "m", "ceilings": {"a": 12}}
    arms = [
        ("no debt, no growth", {"a": 10, "b": 5}, None, today, False),
        ("no debt, growth", {"a": 11, "b": 5}, None, today, True),
        ("a debt, growth within its ceiling", {"a": 12, "b": 5}, debt, today, False),
        ("a debt, growth past its ceiling", {"a": 13, "b": 5}, debt, today, True),
        ("a debt, growth in a total it does not cap", {"a": 11, "b": 6}, debt, today, True),
        ("a debt past its expiry", {"a": 11, "b": 5}, debt, "2026-10-07", True),
        ("a debt on its expiry day", {"a": 11, "b": 5}, debt, "2026-10-06", False),
        ("a paid debt", {"a": 10, "b": 4}, debt, today, True),
        ("a debt with no owner", {"a": 11, "b": 5}, {**debt, "owner": "-"}, today, True),
        ("a debt with no expiry", {"a": 11, "b": 5}, {**debt, "expires": "soon"}, today, True),
        ("a debt past the horizon", {"a": 11, "b": 5}, {**debt, "expires": "2027-09-29"}, today, True),
        ("a debt with no measurement", {"a": 11, "b": 5}, {**debt, "measured": ""}, today, True),
        ("a ceiling at its baseline", {"a": 10, "b": 5}, {**debt, "ceilings": {"a": 10}}, today, True),
        ("a ceiling over no total", {"a": 11, "b": 5}, {**debt, "ceilings": {"a": 12, "c": 1}}, today, True),
    ]
    failed = [name for name, cur, d, day, want in arms if decide(cur, base, d, day)[0] != want]
    print(f"PARAGON_RATCHET_SELFTEST arms={len(arms)} failed={len(failed)}", flush=True)
    for name in failed:
        print(f"  x self-test arm decided wrong: {name}", file=sys.stderr, flush=True)
    return not failed


if not selftest():
    sys.exit(1)

if not DATA_FILE.exists():
    print(f"paragon ratchet: FAIL — {DATA_FILE} missing; run scripts/paragon_ratchet.sh --update", file=sys.stderr)
    sys.exit(1)

baseline = json.loads(DATA_FILE.read_text(encoding="utf-8"))
base_totals = baseline.get("totals", {})
failed, lines, grew = decide(totals, base_totals, baseline.get("debt"), date.today().isoformat())
for line in lines:
    print(line, flush=True)
if grew:
    # Interleave correctly with the stdout lines above. A caller that merges
    # both streams into one log (the suite runner does) otherwise sees every
    # stderr line FIRST -- stderr is unbuffered, stdout block-buffers into a
    # file -- so the per-crate attribution floats away from the metric it
    # attributes.
    base_crates = baseline.get("crates", {})
    for k in grew:
        print(f"      {k}:", file=sys.stderr)
        for crate in sorted(set(crates) | set(base_crates)):
            b = base_crates.get(crate, {}).get(k, 0)
            c = crates.get(crate, {}).get(k, 0)
            if c > b:
                print(f"        {crate}: {b} -> {c}", file=sys.stderr)
    sys.stderr.flush()

if failed:
    sys.stdout.flush()
    print(
        "paragon ratchet: FAIL — quality debt increased (shrink-only), or its owned debt is "
        "malformed, expired or paid. Fix the regression; if a total legitimately went DOWN "
        "elsewhere, refresh with scripts/paragon_ratchet.sh --update.",
        file=sys.stderr,
    )
    sys.stderr.flush()
    # THE VERDICT IS THE LAST LINE ON STDOUT, on the failing path too. The suite
    # runner's `summarize_output` records the last non-blank line of the merged
    # log as a row's DETAIL, and with the verdict on stderr only, a RED
    # `gate::paragon` row read `OK allow_dead_code_sites: ... (+0)` -- the exit
    # code was right and the one line a human scans said the opposite. The
    # detail stays on stderr; only the verdict is repeated here.
    print("paragon ratchet: FAIL — quality debt increased (shrink-only); detail above", flush=True)
    sys.exit(1)

improved = any(totals[k] < base_totals.get(k, 0) for k in totals)
if improved:
    print("paragon ratchet: PASS (improved — consider scripts/paragon_ratchet.sh --update to lock it in)", flush=True)
else:
    print("paragon ratchet: PASS", flush=True)
EOF
