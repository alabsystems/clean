#!/usr/bin/env bash
# Paragon quality ratchet (roadmap "paragon standard", QUALITY leg).
#
# Measures four code-quality debt metrics across crates/ and enforces
# shrink-only against the committed baseline data/paragon_ratchet.json
# (mirrors data/unchecked_decl_ratchet.json):
#
#   (a) files_over_500          .rs files longer than 500 lines
#   (b) unwrap_expect_production .unwrap()/.expect( in non-test production code
#   (c) bare_pub_non_lib        bare `pub fn/struct/enum` outside lib.rs
#   (d) allow_dead_code_sites   #![allow(dead_code)] inner-attribute sites in src/
#
# Usage:
#   scripts/paragon_ratchet.sh            # recompute, FAIL if any total grew
#   scripts/paragon_ratchet.sh --update   # rewrite baseline (intentional ratchet-down)
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
from datetime import date
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


def discover() -> dict[str, list[Path]]:
    by_crate: dict[str, list[Path]] = {}
    import subprocess
    tracked = subprocess.run(["git","ls-files","crates/*.rs","crates/**/*.rs"],capture_output=True,text=True).stdout.splitlines()
    for path in sorted(Path(f) for f in tracked):
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
ALLOW_DEAD_RE = re.compile(r"#!\[allow\([^)]*\bdead_code\b")


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


def is_test_path(path: Path) -> bool:
    if any(p in ("tests", "benches", "examples") for p in path.parts):
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
            "files_over_500": 0,
            "unwrap_expect_production": 0,
            "bare_pub_non_lib": 0,
            "allow_dead_code_sites": 0,
        }
        for path in files:
            text = path.read_text(encoding="utf-8", errors="replace")
            n_lines = text.count("\n") + (1 if text and not text.endswith("\n") else 0)
            if n_lines > 500:
                m["files_over_500"] += 1
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
            "files_over_500",
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
    "files_over_500": "every in-scope .rs file with >500 lines (src, tests, benches, examples) — rust_excellence 500-line rule",
    "unwrap_expect_production": "occurrences of `.unwrap()` and `.expect(` in src/ files only (tests/, benches/, examples/ dirs, sibling test files tests.rs/*_tests.rs/tests_*.rs, and sibling test dirs tests_*/ excluded — all verified #[cfg(test)]-gated), skipping #[cfg(test)]-gated items via a naive brace-depth scanner (string literals and // comments stripped first) and skipping comment text; string contents containing the patterns are not detected — grep heuristic, not a parse",
    "bare_pub_non_lib": "lines in src/ non-lib.rs files (same test-skip heuristic) matching `pub [async|const|unsafe|extern] fn|struct|enum` — bare pub, not pub(crate)/pub(super); proxy for pub(crate) discipline",
    "allow_dead_code_sites": "`#![allow(...dead_code...)]` inner-attribute lines in src/ files (whole-file/module dead-code suppressions)",
}

if MODE == "update":
    doc = {
        "note": "Paragon quality ratchet (rust_excellence.md enforced as ratchets, not advice). Shrink-only: scripts/paragon_ratchet.sh fails if any total increases; rerun with --update only for intentional ratchet-downs.",
        "heuristics": HEURISTICS,
        "totals": totals,
        "crates": crates,
        "worst_offenders_over_500": worst,
        "generated_by": "scripts/paragon_ratchet.sh --update",
        "last_updated": date.today().isoformat(),
    }
    DATA_FILE.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    print(f"paragon ratchet: baseline written to {DATA_FILE}")
    for k, v in totals.items():
        print(f"  {k}: {v}")
    sys.exit(0)

if not DATA_FILE.exists():
    print(f"paragon ratchet: FAIL — {DATA_FILE} missing; run scripts/paragon_ratchet.sh --update", file=sys.stderr)
    sys.exit(1)

baseline = json.loads(DATA_FILE.read_text(encoding="utf-8"))
base_totals = baseline.get("totals", {})
failed = False
for k, cur in totals.items():
    base = base_totals.get(k)
    if base is None:
        print(f"paragon ratchet: FAIL — baseline missing total '{k}'; run --update", file=sys.stderr)
        failed = True
        continue
    delta = cur - base
    marker = "OK " if delta <= 0 else "GREW"
    print(f"  {marker} {k}: baseline={base} current={cur} ({delta:+d})")
    if delta > 0:
        failed = True
        base_crates = baseline.get("crates", {})
        for crate in sorted(set(crates) | set(base_crates)):
            b = base_crates.get(crate, {}).get(k, 0)
            c = crates.get(crate, {}).get(k, 0)
            if c > b:
                print(f"        {crate}: {b} -> {c}", file=sys.stderr)

if failed:
    print(
        "paragon ratchet: FAIL — quality debt increased (shrink-only). "
        "Fix the regression; if a total legitimately went DOWN elsewhere, "
        "refresh with scripts/paragon_ratchet.sh --update.",
        file=sys.stderr,
    )
    sys.exit(1)

improved = any(totals[k] < base_totals.get(k, 0) for k in totals)
if improved:
    print("paragon ratchet: PASS (improved — consider scripts/paragon_ratchet.sh --update to lock it in)")
else:
    print("paragon ratchet: PASS")
EOF
