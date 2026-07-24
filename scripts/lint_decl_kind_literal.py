#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Forbid `decl_kind: 0` literals outside #[cfg(test)] in clean-mathverse.

Context:
    `MathverseConstantHeader.decl_kind` is a u8 with 0 == DeclKind::Theorem.
    Hardcoding `decl_kind: 0` in production shard writers caused silent
    data corruption — every declaration (axioms, definitions, inductives,
    constructors) was tagged as Theorem (see #3508, #3521, #3522).

    After the companion fixes land, new `decl_kind: 0` literals in
    production code would reintroduce the same bug. This lint is the
    regression guard.

Allowed sites:
    1. Files under a `tests/` directory (integration tests).
    2. Files named `tests.rs` or matching `tests_*.rs` / `*_tests.rs`.
    3. Literals INSIDE a `#[cfg(test)] mod ... { ... }` block.
    4. Literals INSIDE a function/item preceded by `#[cfg(test)]`.
    5. Literals on a line (or the preceding line) carrying the explicit
       allow comment `// allow: decl_kind-literal`.

Modes:
    --staged   (default) Lint only files staged for commit under
               crates/clean-mathverse/src/. Exit 0 when no staged files
               match.
    --all      Lint every *.rs file under crates/clean-mathverse/src/.
               Intended for CI / baseline audits.
    --probe    Run the built-in self-test (exercises violation AND
               allowlist paths against fabricated inputs).

Exit codes:
    0 — clean, no violations.
    1 — violation found OR probe failed.
    2 — usage error.

Part of #3508 (epic). Fixes #3523.
"""

from __future__ import annotations

import argparse
import logging
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Sequence

MATHVERSE_SRC = Path("crates/clean-mathverse/src")
# Matches `decl_kind: 0`, `decl_kind:0`, `decl_kind: 0u8`, `decl_kind:0u8`.
# Rejects `decl_kind: 1`, `decl_kind: 0xff`, `decl_kind: 00`, etc.
PATTERN = re.compile(r"\bdecl_kind\s*:\s*0(?:u8)?\b(?!x)")
ALLOW_COMMENT = "// allow: decl_kind-literal"
CFG_TEST = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
# Matches `#[cfg(test)] mod NAME;` (single-line form used in lib.rs) — captures
# the module name so we can treat the corresponding NAME.rs / NAME/mod.rs as
# test-only even though the file itself carries no `#[cfg(test)]` marker.
CFG_TEST_MOD_DECL = re.compile(
    r"#\[\s*cfg\s*\(\s*(?:all\s*\(\s*test[^)]*\)|test)\s*\)\s*\]\s*(?:pub\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;"
)

log = logging.getLogger("lint_decl_kind_literal")


@dataclass
class Violation:
    path: Path
    lineno: int
    line: str


def is_test_file(path: Path) -> bool:
    """Return True for test-only .rs files that may emit decl_kind: 0 freely.

    Identification strategy (ordered):

    1. Path contains a `tests/` directory segment.
    2. Filename matches `tests.rs`, `tests_*.rs`, or `*_tests.rs`.
    3. File is declared as a `#[cfg(test)] mod FOO;` in a sibling
       `lib.rs` / `mod.rs` (covers files whose *inclusion* is
       test-gated but whose body carries no `#[cfg(test)]` marker —
       e.g. `integration.rs`, `mathverse_integration_tests_extra.rs`).
    """
    if "tests" in path.parts:
        return True
    name = path.name
    if name == "tests.rs":
        return True
    if name.startswith("tests_") and name.endswith(".rs"):
        return True
    if name.endswith("_tests.rs"):
        return True
    if name.endswith(".rs") and _is_lib_cfg_test_gated(path):
        return True
    return False


_cfg_test_mod_cache: dict[Path, frozenset[str]] = {}


def _cfg_test_mod_names_for(aggregator: Path) -> frozenset[str]:
    """Return module names declared `#[cfg(test)] mod NAME;` in `aggregator`.

    Handles both the single-line form (`#[cfg(test)] mod NAME;`) and the
    two-line form (`#[cfg(test)]\\nmod NAME;`) commonly used in `lib.rs`.
    Cached per aggregator path. Missing / unreadable aggregators yield
    an empty set.
    """
    cached = _cfg_test_mod_cache.get(aggregator)
    if cached is not None:
        return cached
    if not aggregator.is_file():
        _cfg_test_mod_cache[aggregator] = frozenset()
        return _cfg_test_mod_cache[aggregator]
    try:
        text = aggregator.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        _cfg_test_mod_cache[aggregator] = frozenset()
        return _cfg_test_mod_cache[aggregator]

    lines = text.splitlines()
    names: set[str] = set()
    for i, raw in enumerate(lines):
        m = CFG_TEST_MOD_DECL.search(raw)
        if m:
            names.add(m.group(1))
            continue
        if CFG_TEST.search(raw) and "mod" not in raw:
            for j in range(i + 1, min(i + 5, len(lines))):
                follow = lines[j].strip()
                if not follow or follow.startswith("//"):
                    continue
                mm = re.match(
                    r"(?:pub\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;",
                    follow,
                )
                if mm:
                    names.add(mm.group(1))
                break
    _cfg_test_mod_cache[aggregator] = frozenset(names)
    return _cfg_test_mod_cache[aggregator]


def _is_lib_cfg_test_gated(path: Path) -> bool:
    """Return True if `path` is included as `#[cfg(test)] mod NAME;` in
    the sibling `lib.rs` / `mod.rs` aggregator.
    """
    parent = path.parent
    for aggregator in (parent / "lib.rs", parent / "mod.rs"):
        if path.stem in _cfg_test_mod_names_for(aggregator):
            return True
    return False


def line_is_allow_commented(lines: Sequence[str], idx: int) -> bool:
    """Return True if line `idx` or `idx-1` carries ALLOW_COMMENT."""
    if ALLOW_COMMENT in lines[idx]:
        return True
    # Walk back through the contiguous `//` comment block immediately
    # above the literal (skipping blank lines), up to 8 lines. Allows the
    # escape marker to be paired with a multi-line rationale without
    # requiring it to be literally the prior line.
    LOOKBACK = 8
    j = idx - 1
    steps = 0
    while j >= 0 and steps < LOOKBACK:
        stripped = lines[j].strip()
        if not stripped:
            j -= 1
            steps += 1
            continue
        if not stripped.startswith("//"):
            return False
        if ALLOW_COMMENT in lines[j]:
            return True
        j -= 1
        steps += 1
    return False


def _strip_line_comment(raw: str) -> str:
    """Drop everything after the first `//` on the line (inline comment)."""
    idx = raw.find("//")
    return raw if idx < 0 else raw[:idx]


def _close_stack(scope_stack: List[int], depth: int) -> None:
    """Pop entries from scope_stack while `depth` is below the top target."""
    while scope_stack and depth < scope_stack[-1]:
        scope_stack.pop()


def _update_pending_cfg_test(
    pending: bool, stripped: str, opens: int, closes: int,
) -> bool:
    """Return the new pending state after processing a line.

    `pending=True` means "a #[cfg(test)] attribute is waiting for its
    target item". The attribute is consumed when a braced target
    appears (handled by the caller) or a non-brace target appears on
    this line.
    """
    if not pending:
        return False
    if stripped and not stripped.startswith("#[") and opens == 0 and closes == 0:
        return False  # attribute targeted a non-brace item (use/const)
    return True


def compute_test_gated_lines(lines: Sequence[str]) -> set[int]:
    """Return the 0-indexed line numbers that sit inside a test-only scope.

    A line is "test-gated" when it falls under:
      - A `#[cfg(test)] mod ... { ... }` block (recursive brace tracking).
      - The single item immediately following a `#[cfg(test)]` attribute
        (function / impl / struct / mod / use) until the end of that item.

    Uses a lightweight brace tracker. This is NOT a full Rust parser; it
    intentionally ignores strings/chars and will over-approximate
    test-gated scope in the rare case of braces inside a string literal.
    That bias is safe — it only weakens the guard for pathological input
    and never mis-blames legitimate test code.
    """
    gated: set[int] = set()
    # Each entry records the depth at which a test-gated scope opened;
    # the scope closes when `depth` falls back below that value.
    scope_stack: List[int] = []
    depth = 0
    pending_cfg_test = False  # saw #[cfg(test)] — next braced item is test-only

    for i, raw in enumerate(lines):
        stripped = raw.strip()
        line_is_gated = bool(scope_stack)  # gating BEFORE depth update

        code = _strip_line_comment(raw)
        opens = code.count("{")
        closes = code.count("}")

        if CFG_TEST.search(stripped):
            pending_cfg_test = True

        if pending_cfg_test and opens > 0:
            # Attribute applied to a braced item → register test scope.
            scope_stack.append(depth + 1)
            pending_cfg_test = False
        else:
            pending_cfg_test = _update_pending_cfg_test(
                pending_cfg_test, stripped, opens, closes
            )

        depth += opens
        _close_stack(scope_stack, depth)
        depth -= closes
        _close_stack(scope_stack, depth)

        if line_is_gated or scope_stack:
            gated.add(i)

    return gated


def scan_file(path: Path) -> List[Violation]:
    """Return violations from `path`. Test files return [] immediately."""
    if is_test_file(path):
        return []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as err:
        log.warning("could not read %s: %s", path, err)
        return []

    lines = text.splitlines()
    gated = compute_test_gated_lines(lines)

    out: List[Violation] = []
    for i, line in enumerate(lines):
        # Strip `//` comments before applying the regex so doc-comments
        # (`//!`, `///`) and end-of-line commentary mentioning the
        # literal textually do not generate false positives.
        code = _strip_line_comment(line)
        if not PATTERN.search(code):
            continue
        if i in gated:
            continue
        if line_is_allow_commented(lines, i):
            continue
        out.append(Violation(path=path, lineno=i + 1, line=line.rstrip()))
    return out


def staged_rs_files() -> List[Path]:
    """Return staged .rs files under crates/clean-mathverse/src/."""
    try:
        out = subprocess.check_output(
            ["git", "diff", "--cached", "--name-only", "--diff-filter=ACMRT"],
            text=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    files: List[Path] = []
    for name in out.splitlines():
        name = name.strip()
        if not name.endswith(".rs"):
            continue
        p = Path(name)
        try:
            p.relative_to(MATHVERSE_SRC)
        except ValueError:
            continue
        files.append(p)
    return files


def all_rs_files() -> List[Path]:
    if not MATHVERSE_SRC.is_dir():
        return []
    return sorted(MATHVERSE_SRC.rglob("*.rs"))


def format_violations(vs: Iterable[Violation]) -> str:
    return "\n".join(f"{v.path}:{v.lineno}: {v.line.strip()}" for v in vs)


# ---------------------------------------------------------------------------
# Probe / self-test — delegates to scripts/lint_decl_kind_literal_probes.py.
# ---------------------------------------------------------------------------


def run_probe() -> int:
    """Run the split-out probe battery against this module's scan_file."""
    from lint_decl_kind_literal_probes import run_probe as _run
    return _run(
        scan_fn=scan_file,
        allow_comment=ALLOW_COMMENT,
        cache_clear_hook=_cfg_test_mod_cache.clear,
    )



# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    grp = ap.add_mutually_exclusive_group()
    grp.add_argument(
        "--staged",
        action="store_true",
        help="(default) lint only files staged in git under crates/clean-mathverse/src/",
    )
    grp.add_argument(
        "--all",
        action="store_true",
        help="lint every .rs file under crates/clean-mathverse/src/ (CI mode)",
    )
    grp.add_argument(
        "--probe",
        action="store_true",
        help="run the built-in self-test and exit",
    )
    return ap


def _emit_failure(violations: Sequence[Violation]) -> None:
    log.error("FAIL: `decl_kind: 0` literals found outside #[cfg(test)]:")
    log.error("%s", format_violations(violations))
    log.error(
        "Fix: map from the source-system kind to the correct DeclKind variant "
        "(e.g. DeclKind::Axiom for axioms, DeclKind::Inductive for inductives). "
        "If the literal really is intentional in production, add the comment "
        "`%s` on the line above or the same line.",
        ALLOW_COMMENT,
    )


def main(argv: Sequence[str]) -> int:
    logging.basicConfig(format="%(message)s", level=logging.INFO)
    args = _build_parser().parse_args(argv)

    if args.probe:
        return run_probe()

    mode = "all" if args.all else "staged"
    files = all_rs_files() if args.all else staged_rs_files()

    if not files:
        if mode == "staged":
            return 0  # Nothing staged for this crate — nothing to check.
        log.info("no .rs files found under %s", MATHVERSE_SRC)
        return 0

    violations: List[Violation] = []
    for f in files:
        violations.extend(scan_file(f))

    if not violations:
        log.info(
            "OK: no `decl_kind: 0` literals outside #[cfg(test)] "
            "(%d file(s) scanned, mode=%s)",
            len(files),
            mode,
        )
        return 0

    _emit_failure(violations)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
