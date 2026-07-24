#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Self-test probes for `lint_decl_kind_literal.py`.

Split out of the main lint module to keep it under the 500-line
per-file limit. Not invoked directly — `lint_decl_kind_literal.py
--probe` loads and runs the entry points here.

Probe coverage:

- Violations fire on `decl_kind: 0` and `decl_kind: 0u8`.
- Non-zero / typed-variant literals do NOT fire.
- `#[cfg(test)] mod tests { ... }` block exempts contents.
- Single-item `#[cfg(test)]` attribute (e.g. `fn test_only()`)
  exempts contents.
- `// allow: decl_kind-literal` on the literal line, the line
  above, or anywhere in the contiguous `//` comment block
  immediately above the literal (up to 8 lines) exempts.
- `//!` / `///` doc comments that mention the anti-pattern
  textually do not fire (comment-strip on match line).
- Test-named files (`tests_*.rs`, `*_tests.rs`, `tests.rs`, anything
  under `tests/`) are exempt.
- `#[cfg(test)] mod NAME;` in a sibling `lib.rs` / `mod.rs`
  aggregator (single-line AND split-line forms) exempts the target
  file even when the file body carries no `#[cfg(test)]` marker.
- Ungated siblings still fire in the lib.rs-cfg-test case.
"""

from __future__ import annotations

import logging
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path

log = logging.getLogger("lint_decl_kind_literal_probes")


# ---------------------------------------------------------------------------
# Fixtures — Rust source snippets exercised by the probe.
# ---------------------------------------------------------------------------

PROBE_VIOLATION = """\
// Fabricated production file — lint probe
fn make_bad() -> Header {
    Header { decl_kind: 0 }
}
"""

PROBE_VIOLATION_TYPED = """\
// Fabricated production file — typed 0u8 literal
fn make_typed_bad() -> Header {
    Header { decl_kind: 0u8 }
}
"""

PROBE_NON_MATCHING = """\
// Typed non-zero literal AND explicit DeclKind variant — neither is a match.
fn make_ok() -> Header {
    let _ = Header { decl_kind: 0xff };
    Header { decl_kind: crate::types::DeclKind::Axiom as u8 }
}
"""

PROBE_ALLOWED_CFG_TEST_MOD = """\
fn make_good() -> Header {
    Header { decl_kind: 0xff }
}

#[cfg(test)]
mod tests {
    fn fabricated_test() {
        let h = Header { decl_kind: 0 };
        let _ = h;
    }
}
"""

PROBE_ALLOWED_COMMENT = """\
fn make_scratch() -> Header {
    // allow: decl_kind-literal
    Header { decl_kind: 0 }
}
"""

PROBE_ALLOWED_CFG_TEST_FN = """\
#[cfg(test)]
fn test_only() {
    let h = Header { decl_kind: 0 };
    let _ = h;
}
"""

PROBE_ALLOWED_MULTILINE_COMMENT = """\
fn make_legacy() -> Header {
    // allow: decl_kind-literal
    // Multi-line rationale: this is a legacy / backward-compat path where
    // the decl_kind byte did not exist and is reconstructed as 0.
    Header { decl_kind: 0 }
}
"""

PROBE_DOC_COMMENT = """\
//! Module docs: the old writers hardcoded `decl_kind: 0` here.
/// Summary that also says decl_kind: 0 in passing.
fn make_ok_doc() -> Header {
    Header { decl_kind: crate::types::DeclKind::Axiom as u8 }
}
"""

PROBE_LIB_CFG_TEST_SINGLE = """\
pub mod production_mod;

#[cfg(test)] mod test_only_child;
"""

PROBE_LIB_CFG_TEST_SPLIT = """\
pub mod production_mod;

#[cfg(test)]
mod test_only_child;
"""


# ---------------------------------------------------------------------------
# Probe case definition + evaluator.
# ---------------------------------------------------------------------------


@dataclass
class ProbeCase:
    label: str
    filename: str
    body: str
    expect_hit_line: int  # 0 means "expect no hits"


_TEST_NAMED_FILES: tuple[str, ...] = (
    "tests_foo.rs",
    "foo_tests.rs",
    "tests.rs",
    "tests" + os.sep + "nested.rs",
)


def _write_probe(tmp: Path, name: str, body: str) -> Path:
    p = tmp / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8")
    return p


def _build_probe_cases(allow_comment: str) -> tuple[ProbeCase, ...]:
    return (
        ProbeCase(
            "fires on production decl_kind: 0",
            "prod_bad.rs", PROBE_VIOLATION, expect_hit_line=3,
        ),
        ProbeCase(
            "fires on production decl_kind: 0u8 (typed)",
            "prod_bad_u8.rs", PROBE_VIOLATION_TYPED, expect_hit_line=3,
        ),
        ProbeCase(
            "does not fire on decl_kind: 0xff or DeclKind::X as u8",
            "prod_ok_nonmatch.rs", PROBE_NON_MATCHING, expect_hit_line=0,
        ),
        ProbeCase(
            "allows decl_kind: 0 inside #[cfg(test)] mod tests { ... }",
            "prod_ok_mod.rs", PROBE_ALLOWED_CFG_TEST_MOD, expect_hit_line=0,
        ),
        ProbeCase(
            "allows decl_kind: 0 inside single #[cfg(test)] fn item",
            "prod_ok_fn.rs", PROBE_ALLOWED_CFG_TEST_FN, expect_hit_line=0,
        ),
        ProbeCase(
            f"allows decl_kind: 0 when preceded by `{allow_comment}`",
            "prod_ok_comment.rs", PROBE_ALLOWED_COMMENT, expect_hit_line=0,
        ),
        ProbeCase(
            "does not fire on decl_kind: 0 text inside `//!` / `///` comments",
            "prod_ok_doc.rs", PROBE_DOC_COMMENT, expect_hit_line=0,
        ),
        ProbeCase(
            "allows decl_kind: 0 with multi-line rationale under allow comment",
            "prod_ok_multiline.rs",
            PROBE_ALLOWED_MULTILINE_COMMENT, expect_hit_line=0,
        ),
    )


def _evaluate_case(root: Path, case: ProbeCase, scan_fn) -> tuple[bool, str]:
    path = _write_probe(root, case.filename, case.body)
    vs = scan_fn(path)
    if case.expect_hit_line == 0:
        return (vs == [], f"unexpected hits: {vs!r}")
    ok = len(vs) == 1 and vs[0].lineno == case.expect_hit_line
    return (ok, f"got {vs!r}")


def _evaluate_test_file_names(root: Path, scan_fn) -> list[tuple[str, bool, str]]:
    results: list[tuple[str, bool, str]] = []
    for fname in _TEST_NAMED_FILES:
        path = _write_probe(root, fname, PROBE_VIOLATION)
        vs = scan_fn(path)
        results.append((
            f"test-named file exempt: {path.name}",
            vs == [],
            f"hits: {vs!r}",
        ))
    return results


def _evaluate_lib_cfg_test_cases(root: Path, scan_fn) -> list[tuple[str, bool, str]]:
    """Return (label, pass, detail) for lib.rs cfg-test gating cases."""
    results: list[tuple[str, bool, str]] = []
    for idx, (aggregator_body, label) in enumerate((
        (PROBE_LIB_CFG_TEST_SINGLE, "single-line"),
        (PROBE_LIB_CFG_TEST_SPLIT, "split-line"),
    )):
        subdir = root / f"crate_{idx}"
        subdir.mkdir(parents=True, exist_ok=True)
        (subdir / "lib.rs").write_text(aggregator_body, encoding="utf-8")
        test_child = subdir / "test_only_child.rs"
        test_child.write_text(PROBE_VIOLATION, encoding="utf-8")
        prod_child = subdir / "production_mod.rs"
        prod_child.write_text(PROBE_VIOLATION, encoding="utf-8")

        vs_test = scan_fn(test_child)
        vs_prod = scan_fn(prod_child)

        results.append((
            f"lib.rs {label} cfg(test) mod NAME; exempts target file",
            vs_test == [],
            f"hits on gated child: {vs_test!r}",
        ))
        results.append((
            f"lib.rs {label} ungated sibling still fires",
            len(vs_prod) == 1 and vs_prod[0].lineno == 3,
            f"hits on ungated sibling: {vs_prod!r}",
        ))
    return results


def run_probe(scan_fn, allow_comment: str, cache_clear_hook=None) -> int:
    """Execute the full probe battery. Returns 0 on success, 1 on failure.

    `scan_fn` is the importer's scan_file(path: Path) -> List[Violation].
    `allow_comment` is the exact escape marker string (shown in labels).
    `cache_clear_hook` is optional; when provided, it is called between
    the test-named-file and lib.rs-cfg-test groups so cached cfg(test)
    aggregator state from earlier cases cannot leak.
    """
    log.info("=== decl_kind: 0 lint probe ===")
    fail = 0
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        for case in _build_probe_cases(allow_comment):
            ok, detail = _evaluate_case(root, case, scan_fn)
            if ok:
                log.info("  PASS: %s", case.label)
            else:
                log.error("  FAIL: %s  %s", case.label, detail)
                fail += 1
        for label, ok, detail in _evaluate_test_file_names(root, scan_fn):
            if ok:
                log.info("  PASS: %s", label)
            else:
                log.error("  FAIL: %s  %s", label, detail)
                fail += 1
        if cache_clear_hook is not None:
            cache_clear_hook()
        for label, ok, detail in _evaluate_lib_cfg_test_cases(root, scan_fn):
            if ok:
                log.info("  PASS: %s", label)
            else:
                log.error("  FAIL: %s  %s", label, detail)
                fail += 1

    if fail:
        log.error("PROBE FAILED (%d assertion(s))", fail)
        return 1
    log.info("PROBE PASSED")
    return 0
