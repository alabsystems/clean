#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Read one `clean check --json` report into per-declaration verdicts.

Moved verbatim from family_gate.py on 2026-10-27 (item 17) so that the gate
file stops growing; family_gate.py re-exports every name, so callers and
scripts/test_family_gate.py are unchanged. Pure functions: no process, no
file. The row grammar (DECL_RE) is lean_verdicts.py's, shared with the sealed
LEAN_VERDICTS.json and its minter.
"""

from __future__ import annotations

import json
import re

from lean_verdicts import DECL_RE


def extract_json_report(stdout: str) -> dict | None:
    lines = stdout.splitlines()
    for i, line in enumerate(lines):
        if line.strip() == "{" or line.startswith('{"'):
            try:
                return json.loads("\n".join(lines[i:]))
            except json.JSONDecodeError:
                return None
    return None


def attribute_failures(report: dict, names: list[str], fixture_text: str) -> tuple[set[str], list[str]]:
    """Attribute the report's failures to declarations. Returns (failed
    names, unattributable failure strings). Attribution uses (a) the
    `NAME:`-prefixed trust/kernel failure rows, (b) proof_state_feedback's
    declaration field, (c) `at line L` positions mapped through the fixture's
    declaration start lines, (d) a whole-word name scan — for ATTRIBUTION
    only, never for success."""
    failed: set[str] = set()
    unattributed: list[str] = []
    name_set = set(names)

    # Declaration start lines (1-indexed) for positional attribution.
    decl_lines: list[tuple[int, str]] = []
    for m in DECL_RE.finditer(fixture_text):
        line_no = fixture_text.count("\n", 0, m.start()) + 1
        decl_lines.append((line_no, m.group(1)))
    decl_lines.sort()

    def decl_at_line(line_no: int) -> str | None:
        best = None
        for start, name in decl_lines:
            if start <= line_no:
                best = name
            else:
                break
        return best

    for row in report.get("trust_failures", []) + report.get("kernel_failures", []):
        name = row.split(":", 1)[0].strip()
        if name in name_set:
            failed.add(name)
        else:
            unattributed.append(row)

    for fb in report.get("proof_state_feedback", []):
        decl = fb.get("declaration")
        if decl in name_set:
            failed.add(decl)

    line_re = re.compile(r"at line (\d+)")
    for err in report.get("errors", []):
        m = line_re.search(err)
        if m:
            name = decl_at_line(int(m.group(1)))
            if name in name_set:
                failed.add(name)
                continue
        hits = [n for n in names if re.search(rf"\b{re.escape(n)}\b", err)]
        if hits:
            failed.update(hits)
        else:
            unattributed.append(err)

    return failed, unattributed


def attribute_diverged(report: dict, names: list[str]) -> tuple[set[str], list[str]]:
    """Attribute the report's `diverged` rows to declarations.

    A diverged declaration spent its whole `--decl-budget` without finishing.
    It is NEITHER a pass (nothing was proved) NOR a fail (nothing was refuted),
    so it gets its own bucket here and its own row verdict; the caller must not
    fold it into either. `clean check` writes each row as
    `NAME: did not finish at line L — spent the whole per-declaration budget
    of N kernel operations (...)`, the same `NAME:` prefix convention as the
    trust/kernel failure rows.

    Returns (diverged names, unattributable rows). An unattributable row fails
    the gate upstream exactly like an unattributable failure: a verdict that
    cannot be read back to a declaration is not a verdict.
    """
    diverged: set[str] = set()
    unattributed: list[str] = []
    name_set = set(names)
    for row in report.get("diverged", []):
        name = row.split(":", 1)[0].strip()
        if name in name_set:
            diverged.add(name)
        else:
            unattributed.append(row)
    return diverged, unattributed


def classify_file_verdicts(
    report: dict, names: list[str], fixture_text: str, label: str
) -> tuple[dict[str, str], list[str]]:
    """The three-way per-declaration verdict for one fixture file.

    Returns `({name: "pass"|"fail"|"diverged"}, problems)`. A non-empty
    `problems` means the file produced NO usable verdicts — the caller must
    record the problems as gate failures and skip the file's rows entirely,
    never fall back to a partial reading.

    This is the arithmetic that keeps `diverged` honest, and it is a separate
    function so it can be exercised without a binary (scripts/test_family_gate.py):

      * `fail` and `diverged` must be disjoint. `clean check` rolls a diverged
        declaration's errors back before recording it (`rollback_as_diverged`),
        so an overlap means the report contradicts itself.
      * the names left over — neither failed nor diverged — must number
        EXACTLY `success_count`. This is the load-bearing check: it is what
        makes folding `diverged` into `pass` (or dropping it on the floor)
        impossible to do quietly, because the binary's own success count then
        stops matching.
    """
    problems: list[str] = []
    failed, unattributed = attribute_failures(report, names, fixture_text)
    diverged, diverged_unattributed = attribute_diverged(report, names)
    unattributed = unattributed + diverged_unattributed

    both = sorted(failed & diverged)
    if both:
        problems.append(
            f"{label}: report lists {both} as BOTH failed and diverged — "
            f"contradictory verdicts, so neither is a measurement"
        )
        return {}, problems

    passed = [n for n in names if n not in failed and n not in diverged]
    success_count = report.get("success_count")
    if len(passed) != success_count:
        problems.append(
            f"{label}: verdict attribution mismatch — binary reports "
            f"success_count={success_count} but {len(passed)} declarations have no "
            f"attributed failure or divergence (unattributable: {unattributed[:3]}). A "
            f"verdict that cannot be read from the declaration fails the gate "
            f"(§7.2 property 5)."
        )
        return {}, problems

    verdicts = {
        n: ("fail" if n in failed else "diverged" if n in diverged else "pass")
        for n in names
    }
    return verdicts, problems
