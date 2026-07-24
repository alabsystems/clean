#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Summarize TrustBoundary audit records into a Gate 2 measurement report.

Usage:
    python3 scripts/trust_boundary_audit.py \
        --input /tmp/clean-2875-auto.tsv \
        --input /tmp/clean-2875-elab.tsv \
        --expected scripts/trust_boundary_expected_tests.txt \
        --output reports/research/issue-2875-trustboundary-audit-current.md

The TSV columns emitted by the Rust audit lane are:
    lane  crate_name  test_name  tactic  proof_kind  subsystem  description
    step_index  arithmetic_boundary_steps  local_gap_steps  trust_subterm_count
"""

from __future__ import annotations

import argparse
import logging
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

logger = logging.getLogger(__name__)
REPO_ROOT = Path(__file__).resolve().parent.parent


@dataclass
class AuditRecord:
    lane: str
    crate_name: str
    test_name: str
    tactic: str
    proof_kind: str
    subsystem: str
    description: str
    step_index: str
    arithmetic_boundary_steps: int
    local_gap_steps: int
    trust_subterm_count: int


@dataclass
class GroupedHit:
    crate_name: str
    test_name: str
    lane: str
    tactic: str
    proof_kind: str
    subsystem: str
    count: int = 0
    total_arith: int = 0
    total_local_gap: int = 0
    total_trust: int = 0


def repo_relative_path(raw_path: str) -> Path:
    path = Path(raw_path).expanduser()
    if path.is_absolute():
        return path
    return REPO_ROOT / path


def require_regular_file(
    parser: argparse.ArgumentParser, label: str, path: Path
) -> None:
    if not path.exists():
        parser.error(f"{label} path does not exist: {path}")
    if not path.is_file():
        parser.error(f"{label} path is not a file: {path}")


def parse_tsv(path: Path) -> list[AuditRecord]:
    records: list[AuditRecord] = []
    with open(path) as f:
        for line_number, line in enumerate(f, start=1):
            line = line.rstrip("\n")
            if not line:
                continue
            cols = line.split("\t")
            if len(cols) != 11:
                raise ValueError(
                    f"{path}:{line_number}: expected 11 tab-separated columns, "
                    f"got {len(cols)}"
                )
            try:
                arithmetic_boundary_steps = int(cols[8])
                local_gap_steps = int(cols[9])
                trust_subterm_count = int(cols[10])
            except ValueError as exc:
                raise ValueError(
                    f"{path}:{line_number}: columns 9-11 must be integers"
                ) from exc
            records.append(
                AuditRecord(
                    lane=cols[0],
                    crate_name=cols[1],
                    test_name=cols[2],
                    tactic=cols[3],
                    proof_kind=cols[4],
                    subsystem=cols[5],
                    description=cols[6],
                    step_index=cols[7],
                    arithmetic_boundary_steps=arithmetic_boundary_steps,
                    local_gap_steps=local_gap_steps,
                    trust_subterm_count=trust_subterm_count,
                )
            )
    return records


def load_expected_patterns(path: Path) -> list[str]:
    patterns: list[str] = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                patterns.append(line)
    return patterns


def is_expected(test_name: str, patterns: list[str]) -> bool:
    return any(pattern in test_name for pattern in patterns)


def group_records(records: list[AuditRecord]) -> list[GroupedHit]:
    groups: dict[tuple, GroupedHit] = {}
    for r in records:
        key = (r.crate_name, r.test_name, r.lane, r.tactic, r.proof_kind, r.subsystem)
        if key not in groups:
            groups[key] = GroupedHit(
                crate_name=r.crate_name,
                test_name=r.test_name,
                lane=r.lane,
                tactic=r.tactic,
                proof_kind=r.proof_kind,
                subsystem=r.subsystem,
            )
        g = groups[key]
        g.count += 1
        g.total_arith += r.arithmetic_boundary_steps
        g.total_local_gap += r.local_gap_steps
        g.total_trust += r.trust_subterm_count
    return sorted(groups.values(), key=lambda g: (g.crate_name, g.test_name))


def _classify_hits(
    groups: list[GroupedHit],
    expected_patterns: list[str],
) -> tuple[list[GroupedHit], list[GroupedHit]]:
    expected: list[GroupedHit] = []
    unexpected: list[GroupedHit] = []
    for g in groups:
        (
            expected if is_expected(g.test_name, expected_patterns) else unexpected
        ).append(g)
    return expected, unexpected


def _format_hit_table(hits: list[GroupedHit]) -> list[str]:
    return [
        "| Crate | Test | Lane | Tactic | Subsystem | Count | Arith |",
        "|-------|------|------|--------|-----------|-------|-------|",
        *[
            f"| {g.crate_name} | `{g.test_name}` | {g.lane} "
            f"| {g.tactic} | {g.subsystem} | {g.count} | {g.total_arith} |"
            for g in hits
        ],
    ]


def _format_header(input_paths: list[Path]) -> list[str]:
    return [
        "<!-- Andrew Yates <andrewyates.name@gmail.com> -->\n",
        "# Gate 2 TrustBoundary Audit Report\n",
        "**Issue:** #2875\n",
        "**Generated by:** `scripts/trust_boundary_audit.py`\n",
        f"**Input files:** {', '.join(str(p) for p in input_paths)}\n",
        "",
    ]


def _format_recommendation(
    total_raw: int, unexpected_hits: list[GroupedHit]
) -> list[str]:
    lines = ["## Gate 2 Recommendation\n"]
    if total_raw == 0:
        lines.append(
            "**No trust-boundary hits detected.** Gate 2 criterion 5 is effectively met.\n"
        )
    elif not unexpected_hits:
        lines.append(
            f"**All {total_raw} hits are from expected boundary-only tests.** "
            "Gate 2 criterion 5 is effectively met — no common/medium test goals "
            "trigger TrustBoundary on current HEAD.\n"
        )
    else:
        lines.append(
            f"**{sum(g.count for g in unexpected_hits)} unexpected hit(s) found.** "
            "Gate 2 criterion 5 is NOT yet met. File targeted follow-on packets for:\n"
        )
        seen: set[tuple[str, str]] = set()
        for g in unexpected_hits:
            key = (g.crate_name, g.test_name)
            if key not in seen:
                lines.append(f"- `{g.crate_name}::{g.test_name}`")
                seen.add(key)
        lines.append("")
    return lines


RERUN_COMMANDS = """\
## Rerun Commands

```bash
clean_TRUST_BOUNDARY_AUDIT_PATH=/tmp/clean-2875-auto.tsv \\
  cargo test --locked --message-format=short -j 1 -p clean-auto --lib

clean_TRUST_BOUNDARY_AUDIT_PATH=/tmp/clean-2875-elab.tsv \\
  cargo test --locked --message-format=short -j 1 -p clean-elab --lib --features ay-smt

python3 scripts/trust_boundary_audit.py \\
  --input /tmp/clean-2875-auto.tsv \\
  --input /tmp/clean-2875-elab.tsv \\
  --expected scripts/trust_boundary_expected_tests.txt \\
  --output reports/research/issue-2875-trustboundary-audit-current.md
```
"""


def generate_report(
    groups: list[GroupedHit],
    expected_patterns: list[str],
    input_paths: list[Path],
) -> str:
    total_raw = sum(g.count for g in groups)
    by_crate: dict[str, int] = defaultdict(int)
    for g in groups:
        by_crate[g.crate_name] += g.count

    expected_hits, unexpected_hits = _classify_hits(groups, expected_patterns)

    lines = _format_header(input_paths)
    lines.append("## Summary\n")
    lines.append(f"- **Total raw hits:** {total_raw}")
    for crate_name in sorted(by_crate):
        lines.append(f"  - `{crate_name}`: {by_crate[crate_name]}")
    lines.append(
        f"- **Expected boundary-only hits:** {sum(g.count for g in expected_hits)}"
    )
    lines.append(f"- **Unexpected hits:** {sum(g.count for g in unexpected_hits)}")
    lines.append("")

    if unexpected_hits:
        lines.append("## Unexpected Hits\n")
        lines.append(
            "These hits were NOT matched by any pattern in "
            "`scripts/trust_boundary_expected_tests.txt`.\n"
        )
        lines.extend(_format_hit_table(unexpected_hits))
        lines.append("")

    if expected_hits:
        lines.append("## Expected Boundary-Only Hits\n")
        lines.append(
            "These hits matched patterns in "
            "`scripts/trust_boundary_expected_tests.txt` and are expected.\n"
        )
        lines.extend(_format_hit_table(expected_hits))
        lines.append("")

    lines.extend(_format_recommendation(total_raw, unexpected_hits))
    lines.append(RERUN_COMMANDS)

    return "\n".join(lines)


def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    parser = argparse.ArgumentParser(
        description="Summarize TrustBoundary audit records"
    )
    parser.add_argument(
        "--input", action="append", required=True, help="TSV audit file(s)"
    )
    parser.add_argument(
        "--expected", required=True, help="Expected boundary-only test patterns"
    )
    parser.add_argument("--output", required=True, help="Output Markdown report path")
    args = parser.parse_args()

    input_paths = [repo_relative_path(p) for p in args.input]
    expected_path = repo_relative_path(args.expected)
    output_path = repo_relative_path(args.output)

    for p in input_paths:
        require_regular_file(parser, "--input", p)
    require_regular_file(parser, "--expected", expected_path)

    all_records: list[AuditRecord] = []
    try:
        for p in input_paths:
            all_records.extend(parse_tsv(p))
        expected_patterns = load_expected_patterns(expected_path)
    except ValueError as exc:
        parser.error(str(exc))

    groups = group_records(all_records)
    report = generate_report(groups, expected_patterns, input_paths)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(report)
    logger.info(
        "Report written to %s (%d groups, %d total hits)",
        output_path,
        len(groups),
        sum(g.count for g in groups),
    )


if __name__ == "__main__":
    main()
