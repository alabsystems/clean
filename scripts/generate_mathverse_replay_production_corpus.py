#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Generate fail-closed Mathverse replay production-corpus coverage evidence."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "reports" / "mathverse-replay-production-corpus.json"
SCAN_ROOTS = [
    REPO_ROOT / "data" / "raw" / "mathlib4" / "Mathlib",
    REPO_ROOT
    / "data"
    / "raw"
    / "mathlib4"
    / ".lake"
    / "packages"
    / "batteries"
    / "BatteriesTest"
    / "mathverse",
]
UNSUPPORTED_REPLAY_SAMPLE_PER_SOURCE = 4

TACTIC_PATTERNS = [
    re.compile(r"\bby\s*\(?\s*mathverse\b"),
    re.compile(r"(?:^|[;<|>(]\s*)mathverse\b"),
    re.compile(r"\bfail_if_success\s+mathverse\b"),
]


def _strip_line_comment(line: str) -> str:
    return line.split("--", 1)[0]


def _is_mathverse_tactic_line(line: str) -> bool:
    code = _strip_line_comment(line)
    return any(pattern.search(code) for pattern in TACTIC_PATTERNS)


def _outcome_for(line: str) -> str:
    if "fail_if_success mathverse" in line:
        return "rejected"
    return "unsupported"


def _source_label(path: Path) -> str:
    rel = path.relative_to(REPO_ROOT).as_posix()
    if rel.startswith("data/raw/mathlib4/Mathlib/"):
        return "mathlib4"
    return "batteries-mathverse-benchmark"


def _source_shape(line: str) -> str:
    code = _strip_line_comment(line).strip()
    if code.startswith("example "):
        return "standalone_example"
    if ":= by" in code or " := by" in code:
        return "inline_by_tactic"
    if code == "mathverse" or code.startswith("mathverse "):
        return "tactic_block_line"
    if "by mathverse" in code:
        return "default_argument_or_inline_tactic"
    return "lean_source_line"


def _replay_smoke_for(obligation: dict[str, object], line: str) -> dict[str, object]:
    """Return a conservative per-obligation replay-smoke diagnostic.

    This is intentionally fail-closed: a sampled production obligation only gets
    native/applied credit after a real cleanNative shard plus strict mathverse_use
    application path exists for that exact obligation.
    """

    return {
        "id": obligation["id"],
        "source": obligation["source"],
        "path": obligation["path"],
        "line": obligation["line"],
        "source_shape": _source_shape(line),
        "line_excerpt": line.strip(),
        "replay_status": "unsupported",
        "native_gate_verified": False,
        "applied_through_strict_mathverse_use": False,
        "strict_replay_attempted": False,
        "fail_closed_reasons": [
            "No current production-obligation extractor lowers this Lean4 mathverse tactic site into a clean ProofState goal.",
            "No per-obligation cleanNative Mathverse shard is generated for this source location.",
            "The strict mathverse_use application gate only accepts an already native-gate-verified MathverseLibrary candidate for the active clean kernel goal.",
        ],
        "required_for_credit": [
            "extract the exact production goal and local hypotheses into clean kernel expressions",
            "build or locate a cleanNative shard declaration for that obligation",
            "verify the shard through the native gate",
            "close the extracted goal through default strict mathverse_use",
        ],
    }


def build_report() -> dict:
    obligations: list[dict[str, object]] = []
    source_lines: dict[str, str] = {}
    for root in SCAN_ROOTS:
        for path in sorted(root.rglob("*.lean")):
            rel = path.relative_to(REPO_ROOT).as_posix()
            for lineno, line in enumerate(
                path.read_text(encoding="utf-8").splitlines(), 1
            ):
                if not _is_mathverse_tactic_line(line):
                    continue
                outcome = _outcome_for(line)
                obligations.append(
                    {
                        "id": f"{rel}:{lineno}",
                        "source": _source_label(path),
                        "path": rel,
                        "line": lineno,
                        "outcome": outcome,
                    }
                )
                source_lines[f"{rel}:{lineno}"] = line

    by_outcome = Counter(obligation["outcome"] for obligation in obligations)
    by_source = Counter(obligation["source"] for obligation in obligations)
    counts = {
        "found": len(obligations),
        "native_gate_verified": 0,
        "applied_through_strict_mathverse_use": 0,
        "rejected": by_outcome["rejected"],
        "unsupported": by_outcome["unsupported"],
    }
    unsupported_by_source: dict[str, list[dict[str, object]]] = {}
    for obligation in obligations:
        if obligation["outcome"] != "unsupported":
            continue
        unsupported_by_source.setdefault(str(obligation["source"]), []).append(
            obligation
        )

    replay_smoke_attempts = []
    for source in sorted(unsupported_by_source):
        for obligation in unsupported_by_source[source][
            :UNSUPPORTED_REPLAY_SAMPLE_PER_SOURCE
        ]:
            replay_smoke_attempts.append(
                _replay_smoke_for(obligation, source_lines[str(obligation["id"])])
            )

    return {
        "schema_version": "clean-mathverse-replay-production-corpus-v1",
        "generated_by": "scripts/generate_mathverse_replay_production_corpus.py",
        "deterministic": True,
        "status": "incomplete",
        "claim": (
            "Fixed local Mathlib/Batteries Mathverse tactic corpus was enumerated and "
            "classified with deterministic per-obligation replay-smoke diagnostics. "
            "No production corpus obligation is native-gate verified or applied "
            "through strict mathverse_use yet."
        ),
        "scan_roots": [root.relative_to(REPO_ROOT).as_posix() for root in SCAN_ROOTS],
        "classification": {
            "found": "line contains a syntactic mathverse tactic invocation in a scanned production/upstream Lean file",
            "native_gate_verified": "obligation replayed through the cleanNative Mathverse shard gate",
            "applied_through_strict_mathverse_use": "obligation closed by default strict mathverse_use after native-gate verification",
            "rejected": "source intentionally expects mathverse failure via fail_if_success mathverse",
            "unsupported": "found production/upstream mathverse tactic with no generated replay runner result yet",
        },
        "counts": counts,
        "by_source": dict(sorted(by_source.items())),
        "by_outcome": dict(sorted(by_outcome.items())),
        "replay_smoke": {
            "mode": "fail_closed_sampled_per_obligation_diagnostics",
            "sample_per_source": UNSUPPORTED_REPLAY_SAMPLE_PER_SOURCE,
            "sampled_obligation_count": len(replay_smoke_attempts),
            "strict_replay_attempted": 0,
            "native_gate_verified": 0,
            "applied_through_strict_mathverse_use": 0,
            "unsupported": len(replay_smoke_attempts),
            "attempts": replay_smoke_attempts,
        },
        "sample_obligations": obligations[:25],
        "obligation_count": len(obligations),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    report = build_report()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
