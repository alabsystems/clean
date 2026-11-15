#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Hold data/upstream_soundness_intake.json to the tree it describes.

The ledger is the standing intake of every summer/October-2026 upstream Lean 4
kernel soundness report, with Clean's disposition and the path:line that proves
it. A report that is forgotten, or a disposition that rots because the guard it
points at moved or was deleted, is how Clean would silently fall behind
upstream. This script is that check.

For every row it verifies these things, reading the cited files only as DATA
(it checks that a line exists, never what the line says -- no verdict is minted
from any source text):

1. ``evidence`` is ``path:line`` and resolves: the file exists under the repo
   root and has at least ``line`` lines.
2. a non-null ``fixture`` appears in the replay_forged ``ORDER`` as a
   ``run GenReplayForged.lean <Out>.olean <fixture>`` argument -- i.e. the
   family the row names actually exists in the battery's recipe.
3. a row where the pinned oracle ACCEPTS the forgery (``oracle_verdict``
   contains ``ACCEPTS``), and every ``clean-accepts-live-hole`` row, carries a
   non-empty ``decision`` that names a heading present in ``docs/DECISIONS.md``.
   The differential oracle cannot catch such an exploit, so the row must point
   at the recorded entry that says what Clean does about it, never silently.
4. ``clean_disposition`` is one of the ledger's declared ``dispositions``.
5. a ``clean-accepts-live-hole`` row (Clean was measured to admit the exploit)
   carries ``priority: "P0"``, so a live soundness hole cannot be filed low.
6. a ``not-affected`` row never carries an ``oracle_verdict`` that says
   ``NOT MEASURED``: an unmeasured row is ``unmeasured``, not a claim that
   Clean is safe.
7. a non-empty ``decision`` names exactly ONE heading. Two lanes that take the
   same number (2026-10-20: a branch's R86 beside origin/main's R86) merge
   into two headings without a conflict, and a set of heading tokens would
   still resolve every row that cites either.

This checker never asserts that Clean refuses anything. A refusal is claimed
only by a lane test that runs Clean on the fixture; a ledger row is a pointer.

Usage:
    python3 scripts/check_upstream_soundness_intake.py [--check]
    python3 scripts/check_upstream_soundness_intake.py --self-test

``--self-test`` runs first in the gate leg. It drives every predicate on a
synthetic ledger and confirms each refusal still fires (an unresolved
path:line; a fixture missing from ORDER; an oracle-ACCEPTS row whose decision
names no DECISIONS heading; an undeclared disposition; a live hole filed below
P0; a not-affected row that was never measured). It prints
``self-test ARM FAILED: ...`` and exits 1 if any arm stops firing.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = "data/upstream_soundness_intake.json"
DEFAULT_ORDER = (
    "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/replay_forged/ORDER"
)
DEFAULT_DECISIONS = "docs/DECISIONS.md"
# Clean was MEASURED to admit the exploit: a live soundness hole.
LIVE_HOLE = "clean-accepts-live-hole"

# `run GenReplayForged.lean <Out>.olean <family>` -- the family is the last word.
_ORDER_RUN = re.compile(
    r"^\s*run\s+GenReplayForged\.lean\s+\S+\.olean\s+(?P<fam>\S+)\s*$"
)
# A DECISIONS heading like `### R81. ...` or the pre-landing `### R-EXPLOITS ...`.
_HEADING = re.compile(r"^#{1,6}\s+(?P<tok>R-?[A-Za-z0-9_-]+)\b")


def order_families(order_text: str) -> set[str]:
    """Every family name an ORDER `run GenReplayForged.lean` step mints."""
    out: set[str] = set()
    for line in order_text.splitlines():
        m = _ORDER_RUN.match(line)
        if m:
            out.add(m.group("fam"))
    return out


def decision_tokens(decisions_text: str) -> Counter[str]:
    """Every `R<...>` heading token in DECISIONS.md, with how many headings
    carry it (the archive's R12/R13/R15 appear twice; no row cites them)."""
    out: Counter[str] = Counter()
    for line in decisions_text.splitlines():
        m = _HEADING.match(line)
        if m:
            out[m.group("tok")] += 1
    return out


def resolve_evidence(root: Path, evidence: str) -> str | None:
    """None when `path:line` resolves; else a one-line reason."""
    if not isinstance(evidence, str) or ":" not in evidence:
        return f"evidence is not `path:line`: {evidence!r}"
    path_str, _, line_str = evidence.rpartition(":")
    try:
        line = int(line_str)
    except ValueError:
        return f"evidence line is not an integer: {evidence!r}"
    if line < 1:
        return f"evidence line must be >= 1: {evidence!r}"
    target = root / path_str
    if not target.is_file():
        return f"evidence path does not resolve: {path_str}"
    # Read as DATA: count lines only, never inspect their content.
    try:
        with target.open("rb") as handle:
            count = sum(1 for _ in handle)
    except OSError as error:  # pragma: no cover - unreadable file
        return f"cannot read {path_str}: {error}"
    if count < line:
        return f"evidence line {line} is past EOF ({count} lines): {path_str}"
    return None


def oracle_accepts(row: dict) -> bool:
    """The pinned differential oracle admits the forgery (it cannot catch it)."""
    return "ACCEPTS" in str(row.get("oracle_verdict", ""))


def needs_decision(row: dict) -> bool:
    return oracle_accepts(row) or row.get("clean_disposition") == LIVE_HOLE


def check_rows(
    root: Path,
    rows: list[dict],
    families: set[str],
    decisions: Counter[str],
    dispositions: set[str],
) -> list[str]:
    """Every problem, one string per failing (row, clause)."""
    problems: list[str] = []
    seen_ids: set[str] = set()
    for row in rows:
        rid = str(row.get("id", "<no id>"))
        if rid in seen_ids:
            problems.append(f"row {rid}: duplicate id")
        seen_ids.add(rid)

        evidence = row.get("evidence", "")
        reason = resolve_evidence(root, evidence)
        if reason is not None:
            problems.append(f"row {rid}: {reason}")

        fixture = row.get("fixture")
        if fixture is not None:
            if fixture not in families:
                problems.append(
                    f"row {rid}: fixture {fixture!r} is not minted by any "
                    f"`run GenReplayForged.lean` step in ORDER"
                )

        disposition = row.get("clean_disposition")
        if disposition not in dispositions:
            problems.append(
                f"row {rid}: clean_disposition {disposition!r} is not one of "
                f"the ledger's declared dispositions"
            )
        if disposition == LIVE_HOLE and row.get("priority") != "P0":
            problems.append(
                f"row {rid}: a {LIVE_HOLE} row must carry priority P0, "
                f"got {row.get('priority')!r}"
            )
        if disposition == "not-affected" and "NOT MEASURED" in str(
            row.get("oracle_verdict", "")
        ):
            problems.append(
                f"row {rid}: not-affected but the oracle_verdict says NOT "
                f"MEASURED -- record it as `unmeasured`"
            )

        if needs_decision(row):
            decision = row.get("decision")
            if not decision:
                problems.append(
                    f"row {rid}: oracle ACCEPTS or a live hole, but `decision` "
                    f"is empty -- the recorded DECISIONS entry is required"
                )
            elif decision not in decisions:
                problems.append(
                    f"row {rid}: `decision` {decision!r} names no heading in "
                    f"docs/DECISIONS.md"
                )
        cited = row.get("decision")
        if cited and decisions.get(cited, 0) > 1:
            problems.append(
                f"row {rid}: `decision` {cited!r} names {decisions[cited]} "
                f"headings in docs/DECISIONS.md -- renumber one of them"
            )
    return problems


def load_ledger(root: Path) -> dict:
    with (root / LEDGER).open(encoding="utf-8") as handle:
        return json.load(handle)


def read_text(root: Path, rel: str) -> str:
    return (root / rel).read_text(encoding="utf-8")


def check(root: Path = ROOT) -> list[str]:
    ledger = load_ledger(root)
    rows = ledger.get("rows", [])
    if not isinstance(rows, list) or not rows:
        return ["ledger has no rows"]
    order_rel = ledger.get("fixture_order", DEFAULT_ORDER)
    decisions_rel = ledger.get("decisions", DEFAULT_DECISIONS)
    missing = [
        rel
        for rel in (order_rel, decisions_rel)
        if not (root / rel).is_file()
    ]
    if missing:
        return [f"ledger references a missing file: {rel}" for rel in missing]
    families = order_families(read_text(root, order_rel))
    decisions = decision_tokens(read_text(root, decisions_rel))
    dispositions = {str(d) for d in ledger.get("dispositions", [])}
    if not dispositions:
        return ["ledger declares no dispositions"]
    return check_rows(root, rows, families, decisions, dispositions)


def self_test() -> int:
    failures: list[str] = []

    def arm(name: str, ok: bool, detail: str = "") -> None:
        print(f"  self-test ARM {'ok' if ok else 'FAILED'}: {name}"
              + (f" -- {detail}" if detail and not ok else ""))
        if not ok:
            failures.append(name)

    families = {"honestIsPropStuck", "forgedDeltaPropLargeElim"}
    decisions = Counter({"R-EXPLOITS": 1, "R37": 1, "R80": 1})
    dispositions = {"fixture", "not-affected", "unmeasured", LIVE_HOLE}

    def run(rows: list[dict], heads: Counter[str] = decisions) -> list[str]:
        return check_rows(ROOT, rows, families, heads, dispositions)

    good = [
        {
            "id": "ok-oracle-accepts",
            "clean_disposition": LIVE_HOLE,
            "priority": "P0",
            "evidence": f"{LEDGER}:1",
            "fixture": "honestIsPropStuck",
            "oracle_verdict": "v4.30.0-rc2 leanchecker ACCEPTS",
            "decision": "R-EXPLOITS",
        },
        {
            "id": "ok-plain",
            "clean_disposition": "not-affected",
            "evidence": f"{LEDGER}:1",
            "fixture": None,
            "oracle_verdict": "n/a",
        },
    ]
    arm("a well-formed ledger passes", run(good) == [], "; ".join(run(good)))

    # Arm 1: an unresolved path:line is refused.
    bad_path = [dict(good[0], evidence="crates/clean-kernel/src/does_not_exist.rs:1")]
    arm(
        "an unresolved evidence path:line is refused",
        any("does not resolve" in p for p in run(bad_path)),
    )
    bad_line = [dict(good[0], evidence=f"{LEDGER}:99999999")]
    arm(
        "an evidence line past EOF is refused",
        any("past EOF" in p for p in run(bad_line)),
    )

    # Arm 2: a fixture missing from ORDER is refused.
    bad_fixture = [dict(good[0], fixture="forgedNeverMinted")]
    arm(
        "a fixture missing from ORDER is refused",
        any("is not minted" in p for p in run(bad_fixture)),
    )

    # Arm 3: an oracle-ACCEPTS row whose decision names no heading is refused.
    bad_decision = [dict(good[0], decision="R-NOPE")]
    arm(
        "an oracle-ACCEPTS row whose decision names no DECISIONS heading is refused",
        any("names no heading" in p for p in run(bad_decision)),
    )
    empty_decision = [dict(good[0], decision="")]
    arm(
        "an oracle-ACCEPTS row with an empty decision is refused",
        any("decision` is empty" in p for p in run(empty_decision)),
    )
    hole_no_decision = [
        dict(good[0], oracle_verdict="leanchecker refuses", decision="")
    ]
    arm(
        "a live-hole row needs a decision even when the oracle refuses",
        any("decision` is empty" in p for p in run(hole_no_decision)),
    )

    # Arm 4: an undeclared disposition is refused.
    bad_disposition = [dict(good[1], clean_disposition="fixture-must-refuse")]
    arm(
        "an undeclared clean_disposition is refused",
        any("declared dispositions" in p for p in run(bad_disposition)),
    )

    # Arm 5: a live hole filed below P0 is refused.
    low_hole = [dict(good[0], priority="P2")]
    arm(
        "a live-hole row without priority P0 is refused",
        any("must carry priority P0" in p for p in run(low_hole)),
    )

    # Arm 6: a not-affected row that was never measured is refused.
    unmeasured_safe = [dict(good[1], oracle_verdict="NOT MEASURED on this box")]
    arm(
        "a not-affected row whose oracle_verdict is NOT MEASURED is refused",
        any("record it as `unmeasured`" in p for p in run(unmeasured_safe)),
    )

    # Arm 7: a decision two headings carry is refused, for any row citing it.
    twice = Counter(decisions)
    twice["R-EXPLOITS"] = 2
    arm(
        "a decision that names two DECISIONS headings is refused",
        any("names 2 headings" in p for p in run([dict(good[0])], twice)),
    )
    arm(
        "a non-ACCEPTS row citing a duplicated heading is refused too",
        any("names 2 headings" in p
            for p in run([dict(good[1], decision="R-EXPLOITS")], twice)),
    )

    # Negative controls: an ordinary row needs no decision, and an honest
    # `unmeasured` row is accepted.
    arm("a row with no oracle ACCEPTS and no live hole needs no decision",
        run([dict(good[1])]) == [])
    honest_unmeasured = [
        dict(good[1], clean_disposition="unmeasured",
             oracle_verdict="NOT MEASURED on this box")
    ]
    arm("an unmeasured row that says NOT MEASURED passes",
        run(honest_unmeasured) == [], "; ".join(run(honest_unmeasured)))

    if failures:
        print(f"self-test: {len(failures)} arm(s) FAILED: {', '.join(failures)}")
        return 1
    print("self-test: all arms green")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true",
                       help="hold the committed ledger to the tree (default)")
    group.add_argument("--self-test", action="store_true",
                       help="drive every refusal on a synthetic ledger")
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    problems = check()
    if problems:
        print("UPSTREAM_SOUNDNESS_INTAKE=fail")
        for problem in problems:
            print(f"  {problem}")
        return 1
    print("UPSTREAM_SOUNDNESS_INTAKE=ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
