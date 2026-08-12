#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Silent-tactic ratchet: a tactic that dispatches nothing must NAME itself.

A tactic Clean does not support is supposed to fail loudly —
`TacticFailed(UnknownTactic("foo"))`. Measured on `origin/main` at 2026-08-07,
**27 of 374 probes failed with no diagnostic at all**: whenever a tactic's
ARGUMENT grammar failed, `by_body` recovered the whole block to a
`SyntheticSorry` and `clean check` (which called `parse_file_with_tactics`,
a signature with no room for recovery diagnostics) dropped the deferred
diagnostic on the floor. The user saw one line — "declaration uses synthetic
sorry" — and nothing anywhere named the construct that did nothing.

Recorded as RC-Q in `docs/plans/TACTICS_TO_100_2026-07-29.md`: any coverage
script keyed on `UnknownTactic`/`TacticFailed` UNDER-REPORTS the real gap, and
nobody knew by how much, because the class was unmeasurable by construction.

This gate reads the checked-in census (data/silent_tactic_census.json, produced
by `cargo test --offline -p clean-elab --test silent_tactic_census` with
CLEAN_SILENT_CENSUS_UPDATE=1) and:
  - ENFORCES monotonic decrease of `silent` and `unnamed`;
  - PINS the known-unnamed tokens so the class cannot stop being measured;
  - CHECKS the census is internally consistent (totals match the listed rows);
  - CHECKS the census still covers the whole checked-in probe corpus.

  scripts/check_silent_tactic_ratchet.py            # FAIL on regression
  scripts/check_silent_tactic_ratchet.py --update   # lock in a ratchet-down

Wired into scripts/local_gate.sh. Pure-stdlib; reads only checked-in JSON — it
needs no Lean toolchain, which is why the measurement and the gate are split.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PROBES = REPO_ROOT / "data" / "silent_tactic_probes.json"
CENSUS = REPO_ROOT / "data" / "silent_tactic_census.json"
RATCHET = REPO_ROOT / "data" / "silent_tactic_ratchet.json"

VERDICTS = ("pass", "loud", "unnamed", "silent")


def load(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {path}: {exc}")


def main(argv: list[str]) -> int:
    probes = load(PROBES)
    census = load(CENSUS)
    ratchet = load(RATCHET)

    rows = census.get("rows", [])
    totals = census.get("totals", {})
    for key in ("probes", *VERDICTS, "intentional_sorry"):
        if key not in totals:
            sys.exit(f"FAIL: {CENSUS.name} totals has no `{key}`")

    # --- self-consistency: the totals must describe the rows actually listed.
    if totals["probes"] != len(rows):
        sys.exit(
            f"FAIL: {CENSUS.name} totals.probes={totals['probes']} but "
            f"{len(rows)} rows are listed"
        )
    counted = {v: 0 for v in VERDICTS}
    intentional = 0
    for row in rows:
        verdict = row.get("verdict")
        if verdict not in counted:
            sys.exit(f"FAIL: {CENSUS.name} row {row.get('token')!r} has verdict {verdict!r}")
        if verdict == "silent" and row.get("intentional_sorry"):
            intentional += 1
        else:
            counted[verdict] += 1
    for verdict in VERDICTS:
        if counted[verdict] != totals[verdict]:
            sys.exit(
                f"FAIL: {CENSUS.name} totals.{verdict}={totals[verdict]} but "
                f"{counted[verdict]} rows carry that verdict"
            )
    if intentional != totals["intentional_sorry"]:
        sys.exit(
            f"FAIL: {CENSUS.name} totals.intentional_sorry={totals['intentional_sorry']} "
            f"but {intentional} rows are flagged"
        )

    # --- denominator integrity: the census must cover the WHOLE corpus.
    # Without this the class could be "fixed" by deleting probes.
    corpus = probes.get("probes", [])
    if len(corpus) != len(rows):
        sys.exit(
            f"FAIL: {CENSUS.name} has {len(rows)} rows but {PROBES.name} declares "
            f"{len(corpus)} probes. The denominator may not shrink: a construct that "
            f"stops being probed is not a construct that was fixed."
        )
    corpus_keys = {(p["token"], p["label"]) for p in corpus}
    census_keys = {(r["token"], r["label"]) for r in rows}
    missing = sorted(corpus_keys - census_keys)
    if missing:
        sys.exit(f"FAIL: {CENSUS.name} does not measure these corpus probes: {missing}")

    live_silent = sorted(
        {r["token"] for r in rows if r["verdict"] == "silent" and not r.get("intentional_sorry")}
    )
    live_unnamed = sorted({r["token"] for r in rows if r["verdict"] == "unnamed"})

    if "--update" in argv:
        ratchet.update(
            {
                "baseline_silent": totals["silent"],
                "baseline_unnamed": totals["unnamed"],
                "known_silent": live_silent,
                "known_unnamed": live_unnamed,
            }
        )
        RATCHET.write_text(json.dumps(ratchet, indent=2) + "\n")
        print(
            f"UPDATED {RATCHET.name}: silent={totals['silent']} "
            f"unnamed={totals['unnamed']}"
        )
        return 0

    base_silent = ratchet.get("baseline_silent")
    base_unnamed = ratchet.get("baseline_unnamed")
    if base_silent is None or base_unnamed is None:
        sys.exit(f"FAIL: {RATCHET.name} has no baselines")

    ok = True
    if totals["silent"] > base_silent:
        print(
            f"FAIL: SILENT tactic failures rose {base_silent} -> {totals['silent']}.\n"
            f"      Silent tokens: {live_silent}\n"
            f"      A construct that dispatches nothing MUST emit a diagnostic naming\n"
            f"      itself. A silent synthetic sorry is a gate FAILURE, not a skip: it\n"
            f"      makes the gap invisible to every coverage script in the repo. Do NOT\n"
            f"      raise the baseline to mask this — name the construct in the parser's\n"
            f"      recovery diagnostic (Parser::tactic -> tactic_chain) or reject it in\n"
            f"      the elaborator.",
            file=sys.stderr,
        )
        ok = False
    if totals["unnamed"] > base_unnamed:
        print(
            f"FAIL: tactic failures with NO diagnostic naming the tactic rose "
            f"{base_unnamed} -> {totals['unnamed']}.\n"
            f"      These fail closed but the user cannot tell WHICH tactic did nothing.",
            file=sys.stderr,
        )
        ok = False

    known_unnamed = set(ratchet.get("known_unnamed", []))
    vanished = sorted(known_unnamed - set(live_unnamed))
    if vanished and totals["unnamed"] >= base_unnamed:
        print(
            f"FAIL: known-unnamed tokens are no longer measured: {vanished}.\n"
            f"      If they were genuinely fixed, the count must have DROPPED; drop them\n"
            f"      from {RATCHET.name} in the SAME commit and lower the baseline "
            f"(--update).",
            file=sys.stderr,
        )
        ok = False

    if not ok:
        return 1

    if totals["silent"] < base_silent or totals["unnamed"] < base_unnamed:
        print(
            f"PROGRESS: silent {base_silent} -> {totals['silent']}, "
            f"unnamed {base_unnamed} -> {totals['unnamed']}. "
            f"Run with --update to lock it in."
        )
    else:
        print(
            f"PASS: silent-tactic census flat — silent={totals['silent']}, "
            f"unnamed={totals['unnamed']} (of {totals['probes']} probes over "
            f"{len({r['token'] for r in rows})} tactic tokens; "
            f"{totals['pass']} pass, {totals['loud']} fail loudly, "
            f"{totals['intentional_sorry']} intentional sorry)."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
