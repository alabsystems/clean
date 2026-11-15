#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Judge a Trust verified-lane run against its pinned per-crate floors.

WHY THIS EXISTS
---------------
`publish/config.sh` runs `targo trust check --allow-l0-gaps --workspace
--all-targets --all-features`, and measured 2026-10-01 (targo 1.99.0-dev
321aaeda7) 17 of the 18 crates it reaches report FAILED obligations and nine
more are too slow to launch, so that step cannot be green and says nothing
about any one crate. This leg is ADDITIVE: it does not touch that step. It
runs the verified lane, one `targo trust check -p <crate> --lib` per crate, over
the crates that have been brought to ZERO failed obligations, and refuses a
regression in any of them by name.

`targo` has no floor flag, so this script is the floor. For every crate pinned
in `data/trust_verified_lane.json` it reads that crate's `report.json`
(`verification_gate`) and refuses, each by name:

  * a pinned crate with no report (the check crashed, or was never run);
  * a report for a crate the pin does not name (an unreviewed scope change);
  * a report whose `crate_name` names another package or target kind;
  * a report from another lane than the pinned one;
  * a `targo trust check` exit status that is not 0, or that disagrees with the
    report's own `exit_code`;
  * a decision outside `pass` / `conditional-pass`;
  * ANY failed obligation (`failed > 0`);
  * zero obligations (a check that selected nothing cannot fail);
  * counts that do not sum to `total` (schema drift or a hand edit);
  * `proved` below the pinned floor.

UNKNOWN IS NEVER PROVED. The floor compares `proved` only; `unknown`,
`runtime_checked`, `assumed` and `mandated` rows never count toward it. A green
here means "no obligation FAILED and at least the pinned number PROVED" on the
advisory lane -- it is NOT a claim that the crate is verified: every unknown
row is still unproved, and the report's own `authority` field says no proof
credit is granted. Raising a floor, or adding a crate, is a reviewed edit of
the pin; lowering a floor is the regression this script exists to refuse, so it
is a reviewed edit too and must say why in the pin's `history`.

Usage:
  check_trust_verified_lane.py --reports <dir> [--exit <crate>=<rc> ...]
      <dir>/<crate>/report.json for every pinned crate.
  check_trust_verified_lane.py --crates     print the pinned crate names
  check_trust_verified_lane.py --selftest   run the refusal arms
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PIN = ROOT / "data" / "trust_verified_lane.json"

COUNT_KEYS = ("proved", "failed", "unknown", "runtime_checked", "assumed", "mandated")
ACCEPTED_DECISIONS = ("pass", "conditional-pass")


class Refusal(Exception):
    pass


def load_pin(path: Path) -> dict:
    try:
        pin = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as e:
        raise Refusal(f"pin {path}: unreadable ({e})") from e
    crates = pin.get("crates")
    if not isinstance(crates, dict) or not crates:
        raise Refusal(f"pin {path}: no `crates` (an empty lane cannot fail)")
    lane = pin.get("lane")
    if not isinstance(lane, str) or not lane:
        raise Refusal(f"pin {path}: no `lane`")
    for name, row in crates.items():
        floor = row.get("proved_floor") if isinstance(row, dict) else None
        if not isinstance(floor, int) or isinstance(floor, bool) or floor < 1:
            raise Refusal(f"pin {path}: crate {name}: `proved_floor` must be an integer >= 1 (a zero floor proves nothing)")
        if row.get("target") != "lib":
            raise Refusal(f"pin {path}: crate {name}: `target` must be \"lib\" (the leg runs --lib)")
    return pin


def judge_report(crate: str, row: dict, lane: str, report_path: Path, rc: int | None) -> str:
    if not report_path.is_file():
        raise Refusal(f"{crate}: NO REPORT at {report_path} (the check crashed or never ran)")
    try:
        rep = json.loads(report_path.read_text())
    except (OSError, json.JSONDecodeError) as e:
        raise Refusal(f"{crate}: report unreadable ({e})") from e
    cn = rep.get("crate_name")
    if not isinstance(cn, str) or f'package="{crate}"' not in cn:
        raise Refusal(f"{crate}: report names another package ({str(cn)[:120]})")
    if not re.search(r'kind=\["lib"\]', cn):
        raise Refusal(f"{crate}: report is not for the lib target")
    gate = rep.get("verification_gate")
    if not isinstance(gate, dict):
        raise Refusal(f"{crate}: report has no verification_gate")
    if gate.get("lane") != lane:
        raise Refusal(f"{crate}: lane {gate.get('lane')!r}, pinned {lane!r}")
    if rc is None:
        raise Refusal(f"{crate}: no exit status recorded for the check")
    if rc != 0:
        raise Refusal(f"{crate}: targo trust check exited {rc}")
    if gate.get("exit_code") != rc:
        raise Refusal(f"{crate}: report exit_code {gate.get('exit_code')!r} disagrees with the check's exit {rc}")
    decision = gate.get("decision")
    if decision not in ACCEPTED_DECISIONS:
        raise Refusal(f"{crate}: decision {decision!r}")
    counts = gate.get("counts")
    if not isinstance(counts, dict):
        raise Refusal(f"{crate}: no counts")
    vals = {}
    for k in ("total",) + COUNT_KEYS:
        v = counts.get(k)
        if not isinstance(v, int) or isinstance(v, bool) or v < 0:
            raise Refusal(f"{crate}: count {k!r} missing or not a non-negative integer")
        vals[k] = v
    if vals["total"] == 0:
        raise Refusal(f"{crate}: ZERO obligations (vacuous)")
    if sum(vals[k] for k in COUNT_KEYS) != vals["total"]:
        raise Refusal(f"{crate}: counts do not sum to total {vals['total']} ({vals})")
    if vals["failed"] > 0:
        raise Refusal(f"{crate}: {vals['failed']} FAILED obligation(s)")
    floor = row["proved_floor"]
    if vals["proved"] < floor:
        raise Refusal(f"{crate}: proved {vals['proved']} < pinned floor {floor} (unknown rows never count)")
    return (f"{crate}: ok proved={vals['proved']} (floor {floor}) failed=0 "
            f"unknown={vals['unknown']} runtime_checked={vals['runtime_checked']} "
            f"mandated={vals['mandated']} total={vals['total']}")


def judge(pin: dict, reports: Path, exits: dict[str, int]) -> list[str]:
    crates = pin["crates"]
    if reports.is_dir():
        extra = sorted(p.name for p in reports.iterdir() if p.is_dir() and p.name not in crates)
        if extra:
            raise Refusal(f"reports for crates the pin does not name: {', '.join(extra)}")
    unknown_exit = sorted(set(exits) - set(crates))
    if unknown_exit:
        raise Refusal(f"exit status for crates the pin does not name: {', '.join(unknown_exit)}")
    out = []
    for crate in sorted(crates):
        out.append(judge_report(crate, crates[crate], pin["lane"], reports / crate / "report.json", exits.get(crate)))
    return out


def parse_exits(items: list[str]) -> dict[str, int]:
    exits: dict[str, int] = {}
    for it in items:
        name, sep, rc = it.partition("=")
        if not sep or not rc.lstrip("-").isdigit():
            raise Refusal(f"--exit {it!r}: expected <crate>=<rc>")
        if name in exits:
            raise Refusal(f"--exit {name}: given twice")
        exits[name] = int(rc)
    return exits


# ---------------------------------------------------------------- selftest

def _report(crate: str, **over) -> dict:
    counts = {"total": 10, "proved": 4, "failed": 0, "unknown": 5, "runtime_checked": 0,
              "assumed": 0, "mandated": 1, "contract_panics": 0}
    counts.update(over.pop("counts", {}))
    gate = {"lane": "advisory", "decision": "conditional-pass", "exit_code": 0, "counts": counts}
    gate.update(over.pop("gate", {}))
    rep = {"crate_name": f'cargo-target(package="{crate}",kind=["lib"],target="x")',
           "verification_gate": gate}
    rep.update(over)
    return rep


def selftest() -> int:
    pin = {"lane": "advisory", "crates": {"a": {"target": "lib", "proved_floor": 3},
                                         "b": {"target": "lib", "proved_floor": 4}}}
    arms: list[tuple[str, bool, object]] = []

    def arm(name, expect_ok, reports, exits=None, pin_over=None, extra_dirs=()):
        arms.append((name, expect_ok, (reports, exits, pin_over, extra_dirs)))

    good = {"a": _report("a"), "b": _report("b")}
    ok_exit = {"a": 0, "b": 0}
    arm("green run passes", True, good)
    arm("unknown is never counted toward the floor", False,
        {**good, "b": _report("b", counts={"proved": 3, "unknown": 6})})
    arm("one failed obligation", False,
        {**good, "a": _report("a", counts={"failed": 1, "unknown": 4})})
    arm("proved below floor", False, {**good, "a": _report("a", counts={"proved": 2, "unknown": 7})})
    arm("missing report", False, {"a": good["a"]})
    arm("report for an unpinned crate", False, good, extra_dirs=("c",))
    arm("report names another package", False, {**good, "a": _report("z")})
    arm("report not for the lib target", False,
        {**good, "a": {**_report("a"), "crate_name": 'cargo-target(package="a",kind=["bin"])'}})
    arm("another lane", False, {**good, "a": _report("a", gate={"lane": "strict-but-other"})})
    arm("non-zero targo exit", False, good, exits={"a": 1, "b": 0})
    arm("exit status not recorded", False, good, exits={"b": 0})
    arm("exit for an unpinned crate", False, good, exits={**ok_exit, "c": 0})
    arm("report exit_code disagrees", False, {**good, "a": _report("a", gate={"exit_code": 1})})
    arm("decision fail", False, {**good, "a": _report("a", gate={"decision": "fail"})})
    arm("decision inconclusive", False, {**good, "a": _report("a", gate={"decision": "inconclusive"})})
    arm("zero obligations", False,
        {**good, "a": _report("a", counts={"total": 0, "proved": 0, "unknown": 0, "mandated": 0})})
    arm("counts do not sum", False, {**good, "a": _report("a", counts={"total": 11})})
    arm("negative count", False, {**good, "a": _report("a", counts={"unknown": -1, "total": 4})})
    arm("missing count key", False,
        {**good, "a": {**_report("a"), "verification_gate": {"lane": "advisory", "decision": "pass",
                                                            "exit_code": 0, "counts": {"total": 1}}}})
    arm("pin with zero floor", False, good, pin_over={"lane": "advisory", "crates": {"a": {"target": "lib", "proved_floor": 0}}})
    arm("pin with no crates", False, good, pin_over={"lane": "advisory", "crates": {}})
    arm("pin with a bin target", False, good, pin_over={"lane": "advisory", "crates": {"a": {"target": "bin", "proved_floor": 1}}})

    bad = 0
    for name, expect_ok, (reports, exits, pin_over, extra_dirs) in arms:
        with tempfile.TemporaryDirectory() as td:
            t = Path(td)
            for crate, rep in reports.items():
                (t / crate).mkdir()
                (t / crate / "report.json").write_text(json.dumps(rep))
            for d in extra_dirs:
                (t / d).mkdir()
                (t / d / "report.json").write_text(json.dumps(_report(d)))
            pin_path = t / "pin.json"
            pin_path.write_text(json.dumps(pin_over if pin_over is not None else pin))
            try:
                judge(load_pin(pin_path), t, ok_exit if exits is None else exits)
                got_ok, why = True, ""
            except Refusal as e:
                got_ok, why = False, str(e)
        if got_ok != expect_ok:
            bad += 1
            print(f"SELFTEST ARM FAILED: {name}: expected {'pass' if expect_ok else 'refusal'}, got "
                  f"{'pass' if got_ok else 'refusal: ' + why}", file=sys.stderr)
    # The live pin must itself be well-formed.
    try:
        load_pin(PIN)
    except Refusal as e:
        bad += 1
        print(f"SELFTEST: live pin refused: {e}", file=sys.stderr)
    if bad:
        print(f"TRUST_VERIFIED_LANE_SELFTEST=fail arms={len(arms)} failed={bad}")
        return 1
    print(f"TRUST_VERIFIED_LANE_SELFTEST=ok arms={len(arms)}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--reports", type=Path)
    ap.add_argument("--exit", action="append", default=[], metavar="CRATE=RC")
    ap.add_argument("--crates", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--pin", type=Path, default=PIN)
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    try:
        pin = load_pin(a.pin)
        if a.crates:
            print("\n".join(sorted(pin["crates"])))
            return 0
        if a.reports is None:
            raise Refusal("--reports <dir> is required")
        lines = judge(pin, a.reports, parse_exits(a.exit))
    except Refusal as e:
        print(f"TRUST_VERIFIED_LANE=fail {e}", file=sys.stderr)
        return 1
    for line in lines:
        print(f"  {line}")
    print(f"TRUST_VERIFIED_LANE=ok crates={len(lines)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
