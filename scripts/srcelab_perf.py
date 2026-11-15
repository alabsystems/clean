#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Performance leg of the source-elab gate (SRCELAB).

WHY THIS EXISTS
---------------
Measured by the 2026-09-24 performance audit
(reports/lean4-replacement-audit-2026-09-24/performance.json): the five-file
slice took 1,283 s on 2026-08-31 and 3,941 s on 2026-09-21. The Subtype
floor, which is almost all import, rose from ~175 s to ~290 s the week a
per-module `env.clone()` landed in the importer (caeba00e8), and
Logic/Function/Basic went 326 s -> 1,812 s in one merge (an unbudgeted
`grind` -> superposition fallback). The gate recorded `wall_seconds` and
enforced nothing about it, so a tripling was invisible.

What this module does, per pinned file:
  * reads `import_s` and `elab_s` from the check report's `timing` block
    (`clean check --json`, crates/clean-cli/src/check_timing.rs), and the
    process's peak RSS from `/usr/bin/time` (`-l` on macOS: bytes; `-v` on
    GNU: kbytes) -- the binary cannot read its own without `unsafe` FFI;
  * compares each against the armed baseline in data/source_elab_ratchet.json
    (`files[<key>].perf_baseline`) and FAILS when
        measured > baseline + max(baseline * relative, absolute_floor)
    -- 25 % by default (50 % for peak RSS, the noisier metric: see
    DEFAULT_TOLERANCE), with a floor (15 s, 256 MiB) so a 7-second phase is
    not failed by box noise. A tripled import phase fails on every file.
  * A metric the ratchet is armed on that this run could not measure (a
    binary whose report has no `timing`, a box with no /usr/bin/time) is
    UNMEASURED, and that fails too: an unknown is never rounded up to a pass.

Baselines are written by `scripts/source_elab_gate.sh --update` from the
arming run's own measurement (so a baseline always equals its evidence, which
`--check-artifact` binds), and an arming run that regressed beyond tolerance
is refused like a count regression. So a baseline can drift up by at most one
tolerance per ARMING, visibly, in the dated reports -- never silently. Moving
past a genuine, accepted slowdown is `--update --rebase-perf '<why>'`, which
records the reason.

Usage:
  scripts/srcelab_perf.py --compare BASE_REPORT.json MEASURED_REPORT.json
  scripts/srcelab_perf.py --selftest
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from typing import Dict, List, Optional

METRICS = ("import_s", "elab_s", "max_rss_bytes")
# Peak RSS gets its own, wider relative tolerance because on this box it is the
# NOISIER metric, measured: the same release binary (sha256 2b7aff2d7b14) on the
# same Mathlib/Order/Basic.lean read 7,473,119,232 bytes on one gate run and
# 5,735,071,744 on the next (reports/source-elab/srcelab-2026-09-25-g0276db7f6
# and -g47d86e658; the 2026-09-24 audit read 7.42 GB), a 30 % swing, while the
# other four files agreed within 0.2 % and every timing within 14 %. macOS
# ru_maxrss counts RESIDENT pages, and under memory pressure the compressor
# takes some of them, so a baseline armed on a pressured run sat 23 % below a
# normal one -- at the 25 % timing tolerance the next idle run would have failed
# PERF-REGRESSION on a binary that had not changed. 50 % still fails a doubling.
DEFAULT_TOLERANCE = {"relative": 0.25, "rss_relative": 0.5, "abs_seconds": 15.0,
                     "abs_rss_bytes": 256 * 1024 * 1024}
_MAC_RSS = re.compile(r"^\s*(\d+)\s+maximum resident set size\s*$", re.M)
_GNU_RSS = re.compile(r"Maximum resident set size \(kbytes\):\s*(\d+)")


def rss_from_time_output(text: str) -> Optional[int]:
    """Peak RSS in bytes from `/usr/bin/time -l` (macOS) or `-v` (GNU)."""
    m = _MAC_RSS.search(text or "")
    if m:
        return int(m.group(1))
    m = _GNU_RSS.search(text or "")
    if m:
        return int(m.group(1)) * 1024
    return None


def check_report(stdout_text: str) -> Optional[dict]:
    """The Clean-check-report-v1 object in a captured `clean check --json`."""
    i = (stdout_text or "").find("{")
    if i < 0:
        return None
    try:
        obj, _ = json.JSONDecoder().raw_decode(stdout_text[i:])
    except ValueError:
        return None
    # v2 (2026-09-28) changed only `trust_summary.sorry_axioms`' meaning; the
    # `timing` block this reads is additive since v1 and unchanged
    # (crates/clean-cli/src/check_timing.rs). Reading v1 only made every v2
    # report's timing "absent", and the gate failed perf-unmeasured.
    return obj if obj.get("schema_version") in ("Clean-check-report-v1", "Clean-check-report-v2") else None


def perf_record(stdout_text: str, time_text: Optional[str]) -> dict:
    """The per-file perf fields the gate records in its dated report."""
    rep = check_report(stdout_text) or {}
    timing = rep.get("timing") if isinstance(rep.get("timing"), dict) else None
    out: dict = {
        "import_s": None, "elab_s": None, "total_s": None, "setup_s": None, "parse_s": None,
        "max_rss_bytes": rss_from_time_output(time_text) if time_text is not None else None,
        "max_rss_source": "unavailable" if time_text is None else "/usr/bin/time",
        "slowest_declarations": [],
    }
    if timing is not None:
        for k in ("import_s", "elab_s", "total_s", "setup_s", "parse_s"):
            v = timing.get(k)
            out[k] = float(v) if isinstance(v, (int, float)) and not isinstance(v, bool) else None
        decls = [d for d in timing.get("per_declaration") or [] if isinstance(d, dict)]
        decls.sort(key=lambda d: -float(d.get("elapsed_ms") or 0))
        out["slowest_declarations"] = [
            {"name": d.get("name"), "line": d.get("line"), "elapsed_ms": d.get("elapsed_ms")}
            for d in decls[:10]
        ]
        out["timed_declarations"] = len(timing.get("per_declaration") or [])
    else:
        out["timing_source"] = "absent (a binary that predates `timing`)"
    return out


def diverged_rows(stdout_text: str) -> List[str]:
    rep = check_report(stdout_text) or {}
    return [str(d)[:300] for d in rep.get("diverged") or []]


def tolerance_of(ratchet: Optional[dict]) -> dict:
    tol = dict(DEFAULT_TOLERANCE)
    if isinstance(ratchet, dict) and isinstance(ratchet.get("perf_tolerance"), dict):
        for k, v in ratchet["perf_tolerance"].items():
            if k in tol and isinstance(v, (int, float)) and not isinstance(v, bool) and v >= 0:
                tol[k] = float(v)
    return tol


# A tolerance is part of the artifact, so it has bounds: widening it past these
# is not a tolerance any more but an off switch, and `tolerance_of` alone would
# take any non-negative number it is handed.
TOLERANCE_BOUNDS = {"relative": (0.05, 1.0), "rss_relative": (0.05, 1.0), "abs_seconds": (0.0, 120.0),
                    "abs_rss_bytes": (0.0, 2.0 * 1024 ** 3)}


def validate_artifact(ratchet: Optional[dict]) -> List[str]:
    """Shape problems of the perf half of data/source_elab_ratchet.json."""
    problems: List[str] = []
    if not isinstance(ratchet, dict):
        return problems
    tol = ratchet.get("perf_tolerance")
    if tol is not None:
        if not isinstance(tol, dict):
            problems.append("perf_tolerance is not an object")
        else:
            for k, v in tol.items():
                if k not in TOLERANCE_BOUNDS:
                    problems.append("perf_tolerance.{} is not a known key ({})".format(
                        k, ", ".join(sorted(TOLERANCE_BOUNDS))))
                    continue
                lo, hi = TOLERANCE_BOUNDS[k]
                if isinstance(v, bool) or not isinstance(v, (int, float)) or not lo <= v <= hi:
                    problems.append(
                        "perf_tolerance.{}={!r} is outside [{}, {}] -- a tolerance that wide "
                        "is an off switch, not a tolerance".format(k, v, lo, hi))
    for key, entry in (ratchet.get("files") or {}).items():
        pb = entry.get("perf_baseline") if isinstance(entry, dict) else None
        if pb is None:
            continue
        if not isinstance(pb, dict) or not pb:
            problems.append("{}: perf_baseline is empty or not an object".format(key))
            continue
        for m, v in pb.items():
            if m not in METRICS:
                problems.append("{}: perf_baseline.{} is not a metric ({})".format(key, m, ", ".join(METRICS)))
            elif isinstance(v, bool) or not isinstance(v, (int, float)) or v <= 0:
                problems.append("{}: perf_baseline.{}={!r} is not a positive measurement".format(key, m, v))
    return problems


def armed_files(ratchet: Optional[dict]) -> List[str]:
    """Pinned files whose performance is armed."""
    files = (ratchet or {}).get("files") or {}
    return sorted(k for k, v in files.items() if isinstance(v, dict) and v.get("perf_baseline"))


def limit(base: float, metric: str, tol: dict) -> float:
    if metric == "max_rss_bytes":
        return base + max(base * tol.get("rss_relative", tol["relative"]), tol["abs_rss_bytes"])
    return base + max(base * tol["relative"], tol["abs_seconds"])


def compare(baselines: Dict[str, dict], measured: Dict[str, dict], tol: dict) -> dict:
    """Each armed metric of each file against its measurement."""
    out: dict = {"tolerance": tol, "regressions": [], "unmeasured": [], "checked": [], "unarmed": []}
    for key in sorted(measured):
        base = baselines.get(key) or {}
        if not base:
            out["unarmed"].append(key)
            continue
        for metric in METRICS:
            b = base.get(metric)
            if not isinstance(b, (int, float)) or isinstance(b, bool):
                continue
            m = measured[key].get(metric)
            if not isinstance(m, (int, float)) or isinstance(m, bool):
                out["unmeasured"].append({"file": key, "metric": metric, "baseline": b})
                continue
            lim = limit(float(b), metric, tol)
            row = {"file": key, "metric": metric, "baseline": b, "measured": m,
                   "limit": round(lim, 3), "ratio": round(float(m) / float(b), 3) if b else None}
            (out["regressions"] if m > lim else out["checked"]).append(row)
    return out


def render(res: dict, out=sys.stdout) -> None:
    for r in res["checked"]:
        print("  perf {} {}: {} (baseline {}, limit {})".format(
            r["file"], r["metric"], r["measured"], r["baseline"], r["limit"]), file=out)
    for key in res["unarmed"]:
        print("  perf {}: no perf baseline armed (arm with --update)".format(key), file=out)
    for r in res["unmeasured"]:
        print("  PERF-UNMEASURED {} {}: armed at {} but this run produced no value".format(
            r["file"], r["metric"], r["baseline"]), file=out)
    for r in res["regressions"]:
        print("  PERF-REGRESSION {} {}: {} > limit {} (baseline {}, x{})".format(
            r["file"], r["metric"], r["measured"], r["limit"], r["baseline"], r["ratio"]), file=out)


def _measured_of_report(report: dict) -> Dict[str, dict]:
    return {f.get("key"): {m: f.get(m) for m in METRICS} for f in report.get("files") or []}


# ---------------------------------------------------------------- self-test
def _selftest() -> int:
    fails = 0

    def check(name: str, cond: bool) -> None:
        nonlocal fails
        print("  {}: {}".format("PASS" if cond else "FAIL", name))
        fails += 0 if cond else 1

    tol = dict(DEFAULT_TOLERANCE)
    base = {"F": {"import_s": 300.0, "elab_s": 7.5, "max_rss_bytes": 4_000_000_000}}
    # the env.clone shape: import tripled, everything else flat
    r = compare(base, {"F": {"import_s": 900.0, "elab_s": 7.4, "max_rss_bytes": 4_000_000_000}}, tol)
    check("a tripled import phase is a regression",
          [x["metric"] for x in r["regressions"]] == ["import_s"])
    # noise inside the tolerance passes; the floor protects a small phase
    r = compare(base, {"F": {"import_s": 360.0, "elab_s": 20.0, "max_rss_bytes": 4_200_000_000}}, tol)
    check("within tolerance and floor passes", r["regressions"] == [] and len(r["checked"]) == 3)
    # peak RSS: the measured same-binary swing (5.74 GB armed, 7.47 GB on the
    # next run of Order/Basic) passes; a doubling does not
    rb = {"F": {"max_rss_bytes": 5_735_071_744}}
    check("the measured same-binary RSS swing is not a regression",
          compare(rb, {"F": {"max_rss_bytes": 7_473_119_232}}, tol)["regressions"] == [])
    check("a doubled peak RSS is a regression",
          [x["metric"] for x in compare(rb, {"F": {"max_rss_bytes": 11_470_143_488}}, tol)["regressions"]]
          == ["max_rss_bytes"])
    # an armed metric this run could not measure fails closed
    r = compare(base, {"F": {"import_s": None, "elab_s": 7.0, "max_rss_bytes": None}}, tol)
    check("unmeasured armed metrics are reported", sorted(x["metric"] for x in r["unmeasured"]) == ["import_s", "max_rss_bytes"])
    # an unarmed file enforces nothing, and says so
    r = compare({}, {"F": {"import_s": 1.0}}, tol)
    check("unarmed file is listed, not enforced", r["unarmed"] == ["F"] and r["regressions"] == [])
    # RSS parsing, both time(1) dialects
    check("macOS time -l RSS", rss_from_time_output("  0.1 real\n  2195456  maximum resident set size\n") == 2195456)
    check("GNU time -v RSS", rss_from_time_output("\tMaximum resident set size (kbytes): 1024\n") == 1024 * 1024)
    check("no RSS line is None", rss_from_time_output("nothing") is None)
    # the timing block is read from the report; its absence is recorded, not zero
    rep = {"schema_version": "Clean-check-report-v1", "timing": {"import_s": 1.5, "elab_s": 2.0,
           "per_declaration": [{"name": "a", "line": 1, "elapsed_ms": 5.0}, {"name": "b", "line": 2, "elapsed_ms": 9.0}]}}
    pr = perf_record("noise\n" + json.dumps(rep), "  7  maximum resident set size\n")
    check("perf record reads timing and RSS",
          pr["import_s"] == 1.5 and pr["elab_s"] == 2.0 and pr["max_rss_bytes"] == 7
          and [d["name"] for d in pr["slowest_declarations"]] == ["b", "a"])
    pr = perf_record(json.dumps({"schema_version": "Clean-check-report-v1"}), None)
    check("absent timing is None, never 0", pr["import_s"] is None and pr["max_rss_bytes"] is None)
    # a v2 report's timing is read exactly as a v1 report's; an unknown version is not a report
    rep2 = dict(rep, schema_version="Clean-check-report-v2")
    pr = perf_record(json.dumps(rep2), None)
    check("a v2 report's timing is read", pr["import_s"] == 1.5 and pr["elab_s"] == 2.0)
    pr = perf_record(json.dumps(dict(rep, schema_version="Clean-check-report-v9")), None)
    check("an unknown report version yields no timing", pr["import_s"] is None)
    # ratchet tolerance override is honoured and junk is ignored
    t = tolerance_of({"perf_tolerance": {"relative": 0.5, "abs_seconds": "x"}})
    check("tolerance override", t["relative"] == 0.5 and t["abs_seconds"] == DEFAULT_TOLERANCE["abs_seconds"])
    # the artifact half: a tolerance wide enough to be an off switch, or a
    # baseline that is not a measurement, is refused
    check("a sane artifact validates", validate_artifact(
        {"perf_tolerance": {"relative": 0.25}, "files": {"F": {"perf_baseline": {"import_s": 3.0}}}}) == [])
    check("a 1000% tolerance is refused", bool(validate_artifact({"perf_tolerance": {"relative": 10.0}})))
    check("an unknown tolerance key is refused", bool(validate_artifact({"perf_tolerance": {"rel": 0.2}})))
    check("a zero or unknown baseline is refused",
          bool(validate_artifact({"files": {"F": {"perf_baseline": {"import_s": 0}}}}))
          and bool(validate_artifact({"files": {"F": {"perf_baseline": {"wall": 3.0}}}})))
    check("armed files are the ones with a baseline",
          armed_files({"files": {"F": {"perf_baseline": {"elab_s": 1.0}}, "G": {}}}) == ["F"])
    print("SRCELAB_PERF_SELFTEST={} failed={}".format("ok" if fails == 0 else "fail", fails))
    return 0 if fails == 0 else 1


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--compare", nargs=2, metavar=("BASE_REPORT", "MEASURED_REPORT"))
    ap.add_argument("--ratchet", default=None, help="read perf_tolerance from this ratchet")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return _selftest()
    if not a.compare:
        ap.error("--compare or --selftest is required")
    try:
        with open(a.compare[0], encoding="utf-8") as f:
            base = json.load(f)
        with open(a.compare[1], encoding="utf-8") as f:
            meas = json.load(f)
        ratchet = None
        if a.ratchet:
            with open(a.ratchet, encoding="utf-8") as f:
                ratchet = json.load(f)
    except (OSError, ValueError) as exc:
        print("srcelab-perf: unreadable input: {}".format(exc), file=sys.stderr)
        return 2
    res = compare(_measured_of_report(base), _measured_of_report(meas), tolerance_of(ratchet))
    if a.json:
        json.dump(res, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        render(res)
    return 1 if (res["regressions"] or res["unmeasured"]) else 0


if __name__ == "__main__":
    sys.exit(main())
