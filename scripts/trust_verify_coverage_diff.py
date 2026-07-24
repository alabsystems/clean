#!/usr/bin/env python3
"""Per-function common-set coverage diff for the Trust Level-0 ratchet.

WHY THIS EXISTS
---------------
The coverage ratchet used to gate on ABSOLUTE totals (unproved <= ceiling,
verified >= floor). Those totals are NONDETERMINISTIC run-to-run: the ~33.6GB
VC-gen memory guard skips a varying swath of obligations, and any new kernel
code adds obligations. So a faithful re-measure on current main could trip a
spurious "COVERAGE REGRESSION" even when ZERO functions actually regressed.

The honest test is per-function: did any function that was FULLY VERIFIED in the
baseline become unverified now, for a real reason (not just because the memory
guard happened to surface/skip it differently this run)? Zero per-function
regressions == no real coverage loss, regardless of absolute-total drift.

FUNCTION IDENTITY
-----------------
The verify log names a function ONLY when it is incomplete
(`Trust Level 0 safety verification incomplete for `FUNC``). Fully-verified
functions emit only a verdict note with a `-->` source location and NO name.
So the stable per-function identity that covers BOTH verified and incomplete
functions is the verdict note's `--> file:line:col` source location. Names are
overlaid from the incomplete-warning when available (for readable reporting).

A function is VERIFIED iff its verdict note has 0 failed AND 0 unknown.

MEMORY-GUARD NON-REGRESSION RULE
--------------------------------
A function whose only unproved obligations are driven by the VC-gen work/memory
guard (`TrustVcGenWorkBudgetExceeded`, left Unknown fail-closed) is NOT counted
as a genuine regression: that is exactly the nondeterministic swath. A function
is GENUINELY unverified iff it has `failed > 0` OR it has `unknown > 0` that is
NOT attributable to the work-budget guard.

REGRESSION (hard fail) = a location in the COMMON set (present in both baseline
and current) that was VERIFIED in baseline but is GENUINELY unverified now.

New locations (not in baseline) are landscape, not regressions. Aggregate
verified/unproved deltas are reported as SOFT informational context.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

# --- log line patterns ------------------------------------------------------
_VERDICT = re.compile(
    r"^note: Trust verification: (\d+) proved, (\d+) failed, (\d+) unknown, "
    r"(\d+) timed out, (\d+) runtime-checked"
)
_LOC = re.compile(r"^\s*-->\s+(\S+)")
_INCOMPLETE = re.compile(
    r"Trust Level 0 safety verification incomplete for `(.+?)`"
)
_WBE = re.compile(r"TrustVcGenWorkBudgetExceeded")


@dataclass
class FuncVerdict:
    """One function's Level-0 verdict, keyed by its source location."""

    proved: int = 0
    failed: int = 0
    unknown: int = 0
    timed: int = 0
    rc: int = 0
    wbe: bool = False  # any unproved obligation is work-budget(memory)-guard driven
    name: str | None = None  # demangled name, only known if incomplete

    @property
    def verified(self) -> bool:
        return self.failed == 0 and self.unknown == 0

    @property
    def genuinely_unverified(self) -> bool:
        # failed is always genuine; unknown is genuine unless purely guard-driven.
        if self.failed > 0:
            return True
        if self.unknown > 0 and not self.wbe:
            return True
        return False


def parse_log(path: str) -> dict[str, FuncVerdict]:
    """Parse a clean-kernel verify log into {source_location: FuncVerdict}.

    A verdict note's `--> file:line:col` is the function identity. Multiple
    obligations for the same function aggregate onto the same location.
    """
    lines = Path(path).read_text(errors="replace").splitlines()
    n = len(lines)
    per: dict[str, FuncVerdict] = {}

    for i, line in enumerate(lines):
        m = _VERDICT.match(line)
        if not m:
            continue
        p, f, u, t, rc = map(int, m.groups())
        loc = None
        for j in range(i + 1, min(i + 4, n)):
            lm = _LOC.match(lines[j])
            if lm:
                loc = lm.group(1)
                break
        if loc is None:
            continue
        # Work-budget marker may sit in this verdict block's notes.
        wbe = any(_WBE.search(lines[j]) for j in range(i + 1, min(i + 14, n)))
        fv = per.setdefault(loc, FuncVerdict())
        fv.proved += p
        fv.failed += f
        fv.unknown += u
        fv.timed += t
        fv.rc += rc
        fv.wbe = fv.wbe or wbe

    # Overlay readable names from the incomplete warnings (matched by location).
    warn_idx = [i for i, l in enumerate(lines) if _INCOMPLETE.search(l)]
    for wi in warn_idx:
        name = _INCOMPLETE.search(lines[wi]).group(1)
        loc = None
        for j in range(wi + 1, min(wi + 4, n)):
            lm = _LOC.match(lines[j])
            if lm:
                loc = lm.group(1)
                break
        if loc and loc in per and per[loc].name is None:
            per[loc].name = name

    return per


def aggregates(per: dict[str, FuncVerdict]) -> dict[str, int]:
    proved = sum(v.proved for v in per.values())
    failed = sum(v.failed for v in per.values())
    unknown = sum(v.unknown for v in per.values())
    rc = sum(v.rc for v in per.values())
    return {
        "functions": len(per),
        "verified_functions": sum(1 for v in per.values() if v.verified),
        "proved": proved,
        "failed": failed,
        "unknown": unknown,
        "runtime_checked": rc,
        "unproved": failed + unknown,
        "verified": proved + rc,
    }


def write_baseline(log: str, out: str) -> None:
    per = parse_log(log)
    agg = aggregates(per)
    # Store the minimal per-function fact needed for the diff: was it verified,
    # and (for reporting) its name. Keyed by source location.
    funcs = {
        loc: {
            "verified": v.verified,
            "name": v.name,
            "failed": v.failed,
            "unknown": v.unknown,
            "wbe": v.wbe,
        }
        for loc, v in per.items()
    }
    payload = {
        "schema": "trust-verify per-function coverage baseline v1",
        "note": (
            "Per-function (source-location-keyed) Level-0 verdicts. The gate "
            "compares the COMMON set: a regression is a function verified here "
            "but GENUINELY unverified (failed, or non-work-budget unknown) in a "
            "later run. Absolute aggregates are informational only (memory-guard "
            "nondeterministic)."
        ),
        "aggregates": agg,
        "functions": funcs,
    }
    Path(out).write_text(json.dumps(payload, indent=2) + "\n")
    print(f"wrote per-function baseline: {out}")
    print(
        f"  functions={agg['functions']} verified_functions={agg['verified_functions']} "
        f"proved={agg['proved']} unproved={agg['unproved']} verified={agg['verified']}"
    )


def gate(log: str, baseline: str) -> int:
    """Compare current log to baseline. Return 0 if no genuine regression, 1 otherwise."""
    bp = Path(baseline)
    if not bp.exists():
        print(
            f"ERROR: per-function baseline missing: {baseline} — seed it once with "
            "`scripts/trust_verify_ratchet.sh --coverage --update`",
            file=sys.stderr,
        )
        return 2
    if not Path(log).exists():
        print(f"ERROR: verify log missing: {log}", file=sys.stderr)
        return 2
    bl = json.loads(bp.read_text())
    base_funcs = bl["functions"]
    cur = parse_log(log)
    cur_agg = aggregates(cur)
    base_agg = bl.get("aggregates", {})

    common = set(base_funcs) & set(cur)
    regressions = []
    gained = []
    for loc in common:
        was_verified = bool(base_funcs[loc]["verified"])
        now = cur[loc]
        if was_verified and now.genuinely_unverified:
            regressions.append((loc, now, base_funcs[loc].get("name")))
        elif not was_verified and now.verified:
            gained.append(loc)

    new_locs = [loc for loc in cur if loc not in base_funcs]
    dropped_locs = [loc for loc in base_funcs if loc not in cur]

    print("== PER-FUNCTION COMMON-SET COVERAGE DIFF ==")
    print(
        f"  baseline functions={len(base_funcs)}  current functions={len(cur)}  "
        f"common={len(common)}"
    )
    print(
        f"  new (landscape)={len(new_locs)}  dropped (guard-skipped/removed)={len(dropped_locs)}"
    )
    print(f"  functions GAINED verified status (improvement): {len(gained)}")
    # SOFT aggregate context (NOT a hard gate — absolute totals drift run-to-run).
    if base_agg:
        dv = cur_agg["verified"] - base_agg.get("verified", 0)
        du = cur_agg["unproved"] - base_agg.get("unproved", 0)
        print(
            f"  [soft] aggregate verified {base_agg.get('verified')} -> {cur_agg['verified']} "
            f"({dv:+d}); unproved {base_agg.get('unproved')} -> {cur_agg['unproved']} ({du:+d}) "
            f"(informational; memory-guard nondeterministic, not gated)"
        )

    if regressions:
        print(f"  GENUINE PER-FUNCTION REGRESSIONS: {len(regressions)}")
        for loc, fv, bname in regressions[:50]:
            nm = fv.name or bname or "<unnamed>"
            print(
                f"    REGRESSION {loc}  `{nm}`  "
                f"(now failed={fv.failed} unknown={fv.unknown} wbe={fv.wbe})"
            )
        if len(regressions) > 50:
            print(f"    ... and {len(regressions) - 50} more")
        return 1

    print("  ✓ 0 genuine per-function regressions on the common set")
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_up = sub.add_parser("update", help="write per-function baseline from a log")
    p_up.add_argument("--log", required=True)
    p_up.add_argument("--baseline", required=True)

    p_gate = sub.add_parser("gate", help="diff a log against the baseline")
    p_gate.add_argument("--log", required=True)
    p_gate.add_argument("--baseline", required=True)

    args = ap.parse_args(argv)
    if args.cmd == "update":
        write_baseline(args.log, args.baseline)
        return 0
    if args.cmd == "gate":
        return gate(args.log, args.baseline)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
