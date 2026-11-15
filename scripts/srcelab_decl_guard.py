#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Per-declaration slice guard for the source-elab gate (SRCELAB).

WHY THIS EXISTS
---------------
`data/source_elab_ratchet.json` ratchets PER-FILE success counts. A count is
blind to a row that starts failing while another row in the same file starts
passing: on 2026-09-21 the arming at 4020124a1 moved `Mathlib/Logic/Basic.lean`
221 -> 224 while `dite_dite_comm` (grind: no progress) and `ite_ite_comm` (its
cascade) went from passing to failing, and the gate said PASS. The notes
recorded both rows by hand, from a per-declaration diff that lived OUTSIDE the
repo (`~/.cache/clean-lane/diff_reports.py`) and that keyed every anonymous
instance under the single shared name `[anonymous]` -- so two anonymous rows
trading places read as no change at all.

This module is that diff, moved into the gate and made to decide:

  * A row is keyed by its declaration NAME. An anonymous declaration (Lean's
    `instance : C := ...`, a parse-recovery raw declaration) is keyed by the
    SOURCE LINE its error names (`[anonymous]@line:43`), or, when the error
    names no line, by a content hash of the error with volatile numerals
    (fvar ids, universe metas) normalised away.
  * A NEW failure is a key that is failing (an error row, or a declaration
    that spent its whole budget -- `diverged` is not a pass) in the measured
    report and was NOT failing in the baseline report, in the same file.
    Parser-recovery NOTES are not declarations (they are not in `decl_count`,
    see `srcelab_parse` in the gate) and are not keyed.
  * A new failure FAILS the gate even when the file's count holds, unless the
    ratchet's `decl_regression_ledger` lists it (file + row key) with an owner,
    a reason and an unexpired date at most 180 days out -- the same dated
    account shape the ratchet's other exceptions use.

A row that FAILED before under an anonymous parse-recovery key and now fails
under its real name (the parser learned the construct; the wall moved one
layer later) is still a new key. It is reported with a hint naming the raw row
it most likely replaces, and it still needs a ledger entry: deciding that two
rows are the same declaration from line proximity alone is a guess, and a
guard that guesses in the permissive direction is the kind this repo keeps
finding vacuous.

Usage:
  scripts/srcelab_decl_guard.py --baseline OLD.json --measured NEW.json \\
      [--ratchet data/source_elab_ratchet.json] [--json]
  scripts/srcelab_decl_guard.py --validate-ledger [--ratchet ...]
  scripts/srcelab_decl_guard.py --selftest

Exit: 0 no unledgered new failure; 1 at least one; 2 usage / unreadable input.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import re
import sys
from typing import Dict, List, Optional, Tuple

_LINE_RE = re.compile(r"\bat line (\d+)\b")
# Volatile spellings that differ run to run for the SAME failure; normalised
# out of the content hash so an anonymous row without a line keeps its key.
_VOLATILE_RE = re.compile(
    r"fvar#\d+|FVarId\(\d+\)|\?u_\d+|\?m\.\d+|#F\d+|_uniq\.\d+|\b\d{6,}\b"
)
_ANON_NAMES = {"[anonymous]", "(anonymous)", "_", "?", ""}
# `srcelab_classify.decl_of` names a parser-recovery NOTE by this prefix.
_RECOVERY_PREFIX = "parser recovery"
_ISO_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
LEDGER_KEY = "decl_regression_ledger"
LEDGER_HORIZON_DAYS = 180
MOVED_WINDOW_LINES = 5


def error_line(error: str) -> Optional[int]:
    m = _LINE_RE.search(error or "")
    return int(m.group(1)) if m else None


def row_key(decl: str, error: str) -> str:
    """The identity of one failing row within a file."""
    name = (decl or "").strip()
    if name not in _ANON_NAMES:
        return name
    line = error_line(error)
    if line is not None:
        return "[anonymous]@line:{}".format(line)
    norm = _VOLATILE_RE.sub("#", error or "")
    return "[anonymous]@sha256:" + hashlib.sha256(norm.encode("utf-8")).hexdigest()[:12]


def _is_raw_parse_row(error: str) -> bool:
    return "raw declaration" in (error or "") or "Parse error" in (error or "")


def failing_rows(file_rec: dict) -> Dict[str, dict]:
    """Every row of one srcelab report file entry that did NOT pass."""
    rows: Dict[str, dict] = {}
    for e in file_rec.get("per_error_class") or []:
        decl = str(e.get("decl", ""))
        err = str(e.get("error", ""))
        if decl.startswith(_RECOVERY_PREFIX):
            continue  # a note about source text, not a declaration
        key = row_key(decl, err)
        rows.setdefault(key, {"decl": decl, "line": error_line(err), "error": err,
                              "raw_parse": _is_raw_parse_row(err) and key.startswith("[anonymous]")})
    for d in file_rec.get("diverged_rows") or []:
        text = str(d)
        decl = text.split(":", 1)[0].strip() if ":" in text else ""
        key = row_key(decl, text)
        rows.setdefault(key, {"decl": decl, "line": error_line(text),
                              "error": text, "raw_parse": False, "diverged": True})
    return rows


def _moved_hint(key: str, row: dict, base: Dict[str, dict], meas: Dict[str, dict]) -> Optional[str]:
    """Name the baseline raw-parse row this new named row most likely replaces."""
    line = row.get("line")
    if line is None or key.startswith("[anonymous]"):
        return None
    for bkey, brow in base.items():
        bl = brow.get("line")
        if not brow.get("raw_parse") or bl is None or bkey in meas:
            continue
        if bl <= line <= bl + MOVED_WINDOW_LINES:
            return bkey
    return None


def ledger_entries(ratchet: Optional[dict]) -> List[dict]:
    if not isinstance(ratchet, dict):
        return []
    led = ratchet.get(LEDGER_KEY) or []
    return led if isinstance(led, list) else []


def _valid_expiry(v, today: _dt.date) -> bool:
    if not _ISO_RE.match(str(v or "")):
        return False
    try:
        d = _dt.date.fromisoformat(str(v))
    except ValueError:
        return False
    return today <= d <= today + _dt.timedelta(days=LEDGER_HORIZON_DAYS)


def validate_ledger(ratchet: Optional[dict], pinned_keys: Optional[List[str]] = None,
                    today: Optional[_dt.date] = None) -> List[str]:
    """Shape problems of the ratchet's accepted-regression ledger."""
    today = today or _dt.date.today()
    problems: List[str] = []
    if not isinstance(ratchet, dict):
        return problems
    raw = ratchet.get(LEDGER_KEY)
    if raw is None:
        return problems
    if not isinstance(raw, list):
        return ["`{}` is not a list".format(LEDGER_KEY)]
    seen = set()
    for i, e in enumerate(raw):
        if not isinstance(e, dict):
            problems.append("{}[{}] is not an object".format(LEDGER_KEY, i))
            continue
        for k in ("file", "decl", "owner", "reason", "expires"):
            if not str(e.get(k) or "").strip():
                problems.append("{}[{}] is missing `{}`".format(LEDGER_KEY, i, k))
        if pinned_keys is not None and e.get("file") and e["file"] not in pinned_keys:
            problems.append("{}[{}] names file {!r}, which is not a pinned file".format(
                LEDGER_KEY, i, e.get("file")))
        if e.get("expires") and not _valid_expiry(e.get("expires"), today):
            problems.append(
                "{}[{}] ({} in {}) expires={!r}: an accepted regression is a DATED "
                "account -- a YYYY-MM-DD no earlier than today and at most {} days "
                "out. Fix the row or renew the entry in review.".format(
                    LEDGER_KEY, i, e.get("decl"), e.get("file"), e.get("expires"),
                    LEDGER_HORIZON_DAYS))
        ident = (e.get("file"), e.get("decl"))
        if ident in seen:
            problems.append("{}[{}] duplicates an earlier entry for {}".format(LEDGER_KEY, i, ident))
        seen.add(ident)
    return problems


def _ledger_match(ledger: List[dict], file_key: str, key: str, today: _dt.date) -> Optional[dict]:
    for e in ledger:
        if e.get("file") == file_key and e.get("decl") == key and _valid_expiry(e.get("expires"), today) \
                and str(e.get("owner") or "").strip() and str(e.get("reason") or "").strip():
            return e
    return None


def guard(baseline: dict, measured: dict, ratchet: Optional[dict] = None,
          today: Optional[_dt.date] = None) -> dict:
    """Per-declaration diff of two srcelab reports, with the ledger applied."""
    today = today or _dt.date.today()
    ledger = ledger_entries(ratchet)
    base_files = {f.get("key") or f.get("path"): f for f in baseline.get("files") or []}
    out = {"new_failures": [], "ledgered": [], "fixed": [], "files": []}
    for mf in measured.get("files") or []:
        fkey = mf.get("key") or mf.get("path")
        bf = base_files.get(fkey)
        if bf is None:
            out["files"].append({"file": fkey, "note": "no baseline entry; not compared"})
            continue
        base, meas = failing_rows(bf), failing_rows(mf)
        new = sorted(k for k in meas if k not in base)
        fixed = sorted(k for k in base if k not in meas)
        for k in new:
            row = {"file": fkey, "decl": k, "line": meas[k].get("line"),
                   "error": meas[k].get("error", "")[:240]}
            hint = _moved_hint(k, meas[k], base, meas)
            if hint:
                row["likely_moved_from"] = hint
            ent = _ledger_match(ledger, fkey, k, today)
            if ent is not None:
                row["ledger"] = {"owner": ent.get("owner"), "expires": ent.get("expires")}
                out["ledgered"].append(row)
            else:
                out["new_failures"].append(row)
        out["fixed"].extend({"file": fkey, "decl": k} for k in fixed)
        summary = {
            "file": fkey,
            "success": [bf.get("success_count"), mf.get("success_count")],
            "new_failing_rows": len(new), "fixed_rows": len(fixed),
        }
        # A report minted before 2026-09-24 records HOW MANY declarations
        # diverged but not WHICH, so a row that diverged then and diverges now
        # reads as new. That errs toward red (a ledger entry clears it), and it
        # is said rather than left for the reader to rediscover.
        if (bf.get("diverged_count") or 0) > 0 and "diverged_rows" not in bf:
            summary["baseline_note"] = ("baseline predates `diverged_rows`: {} diverged row(s) "
                                        "are unnamed there".format(bf.get("diverged_count")))
        out["files"].append(summary)
    return out


def render(result: dict, out=sys.stdout) -> None:
    for f in result["files"]:
        if "note" in f:
            print("  decl-guard {}: {}".format(f["file"], f["note"]), file=out)
            continue
        s0, s1 = f["success"]
        print("  decl-guard {}: success {} -> {}, {} newly failing row(s), {} fixed{}".format(
            f["file"], s0, s1, f["new_failing_rows"], f["fixed_rows"],
            " ({})".format(f["baseline_note"]) if f.get("baseline_note") else ""), file=out)
    for r in result["new_failures"]:
        hint = " (likely the unnamed raw-parse row {} moving to its next wall -- "\
               "ledger it if so)".format(r["likely_moved_from"]) if r.get("likely_moved_from") else ""
        print("  NEW-FAIL {} :: {}{} -- {}".format(r["file"], r["decl"], hint, r["error"][:160].replace("\n", " ")),
              file=out)
    for r in result["ledgered"]:
        print("  LEDGERED {} :: {} (owner {}, expires {})".format(
            r["file"], r["decl"], r["ledger"]["owner"], r["ledger"]["expires"]), file=out)


def _load(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


# ---------------------------------------------------------------- self-test
def _rep(rows: List[Tuple[str, str]], success: int = 1, diverged: Optional[List[str]] = None) -> dict:
    f = {"key": "F.lean", "success_count": success,
         "per_error_class": [{"decl": d, "error": e} for d, e in rows]}
    if diverged:
        f["diverged_rows"] = diverged
    return {"files": [f]}


def _selftest() -> int:
    today = _dt.date(2026, 9, 24)
    fails = 0

    def check(name: str, cond: bool) -> None:
        nonlocal fails
        print("  {}: {}".format("PASS" if cond else "FAIL", name))
        fails += 0 if cond else 1

    # 1. a newly failing named row is caught although the count ROSE
    base = _rep([("a", "a: elaboration error at line 3: x")], success=5)
    meas = _rep([("b", "b: elaboration error at line 9: y")], success=6)
    r = guard(base, meas, None, today)
    check("new named failure caught with a rising count",
          [x["decl"] for x in r["new_failures"]] == ["b"] and [x["decl"] for x in r["fixed"]] == ["a"])
    # 2. two anonymous rows trading places are NOT one row
    base = _rep([("[anonymous]", "[anonymous]: elaboration error at line 43: x")])
    meas = _rep([("[anonymous]", "[anonymous]: elaboration error at line 226: x")])
    r = guard(base, meas, None, today)
    check("anonymous rows keyed by line",
          [x["decl"] for x in r["new_failures"]] == ["[anonymous]@line:226"])
    # 3. the same anonymous row with a different fvar spelling and no line keeps its key
    k1 = row_key("[anonymous]", "[anonymous]: Kernel check failed: FVarId(9223372036854775809)")
    k2 = row_key("[anonymous]", "[anonymous]: Kernel check failed: FVarId(9223372036854775900)")
    check("line-less anonymous row keyed by a normalised content hash", k1 == k2 and k1.startswith("[anonymous]@sha256:"))
    # 4. parser-recovery NOTES are not declarations
    base = _rep([])
    meas = _rep([("parser recovery [parser.recovery]", "parser recovery [parser.recovery]: at line 5")])
    check("parser-recovery notes are not keyed", guard(base, meas, None, today)["new_failures"] == [])
    # 5. a declaration that spent its budget is not a pass
    meas = _rep([], diverged=["slow: did not finish at line 12 -- spent the whole budget"])
    check("a diverged row is a new failure", [x["decl"] for x in guard(_rep([]), meas, None, today)["new_failures"]] == ["slow"])
    # 6. the ledger admits exactly the named row, dated, owned
    ratchet = {LEDGER_KEY: [{"file": "F.lean", "decl": "b", "owner": "o", "reason": "r", "expires": "2026-10-01"}]}
    meas = _rep([("b", "b: at line 1: y"), ("c", "c: at line 2: z")])
    r = guard(_rep([]), meas, ratchet, today)
    check("ledger admits only its own row",
          [x["decl"] for x in r["ledgered"]] == ["b"] and [x["decl"] for x in r["new_failures"]] == ["c"])
    # 7. an EXPIRED or ownerless or far-future entry admits nothing and is a problem
    for bad in ({"expires": "2026-09-01"}, {"owner": ""}, {"expires": "2999-01-01"}):
        e = dict(ratchet[LEDGER_KEY][0])
        e.update(bad)
        rr = {LEDGER_KEY: [e]}
        r = guard(_rep([]), _rep([("b", "b: at line 1: y")]), rr, today)
        check("ledger entry {} admits nothing".format(bad), [x["decl"] for x in r["new_failures"]] == ["b"])
        check("ledger entry {} is a validation problem".format(bad), bool(validate_ledger(rr, ["F.lean"], today)))
    # 8. the moved-wall hint names the raw row but still FAILS
    base = _rep([("[anonymous]", "[anonymous]: elaboration error at line 435: Parse error: parser recovery produced raw declaration")])
    meas = _rep([("P.inj", "P.inj: elaboration error at line 436: match pattern")])
    r = guard(base, meas, None, today)
    check("moved wall is hinted and still fails",
          len(r["new_failures"]) == 1 and r["new_failures"][0].get("likely_moved_from") == "[anonymous]@line:435")
    print("SRCELAB_DECL_GUARD_SELFTEST={} failed={}".format("ok" if fails == 0 else "fail", fails))
    return 0 if fails == 0 else 1


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--baseline")
    ap.add_argument("--measured")
    ap.add_argument("--ratchet", default="data/source_elab_ratchet.json")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--validate-ledger", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return _selftest()
    try:
        ratchet = _load(a.ratchet) if a.ratchet else None
    except (OSError, ValueError) as exc:
        print("decl-guard: unreadable ratchet {}: {}".format(a.ratchet, exc), file=sys.stderr)
        return 2
    if a.validate_ledger:
        pinned = sorted((ratchet or {}).get("files", {}).keys())
        probs = validate_ledger(ratchet, pinned)
        for p in probs:
            print("  decl-guard ledger: " + p, file=sys.stderr)
        return 1 if probs else 0
    if not a.baseline or not a.measured:
        ap.error("--baseline and --measured are required")
    try:
        res = guard(_load(a.baseline), _load(a.measured), ratchet)
    except (OSError, ValueError) as exc:
        print("decl-guard: unreadable report: {}".format(exc), file=sys.stderr)
        return 2
    if a.json:
        json.dump(res, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
    else:
        render(res)
    return 1 if res["new_failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
