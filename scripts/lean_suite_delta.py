#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""What changed between two Lean test-suite conformance ledgers.

`scripts/lean_suite_conformance.py` keeps one ledger
(`data/lean_suite_conformance.json`): per file of Lean's own `tests/elab` and
`tests/elab_fail`, the pinned Lean's verdict, `clean check`'s, and the outcome
they derive. A re-mint replaces it whole. This script says, row by row, what a
re-mint changed, so that a figure quoted from the new ledger can be read
against the old one: which false accepts cleared, which agreements were lost
(an `--update --rebase` accepts those), which were gained.

Usage:
  scripts/lean_suite_delta.py OLD [NEW] [--out REPORT.json]
  scripts/lean_suite_delta.py --selftest

OLD and NEW are each a path, or `<rev>:<path>` read with `git show` (rev a hex
sha or a ref name; an ambiguous name, or a file of that name beside the
ref, is refused: write `./<name>` for the file). NEW defaults to the ledger
in the working tree. Both must pass the conformance script's own ledger
validation, and both must be OF the same Lean tests checkout
(`tests_source.git_rev`), Lean toolchain and world: rows of two checkouts
share file names, not file texts, so a delta across them is refused rather
than reported. Rebases are append-only, so a NEW whose rebases do not extend
OLD's is refused as the wrong order.

The report names both ledgers (the ref given and whether it was a file or a
git read, the sha256 of the bytes read, the date, the Clean tree, the Lean
toolchain and world, the caps and the date of Lean's verdicts), the totals
before and after, every outcome transition with its count (a row only one
ledger has goes from or to `absent`), and the files in each of: new false
accepts, false accepts cleared, agreements lost, agreements gained, Lean's
verdict changed, verdicts changed with the outcome unchanged, added and
removed; the rebases NEW records that OLD does not; and the regressions no
such rebase records, each kind only by the list of its kind
(`lean_suite_conformance.rebase_record`). It reports; it is not a gate, and
exits 0 whatever it lists.

Verdict line: LEAN_SUITE_DELTA=reported | selftest-ok |
failed:unreadable|not-comparable|unwritable|selftest.
Exit 0 / 1 (failed) / 2 (usage).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from typing import Callable, Dict, List, Optional, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_suite_conformance as conf  # noqa: E402

REV_PATH_RE = re.compile(r"^([0-9A-Za-z][0-9A-Za-z._/~^-]*):(\S+)$")
SCHEMA = "Clean-lean-suite-delta-v1"


class DeltaError(Exception):
    """A ledger that cannot be read (`unreadable`), or two that cannot be
    compared (`not-comparable`)."""

    def __init__(self, msg: str, kind: str = "unreadable") -> None:
        super().__init__(msg)
        self.kind = kind


def _resolve_rev(rev: str, root: str) -> Optional[str]:
    """The commit `rev` names, or None. An ambiguous name is refused: git
    picks one and only warns, and the report would carry the one it picked."""
    try:
        r = subprocess.run(["git", "-C", root, "rev-parse", "--short=9", "--verify", rev + "^{commit}"],
                           capture_output=True, text=True, env=conf.git_env())
    except OSError as exc:
        raise DeltaError("git cannot run ({})".format(exc))
    if "ambiguous" in r.stderr:
        raise DeltaError("{}: an ambiguous ref name; give the commit".format(rev))
    return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else None


def read_ledger(spec: str, root: str) -> Tuple[dict, dict]:
    """(ledger, identity) for a path or a `<rev>:<path>` spec."""
    m = REV_PATH_RE.match(spec)
    rev = _resolve_rev(m.group(1), root) if m else None
    if os.path.exists(spec) and rev:
        raise DeltaError("{}: both a file and <rev>:<path>; write ./{} for the file".format(spec, spec))
    if os.path.exists(spec):
        try:
            with open(spec, "rb") as f:
                raw = f.read()
        except OSError as exc:
            raise DeltaError("{}: unreadable ({})".format(spec, exc))
        ref = os.path.relpath(os.path.realpath(spec), os.path.realpath(root))
        ref = os.path.abspath(spec) if ref.startswith("..") else ref
        source = "file"
    elif rev and m:
        try:
            raw = subprocess.run(["git", "-C", root, "show", "{}:{}".format(rev, m.group(2))],
                                 capture_output=True, check=True, env=conf.git_env()).stdout
        except (OSError, subprocess.CalledProcessError) as exc:
            raise DeltaError("{}: git cannot read it ({})".format(spec, exc))
        ref = "{}:{}".format(rev, m.group(2))
        source = "git"
    else:
        raise DeltaError("{}: no such file, and no commit for a <rev>:<path>".format(spec))
    try:
        led = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, ValueError) as exc:
        raise DeltaError("{}: not JSON ({})".format(spec, exc))
    if not isinstance(led, dict):
        raise DeltaError("{}: not a ledger object".format(spec))
    probs = conf.validate_ledger(led)
    if probs:
        raise DeltaError("{}: not a valid ledger: {}".format(spec, "; ".join(probs[:3])))
    ident = {"ref": ref, "source": source, "sha256": hashlib.sha256(raw).hexdigest(), "generated": led.get("generated"),
             "clean_tree_commit": (led.get("clean") or {}).get("tree_commit"),
             "lean_toolchain": led.get("lean_toolchain"), "lean_world": led.get("lean_world"),
             "lean_verdicts_measured_on": (led.get("lean") or {}).get("verdicts_measured_on"),
             "caps": led.get("caps"), "tests_git_rev": led["tests_source"]["git_rev"]}
    return led, ident


ABSENT = "absent"


def _comparable(old: dict, new: dict) -> None:
    """Refuse two ledgers whose rows do not measure the same thing, or whose
    order is not OLD then NEW."""
    for what, get in (("Lean tests checkouts", lambda l: l["tests_source"]["git_rev"]),
                      ("Lean toolchains", lambda l: l.get("lean_toolchain")),
                      ("Lean worlds", lambda l: l.get("lean_world") or (l.get("lean_toolchain") or "").split(":")[-1])):
        if get(old) != get(new):
            raise DeltaError("the ledgers are of different {} ({} and {}); their rows share names, not "
                             "verdicts of one thing".format(what, get(old), get(new)), "not-comparable")
    ro, rn = old.get("rebases") or [], new.get("rebases") or []
    if rn[:len(ro)] != ro:
        raise DeltaError("NEW's rebases do not extend OLD's: rebases are append-only, so NEW is older than "
                         "OLD or of another line", "not-comparable")


def delta(old: dict, new: dict) -> dict:
    """The row-by-row difference from `old` to `new` (both valid ledgers).
    A row only one ledger has is a transition from or to `absent`."""
    _comparable(old, new)
    a, b = old["files"], new["files"]
    transitions: Dict[str, int] = {}
    lists: Dict[str, List[dict]] = {k: [] for k in (
        "new_false_accepts", "false_accepts_cleared", "agreements_lost", "agreements_gained",
        "lean_verdict_changed", "verdicts_changed_same_outcome")}
    for k in sorted(set(a) | set(b)):
        x, y = a.get(k), b.get(k)
        was, now = (x or {}).get("outcome", ABSENT), (y or {}).get("outcome", ABSENT)
        if x and y and x["lean"] != y["lean"]:
            lists["lean_verdict_changed"].append({"file": k, "was": x["lean"], "now": y["lean"]})
        if was == now:
            if x and y and (x["lean"], x["clean"]) != (y["lean"], y["clean"]):
                lists["verdicts_changed_same_outcome"].append(
                    {"file": k, "outcome": now, "was": [x["lean"], x["clean"]], "now": [y["lean"], y["clean"]]})
            continue
        key = "{} -> {}".format(was, now)
        transitions[key] = transitions.get(key, 0) + 1
        row = {"file": k, "was": was, "now": now}
        if now == conf.FALSE_ACCEPT:
            lists["new_false_accepts"].append(row)
        if was == conf.FALSE_ACCEPT and now in conf.AGREE:
            lists["false_accepts_cleared"].append(row)
        if was in conf.AGREE and now not in conf.AGREE:
            lists["agreements_lost"].append(row)
        if now in conf.AGREE and was not in conf.AGREE:
            lists["agreements_gained"].append(row)
    ta, tb = old["totals"], new["totals"]
    added = (new.get("rebases") or [])[len(old.get("rebases") or []):]
    # `--update` writes over a regression only with `--rebase`, whose record
    # (lean_suite_conformance.rebase_record) names each file it accepted in
    # the list of its kind: a lost agreement, a new false accept (an
    # unledgered row by its outcome), a row no longer measured. Each kind is
    # accounted only by its own list, so a file accepted as a disagreement
    # does not also cover its becoming a false accept.
    def recorded(kind: str) -> List[dict]:
        return [x for r in added for x in (r.get(kind) or []) if isinstance(x, dict)]
    lost_ok = {x.get("file") for x in recorded("new_disagreements")}
    fa_ok = {x.get("file") for x in recorded("new_false_accepts")} | {
        x.get("file") for x in recorded("extra") if x.get("now") == conf.FALSE_ACCEPT}
    missing_ok = {f for r in added for f in (r.get("missing") or []) if isinstance(f, str)}
    unnamed = sorted({r["file"] for r in lists["new_false_accepts"] if r["file"] not in fa_ok}
                     | {r["file"] for r in lists["agreements_lost"]
                        if r["file"] not in (missing_ok if r["now"] == ABSENT else lost_ok)})
    return {
        "totals": {k: {"before": ta.get(k, 0), "after": tb.get(k, 0), "change": tb.get(k, 0) - ta.get(k, 0)}
                   for k in sorted(set(ta) | set(tb), key=lambda k: (k not in conf.OUTCOMES, k))},
        "transitions": dict(sorted(transitions.items(), key=lambda kv: (-kv[1], kv[0]))),
        **lists,
        "added": sorted(set(b) - set(a)),
        "removed": sorted(set(a) - set(b)),
        "rebases_added": added,
        "regressions_without_a_rebase": unnamed,
        "unchanged_rows": sum(1 for k in set(a) & set(b) if a[k] == b[k]),
        "caps_changed": old.get("caps") != new.get("caps"),
    }


def report(old_spec: str, new_spec: str, root: str) -> dict:
    old, oi = read_ledger(old_spec, root)
    new, ni = read_ledger(new_spec, root)
    return {"schema_version": SCHEMA,
            "what": ("Row-by-row difference between two lean-suite conformance ledgers, written by "
                     "scripts/lean_suite_delta.py from the two refs below; never hand-edited."),
            "old": oi, "new": ni, **delta(old, new)}


def render(rep: dict) -> None:
    o, n = rep["old"], rep["new"]
    print("  {} ({}, Clean {}) -> {} ({}, Clean {})".format(o["ref"], o["generated"], o["clean_tree_commit"],
                                                            n["ref"], n["generated"], n["clean_tree_commit"]))
    for k, t in rep["totals"].items():
        if t["change"]:
            print("  {:<28} {:>5} -> {:>5} ({:+d})".format(k, t["before"], t["after"], t["change"]))
    for k, c in rep["transitions"].items():
        print("  {:>4}  {}".format(c, k))
    for k in ("new_false_accepts", "agreements_lost", "regressions_without_a_rebase", "lean_verdict_changed",
              "verdicts_changed_same_outcome", "added", "removed"):
        if rep[k]:
            print("  {}: {}".format(k, len(rep[k])))
    if rep["rebases_added"]:
        print("  rebases recorded since: {}".format(len(rep["rebases_added"])))
    if rep["caps_changed"]:
        print("  the caps changed: a cap row can move with them")


# ----------------------------------------------------------------- self-test
def selftest_checks(check: Callable[[str, bool], None]) -> None:
    """The delta's own checks, run by this script's --selftest and by
    lean_suite_conformance.py --selftest (the hook leg)."""
    rows = {
        "elab/a.lean": {"contract": "accept", "lean": "accept", "clean": "accept"},
        "elab/b.lean": {"contract": "accept", "lean": "accept", "clean": "reject"},
        "elab_fail/c.lean": {"contract": "reject", "lean": "reject", "clean": "reject"},
        "elab_fail/d.lean": {"contract": "reject", "lean": "reject", "clean": "accept"},
    }

    def led(over: Optional[Dict[str, dict]] = None, rev: str = "abc") -> dict:
        r = json.loads(json.dumps(rows))
        for k, v in (over or {}).items():
            r[k] = dict(r.get(k, {}), **v)
        return conf.build_ledger(None, r, {"git_rev": rev}, "clean", {}, True)

    base = led()
    d = delta(base, led())
    check("delta: identical ledgers differ in nothing",
          not d["transitions"] and d["unchanged_rows"] == 4 and not any(d[k] for k in (
              "new_false_accepts", "false_accepts_cleared", "agreements_lost", "agreements_gained",
              "lean_verdict_changed", "added", "removed")))
    d = delta(base, led({"elab/a.lean": {"clean": "reject"}, "elab_fail/d.lean": {"clean": "reject"}}))
    check("delta: a lost agreement and a cleared false accept are each named",
          [r["file"] for r in d["agreements_lost"]] == ["elab/a.lean"]
          and d["regressions_without_a_rebase"] == ["elab/a.lean"]
          and [r["file"] for r in d["false_accepts_cleared"]] == ["elab_fail/d.lean"]
          and [r["file"] for r in d["agreements_gained"]] == ["elab_fail/d.lean"]
          and d["transitions"] == {"agree-accept -> clean-rejects-lean-accepts": 1,
                                   "clean-accepts-lean-rejects -> agree-reject": 1}
          and d["totals"][conf.FALSE_ACCEPT]["change"] == -1)
    d = delta(base, led({"elab_fail/c.lean": {"clean": "accept"}}))
    check("delta: a new false accept is named",
          [r["file"] for r in d["new_false_accepts"]] == ["elab_fail/c.lean"]
          and d["regressions_without_a_rebase"] == ["elab_fail/c.lean"])
    def rebased_to(over: Dict[str, dict], extra: Optional[Dict[str, dict]] = None,
                   drop: Tuple[str, ...] = (), forget: Optional[Tuple[str, str]] = None) -> dict:
        """NEW as `--update --rebase` writes it over `over`, `extra` and `drop`
        (the producer's own compare and rebase_record); `forget` removes one
        file from one list of the record, as a hand edit would."""
        measured = {k: {"clean": dict(rows[k], **over.get(k, {}))["clean"]} for k in rows if k not in drop}
        measured.update(extra or {})
        res = conf.compare(base, measured)
        rec = conf.rebase_record(res, "selftest: accepted on the record", "2026-10-28")
        if forget:
            rec[forget[0]] = [x for x in rec[forget[0]] if (x if isinstance(x, str) else x["file"]) != forget[1]]
        new = conf.build_ledger(base, res["rows"], {"git_rev": "abc"}, "clean", {}, True)
        new["rebases"] = [rec]
        return new
    fa_lost = {"elab_fail/c.lean": {"clean": "accept"}, "elab/a.lean": {"clean": "reject"}}
    d = delta(base, rebased_to(fa_lost))
    check("delta: every regression the producer's rebase record names is accounted",
          d["regressions_without_a_rebase"] == [] and len(d["rebases_added"]) == 1
          and [r["file"] for r in d["new_false_accepts"]] == ["elab_fail/c.lean"])
    d = delta(base, rebased_to(fa_lost, forget=("new_false_accepts", "elab_fail/c.lean")))
    check("delta: a file accepted as a lost agreement does not also cover its new false accept",
          d["regressions_without_a_rebase"] == ["elab_fail/c.lean"])
    new_fa = {"elab_fail/n.lean": {"contract": "reject", "lean": "reject", "clean": "accept"}}
    d = delta(base, led(new_fa))
    check("delta: a false accept in a row OLD does not have is a new false accept",
          [r["file"] for r in d["new_false_accepts"]] == ["elab_fail/n.lean"]
          and d["new_false_accepts"][0]["was"] == ABSENT
          and d["regressions_without_a_rebase"] == ["elab_fail/n.lean"]
          and delta(base, rebased_to({}, extra=new_fa))["regressions_without_a_rebase"] == [])
    gone = json.loads(json.dumps(base))
    del gone["files"]["elab/a.lean"]
    d = delta(base, gone)
    check("delta: an agreeing row NEW no longer has is a lost agreement",
          [(r["file"], r["now"]) for r in d["agreements_lost"]] == [("elab/a.lean", ABSENT)]
          and d["regressions_without_a_rebase"] == ["elab/a.lean"]
          and delta(base, rebased_to({}, drop=("elab/a.lean",)))["regressions_without_a_rebase"] == [])
    d = delta(base, led({"elab_fail/d.lean": {"clean": conf.PARTIAL}}))
    check("delta: a row whose verdicts move but whose outcome stays is named",
          [r["file"] for r in d["verdicts_changed_same_outcome"]] == ["elab_fail/d.lean"]
          and not d["transitions"])
    d = delta(base, led({"elab/b.lean": {"lean": "reject"}}))
    check("delta: a changed Lean verdict is named although no Clean verdict moved",
          [r["file"] for r in d["lean_verdict_changed"]] == ["elab/b.lean"])
    grown = led({"elab/e.lean": {"contract": "accept", "lean": "accept", "clean": "accept"}})
    d = delta(base, grown)
    check("delta: added and removed rows are named", d["added"] == ["elab/e.lean"]
          and delta(grown, base)["removed"] == ["elab/e.lean"])
    try:
        delta(base, led(rev="def"))
        refused = False
    except DeltaError:
        refused = True
    check("delta: ledgers of two tests checkouts are refused, not compared", refused)

    def refused_as(old: dict, new: dict) -> str:
        try:
            delta(old, new)
        except DeltaError as exc:
            return exc.kind
        return ""
    other = led()
    other["lean_toolchain"] = "leanprover/lean4:v4.31.0"
    later = rebased_to(fa_lost)
    check("delta: ledgers of two Lean toolchains, or in the wrong order, are refused, not compared",
          refused_as(base, other) == "not-comparable" and refused_as(later, base) == "not-comparable"
          and refused_as(base, later) == "")
    with tempfile.TemporaryDirectory() as tmp:
        p = os.path.join(tmp, "l.json")
        subprocess.run(["git", "-C", tmp, "init", "-q"], check=False, capture_output=True, env=conf.git_env())
        with open(p, "w", encoding="utf-8") as f:
            json.dump(base, f)
        subprocess.run(["git", "-C", tmp, "add", "l.json"], check=False, capture_output=True, env=conf.git_env())
        subprocess.run(["git", "-C", tmp, "-c", "user.email=selftest@example.invalid", "-c", "user.name=selftest",
                        "-c", "commit.gpgsign=false", "commit", "-q", "-m", "fixture"],
                       check=False, capture_output=True, env=conf.git_env())
        changed = led({"elab/a.lean": {"clean": "reject"}})
        with open(p, "w", encoding="utf-8") as f:
            json.dump(changed, f)
        try:
            rep = report("HEAD:l.json", p, tmp)
            ok = (rep["old"]["ref"].endswith(":l.json") and rep["new"]["ref"] == "l.json"
                  and (rep["old"]["source"], rep["new"]["source"]) == ("git", "file")
                  and [r["file"] for r in rep["agreements_lost"]] == ["elab/a.lean"])
        except DeltaError:
            ok = False
        check("delta: a <rev>:<path> ledger is read through git, beside a working-tree one", ok)
        bad = json.loads(json.dumps(base))
        bad["files"]["elab/a.lean"]["outcome"] = "agree-reject"
        with open(p, "w", encoding="utf-8") as f:
            json.dump(bad, f)
        try:
            report("HEAD:l.json", p, tmp)
            refused = False
        except DeltaError:
            refused = True
        check("delta: a ledger the conformance validator refuses is refused", refused)

        def git(*args: str) -> None:
            subprocess.run(["git", "-C", tmp, "-c", "user.email=selftest@example.invalid", "-c",
                            "user.name=selftest", "-c", "commit.gpgsign=false"] + list(args),
                           check=False, capture_output=True, env=conf.git_env())
        with open(p, "w", encoding="utf-8") as f:
            json.dump(changed, f)
        git("commit", "-q", "-am", "second")
        git("branch", "dup", "HEAD~1")
        git("tag", "dup", "HEAD")
        try:
            report("dup:l.json", p, tmp)
            ambiguous = ""
        except DeltaError as exc:
            ambiguous = str(exc)
        here = os.getcwd()
        os.chdir(tmp)
        try:
            with open("HEAD:l.json", "w", encoding="utf-8") as f:
                json.dump(base, f)
            try:
                report("HEAD:l.json", "l.json", tmp)
                shadow = ""
            except DeltaError as exc:
                shadow = str(exc)
            plain = report("./HEAD:l.json", "l.json", tmp)["old"]
        finally:
            os.chdir(here)
        check("delta: an ambiguous ref, or a file that shadows a <rev>:<path>, is refused, not guessed",
              "ambiguous" in ambiguous and "both a file and" in shadow
              and (plain["ref"], plain["source"]) == ("HEAD:l.json", "file"))


def _selftest() -> int:
    fails = 0

    def check(name: str, cond: bool) -> None:
        nonlocal fails
        print("  {}: {}".format("PASS" if cond else "FAIL", name))
        fails += 0 if cond else 1
    selftest_checks(check)
    print("LEAN_SUITE_DELTA={}".format("selftest-ok" if fails == 0 else "failed:selftest"))
    return 0 if fails == 0 else 1


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("old", nargs="?")
    ap.add_argument("new", nargs="?", default=conf.LEDGER)
    ap.add_argument("--out", help="write the report (JSON) here")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return _selftest()
    if not a.old:
        ap.error("OLD is required")
    try:
        rep = report(a.old, a.new, conf.ROOT)
    except DeltaError as exc:
        print("  " + str(exc), file=sys.stderr)
        print("LEAN_SUITE_DELTA=failed:{}".format(exc.kind))
        return 1
    render(rep)
    if a.out:
        try:
            with open(a.out, "w", encoding="utf-8") as f:
                json.dump(rep, f, indent=1)
                f.write("\n")
        except OSError as exc:
            print("  cannot write {}: {}".format(a.out, exc), file=sys.stderr)
            print("LEAN_SUITE_DELTA=failed:unwritable")
            return 1
        print("  report written: {}".format(a.out))
    print("LEAN_SUITE_DELTA=reported")
    return 0


if __name__ == "__main__":
    sys.exit(main())
