#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The suite runner's durable record is journalled, and the journal is wired.

WHY THIS EXISTS
---------------
`data/suite_state/` serves two roles that fight each other. It is EVIDENCE --
tracked, reviewable, readable from other machines -- and it is RUNNER OUTPUT
that changes without a commit. The second role makes every `git checkout`,
`git restore` or branch switch over that directory a silent data loss: the
files revert to their committed content (or vanish), with exit code 0 and no
warning. A routine crash-recovery checkout destroyed a complete 14.33-hour
sweep that way, and the results survived only because the worker's out-of-tree
log happened to still hold them.

The fix makes the tracked directory a PROJECTION of an append-only journal that
lives outside the working tree, where git has no handle on it:

    write_record() -> journal_append()   truth, append-only, out of tree
                   -> _project_record()  projection, tracked, reviewable

That fix has exactly one way to become worthless, and it is the way this repo
has now found seven times: somebody removes the journal call, or the heal, and
nothing notices, because the projection still looks right until the day a
checkout happens. So the wiring is re-derived here rather than trusted, on
every push.

FIVE CLAUSES, EACH FALSIFIABLE
------------------------------
  J1 WIRED        `write_record` calls `journal_append` BEFORE `_project_record`,
                  and `cmd_status` heals the projection. Read out of the runner's
                  source; delete either call and this goes red.
  J2 INTACT       every line of the journal parses as a journal entry. A torn
                  write is reported, never skipped.
  J3 PROJECTED    the projection does not disagree with the journal. A `restore`
                  row here IS the accident, caught before it is forgotten.
  J4 SUPERSEDED   every `superseded-*/` directory under `data/suite_state/shards/`
                  carries a marker saying what retired it, and none of its record
                  ids collides with a live shard plan. Those records are kept as
                  evidence and are mechanically inert; this pins both halves.
  J5 UNPROTECTED  a record file that is git-dirty (modified or untracked) and NOT
                  covered by the journal is an unprotected write -- exactly the
                  thing a checkout eats. Committed records are safe because git
                  holds them; uncommitted ones must be in the journal.

J5 is why this gate is safe in a throwaway worktree: a fresh checkout has a
clean `data/suite_state/`, so it has nothing to protect and nothing to report.

Usage:
    scripts/check_suite_journal.py             # check (fail-closed, ~0.1 s)
    scripts/check_suite_journal.py --selftest  # mutation arms on itself
    scripts/check_suite_journal.py --json
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RUNNER = "scripts/verify_runner.py"
STATE_REL = "data/suite_state"
PLAN_REL = "data/suite_plans"
SUPERSEDED_PREFIX = "superseded-"
MARKER = "SUPERSEDED.json"
MARKER_FIELDS = ("schema", "superseded_by", "retired_at", "record_count", "disposition")
VERDICT = "SUITE_JOURNAL"


class Red(Exception):
    """A refusal, carrying the actionable diagnostic and nothing else."""


# ── J1: the wiring, re-derived from the runner's source ──────────────────────


def check_wiring(root: Path) -> list[str]:
    """Read the runner and require the two calls that make the journal load-bearing.

    Deliberately source-level rather than behavioural: the behavioural proof
    lives in scripts/test_verify_runner.py, which needs a git repo and a sweep.
    This runs in milliseconds inside the pre-push hook and catches the only
    edit that silently disarms the protection.
    """
    path = root / RUNNER
    try:
        src = path.read_text()
    except OSError as exc:
        return [f"J1 WIRED: cannot read {RUNNER}: {exc}"]
    out: list[str] = []
    body = re.search(
        r"\ndef write_record\(record: dict\[str, Any\]\) -> None:\n(.*?)(?=\n\ndef |\n\n# )",
        src, re.S,
    )
    if not body:
        return [f"J1 WIRED: {RUNNER} has no `write_record(record) -> None` to inspect"]
    text = body.group(1)
    j = text.find("journal_append(record)")
    p = text.find("_project_record(record)")
    if j < 0:
        out.append(
            "J1 WIRED: write_record no longer calls journal_append(record) -- every verdict it "
            "writes is again a tracked file and nothing else, so the next `git checkout` over "
            f"{STATE_REL}/ loses it silently. Restore the write-through in {RUNNER}."
        )
    if p < 0:
        out.append(f"J1 WIRED: write_record no longer calls _project_record(record) in {RUNNER}")
    if j >= 0 and p >= 0 and j > p:
        out.append(
            "J1 WIRED: write_record projects BEFORE it journals. The order is the protection: "
            "journal-last leaves a window in which the tracked file exists and the durable one "
            "does not, and that window is exactly when a checkout is fatal."
        )
    # Built from parts, and backticked in the message below: a bare
    # `scripts/<name>.py` literal in this file reads as an INVOCATION to
    # check_gate_registry.py's runner scan, which then walks that file and
    # demands registry rows for everything IT mentions.
    tests = root / "scripts" / "test_verify_runner.py"
    if tests.exists() and 'VERIFY_RUNNER_JOURNAL_DIR' not in tests.read_text():
        out.append(
            "J1 WIRED: `scripts/test_verify_runner.py` does not redirect "
            "VERIFY_RUNNER_JOURNAL_DIR, so every synthetic record it writes lands in the "
            "REAL machine journal -- where it is indistinguishable from a measurement and "
            "can be re-projected into the tracked directory by any `status`. Sandbox it "
            "beside VERIFY_RUNNER_STATE_DIR and VERIFY_RUNNER_TARGET_DIR."
        )
    if "heal_projection()" not in src:
        out.append(
            "J1 WIRED: nothing calls heal_projection() -- the journal would still hold the "
            f"verdicts, but `{RUNNER} status` would keep reporting UNKNOWN for records the "
            "working tree lost, which is the 14.33-hour outcome all over again."
        )
    return out


# ── J2/J3: the journal itself, and the projection derived from it ────────────


def reconcile_report(root: Path, env: dict[str, str] | None = None) -> dict:
    """Ask the runner, do not re-implement it.

    A second implementation of "does the projection match the journal" is a
    second thing to keep in sync, and the one that drifts is always the copy in
    the gate.
    """
    argv = [sys.executable, str(root / RUNNER), "journal", "--json"]
    proc = subprocess.run(argv, capture_output=True, text=True, env=env or os.environ.copy())
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise Red(
            f"J3 PROJECTED: `{RUNNER} journal --json` produced no readable report "
            f"({exc.msg}); exit {proc.returncode}, stderr: {proc.stderr.strip()[:400]}"
        ) from exc


def check_report(report: dict) -> list[str]:
    out: list[str] = []
    for problem in report.get("problems", []):
        out.append(
            f"J2 INTACT: the journal has a line that is not a journal entry -- {problem}. "
            "A torn or truncated append means the history is not what it claims; inspect the "
            "file before trusting any row derived from it."
        )
    restores = [a for a in report.get("actions", []) if a.get("verdict") == "restore"]
    if restores:
        names = ", ".join(a["target"] for a in restores[:6])
        more = f" (+{len(restores) - 6} more)" if len(restores) > 6 else ""
        out.append(
            f"J3 PROJECTED: {len(restores)} record(s) in {STATE_REL}/ are missing or older than "
            f"the journal -- {names}{more}. This is the checkout accident, caught. Recover with "
            f"`{RUNNER} journal --apply` (or any `status`), then COMMIT the restored files."
        )
    return out


# ── J4: the retired fine-cut shard records ───────────────────────────────────


def check_superseded(root: Path) -> list[str]:
    out: list[str] = []
    shard_root = root / STATE_REL / "shards"
    if not shard_root.is_dir():
        return out
    live_ids: set[str] = set()
    plan_dir = root / PLAN_REL
    if plan_dir.is_dir():
        for plan_path in sorted(plan_dir.glob("*.json")):
            try:
                plan = json.loads(plan_path.read_text())
            except (OSError, json.JSONDecodeError):
                continue
            for shard in plan.get("shards", []):
                key = shard.get("key")
                if key:
                    live_ids.add(str(key))
    for parent in sorted(p for p in shard_root.iterdir() if p.is_dir()):
        for retired in sorted(p for p in parent.iterdir() if p.is_dir()):
            if not retired.name.startswith(SUPERSEDED_PREFIX):
                out.append(
                    f"J4 SUPERSEDED: {retired.relative_to(root)} is a directory the runner never "
                    f"reads (record_path only addresses shards/<parent>/<id>.json) and whose name "
                    f"does not start with `{SUPERSEDED_PREFIX}`. Either it is live evidence in the "
                    "wrong place, or it is retired and must say so in its name."
                )
                continue
            marker = retired / MARKER
            if not marker.exists():
                out.append(
                    f"J4 SUPERSEDED: {retired.relative_to(root)} holds "
                    f"{len(list(retired.glob('*.json')))} retired record(s) with no {MARKER}. "
                    "Records nobody reads and nobody dated are indistinguishable from records "
                    "somebody forgot; state what retired them."
                )
                continue
            try:
                doc = json.loads(marker.read_text())
            except (OSError, json.JSONDecodeError) as exc:
                out.append(f"J4 SUPERSEDED: {marker.relative_to(root)} is unreadable: {exc}")
                continue
            missing = [f for f in MARKER_FIELDS if f not in doc]
            if missing:
                out.append(
                    f"J4 SUPERSEDED: {marker.relative_to(root)} is missing {missing}"
                )
                continue
            declared = doc.get("record_count")
            actual = len([p for p in retired.glob("*.json") if p.name != MARKER])
            if declared != actual:
                out.append(
                    f"J4 SUPERSEDED: {marker.relative_to(root)} declares {declared} retired "
                    f"record(s); {actual} are present. A retired set that changes size is either "
                    "being edited or being read."
                )
            collisions = sorted(
                {
                    key
                    for key in live_ids
                    if (retired / f"{parent.name}__shard__{key}.json").exists()
                }
            )
            if collisions:
                out.append(
                    f"J4 SUPERSEDED: shard key(s) {collisions} exist BOTH in the live plan and "
                    f"in {retired.relative_to(root)}. A human globbing the shard directory would "
                    "mix a retired measurement with a live one."
                )
    return out


# ── J5: dirty records the journal does not cover ─────────────────────────────


def check_unprotected(root: Path, report: dict) -> list[str]:
    """A record that is uncommitted AND unjournalled is protected by nothing."""
    if shutil.which("git") is None:
        return []
    proc = subprocess.run(
        # -uall, not the default: git COLLAPSES an untracked directory to one
        # `?? data/suite_state/` line, and a collapsed line names no record. The
        # first version of this clause missed exactly that case.
        ["git", "-C", str(root), "status", "--porcelain", "-uall", "--", STATE_REL],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        return []
    dirty: list[str] = []
    for line in proc.stdout.splitlines():
        rel = line[3:].strip().strip('"')
        if " -> " in rel:
            rel = rel.split(" -> ", 1)[1]
        if rel.endswith(".json") and Path(rel).name != MARKER:
            dirty.append(rel)
    if not dirty:
        return []
    covered: set[str] = set()
    for action in report.get("actions", []):
        covered.add(action["target"])
    unprotected = []
    for rel in dirty:
        path = root / rel
        try:
            target = json.loads(path.read_text()).get("target")
        except (OSError, json.JSONDecodeError):
            continue
        if target and target not in covered:
            unprotected.append(f"{rel} ({target})")
    if not unprotected:
        return []
    shown = ", ".join(unprotected[:6])
    more = f" (+{len(unprotected) - 6} more)" if len(unprotected) > 6 else ""
    return [
        f"J5 UNPROTECTED: {len(unprotected)} record(s) under {STATE_REL}/ are uncommitted AND "
        f"absent from the journal -- {shown}{more}. Git does not hold them and the journal does "
        f"not either, so one checkout ends them. Run `{RUNNER} journal --adopt` to take local "
        "ownership of records that arrived some other way, or commit them."
    ]


# ── driver ───────────────────────────────────────────────────────────────────


def check(root: Path, env: dict[str, str] | None = None) -> tuple[list[str], dict]:
    report = reconcile_report(root, env)
    failures = check_wiring(root)
    failures += check_report(report)
    failures += check_superseded(root)
    failures += check_unprotected(root, report)
    return failures, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--selftest", action="store_true", help="run the mutation arms")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    if args.selftest:
        return selftest()
    try:
        failures, report = check(ROOT)
    except Red as exc:
        print(f"{VERDICT}=red", file=sys.stderr)
        print(f"  {exc}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps({"verdict": "red" if failures else "ok",
                          "failures": failures, "reconcile": report}, indent=2, sort_keys=True))
        return 1 if failures else 0
    if failures:
        print(f"{VERDICT}=red")
        for failure in failures:
            print(f"  {failure}")
        return 1
    journal = report.get("journal", "?")
    counts = report.get("counts", {})
    print(f"{VERDICT}=ok journal={journal} "
          f"exists={str(report.get('journal_exists')).lower()} "
          f"ok={counts.get('ok', 0)} foreign={counts.get('foreign', 0)} "
          f"unjournalled={len(report.get('unjournalled', []))}")
    return 0


# ── the mutation arms ────────────────────────────────────────────────────────
#
# Every arm below plants a defect in a COPY of the tree and requires this
# checker to say no, then requires the unmutated copy to say yes. A gate whose
# arms only run one direction cannot tell "refuses correctly" from "refuses
# always".


def _sandbox(tmp: Path) -> Path:
    root = tmp / "root"
    (root / "scripts").mkdir(parents=True)
    (root / STATE_REL / "shards" / "clean-verify__lib").mkdir(parents=True)
    (root / PLAN_REL).mkdir(parents=True)
    shutil.copy2(ROOT / RUNNER, root / RUNNER)
    return root


def _env_for(root: Path, tmp: Path) -> dict[str, str]:
    env = os.environ.copy()
    env["VERIFY_RUNNER_STATE_DIR"] = str(root / STATE_REL)
    env["VERIFY_RUNNER_JOURNAL_DIR"] = str(tmp / "journal")
    env["VERIFY_RUNNER_TARGET_DIR"] = str(tmp / "target")
    return env


def _write_record(root: Path, tmp: Path, target: str, status: str, stamp: str,
                  journalled: bool = True) -> None:
    """Drive the REAL runner, so the arms exercise the shipped write path."""
    record = {"schema": "clean.suite_state/v1", "target": target, "status": status,
              "source": "measured", "finished_at": stamp, "final_line": "test result: ok"}
    code = (
        "import json,sys;sys.path.insert(0,%r);import verify_runner as vr;"
        "rec=json.loads(sys.argv[1]);"
        "(vr.write_record if %r else vr._project_record)(rec)"
        % (str(root / "scripts"), journalled)
    )
    subprocess.run([sys.executable, "-c", code, json.dumps(record)],
                   check=True, env=_env_for(root, tmp), capture_output=True)


def _rewrite_write_record(src: str, body: str) -> str:
    """Replace write_record's whole body, for the J1 arms."""
    pattern = r"(\ndef write_record\(record: dict\[str, Any\]\) -> None:\n)(.*?)(\n\n\ndef )"
    out, count = re.subn(pattern, lambda m: m.group(1) + body + m.group(3), src, count=1, flags=re.S)
    if count != 1:
        raise Red("selftest: could not locate write_record's body to mutate")
    return out


def selftest() -> int:
    arms: list[tuple[str, bool, str]] = []

    def arm(name: str, root: Path, tmp: Path, want_red: bool, expect: str = "") -> None:
        try:
            failures, _ = check(root, _env_for(root, tmp))
            got_red = bool(failures)
            blob = " | ".join(failures)
        except Red as exc:
            got_red, blob = True, str(exc)
        ok = got_red == want_red and (not expect or expect in blob)
        arms.append((name, ok, blob[:200] if not ok else ""))

    with tempfile.TemporaryDirectory(prefix="suite_journal_selftest_") as raw:
        tmp = Path(raw)
        # ---- the clean baseline: nothing planted, must be GREEN -------------
        base = _sandbox(tmp / "clean")
        _write_record(base, tmp / "clean", "gate::clippy", "GREEN", "2026-08-25T00:00:00Z")
        arm("clean sandbox is green", base, tmp / "clean", False)

        # ---- J1: the journal call removed from write_record -----------------
        #
        # The mutation REWRITES the whole body rather than deleting a line, so
        # the arm keeps working when the body grows (it already has: the OSError
        # branch that keeps a measurement alive when the journal cannot be
        # written). A mutation pinned to one literal line is a mutation that
        # stops firing the next time somebody edits around it.
        m = _sandbox(tmp / "j1a")
        (m / RUNNER).write_text(_rewrite_write_record(
            (m / RUNNER).read_text(), "    _project_record(record)"))
        arm("J1 unwired journal_append", m, tmp / "j1a", True, "no longer calls journal_append")

        # ---- J1: journalling AFTER projecting -------------------------------
        m = _sandbox(tmp / "j1b")
        (m / RUNNER).write_text(_rewrite_write_record(
            (m / RUNNER).read_text(),
            "    _project_record(record)\n    journal_append(record)"))
        arm("J1 wrong order", m, tmp / "j1b", True, "projects BEFORE it journals")

        # ---- J1: the heal removed -------------------------------------------
        m = _sandbox(tmp / "j1c")
        src = (m / RUNNER).read_text().replace("        heal_projection()", "        pass")
        (m / RUNNER).write_text(src)
        arm("J1 unwired heal", m, tmp / "j1c", True, "nothing calls heal_projection()")

        # ---- J1: the runner's own tests writing the real journal ------------
        # Not hypothetical: this is what the tests DID until it was measured.
        m = _sandbox(tmp / "j1d")
        (m / "scripts" / "test_verify_runner.py").write_text(
            'os.environ["VERIFY_RUNNER_STATE_DIR"] = "x"\n')
        arm("J1 tests not sandboxing the journal", m, tmp / "j1d", True,
            "does not redirect VERIFY_RUNNER_JOURNAL_DIR")

        # ---- J2: a torn line in the journal ---------------------------------
        m = _sandbox(tmp / "j2")
        _write_record(m, tmp / "j2", "gate::clippy", "GREEN", "2026-08-25T00:00:00Z")
        jf = next((tmp / "j2" / "journal").glob("*.jsonl"))
        jf.write_text(jf.read_text() + '{"schema":"clean.suite_journal/v1","tar\n')
        arm("J2 torn journal line", m, tmp / "j2", True, "not a journal entry")

        # ---- J3: THE ACCIDENT -- the projected record removed ---------------
        m = _sandbox(tmp / "j3")
        _write_record(m, tmp / "j3", "gate::clippy", "GREEN", "2026-08-25T00:00:00Z")
        (m / STATE_REL / "gate__clippy.json").unlink()
        arm("J3 record lost from the projection", m, tmp / "j3", True, "This is the checkout accident")

        # ---- J3: the record REWOUND to older content (the harder form) ------
        m = _sandbox(tmp / "j3b")
        _write_record(m, tmp / "j3b", "gate::clippy", "GREEN", "2026-08-25T00:00:00Z")
        (m / STATE_REL / "gate__clippy.json").write_text(json.dumps(
            {"schema": "clean.suite_state/v1", "target": "gate::clippy", "status": "GREEN",
             "source": "measured", "finished_at": "2026-08-01T00:00:00Z"}, indent=2) + "\n")
        arm("J3 record rewound to stale content", m, tmp / "j3b", True, "missing or older than")

        # ---- J3: a NEWER foreign record is not an accident ------------------
        m = _sandbox(tmp / "j3c")
        _write_record(m, tmp / "j3c", "gate::clippy", "GREEN", "2026-08-25T00:00:00Z")
        (m / STATE_REL / "gate__clippy.json").write_text(json.dumps(
            {"schema": "clean.suite_state/v1", "target": "gate::clippy", "status": "RED",
             "source": "measured", "finished_at": "2026-09-01T00:00:00Z"}, indent=2) + "\n")
        arm("J3 newer foreign record is allowed", m, tmp / "j3c", False)

        # ---- J3: an ADOPTED entry never overwrites differing content --------
        # The arm that stops adoption becoming a laundering path: a snapshot the
        # journal did not witness being measured must not be able to displace a
        # record that arrived by git.
        m = _sandbox(tmp / "j3d")
        (m / STATE_REL / "gate__clippy.json").write_text(json.dumps(
            {"schema": "clean.suite_state/v1", "target": "gate::clippy", "status": "GREEN",
             "source": "measured", "finished_at": "2026-08-25T00:00:00Z"}, indent=2) + "\n")
        subprocess.run([sys.executable, str(m / RUNNER), "journal", "--adopt"],
                       check=True, env=_env_for(m, tmp / "j3d"), capture_output=True)
        (m / STATE_REL / "gate__clippy.json").write_text(json.dumps(
            {"schema": "clean.suite_state/v1", "target": "gate::clippy", "status": "RED",
             "source": "measured", "finished_at": "2026-08-01T00:00:00Z"}, indent=2) + "\n")
        arm("J3 an adopted entry never overwrites", m, tmp / "j3d", False)

        # ---- J4: a retired directory with no marker -------------------------
        m = _sandbox(tmp / "j4a")
        retired = m / STATE_REL / "shards" / "clean-verify__lib" / "superseded-fine-cut-deadbeef"
        retired.mkdir(parents=True)
        (retired / "clean-verify__lib__shard__x.json").write_text("{}\n")
        arm("J4 retired dir without a marker", m, tmp / "j4a", True, f"no {MARKER}")

        # ---- J4: the marker's count disagrees with the directory ------------
        m = _sandbox(tmp / "j4b")
        retired = m / STATE_REL / "shards" / "clean-verify__lib" / "superseded-fine-cut-deadbeef"
        retired.mkdir(parents=True)
        (retired / "clean-verify__lib__shard__x.json").write_text("{}\n")
        (retired / MARKER).write_text(json.dumps(
            {"schema": "clean.suite_state_superseded/v1", "superseded_by": "x",
             "retired_at": "2026-01-01", "record_count": 99, "disposition": "kept"}) + "\n")
        arm("J4 marker miscounts the retired set", m, tmp / "j4b", True, "are present")

        # ---- J4: a retired shard key that is also live ----------------------
        m = _sandbox(tmp / "j4c")
        retired = m / STATE_REL / "shards" / "clean-verify__lib" / "superseded-fine-cut-deadbeef"
        retired.mkdir(parents=True)
        (retired / "clean-verify__lib__shard__misc.json").write_text("{}\n")
        (retired / MARKER).write_text(json.dumps(
            {"schema": "clean.suite_state_superseded/v1", "superseded_by": "x",
             "retired_at": "2026-01-01", "record_count": 1, "disposition": "kept"}) + "\n")
        (m / PLAN_REL / "clean-verify__lib.json").write_text(json.dumps(
            {"shards": [{"key": "misc"}]}) + "\n")
        arm("J4 retired key collides with a live one", m, tmp / "j4c", True, "BOTH in the live plan")

        # ---- J4: a correctly-marked retired set is fine ---------------------
        m = _sandbox(tmp / "j4d")
        retired = m / STATE_REL / "shards" / "clean-verify__lib" / "superseded-fine-cut-deadbeef"
        retired.mkdir(parents=True)
        (retired / "clean-verify__lib__shard__gone.json").write_text("{}\n")
        (retired / MARKER).write_text(json.dumps(
            {"schema": "clean.suite_state_superseded/v1", "superseded_by": "x",
             "retired_at": "2026-01-01", "record_count": 1, "disposition": "kept"}) + "\n")
        arm("J4 a marked retired set is allowed", m, tmp / "j4d", False)

        # ---- J5: an uncommitted, unjournalled record ------------------------
        m = _sandbox(tmp / "j5")
        subprocess.run(["git", "-C", str(m), "init", "-q", "-b", "main"], check=True,
                       capture_output=True)
        for key, value in (("user.email", "t@e.com"), ("user.name", "t")):
            subprocess.run(["git", "-C", str(m), "config", key, value], check=True,
                           capture_output=True)
        _write_record(m, tmp / "j5", "gate::from_elsewhere", "GREEN", "2026-08-25T00:00:00Z",
                      journalled=False)
        arm("J5 uncommitted and unjournalled", m, tmp / "j5", True, "Git does not hold them")

        # ---- J5: the same record, once COMMITTED, is protected by git -------
        subprocess.run(["git", "-C", str(m), "add", "-A"], check=True, capture_output=True)
        subprocess.run(["git", "-C", str(m), "commit", "-qm", "state"], check=True,
                       capture_output=True)
        arm("J5 committed record is protected", m, tmp / "j5", False)

    width = max(len(name) for name, _, _ in arms)
    failed = 0
    for name, ok, detail in arms:
        print(f"  {'PASS' if ok else 'FAIL'}  {name:<{width}}{'' if ok else '  <- ' + detail}")
        failed += 0 if ok else 1
    print(f"{VERDICT}_SELFTEST={'ok' if not failed else 'red'} "
          f"{len(arms) - failed}/{len(arms)} arms")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
