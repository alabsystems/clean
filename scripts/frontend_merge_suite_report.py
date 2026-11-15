#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Plan and judge the frontend merge suite (scripts/frontend_merge_suite.sh).

The driver runs `targo --unverified test --locked --no-fail-fast` over the
frontend crates in two legs -- lib/bins/integration targets, then doctests --
and hands the raw cargo output here. This file owns the two decisions the
driver must not make by eye:

  plan    Which targets the run leg selects. Every integration test target of
          the selected packages, minus the PINNED slow-list, and the slow-list
          is refused unless each entry was MEASURED over the budget: a
          slow-list entry under budget is a suppression, not a pin.

  report  One verdict per target from the cargo output, a table, and a
          machine-readable summary. Verdicts:

            GREEN    ran, `test result: ok`, at least one test passed
            EMPTY    ran, `test result: ok`, zero tests passed and none ignored,
                     and the target is a BIN or a DOCTEST target (a bin with no
                     tests, a crate with no doctests). Not evidence; not red.
            RED      `test result: FAILED`, a binary that died before printing
                     a result line (signal, stack overflow, abort), a target
                     cargo itself lists under `error: N targets failed` -- or a
                     VACUOUS pass: a LIB or INTEGRATION target that passed zero
                     tests, or any target whose every test is `#[ignore]`d.
                     Nothing here filters by name, so a lib or `tests/*.rs`
                     target reporting `0 passed` tests nothing, and reading it
                     as not-red would be the repo's zero-selected-tests vacuity
                     (CLAUDE.md, "A run that selected zero tests is UNKNOWN").
                     Replayed 2026-09-25 over this suite's real run log: the
                     clean-elab lib's line rewritten to `0 passed; ...; 11976
                     ignored` read EMPTY and the suite said green.
            TIMEOUT  (a RED row) the per-target guard killed the binary: it
                     ran longer than FRONTEND_SUITE_TARGET_TIMEOUT_S. A hang is
                     not a result, and it must not hold every target after it
                     hostage (2026-10-07: one clean-elab test ran 53 CPU-minutes
                     without finishing and the suite could not complete).
            NOT_RUN  expected, but cargo never ran it -- the build failed, or
                     the run leg died. Counted as red: 0 targets not run is
                     the exit criterion, because cargo's own fail-fast used to
                     hide every target after the first failure.
            SLOW     excluded by the pinned slow-list; printed with its
                     measurement so the table never hides it.

          Exit 0 only when there is no RED and no NOT_RUN, and every leg's exit
          code agrees with the targets: a leg that exited non-zero with no
          target attributed a failure is red too (fail-closed, never "probably
          fine").

  run-target  The per-target guard: cargo's target RUNNER for the run leg
          (`--config target.<host>.runner=[...]`), so cargo hands every test
          binary of that leg here instead of executing it. It runs the binary
          in its own process group and kills the whole group once it outlives
          `--timeout`, printing the TIMEOUT marker `report` reads. It is an
          additional guard, never a fix: a target it kills is RED.

`--selftest` runs the refusal arms over recorded cargo output, and the guard's
arms over real processes. Pure stdlib and Python 3.9 compatible: the driver
runs it with the ambient `python3`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCHEMA = "clean-frontend-merge-suite-v1"
HEADER = re.compile(r"^\s+Running (?:unittests )?(\S+) \((.+)\)\s*$")
DOC_HEADER = re.compile(r"^\s+Doc-tests (\S+)\s*$")
RESULT = re.compile(
    r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored; "
    r"(\d+) measured; (\d+) filtered out; finished in ([0-9.]+)s"
)
FAILED_ITEM = re.compile(r"^\s+`-p (\S+) (--lib|--doc|--bin (\S+)|--test (\S+))`\s*$")
TIMEOUT_MARK = "frontend-merge-suite: TIMEOUT"
TIMEOUT = re.compile(r"^frontend-merge-suite: TIMEOUT (\S+) killed after (\d+)s\b")
TIMEOUT_EXIT = 124
HASH_SUFFIX = re.compile(r"-[0-9a-f]{16}$")


class PlanError(Exception):
    """The plan inputs are inconsistent; the suite must not run on them."""


def norm(name: str) -> str:
    return name.replace("-", "_")


def targets_from_metadata(metadata: dict, packages: list[str]) -> dict:
    """(kind, normalized name) -> target row, for the selected packages.

    `optional` marks a target cargo may legitimately skip: one with
    `required-features`, which `--bins`/`--tests` drop silently when the
    features are off.
    """
    out: dict = {}
    by_name = {p["name"]: p for p in metadata.get("packages", [])}

    def put(kind: str, pkg: str, t: dict, optional: bool) -> None:
        # cargo's output names a test binary by TARGET name only, so two
        # selected packages sharing one (kind, name) could not be told apart
        # in the log: refuse rather than attribute a verdict to a guess.
        key = (kind, norm(t["name"]))
        if key in out and out[key]["package"] != pkg:
            raise PlanError(f"{out[key]['package']} and {pkg} both have a {kind} target `{t['name']}`; "
                            "cargo's output cannot say which one a verdict belongs to")
        out[key] = dict(package=pkg, kind=kind, name=t["name"], optional=optional)

    for pkg in packages:
        if pkg not in by_name:
            raise PlanError(f"package {pkg} is not in the workspace metadata")
        for t in by_name[pkg]["targets"]:
            kinds = t.get("kind", [])
            optional = bool(t.get("required-features"))
            if "lib" in kinds or "rlib" in kinds or "proc-macro" in kinds:
                if t.get("test", True):
                    put("lib", pkg, t, False)
                if t.get("doctest", True):
                    put("doc", pkg, t, False)
            elif "bin" in kinds and t.get("test", True):
                put("bin", pkg, t, optional)
            elif "test" in kinds:
                put("test", pkg, t, optional)
    return out


def read_slow_list(path: Path | None, targets: dict, budget_s: float) -> list[dict]:
    """Parse and VALIDATE the pinned slow-list. Every refusal is a PlanError."""
    if path is None or not path.exists():
        return []
    rows = []
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        cols = [c.strip() for c in line.split("|")]
        if len(cols) != 5 or not all(cols):
            raise PlanError(f"{path}:{lineno}: want `package | test-target | seconds | measured | runs-instead`")
        pkg, name, secs, measured, instead = cols
        try:
            seconds = float(secs)
        except ValueError as exc:
            raise PlanError(f"{path}:{lineno}: measured seconds `{secs}` is not a number") from exc
        hit = targets.get(("test", norm(name)))
        if hit is None or hit["package"] != pkg:
            raise PlanError(f"{path}:{lineno}: {pkg} has no integration test target `{name}` -- a stale slow-list row")
        if seconds <= budget_s:
            raise PlanError(
                f"{path}:{lineno}: `{name}` was measured at {seconds:.2f}s, inside the {budget_s:.0f}s budget. "
                "A slow-list row under budget is a suppression, not a pin: delete it."
            )
        rows.append(dict(package=pkg, name=name, seconds=seconds, measured=measured, instead=instead))
    return rows


def plan_args(targets: dict, slow: list[dict]) -> list[str]:
    """The run leg's target selection. `--lib --bins --tests` when nothing is
    pinned slow; otherwise every non-slow integration test named explicitly."""
    if not slow:
        return ["--lib", "--bins", "--tests"]
    skip = {norm(s["name"]) for s in slow}
    args = ["--lib", "--bins"]
    for (kind, key), t in sorted(targets.items()):
        if kind == "test" and key not in skip and not t["optional"]:
            args += ["--test", t["name"]]
    return args


def parse_log(text: str, targets: dict, doc: bool) -> tuple[dict, set]:
    """Per-target observations and cargo's own failed-target list."""
    seen: dict = {}
    failed_listed: set = set()
    current = None
    for line in text.splitlines():
        m = DOC_HEADER.match(line) if doc else HEADER.match(line)
        if m:
            if current is not None and "result" not in seen[current]:
                seen[current]["crashed"] = True
            if doc:
                key = ("doc", norm(m.group(1)))
            else:
                src, binary = m.group(1), m.group(2)
                stem = HASH_SUFFIX.sub("", Path(binary).name)
                kind = "test" if src.startswith("tests/") else ("lib" if src.endswith("lib.rs") else "bin")
                key = (kind, norm(stem))
            seen.setdefault(key, {})
            current = key
            continue
        t = TIMEOUT.match(line)
        if t and current is not None:
            seen[current]["timeout_s"] = int(t.group(2))
            continue
        r = RESULT.match(line)
        if r and current is not None:
            seen[current]["result"] = dict(
                ok=r.group(1) == "ok", passed=int(r.group(2)), failed=int(r.group(3)),
                ignored=int(r.group(4)), seconds=float(r.group(7)),
            )
            continue
        f = FAILED_ITEM.match(line)
        if f:
            pkg, flag, bin_name, test_name = f.group(1), f.group(2), f.group(3), f.group(4)
            if flag == "--lib":
                key = ("lib", pkg)
            elif flag == "--doc":
                key = ("doc", pkg)
            elif bin_name:
                key = ("bin", norm(bin_name))
            else:
                key = ("test", norm(test_name))
            failed_listed.add(key)
    if current is not None and "result" not in seen[current]:
        seen[current]["crashed"] = True
    return seen, failed_listed


def judge(targets: dict, slow: list[dict], logs: dict, rcs: dict) -> dict:
    """Combine expectations, observations and leg exit codes into verdicts."""
    slow_keys = {("test", norm(s["name"])): s for s in slow}
    rows = []
    observed = {}
    for leg in ("run", "doc"):
        seen, listed = parse_log(logs.get(leg, ""), targets, doc=(leg == "doc"))
        for key, obs in seen.items():
            observed[key] = obs
        for key in listed:
            # cargo names a lib/doc failure by PACKAGE; map it to the target.
            if key[0] in ("lib", "doc"):
                key = next((k for k, t in targets.items() if k[0] == key[0] and t["package"] == key[1]), key)
            observed.setdefault(key, {})["listed_failed"] = True
    for key, t in sorted(targets.items(), key=lambda kv: (kv[1]["package"], kv[0][0], kv[0][1])):
        if key[0] == "doc" and "doc" not in logs:
            continue
        obs = observed.get(key)
        row = dict(package=t["package"], kind=t["kind"], name=t["name"])
        if key in slow_keys:
            row.update(verdict="SLOW", seconds=slow_keys[key]["seconds"], note=slow_keys[key]["instead"])
        elif obs is None:
            if t["optional"]:
                continue
            row.update(verdict="NOT_RUN")
        else:
            res = obs.get("result")
            if res is not None:
                row.update(passed=res["passed"], failed=res["failed"], ignored=res["ignored"], seconds=res["seconds"])
            if obs.get("timeout_s") is not None:
                row["verdict"] = "RED"
                row["timeout_s"] = obs["timeout_s"]
                row["note"] = (f"TIMEOUT: killed by the per-target guard after {obs['timeout_s']}s "
                               "-- a hang, not a result")
            elif obs.get("listed_failed") or obs.get("crashed") or (res is not None and not res["ok"]):
                row["verdict"] = "RED"
                if res is None:
                    row["note"] = "no `test result:` line: the binary died before reporting"
            elif res["passed"] == 0 and (t["kind"] in ("lib", "test") or res["ignored"] > 0):
                # A vacuous pass is not a pass (see the module docstring).
                row["verdict"] = "RED"
                row["note"] = ("every test is #[ignore]d: the target tests nothing" if res["ignored"] > 0
                               else f"zero tests ran: a {t['kind']} target that tests nothing is vacuous, not green")
            elif res["passed"] == 0:
                row["verdict"] = "EMPTY"
            else:
                row["verdict"] = "GREEN"
        rows.append(row)
    unknown = sorted(k for k in observed if k not in targets)
    counts = {v: sum(1 for r in rows if r["verdict"] == v) for v in ("GREEN", "EMPTY", "RED", "NOT_RUN", "SLOW")}
    problems = []
    for leg, rc in rcs.items():
        if rc is None:
            continue
        leg_rows = [r for r in rows if (r["kind"] == "doc") == (leg == "doc")]
        if rc != 0 and not any(r["verdict"] in ("RED", "NOT_RUN") for r in leg_rows):
            problems.append(f"the {leg} leg exited {rc} but no target was attributed a failure")
    for key in unknown:
        problems.append(f"cargo ran {key[0]} `{key[1]}`, which is not in the planned target set")
    red = counts["RED"] + counts["NOT_RUN"] + len(problems)
    return dict(verdict="red" if red else "green", counts=counts, targets=rows, problems=problems)


def render(summary: dict, budget_s: float) -> str:
    out = []
    for r in summary["targets"]:
        secs = f"{r['seconds']:.2f}s" if "seconds" in r else "-"
        tally = f"{r.get('passed', '-')}/{r.get('failed', '-')}"
        note = f"  ({r['note']})" if r.get("note") else ""
        out.append(f"  {r['verdict']:<8} {r['package']:<13} {r['kind']:<4} {r['name']:<52} {tally:>9} {secs:>10}{note}")
    over = [r for r in summary["targets"] if r["verdict"] != "SLOW" and r.get("seconds", 0) > budget_s]
    for r in over:
        # Only an integration test target can be pinned slow (read_slow_list
        # refuses anything else): a lib, bin or doctest target IS the suite.
        advice = ("a slow-list candidate (pin it with its measurement, or make it faster)" if r["kind"] == "test"
                  else "not pinnable -- only integration test targets can be slow-listed, so it runs every time")
        out.append(f"  NOTE: {r['package']} {r['kind']} {r['name']} ran {r['seconds']:.2f}s, over the {budget_s:.0f}s budget "
                   f"-- {advice}")
    for p in summary["problems"]:
        out.append(f"  PROBLEM: {p}")
    c = summary["counts"]
    out.append(
        f"FRONTEND_MERGE_SUITE={summary['verdict']} green={c['GREEN']} red={c['RED']} not_run={c['NOT_RUN']} "
        f"empty={c['EMPTY']} slow={c['SLOW']} problems={len(summary['problems'])}"
    )
    return "\n".join(out)


def _load_targets(args) -> tuple[dict, list[dict]]:
    metadata = json.loads(Path(args.metadata).read_text())
    packages = [p for p in args.packages.split(",") if p]
    targets = targets_from_metadata(metadata, packages)
    slow = read_slow_list(Path(args.slow_list) if args.slow_list else None, targets, args.budget)
    return targets, slow


def run_target(command: list[str], timeout_s: float) -> int:
    """Run one test binary under the per-target guard; its exit status, or
    TIMEOUT_EXIT after killing its whole process group."""
    if not command:
        print("frontend-merge-suite: run-target: no command", file=sys.stderr)
        return 64
    # A new session, so the kill reaches whatever the binary spawned too.
    proc = subprocess.Popen(command, start_new_session=True)

    def forward(signum, _frame):
        try:
            os.killpg(proc.pid, signum)
        except ProcessLookupError:
            pass

    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, forward)
    try:
        rc = proc.wait(timeout=timeout_s)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()
        # One line on stdout, after every byte the binary wrote: `report`
        # attributes it to the target whose `Running` header precedes it.
        sys.stdout.flush()
        print(f"{TIMEOUT_MARK} {Path(command[0]).name} killed after {timeout_s:.0f}s "
              "(the per-target guard, FRONTEND_SUITE_TARGET_TIMEOUT_S)", flush=True)
        return TIMEOUT_EXIT
    return 128 - rc if rc < 0 else rc


def cmd_run_target(args) -> int:
    command = list(args.command)
    if command and command[0] == "--":
        command = command[1:]
    if args.timeout <= 0:
        print("frontend-merge-suite: run-target: --timeout must be positive", file=sys.stderr)
        return 64
    return run_target(command, args.timeout)


def cmd_plan(args) -> int:
    try:
        targets, slow = _load_targets(args)
    except PlanError as exc:
        print(f"frontend-merge-suite: PLAN REFUSED: {exc}", file=sys.stderr)
        return 2
    print("\n".join(plan_args(targets, slow)))
    return 0


def cmd_report(args) -> int:
    try:
        targets, slow = _load_targets(args)
    except PlanError as exc:
        print(f"frontend-merge-suite: PLAN REFUSED: {exc}", file=sys.stderr)
        return 2
    logs = {"run": Path(args.run_log).read_text(errors="replace") if args.run_log else ""}
    if args.doc_log:
        logs["doc"] = Path(args.doc_log).read_text(errors="replace")
    rcs = {"build": None, "run": args.run_rc, "doc": args.doc_rc if args.doc_log else None}
    summary = judge(targets, slow, logs, rcs)
    if args.build_rc not in (None, 0):
        summary["problems"].insert(0, f"the build leg exited {args.build_rc}")
        summary["verdict"] = "red"
    summary = dict(schema_version=SCHEMA, packages=args.packages.split(","), budget_s=args.budget,
                   slow_list=slow, legs=json.loads(args.legs) if args.legs else {}, **summary)
    if args.summary_out:
        Path(args.summary_out).write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
    print(render(summary, args.budget))
    return 0 if summary["verdict"] == "green" else 1


# --------------------------------------------------------------- selftest
_META = {"packages": [
    {"name": "p-a", "targets": [
        {"name": "p_a", "kind": ["lib"], "test": True, "doctest": True},
        {"name": "tool", "kind": ["bin"], "test": True},
        {"name": "gated", "kind": ["bin"], "test": True, "required-features": ["cli"]},
        {"name": "fast_e2e", "kind": ["test"], "test": True},
        {"name": "slow_probe", "kind": ["test"], "test": True},
    ]},
]}
_OK = "test result: ok. {p} passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in {s}s"
_BAD = "test result: FAILED. 3 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.37s"


def _log(*blocks: str) -> str:
    return "\n".join(blocks) + "\n"


def _hdr(src: str, stem: str) -> str:
    return f"     Running {src} (target/wt/debug/deps/{stem}-0123456789abcdef)"


def selftest() -> int:
    targets = targets_from_metadata(_META, ["p-a"])
    green_run = _log(_hdr("unittests src/lib.rs", "p_a"), _OK.format(p=5, s="1.0"),
                     _hdr("unittests src/bin/tool.rs", "tool"), _OK.format(p=0, s="0.0"),
                     _hdr("tests/fast_e2e.rs", "fast_e2e"), _OK.format(p=2, s="0.5"),
                     _hdr("tests/slow_probe.rs", "slow_probe"), _OK.format(p=1, s="900.0"))
    green_doc = _log("   Doc-tests p_a", _OK.format(p=1, s="0.2"))
    arms = []

    def arm(name, cond):
        arms.append((name, bool(cond)))

    s = judge(targets, [], {"run": green_run, "doc": green_doc}, {"run": 0, "doc": 0})
    arm("an all-green run is green, and a zero-test bin is EMPTY, not GREEN",
        s["verdict"] == "green" and s["counts"]["GREEN"] == 4 and s["counts"]["EMPTY"] == 1)
    arm("a required-features bin cargo skipped is not NOT_RUN", s["counts"]["NOT_RUN"] == 0)
    # Vacuous passes (2026-09-25 review): zero tests in a lib or integration
    # target, or every test ignored anywhere, is RED -- with the zero-test bin
    # above and a doctest-free crate below as the controls that stay EMPTY.
    for label, old, new, kind in (
            ("a lib target that runs zero tests is RED, not EMPTY",
             _OK.format(p=5, s="1.0"), _OK.format(p=0, s="0.0"), "lib"),
            ("an integration target that runs zero tests is RED, not EMPTY",
             _OK.format(p=2, s="0.5"), _OK.format(p=0, s="0.0"), "test"),
            ("a bin whose every test is ignored is RED, not EMPTY",
             _OK.format(p=0, s="0.0"), _OK.format(p=0, s="0.0").replace("0 ignored", "3 ignored"), "bin")):
        s = judge(targets, [], {"run": green_run.replace(old, new), "doc": green_doc}, {"run": 0, "doc": 0})
        arm(label, s["verdict"] == "red" and s["counts"]["RED"] == 1
            and any(r["kind"] == kind and r["verdict"] == "RED" and "note" in r for r in s["targets"]))
    s = judge(targets, [], {"run": green_run, "doc": green_doc.replace(_OK.format(p=1, s="0.2"), _OK.format(p=0, s="0.0"))},
              {"run": 0, "doc": 0})
    arm("control: a crate with no doctests stays EMPTY and the suite green",
        s["verdict"] == "green" and s["counts"]["EMPTY"] == 2)
    notes = [ln for ln in render(s, 0.9).splitlines() if "NOTE:" in ln]
    arm("an over-budget lib is flagged but never offered to the slow-list, an over-budget test is",
        any("lib p_a ran 1.00s" in ln and "not pinnable" in ln for ln in notes)
        and any("test slow_probe ran 900.00s" in ln and "slow-list candidate" in ln for ln in notes)
        and len(notes) == 2)
    red_run = green_run.replace(_OK.format(p=2, s="0.5"), _BAD)
    s = judge(targets, [], {"run": red_run, "doc": green_doc}, {"run": 101, "doc": 0})
    arm("a FAILED result line is RED", s["verdict"] == "red" and s["counts"]["RED"] == 1)
    crash = _log(_hdr("unittests src/lib.rs", "p_a"), "error: test failed",
                 _hdr("tests/fast_e2e.rs", "fast_e2e"), _OK.format(p=2, s="0.5"))
    s = judge(targets, [], {"run": crash, "doc": green_doc}, {"run": 101, "doc": 0})
    arm("a binary that dies before its result line is RED",
        any(r["name"] == "p_a" and r["kind"] == "lib" and r["verdict"] == "RED" for r in s["targets"]))
    arm("a target cargo never ran is NOT_RUN", s["counts"]["NOT_RUN"] == 2 and s["verdict"] == "red")
    s = judge(targets, [], {"run": green_run, "doc": green_doc}, {"run": 101, "doc": 0})
    arm("a non-zero leg with every target green is still red (unattributed failure)",
        s["verdict"] == "red" and s["problems"])
    listed = green_run + _log("error: 1 target failed:", "    `-p p-a --test fast_e2e`")
    s = judge(targets, [], {"run": listed, "doc": green_doc}, {"run": 101, "doc": 0})
    arm("a target cargo lists under `targets failed` is RED even with an ok line",
        any(r["name"] == "fast_e2e" and r["verdict"] == "RED" for r in s["targets"]))
    doc_listed = _log("   Doc-tests p_a", _BAD, "error: 1 target failed:", "    `-p p-a --doc`")
    s = judge(targets, [], {"run": green_run, "doc": doc_listed}, {"run": 0, "doc": 101})
    arm("a doctest failure is attributed to the doc target",
        any(r["kind"] == "doc" and r["verdict"] == "RED" for r in s["targets"]) and not s["problems"])
    # A private temp file, never a path in the tree: two selftests running at
    # once (the gate leg and a hand run) must not share it.
    fd, tmp_name = tempfile.mkstemp(prefix="frontend_suite_selftest_slow_", suffix=".txt")
    os.close(fd)
    slow_path = Path(tmp_name)
    try:
        slow_path.write_text("p-a | slow_probe | 1400.5 | 2026-09-24 | verify_runner\n")
        slow = read_slow_list(slow_path, targets, 600)
        arm("a measured-over-budget row pins a slow target", len(slow) == 1)
        args = plan_args(targets, slow)
        arm("the plan names every non-slow test and drops the slow one",
            "fast_e2e" in args and "slow_probe" not in args and "--bins" in args)
        without_slow = green_run.split(_hdr("tests/slow_probe.rs", "slow_probe"))[0]
        s = judge(targets, slow, {"run": without_slow, "doc": green_doc}, {"run": 0, "doc": 0})
        arm("a SLOW target is reported, not hidden, and does not count as NOT_RUN",
            s["counts"]["SLOW"] == 1 and s["counts"]["NOT_RUN"] == 0 and s["verdict"] == "green")
        for bad, why in (("p-a | slow_probe | 30.0 | 2026-09-24 | verify_runner\n", "under-budget row refused"),
                         ("p-a | gone_probe | 1400 | 2026-09-24 | verify_runner\n", "stale row refused"),
                         ("p-a | slow_probe | 1400 |  | verify_runner\n", "row without a measurement date refused")):
            slow_path.write_text(bad)
            try:
                read_slow_list(slow_path, targets, 600)
                arm(why, False)
            except PlanError:
                arm(why, True)
    finally:
        slow_path.unlink(missing_ok=True)
    arm("an empty slow-list plans the whole --tests set", plan_args(targets, []) == ["--lib", "--bins", "--tests"])
    twin = {"packages": _META["packages"] + [
        {"name": "p-b", "targets": [{"name": "fast_e2e", "kind": ["test"], "test": True}]}]}
    try:
        targets_from_metadata(twin, ["p-a", "p-b"])
        arm("two packages sharing a test target name are refused", False)
    except PlanError:
        arm("two packages sharing a test target name are refused", True)
    # The per-target guard (2026-10-07). Report side: a TIMEOUT marker makes
    # its target RED with a TIMEOUT note, and the targets after it are still
    # judged on their own lines.
    hung = _log(_hdr("unittests src/lib.rs", "p_a"), _OK.format(p=5, s="1.0"),
                _hdr("unittests src/bin/tool.rs", "tool"), _OK.format(p=0, s="0.0"),
                _hdr("tests/fast_e2e.rs", "fast_e2e"), "running 2 tests",
                f"{TIMEOUT_MARK} fast_e2e-0123456789abcdef killed after 900s (the per-target guard)",
                "error: test failed, to rerun pass `-p p-a --test fast_e2e`",
                _hdr("tests/slow_probe.rs", "slow_probe"), _OK.format(p=1, s="900.0"))
    s = judge(targets, [], {"run": hung, "doc": green_doc}, {"run": 101, "doc": 0})
    arm("a target the per-target guard killed is RED with a TIMEOUT note",
        s["verdict"] == "red" and s["counts"]["RED"] == 1 and s["counts"]["NOT_RUN"] == 0
        and any(r["name"] == "fast_e2e" and r["verdict"] == "RED" and r.get("timeout_s") == 900
                and "TIMEOUT" in r.get("note", "") for r in s["targets"])
        and any(r["name"] == "slow_probe" and r["verdict"] == "GREEN" for r in s["targets"]))
    # Process side: real children, a fraction of a second each.
    started = time.monotonic()
    rc = run_target([sys.executable, "-c", "import time; time.sleep(30)"], 0.5)
    arm("the guard kills a binary that outlives its timeout and exits 124",
        rc == TIMEOUT_EXIT and time.monotonic() - started < 15)
    fd, pid_name = tempfile.mkstemp(prefix="frontend_suite_selftest_child_", suffix=".pid")
    os.close(fd)
    pid_path = Path(pid_name)
    try:
        spawn = ("import pathlib, subprocess, sys, time; "
                 "c = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)']); "
                 f"pathlib.Path({str(pid_path)!r}).write_text(str(c.pid)); time.sleep(30)")
        started = time.monotonic()
        rc = run_target([sys.executable, "-c", spawn], 2.0)
        child = int(pid_path.read_text() or "0")
        alive = child > 0
        deadline = time.monotonic() + 10
        while alive and time.monotonic() < deadline:
            try:
                os.kill(child, 0)
                time.sleep(0.1)
            except ProcessLookupError:
                alive = False
        arm("the guard kills the binary's whole process group, not only the binary",
            rc == TIMEOUT_EXIT and child > 0 and not alive and time.monotonic() - started < 20)
    finally:
        pid_path.unlink(missing_ok=True)
    arm("a binary inside its timeout keeps its own exit status",
        run_target([sys.executable, "-c", "import sys; sys.exit(3)"], 30) == 3
        and run_target([sys.executable, "-c", "pass"], 30) == 0)
    failed = [n for n, ok in arms if not ok]
    for n, ok in arms:
        print(f"  selftest {'ok' if ok else 'FAILED'}: {n}")
    print(f"FRONTEND_MERGE_SUITE_SELFTEST={'fail' if failed else 'ok'} arms={len(arms)} failed={len(failed)}")
    return 1 if failed else 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--selftest", action="store_true")
    sub = ap.add_subparsers(dest="cmd")
    rt = sub.add_parser("run-target", help="the per-target guard (cargo's runner for the run leg)")
    rt.add_argument("--timeout", type=float, required=True, help="seconds before the binary's group is killed")
    rt.add_argument("command", nargs=argparse.REMAINDER)
    for name in ("plan", "report"):
        p = sub.add_parser(name)
        p.add_argument("--metadata", required=True)
        p.add_argument("--packages", required=True)
        p.add_argument("--slow-list")
        p.add_argument("--budget", type=float, default=600.0)
        if name == "report":
            p.add_argument("--run-log")
            p.add_argument("--doc-log")
            p.add_argument("--build-rc", type=int)
            p.add_argument("--run-rc", type=int)
            p.add_argument("--doc-rc", type=int)
            p.add_argument("--legs", help="JSON object of per-leg facts (wall seconds, commands)")
            p.add_argument("--summary-out")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    if args.cmd == "run-target":
        return cmd_run_target(args)
    if args.cmd == "plan":
        return cmd_plan(args)
    if args.cmd == "report":
        return cmd_report(args)
    ap.print_help()
    return 64


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
