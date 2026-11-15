#!/usr/bin/env python3
"""olean_replay_differential -- Lean's `leanchecker` against `clean olean replay`, per module.

WHAT IT MEASURES. For every module of a list, whether Clean's `clean olean replay --exact
--json <M>` (the module's own declarations replayed over its trusted imports, Clean's kernel
as the checker) reaches the same VERDICT as Lean's own replay of that module, and, for a
refused module, whether Clean refuses the declaration Lean names.

THE LEAN SIDE IS LEAN'S OWN CODE. `leanchecker <M>` (`src/lean/LeanChecker.lean`, pinned
v4.30.0-rc2) replays every module `M` is a dotted prefix of, as parallel tasks, so on an
internal module such as `Std` its verdict covers hundreds of modules and it needs several
gigabytes (measured 2026-09-25: killed at a 5 GB cap). So each module's Lean verdict comes
from `scripts/leanchecker_exact.lean`, which runs leanchecker's `replayFromImports`, copied
verbatim, on exactly that module; and on every module with no submodule -- where the two
select the same module -- `leanchecker` itself runs too, and the two must agree or the run
fails. Nothing here reads a verdict from prose: Lean's is the driver's `EXACT <m> ok|fail`
line and leanchecker's exit status; Clean's is the `ok` field of the one JSON record the verb
prints for the module, which must agree with its exit status.

FAIL-CLOSED. Exit 0 only when every module was measured on every side and every verdict
agrees (with the named declaration refused on both sides). A disagreement, a timeout, an
RSS-cap kill, a crash, a missing or duplicate record, or an empty module list is exit 1; a
usage or environment problem (no toolchain, no `clean` binary) is exit 2. Rows are appended
to `--out` as JSON lines, so an interrupted run resumes; every Clean row carries the sha256
of the binary that produced it, and a resume reuses only rows of the binary it runs now (a
row of any other binary is measured again, never mixed in); `--summary` writes the verdicts,
the disagreements with both sides' reasons, and a time/RSS table over the modules with no
submodule, for which `leanchecker`'s run replays that module alone (both tools measured by
`/usr/bin/time`: wall seconds and peak RSS).

MEMORY. Run it under scripts/heavy_gate.sh. The Lean side runs `--lean-jobs` processes at a
time (each well under 2 GB on Init/Std); the Clean side runs `--clean-jobs` modules at a time,
each capped at `--rss-cap-gb`, so reserve at least their product.

USAGE
  python3 scripts/olean_replay_differential.py --clean target/release/clean \\
      --prefix Init --prefix Std --out replay.jsonl --summary replay-summary.json
  python3 scripts/olean_replay_differential.py --clean <bin> --lean-path <mathlib LEAN_PATH> \\
      --modules-file sample.txt --out mathlib.jsonl --summary mathlib-summary.json
  python3 scripts/olean_replay_differential.py --selftest
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
EXACT_DRIVER = REPO / "scripts" / "leanchecker_exact.lean"
PROBLEM_RE = re.compile(r"leanchecker found a problem in (\S+)")
EXACT_RE = re.compile(r"^EXACT (\S+) (ok|fail)(?: (.*))?$")
# The declaration a Lean replay failure names: `replayConstant`'s wrapper, or
# `checkPostponedConstructors`/`Recursors` (`Lean/Replay.lean`).
DECL_RES = (
    re.compile(r"while replaying declaration '([^']*)'"),
    re.compile(r"(?:Invalid|No such) (?:constructor|recursor) (\S+)"),
)
MAXRSS_MAC = re.compile(r"(\d+)\s+maximum resident set size")
MAXRSS_LINUX = re.compile(r"Maximum resident set size \(kbytes\):\s*(\d+)")
REAL_MAC = re.compile(r"(\d+(?:\.\d+)?)\s+real\b")


class SetupError(Exception):
    """A usage or environment problem: exit 2."""


# ---------------------------------------------------------------- toolchain & paths
def pinned_toolchain() -> Path:
    """The toolchain this checkout's `lean-toolchain` pins, under ~/.elan."""
    pin = (REPO / "lean-toolchain").read_text().strip()
    # `leanprover/lean4:v4.30.0-rc2` -> `leanprover--lean4---v4.30.0-rc2`
    org_repo, _, version = pin.partition(":")
    name = org_repo.replace("/", "--") + "---" + version
    path = Path.home() / ".elan" / "toolchains" / name
    if not (path / "bin" / "leanchecker").is_file():
        raise SetupError(f"pinned toolchain {pin} has no leanchecker at {path}")
    return path


def search_path(lean_path: str, toolchain: Path) -> list[Path]:
    """`initSearchPath`: LEAN_PATH entries, then `<toolchain>/lib/lean`."""
    roots = [Path(p) for p in lean_path.split(os.pathsep) if p]
    roots.append(toolchain / "lib" / "lean")
    out: list[Path] = []
    for root in roots:
        if root not in out:
            out.append(root)
    return out


def modules_under(prefix: str, roots: list[Path]) -> set[str]:
    """Every module `prefix` is a component prefix of (itself included)."""
    parts = prefix.split(".")
    found: set[str] = set()
    for root in roots:
        stem = root.joinpath(*parts)
        if (stem.parent / (stem.name + ".olean")).is_file():
            found.add(prefix)
        if stem.is_dir():
            for olean in stem.rglob("*.olean"):
                rel = olean.relative_to(root).with_suffix("")
                if all("." not in p for p in rel.parts):
                    found.add(".".join(rel.parts))
    return found


def lean_declaration(message: str) -> str | None:
    for pattern in DECL_RES:
        m = pattern.search(message or "")
        if m:
            return m.group(1)
    return None


# ---------------------------------------------------------------- measured runs
def children(pid: int) -> list[int]:
    out = subprocess.run(["pgrep", "-P", str(pid)], capture_output=True, text=True).stdout
    return [int(x) for x in out.split()]


def rss_kb(pid: int) -> int:
    out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True)
    text = out.stdout.strip()
    return int(text) if text.isdigit() else 0


def timed_run(cmd: list[str], env: dict, timeout: float, rss_cap_kb: int) -> dict:
    """Run `cmd` under `/usr/bin/time`, polling RSS; kill on timeout or cap."""
    flag = "-l" if sys.platform == "darwin" else "-v"
    with tempfile.TemporaryFile(mode="w+") as err:
        start = time.monotonic()
        proc = subprocess.Popen(["/usr/bin/time", flag, *cmd], stdout=subprocess.PIPE,
                                stderr=err, text=True, env=env)
        out_chunks: list[str] = []
        reader = threading.Thread(target=lambda: out_chunks.append(proc.stdout.read()))
        reader.start()
        killed = None
        peak = 0
        while proc.poll() is None:
            kids = children(proc.pid)
            total = sum(rss_kb(k) for k in kids)
            peak = max(peak, total)
            if killed is None and rss_cap_kb and total > rss_cap_kb:
                killed = "rss_cap"
            if killed is None and time.monotonic() - start > timeout:
                killed = "timeout"
            if killed:
                for k in kids:
                    try:
                        os.kill(k, 9)
                    except OSError:
                        pass
            time.sleep(0.1)
        reader.join()
        wall = time.monotonic() - start
        err.seek(0)
        stderr = err.read()
    m = MAXRSS_MAC.search(stderr)
    maxrss = int(m.group(1)) if m else None
    if maxrss is None:
        m = MAXRSS_LINUX.search(stderr)
        maxrss = int(m.group(1)) * 1024 if m else None
    # `/usr/bin/time`'s own elapsed time where it reports one (macOS `-l`);
    # otherwise the polling loop's, which overshoots by up to one poll.
    reals = REAL_MAC.findall(stderr)
    if reals:
        wall = float(reals[-1])
    return {"rc": proc.returncode, "wall_s": round(wall, 3), "killed": killed,
            "maxrss_bytes": maxrss, "poll_peak_bytes": peak * 1024,
            "stdout": "".join(out_chunks), "stderr": stderr}


def measured(run: dict) -> dict:
    return {k: run[k] for k in ("rc", "wall_s", "killed", "maxrss_bytes", "poll_peak_bytes")}


def exact_rows(batch: list[str], toolchain: Path, env: dict, timeout: float,
               cap_kb: int) -> list[dict]:
    """Lean's `replayFromImports` on exactly each module of `batch`, one process."""
    run = timed_run([str(toolchain / "bin" / "lean"), "--run", str(EXACT_DRIVER), *batch],
                    env, timeout, cap_kb)
    seen: dict[str, dict] = {}
    for line in run["stdout"].splitlines():
        m = EXACT_RE.match(line.strip())
        if m and m.group(1) in batch:
            message = m.group(3) or ""
            seen[m.group(1)] = {"verdict": "accept" if m.group(2) == "ok" else "reject",
                                "message": message[:2000],
                                "declaration": lean_declaration(message)}
    rows = []
    for module in batch:
        row = {"tool": "lean-exact", "module": module, "batch_wall_s": run["wall_s"],
               "batch_killed": run["killed"]}
        row.update(seen.get(module, {"verdict": "error", "stderr_tail": run["stderr"][-1500:]}))
        rows.append(row)
    return rows


def leanchecker_row(module: str, toolchain: Path, env: dict, timeout: float,
                    cap_kb: int) -> dict:
    run = timed_run([str(toolchain / "bin" / "leanchecker"), module], env, timeout, cap_kb)
    row = {"tool": "leanchecker", "module": module, **measured(run)}
    problem = PROBLEM_RE.search(run["stderr"])
    if run["killed"]:
        row["verdict"] = "error"
    elif run["rc"] == 0:
        row["verdict"] = "accept"
    elif run["rc"] == 1 and problem:
        row["verdict"] = "reject"
        row["problem_module"] = problem.group(1)
        row["declaration"] = lean_declaration(run["stderr"])
    else:
        row["verdict"] = "error"
    if row["verdict"] != "accept":
        row["stderr_tail"] = run["stderr"][-1500:]
    return row


def sha256_of(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def clean_row(module: str, clean: Path, clean_sha: str, env: dict, timeout: float,
              cap_kb: int) -> dict:
    run = timed_run([str(clean), "olean", "replay", "--exact", "--json", module], env,
                    timeout, cap_kb)
    row = {"tool": "clean", "module": module, "clean_sha256": clean_sha, **measured(run)}
    records = []
    for line in run["stdout"].splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    mine = [r for r in records if r.get("module") == module]
    if run["killed"] or len(mine) != 1:
        row["verdict"] = "error"
        row["records"] = len(mine)
        row["stderr_tail"] = run["stderr"][-1500:]
        return row
    rec = mine[0]
    ok = bool(rec.get("ok"))
    # The exit status must agree with the record; a disagreement is a harness error.
    if ok != (run["rc"] == 0):
        row["verdict"] = "error"
        row["inconsistent"] = f"ok={ok} rc={run['rc']}"
    else:
        row["verdict"] = "accept" if ok else "reject"
    for key in ("constants_checked", "admitted", "not_replayable", "restated", "load_ms",
                "replay_ms", "peak_rss_bytes", "load_error", "first_refusal"):
        row[key] = rec.get(key)
    refusals = rec.get("refusals") or []
    row["refusals"] = len(refusals)
    row["refused_constants"] = [r.get("constant") for r in refusals[:500]]
    return row


# ---------------------------------------------------------------- comparison
def compare(modules: list[str], leaves: set[str], exact: dict, checker: dict,
            clean: dict) -> tuple[list[dict], list[dict]]:
    """Per module: Lean's exact verdict against Clean's, and leanchecker's on leaves."""
    rows, bad = [], []
    for module in modules:
        x, c = exact.get(module), clean.get(module)
        xv = x["verdict"] if x else "missing"
        cv = c["verdict"] if c else "missing"
        row = {"module": module, "lean": xv, "clean": cv}
        agree = xv == cv and xv in ("accept", "reject")
        if module in leaves:
            k = checker.get(module)
            kv = k["verdict"] if k else "missing"
            row["leanchecker"] = kv
            if kv != xv:
                agree = False
                row["harness"] = "leanchecker and its exact replay disagree"
        # A refusal must name, on Clean's side, the declaration Lean names.
        if agree and xv == "reject":
            named = x.get("declaration")
            if named and named not in (c.get("refused_constants") or []):
                agree = False
                row["attribution"] = f"Lean refuses `{named}`; Clean does not"
        row["agree"] = agree
        rows.append(row)
        if not agree:
            detail = dict(row)
            if x:
                detail["lean_detail"] = {k: x.get(k) for k in ("message", "declaration")}
            if c:
                detail["clean_detail"] = {k: c.get(k) for k in
                                          ("first_refusal", "load_error", "killed", "refusals")}
            bad.append(detail)
    return rows, bad


def ratio_table(leaves: set[str], checker: dict, clean: dict) -> dict:
    """Time/RSS over the modules with no submodule, where `leanchecker` replays one module."""
    pairs = [(checker[m], clean[m]) for m in sorted(leaves)
             if m in checker and m in clean and checker[m]["verdict"] != "error"
             and clean[m]["verdict"] != "error"]
    if not pairs:
        return {"modules_paired": 0}
    lw = [p[0]["wall_s"] for p in pairs]
    cw = [p[1]["wall_s"] for p in pairs]
    ratios = sorted(c / max(l, 1e-3) for l, c in zip(lw, cw))
    lr = sorted(p[0]["maxrss_bytes"] or 0 for p in pairs)
    cr = sorted(p[1]["maxrss_bytes"] or 0 for p in pairs)

    def pct(xs, q):
        return xs[min(len(xs) - 1, int(q * (len(xs) - 1) + 0.5))]

    slow = sorted(pairs, key=lambda p: -p[1]["wall_s"])[:10]
    return {
        "modules_paired": len(pairs),
        "leanchecker_wall_s_total": round(sum(lw), 1),
        "clean_wall_s_total": round(sum(cw), 1),
        "leanchecker_wall_s_median": round(statistics.median(lw), 3),
        "clean_wall_s_median": round(statistics.median(cw), 3),
        "wall_ratio_median": round(statistics.median(ratios), 2),
        "wall_ratio_p90": round(pct(ratios, 0.9), 2),
        "wall_ratio_max": round(ratios[-1], 2),
        "leanchecker_maxrss_gb_median": round(statistics.median(lr) / 2**30, 3),
        "clean_maxrss_gb_median": round(statistics.median(cr) / 2**30, 3),
        "leanchecker_maxrss_gb_max": round(lr[-1] / 2**30, 2),
        "clean_maxrss_gb_max": round(cr[-1] / 2**30, 2),
        "slowest_clean": [{"module": c["module"], "clean_wall_s": c["wall_s"],
                           "leanchecker_wall_s": l["wall_s"],
                           "clean_maxrss_gb": round((c["maxrss_bytes"] or 0) / 2**30, 2),
                           "leanchecker_maxrss_gb": round((l["maxrss_bytes"] or 0) / 2**30, 2)}
                          for l, c in slow],
    }


# ---------------------------------------------------------------- driver
def load_done(out: Path, clean_sha: str) -> tuple[dict[str, dict], int]:
    """The rows `out` already holds, and how many Clean rows were set aside because a
    DIFFERENT `clean` binary produced them (or none is recorded): a verdict belongs to
    the binary that minted it, so those modules are measured again."""
    tables: dict[str, dict] = {"lean-exact": {}, "leanchecker": {}, "clean": {}}
    stale = 0
    if out.exists():
        for line in out.read_text().splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            if row.get("tool") == "clean" and row.get("clean_sha256") != clean_sha:
                stale += 1
                continue
            if row.get("tool") in tables:
                tables[row["tool"]][row["module"]] = row
    return tables, stale


def append(out: Path, row: dict, lock: threading.Lock) -> None:
    with lock, out.open("a") as fh:
        fh.write(json.dumps(row) + "\n")


def run(args: argparse.Namespace) -> int:
    toolchain = Path(args.toolchain) if args.toolchain else pinned_toolchain()
    clean = Path(args.clean).resolve()
    if not clean.is_file():
        raise SetupError(f"no clean binary at {clean}")
    lean_path = args.lean_path if args.lean_path is not None else os.environ.get("LEAN_PATH", "")
    roots = search_path(lean_path, toolchain)
    requested: set[str] = set(args.modules or [])
    if args.modules_file:
        requested |= {l.strip() for l in Path(args.modules_file).read_text().splitlines()
                      if l.strip() and not l.startswith("#")}
    for prefix in args.prefix or []:
        requested |= modules_under(prefix, roots)
    if not requested:
        raise SetupError("empty module list")
    under = {m: modules_under(m, roots) for m in requested}
    missing = sorted(m for m, found in under.items() if m not in found)
    if missing:
        raise SetupError(f"no .olean on the search path for: {', '.join(missing[:10])}")
    modules = sorted(requested)
    leaves = {m for m in modules if under[m] == {m}}
    env = dict(os.environ)
    env.update({"LEAN_PATH": os.pathsep.join(str(r) for r in roots[:-1]),
                "ATERM_NO_REROUTE": "1",
                "PATH": f"{toolchain / 'bin'}{os.pathsep}{env.get('PATH', '')}"})
    out = Path(args.out)
    clean_sha = sha256_of(clean)
    tables, stale = load_done(out, clean_sha)
    if stale:
        print(f"{stale} Clean row(s) in {out} came from another binary; re-measuring them",
              flush=True)
    exact, checker, cleanrows = tables["lean-exact"], tables["leanchecker"], tables["clean"]
    lock = threading.Lock()
    cap_kb = int(args.rss_cap_gb * 1024 * 1024)
    print(f"modules: {len(modules)} ({len(leaves)} with no submodule)", flush=True)

    todo = [m for m in modules if m not in exact]
    batches = [todo[i:i + args.exact_batch] for i in range(0, len(todo), args.exact_batch)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.lean_jobs)) as pool:
        futures = [pool.submit(exact_rows, b, toolchain, env, args.timeout, cap_kb)
                   for b in batches]
        for fut in concurrent.futures.as_completed(futures):
            for row in fut.result():
                exact[row["module"]] = row
                append(out, row, lock)
                if row["verdict"] != "accept":
                    print(f"lean-exact {row['module']}: {row['verdict']}", flush=True)
    todo = [m for m in modules if m in leaves and m not in checker]
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.lean_jobs)) as pool:
        futures = [pool.submit(leanchecker_row, m, toolchain, env, args.timeout, cap_kb)
                   for m in todo]
        for fut in concurrent.futures.as_completed(futures):
            row = fut.result()
            checker[row["module"]] = row
            append(out, row, lock)
            if row["verdict"] != "accept":
                print(f"leanchecker {row['module']}: {row['verdict']}", flush=True)
    print(f"lean side: {len(exact)} exact, {len(checker)} leanchecker", flush=True)
    if args.lean_only:
        lean_errors = [m for m in modules if exact.get(m, {}).get("verdict") not in
                       ("accept", "reject") or (m in leaves and checker.get(m, {}).get(
                           "verdict") not in ("accept", "reject"))]
        print(f"--lean-only: {len(lean_errors)} module(s) without a Lean verdict", flush=True)
        return 1 if lean_errors else 0
    todo = [m for m in modules if m not in cleanrows]
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.clean_jobs)) as pool:
        futures = [pool.submit(clean_row, m, clean, clean_sha, env, args.timeout, cap_kb)
                   for m in todo]
        for fut in concurrent.futures.as_completed(futures):
            row = fut.result()
            cleanrows[row["module"]] = row
            append(out, row, lock)
            print(f"clean {row['module']}: {row['verdict']} ({row['wall_s']} s)", flush=True)

    rows, bad = compare(modules, leaves, exact, checker, cleanrows)
    summary = {
        "generated_by": "scripts/olean_replay_differential.py",
        "toolchain": str(toolchain),
        "clean": str(clean),
        "clean_sha256": clean_sha,
        "modules": len(modules),
        "modules_without_submodules": len(leaves),
        "agree": sum(r["agree"] for r in rows),
        "disagree": len(bad),
        "lean_rejects": sum(r["lean"] == "reject" for r in rows),
        "clean_rejects": sum(r["clean"] == "reject" for r in rows),
        "disagreements": bad,
        "time_rss": ratio_table(leaves, checker, cleanrows),
    }
    if args.summary:
        Path(args.summary).write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "disagreements"}, indent=2))
    for item in bad[:20]:
        print("DISAGREE", json.dumps(item)[:1500], flush=True)
    return 0 if not bad and rows else 1


# ---------------------------------------------------------------- self-test
def selftest() -> int:
    """The comparison decides the verdict, so it is what the self-test pins."""
    modules = ["A", "A.B", "D"]
    leaves = {"A.B", "D"}
    acc = lambda m: {"module": m, "verdict": "accept"}  # noqa: E731
    exact = {m: acc(m) for m in modules}
    checker = {m: acc(m) for m in leaves}
    clean = {m: acc(m) for m in modules}
    rows, bad = compare(modules, leaves, exact, checker, clean)
    assert not bad and all(r["agree"] for r in rows), rows
    # Clean refuses a module Lean accepts.
    clean["A.B"] = {"module": "A.B", "verdict": "reject", "refused_constants": ["x"]}
    _, bad = compare(modules, leaves, exact, checker, clean)
    assert [b["module"] for b in bad] == ["A.B"], bad
    # Both refuse, and Clean refuses the declaration Lean names: agreement.
    exact["A.B"] = {"module": "A.B", "verdict": "reject", "declaration": "x"}
    checker["A.B"] = {"module": "A.B", "verdict": "reject"}
    _, bad = compare(modules, leaves, exact, checker, clean)
    assert not bad, bad
    # Both refuse, but Lean names a declaration Clean admitted: disagreement.
    exact["A.B"]["declaration"] = "y"
    _, bad = compare(modules, leaves, exact, checker, clean)
    assert [b["module"] for b in bad] == ["A.B"], bad
    exact["A.B"]["declaration"] = "x"
    # leanchecker and the exact driver disagree on a leaf: a harness failure.
    checker["D"] = {"module": "D", "verdict": "reject"}
    _, bad = compare(modules, leaves, exact, checker, clean)
    assert [b["module"] for b in bad] == ["D"], bad
    checker["D"] = acc("D")
    # A missing or errored row is never agreement.
    del clean["D"]
    _, bad = compare(modules, leaves, exact, checker, clean)
    assert [b["module"] for b in bad] == ["D"], bad
    clean["D"] = {"module": "D", "verdict": "error"}
    _, bad = compare(modules, leaves, exact, checker, clean)
    assert [b["module"] for b in bad] == ["D"], bad
    # A resume keeps only the Clean rows of the binary it runs now.
    with tempfile.TemporaryDirectory() as tmp:
        rows_file = Path(tmp) / "rows.jsonl"
        rows_file.write_text("\n".join(json.dumps(r) for r in [
            {"tool": "clean", "module": "A", "clean_sha256": "old", "verdict": "accept"},
            {"tool": "clean", "module": "D", "verdict": "accept"},
            {"tool": "clean", "module": "A.B", "clean_sha256": "new", "verdict": "reject"},
            {"tool": "lean-exact", "module": "A", "verdict": "accept"},
        ]) + "\n")
        tables, stale = load_done(rows_file, "new")
        assert stale == 2 and set(tables["clean"]) == {"A.B"}, (stale, tables)
        assert set(tables["lean-exact"]) == {"A"}, tables
    assert lean_declaration("while replaying declaration 'f.eq_1':\n(kernel)") == "f.eq_1"
    assert lean_declaration("Invalid recursor FRT.rec") == "FRT.rec"
    assert EXACT_RE.match("EXACT Init.Core ok").group(2) == "ok"
    print("olean_replay_differential selftest: OK")
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--clean", help="the `clean` binary")
    ap.add_argument("--toolchain", help="Lean toolchain dir (default: this checkout's pin)")
    ap.add_argument("--lean-path", help="LEAN_PATH for both tools (default: $LEAN_PATH)")
    ap.add_argument("--modules", nargs="*", help="modules to compare")
    ap.add_argument("--modules-file", help="file of module names, one per line")
    ap.add_argument("--prefix", action="append", help="every module under this prefix")
    ap.add_argument("--out", help="JSON-lines results (appended; resumes)")
    ap.add_argument("--summary", help="write the summary JSON here")
    ap.add_argument("--timeout", type=float, default=1800.0, help="seconds per process")
    ap.add_argument("--rss-cap-gb", type=float, default=7.5, help="kill a process above this")
    ap.add_argument("--lean-jobs", type=int, default=4, help="Lean processes at a time")
    ap.add_argument("--exact-batch", type=int, default=40,
                    help="modules per exact-replay process")
    ap.add_argument("--clean-jobs", type=int, default=1,
                    help="clean replays at a time (reserve jobs x --rss-cap-gb)")
    ap.add_argument("--lean-only", action="store_true",
                    help="measure the Lean side only (rows resume in a later full run)")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    if not args.clean or not args.out:
        ap.error("--clean and --out are required")
    try:
        return run(args)
    except SetupError as err:
        print(f"olean_replay_differential: {err}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
