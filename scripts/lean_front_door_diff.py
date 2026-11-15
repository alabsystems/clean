#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Byte-diff harness for `clean lean`, the `lean`-compatible front door.

WHAT IT MEASURES
----------------
For every corpus file it runs pinned Lean and `clean lean` with the SAME
arguments in the SAME working directory and records, per file: the exit
status, and the SHA-256 and length of stdout and of stderr, of each. A file
MATCHES when all three agree byte for byte. Nothing is normalized: Lean's own
test runner rewrites metavariable suffixes and the like before it diffs, and
this harness does not, so a match here is the strict one.

`clean lean` is told which Lean it is (`CLEAN_LEAN_VERSION`), because Lean's
test tree pins its toolchain by a build path no release name matches; the
Lean binary is the pinned toolchain of that release.

CORPORA
-------
* `elab`: Lean v4.30.0-rc2's own `tests/elab` (a checkout at `--tests-root`,
  `$LEAN4_TESTS_DIR`, else `~/lean4-src/tests`): every `*.lean` that has a
  `.lean.out.expected` sibling or whose header (comments and strings blanked)
  names no `import` / `prelude` / `module`, less those with a `.sh` / `.flags`
  sibling (they set up an environment the plain invocation does not). Run
  under 4.30.0-rc2 as the suite's own runner runs them, cwd = the pile dir,
  `--root=.. -DprintMessageEndPos=true -Dlinter.all=false`, without the
  runner's `-DElab.inServer=true`: Clean's `-D` table is pinned Lean 4.8.0's,
  which has no such option, and `clean lean` refuses rather than ignores it.
* `fixtures`: `tests/fixtures/lean_front_door/*.lean` in this repository,
  small files written for the front door, run under BOTH modelled releases.

THE GATE (`check`)
------------------
Against the committed artifact (`reports/lean-front-door/byte-diff.json`),
`check` re-runs `clean lean` on every file the artifact records as MATCHING
and compares with the Lean bytes recorded there (Lean is not re-run). It FAILS
on a file that stopped matching, and on a matched file whose text changed
since it was measured (re-measure with `measure --update`). It never needs the
Lean binary; a missing `elab` checkout is a skip of those rows
(`LEAN_FRONT_DOOR_REQUIRE_MEASURED=1` makes every skip a failure), and the
in-repository fixtures always run. A missing `clean` binary is a refusal.

Usage:
  scripts/lean_front_door_diff.py measure --clean BIN [--corpus elab,fixtures]
        [--jobs N] [--out PATH] [--update] [--lean-only]
  scripts/lean_front_door_diff.py check --clean BIN [--artifact PATH]
  scripts/lean_front_door_diff.py check-artifact [--artifact PATH]
  scripts/lean_front_door_diff.py summary [--artifact PATH] [--top N]
  scripts/lean_front_door_diff.py --selftest

Verdict line: LEAN_FRONT_DOOR=measured | checked | artifact-ok | skipped:<why> |
failed:<why>. Exit 0 / 1 (failed) / 2 (usage).
"""

from __future__ import annotations

import argparse
import collections
import concurrent.futures
import datetime as _dt
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
from typing import Dict, List, Optional, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_suite_conformance import IMPORT_RE, _rss_bytes, blank_noncode_lean, tests_identity  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCHEMA = "Clean-lean-front-door-byte-diff-v1"
ARTIFACT = os.path.join(ROOT, "reports", "lean-front-door", "byte-diff.json")
FIXTURES = os.path.join(ROOT, "tests", "fixtures", "lean_front_door")
ARGS = ["--root=..", "-DprintMessageEndPos=true", "-Dlinter.all=false"]
RELEASES = {
    "4.8.0": os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.8.0/bin/lean"),
    "4.30.0-rc2": os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean"),
}
# (corpus, release) pairs `measure` runs by default.
CORPORA = (("elab", "4.30.0-rc2"), ("fixtures", "4.8.0"), ("fixtures", "4.30.0-rc2"))
DEFAULT_WALL_S = 60.0
DEFAULT_RSS_BYTES = 3 * 1024 ** 3
POLL_S = 0.1
# How much of the first differing line a row keeps (enough to classify it).
DIFF_CHARS = 160
LEAN_CACHE = os.environ.get("LEAN_FRONT_DOOR_LEAN_CACHE") or os.path.expanduser(
    "~/.cache/clean-lean-front-door")


def verdict_line(v: str) -> None:
    print("LEAN_FRONT_DOOR=" + v)


def skip(why: str, text: str) -> int:
    print("SKIP: {}".format(text))
    verdict_line("skipped:" + why)
    return 1 if os.environ.get("LEAN_FRONT_DOOR_REQUIRE_MEASURED") in ("1", "true", "yes") else 0


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: str) -> str:
    with open(path, "rb") as fh:
        return sha256_bytes(fh.read())


# ------------------------------------------------------------------ selection
def tests_root(arg: Optional[str]) -> str:
    return arg or os.environ.get("LEAN4_TESTS_DIR") or os.path.expanduser("~/lean4-src/tests")


def select_elab(root: str) -> List[str]:
    """Relative paths `elab/x.lean` of the `elab` corpus, sorted."""
    pile = os.path.join(root, "elab")
    sibs = set(os.listdir(pile))
    out: List[str] = []
    for f in sorted(sibs):
        if not f.endswith(".lean"):
            continue
        if any(s.startswith(f + ".") and (s.endswith(".sh") or s.endswith(".flags")) for s in sibs):
            continue
        expected = (f + ".out.expected") in sibs
        with open(os.path.join(pile, f), encoding="utf-8", errors="replace") as fh:
            import_free = not IMPORT_RE.search(blank_noncode_lean(fh.read()))
        if expected or import_free:
            out.append("elab/" + f)
    return out


def select_fixtures() -> List[str]:
    if not os.path.isdir(FIXTURES):
        return []
    return ["lean_front_door/" + f for f in sorted(os.listdir(FIXTURES)) if f.endswith(".lean")]


def corpus_base(corpus: str, root: str) -> str:
    """The directory the corpus's relative paths are relative to; each file
    runs with cwd = its own directory (the pile), as Lean's runner does."""
    return root if corpus == "elab" else os.path.dirname(FIXTURES)


# ------------------------------------------------------------------- running
def run_capped(cmd: List[str], cwd: str, env: Dict[str, str], wall_s: float,
               rss_bytes: int) -> dict:
    """Run `cmd` with stdout and stderr to files, killing its process group at
    the wall or RSS cap; the bytes it wrote, its status and what it cost."""
    t0 = time.monotonic()
    with tempfile.TemporaryFile() as out_f, tempfile.TemporaryFile() as err_f:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=out_f,
                             stderr=err_f, start_new_session=True)
        peak, killed = 0, None
        while True:
            try:
                p.wait(timeout=POLL_S)
                break
            except subprocess.TimeoutExpired:
                peak = max(peak, _rss_bytes(p.pid))
                if peak > rss_bytes:
                    killed = "cap-rss"
                elif time.monotonic() - t0 > wall_s:
                    killed = "cap-wall"
                if killed:
                    try:
                        os.killpg(p.pid, signal.SIGKILL)
                    except (ProcessLookupError, PermissionError):
                        p.kill()
                    p.wait()
                    break
        out_f.seek(0)
        err_f.seek(0)
        stdout, stderr = out_f.read(), err_f.read()
    return {"exit": killed or p.returncode, "stdout": stdout, "stderr": stderr,
            "wall_s": round(time.monotonic() - t0, 2), "peak_rss_bytes": peak}


def summarize(res: dict) -> dict:
    return {"exit": res["exit"], "stdout_sha256": sha256_bytes(res["stdout"]),
            "stdout_bytes": len(res["stdout"]), "stderr_sha256": sha256_bytes(res["stderr"]),
            "stderr_bytes": len(res["stderr"]), "wall_s": res["wall_s"]}


def first_diff(lean: dict, clean: dict) -> Optional[dict]:
    """The first line where the two runs' output differs, stdout first."""
    for stream in ("stdout", "stderr"):
        a = lean[stream].decode("utf-8", "replace").split("\n")
        b = clean[stream].decode("utf-8", "replace").split("\n")
        for i in range(max(len(a), len(b))):
            la = a[i] if i < len(a) else None
            lb = b[i] if i < len(b) else None
            if la != lb:
                return {"stream": stream, "line": i + 1,
                        "lean": None if la is None else la[:DIFF_CHARS],
                        "clean": None if lb is None else lb[:DIFF_CHARS]}
    return None


def clean_env(release: str) -> Dict[str, str]:
    env = {k: v for k, v in os.environ.items() if not k.startswith("CLEAN_LEAN_VERSION")}
    env["CLEAN_LEAN_VERSION"] = release
    return env


def run_clean(clean_bin: str, rel: str, base: str, release: str, wall_s: float,
              rss_bytes: int) -> dict:
    path = os.path.join(base, rel)
    return run_capped([clean_bin, "lean", *ARGS, os.path.basename(path)], os.path.dirname(path),
                      clean_env(release), wall_s, rss_bytes)


def run_lean(lean_bin: str, rel: str, base: str, wall_s: float, rss_bytes: int) -> dict:
    path = os.path.join(base, rel)
    env = {k: v for k, v in os.environ.items() if k != "LEAN_PATH"}
    return run_capped([lean_bin, *ARGS, os.path.basename(path)], os.path.dirname(path), env,
                      wall_s, rss_bytes)


def lean_cache_path(release: str, rel: str, base: str) -> str:
    """Where pinned Lean's bytes for one file are cached: keyed by the
    release, the arguments, the file's path and its text, so an edited file
    or a changed argument list is never served a stale answer."""
    key = sha256_bytes(json.dumps([release, RELEASES[release], ARGS, rel,
                                   sha256_file(os.path.join(base, rel))]).encode())
    return os.path.join(LEAN_CACHE, release, key + ".json")


def cached_lean(release: str, rel: str, base: str, wall_s: float, rss_bytes: int) -> dict:
    """Pinned Lean's run of one file, from the cache when it was measured
    before (a capped run is never cached: it is the box's answer, not Lean's)."""
    import base64
    path = lean_cache_path(release, rel, base)
    try:
        with open(path, encoding="utf-8") as fh:
            c = json.load(fh)
        return {"exit": c["exit"], "stdout": base64.b64decode(c["stdout"]),
                "stderr": base64.b64decode(c["stderr"]), "wall_s": c["wall_s"],
                "peak_rss_bytes": c.get("peak_rss_bytes", 0)}
    except (OSError, ValueError, KeyError):
        pass
    res = run_lean(RELEASES[release], rel, base, wall_s, rss_bytes)
    if not isinstance(res["exit"], str):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        tmp = path + ".tmp{}".format(os.getpid())
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump({"exit": res["exit"], "stdout": base64.b64encode(res["stdout"]).decode(),
                       "stderr": base64.b64encode(res["stderr"]).decode(),
                       "wall_s": res["wall_s"], "peak_rss_bytes": res["peak_rss_bytes"]}, fh)
        os.replace(tmp, path)
    return res


def measure_one(corpus: str, release: str, rel: str, base: str, clean_bin: Optional[str],
                wall_s: float, rss_bytes: int) -> Optional[dict]:
    lean = cached_lean(release, rel, base, wall_s, rss_bytes)
    if clean_bin is None:
        return None
    clean = run_clean(clean_bin, rel, base, release, wall_s, rss_bytes)
    ls, cs = summarize(lean), summarize(clean)
    row = {"corpus": corpus, "release": release, "file": rel,
           "file_sha256": sha256_file(os.path.join(base, rel)), "lean": ls, "clean": cs,
           "same_exit": ls["exit"] == cs["exit"],
           "same_stdout": ls["stdout_sha256"] == cs["stdout_sha256"],
           "same_stderr": ls["stderr_sha256"] == cs["stderr_sha256"]}
    row["match"] = row["same_exit"] and row["same_stdout"] and row["same_stderr"]
    if not row["match"]:
        row["first_diff"] = first_diff(lean, clean)
    return row


def row_key(row: dict) -> str:
    return "{}@{}:{}".format(row["corpus"], row["release"], row["file"])


def totals_of(rows: List[dict]) -> Dict[str, Dict[str, int]]:
    out: Dict[str, Dict[str, int]] = {}
    for row in rows:
        t = out.setdefault("{}@{}".format(row["corpus"], row["release"]), collections.Counter())
        t["files"] += 1
        for k in ("match", "same_exit", "same_stdout", "same_stderr"):
            t[k] += int(row[k])
        t["lean_exit_0"] += int(row["lean"]["exit"] == 0)
        t["clean_exit_0"] += int(row["clean"]["exit"] == 0)
        t["clean_capped"] += int(isinstance(row["clean"]["exit"], str))
        t["lean_capped"] += int(isinstance(row["lean"]["exit"], str))
        t["clean_exit_0_lean_not"] += int(row["clean"]["exit"] == 0 and row["lean"]["exit"] != 0)
    return {k: dict(sorted(v.items())) for k, v in sorted(out.items())}


# ------------------------------------------------------------------- classes
def mismatch_class(row: dict) -> str:
    """A coarse class of a mismatch, for the summary: which half differs and
    the shape of the first differing line (digits and file names folded)."""
    le, ce = row["lean"]["exit"], row["clean"]["exit"]
    if isinstance(ce, str):
        return "clean " + ce
    if isinstance(le, str):
        return "lean " + le
    head = "exit lean={} clean={}".format(le, ce) if le != ce else "same exit"
    diff = row.get("first_diff") or {}
    def shape(line: Optional[str]) -> str:
        if line is None:
            return "<missing>"
        line = re.sub(r"^[^\s:]+\.lean:\d+:\d+(-\d+:\d+)?: ", "F:L:C: ", line)
        line = re.sub(r"\d+", "N", line)
        return line[:70]
    return "{} | {} | lean: {} | clean: {}".format(
        head, diff.get("stream", "?"), shape(diff.get("lean")), shape(diff.get("clean")))


# --------------------------------------------------------------------- modes
def require_clean(path: Optional[str]) -> str:
    path = path or os.environ.get("CLEAN_BIN") or os.path.join(ROOT, "target", "release", "clean")
    if not os.access(path, os.X_OK):
        print("REFUSED: no clean binary at {} (pass --clean; the harness never builds one)".format(path))
        verdict_line("failed:no-clean-binary")
        sys.exit(1)
    return os.path.abspath(path)


def plan(corpora: List[Tuple[str, str]], root: str) -> List[Tuple[str, str, str, str]]:
    jobs = []
    for corpus, release in corpora:
        if corpus == "elab":
            if not os.path.isdir(os.path.join(root, "elab")):
                print("note: no Lean tests/elab at {}; the elab corpus is not measured".format(root))
                continue
            files = select_elab(root)
        else:
            files = select_fixtures()
        base = corpus_base(corpus, root)
        jobs.extend((corpus, release, rel, base) for rel in files)
    return jobs


def write_artifact(path: str, artifact: dict) -> None:
    """The artifact with its header indented and one row per line, so a diff
    of two measurements is one line per file that moved."""
    head = {k: v for k, v in artifact.items() if k != "rows"}
    text = json.dumps(head, indent=1, ensure_ascii=False)
    assert text.endswith("\n}")
    rows = ",\n".join("  " + json.dumps(r, separators=(",", ":"), ensure_ascii=False)
                      for r in artifact["rows"])
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text[:-2] + ',\n "rows": [\n' + rows + "\n ]\n}\n")


def cmd_measure(a: argparse.Namespace) -> int:
    clean_bin = None if a.lean_only else require_clean(a.clean)
    root = tests_root(a.tests_root)
    wanted = set(a.corpus.split(","))
    corpora = [c for c in CORPORA if c[0] in wanted]
    for _, release in corpora:
        if not os.access(RELEASES[release], os.X_OK):
            return skip("no-lean", "pinned Lean {} is not installed at {}".format(
                release, RELEASES[release]))
    jobs = plan(corpora, root)
    if a.limit:
        jobs = jobs[: a.limit]
    rows: List[dict] = []
    t0 = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        futs = [pool.submit(measure_one, c, r, rel, base, clean_bin, a.wall_s, a.rss_bytes)
                for c, r, rel, base in jobs]
        for i, fut in enumerate(concurrent.futures.as_completed(futs), 1):
            row = fut.result()
            if row is not None:
                rows.append(row)
            if i % 100 == 0:
                print("  {}/{} measured ({:.0f}s)".format(i, len(jobs), time.monotonic() - t0),
                      flush=True)
    if clean_bin is None:
        print("cached pinned Lean's bytes for {} file(s) under {}".format(len(jobs), LEAN_CACHE))
        verdict_line("measured")
        return 0
    rows.sort(key=row_key)
    artifact = {
        "schema": SCHEMA,
        "measured": _dt.date.today().isoformat(),
        "args": ARGS,
        "clean_binary": {"path": clean_bin, "version": subprocess.run(
            [clean_bin, "--version"], capture_output=True, text=True).stdout.strip()},
        "lean_binaries": {r: RELEASES[r] for _, r in corpora},
        "tests": tests_identity(root) if any(c == "elab" for c, _ in corpora) else None,
        "caps": {"wall_s": a.wall_s, "rss_bytes": a.rss_bytes},
        "totals": totals_of(rows),
        "rows": rows,
    }
    out = a.out or (ARTIFACT if a.update else None)
    if out:
        write_artifact(out, artifact)
        print("wrote {}".format(os.path.relpath(out, ROOT)))
    print(json.dumps(artifact["totals"], indent=1))
    verdict_line("measured")
    return 0


def artifact_problems(artifact: dict) -> List[str]:
    """Why an artifact is not what `measure` writes: an unknown schema, a row
    whose verdict flags do not follow from its recorded hashes, a duplicate
    row, or totals that do not add up -- the shapes of a hand edit."""
    if artifact.get("schema") != SCHEMA:
        return ["schema is {!r}, not {!r}".format(artifact.get("schema"), SCHEMA)]
    problems: List[str] = []
    rows = artifact.get("rows", [])
    keys = [row_key(r) for r in rows]
    if len(set(keys)) != len(keys):
        problems.append("duplicate rows")
    for r in rows:
        le, ce = r["lean"], r["clean"]
        want = {"same_exit": le["exit"] == ce["exit"],
                "same_stdout": le["stdout_sha256"] == ce["stdout_sha256"],
                "same_stderr": le["stderr_sha256"] == ce["stderr_sha256"]}
        want["match"] = all(want.values())
        for k, v in want.items():
            if r.get(k) != v:
                problems.append("{}: {} is {} but its hashes say {}".format(row_key(r), k, r.get(k), v))
    if "totals" in artifact and artifact["totals"] != totals_of(rows):
        problems.append("totals do not add up over the rows")
    return problems


def cmd_check_artifact(a: argparse.Namespace) -> int:
    with open(a.artifact, encoding="utf-8") as fh:
        problems = artifact_problems(json.load(fh))
    for p in problems:
        print("FAIL: " + p)
    verdict_line("failed:artifact" if problems else "artifact-ok")
    return 1 if problems else 0


def cmd_check(a: argparse.Namespace) -> int:
    clean_bin = require_clean(a.clean)
    with open(a.artifact, encoding="utf-8") as fh:
        artifact = json.load(fh)
    problems = artifact_problems(artifact)
    if problems:
        for p in problems:
            print("FAIL: " + p)
        verdict_line("failed:artifact")
        return 1
    root = tests_root(a.tests_root)
    matched = [r for r in artifact["rows"] if r["match"]]
    failures: List[str] = []
    skipped = 0
    checked = 0
    for row in matched:
        base = corpus_base(row["corpus"], root)
        path = os.path.join(base, row["file"])
        if not os.path.isfile(path):
            skipped += 1
            continue
        if sha256_file(path) != row["file_sha256"]:
            failures.append("{}: the file changed since it was measured".format(row_key(row)))
            continue
        res = run_clean(clean_bin, row["file"], base, row["release"], a.wall_s, a.rss_bytes)
        got = summarize(res)
        checked += 1
        for field in ("exit", "stdout_sha256", "stderr_sha256"):
            if got[field] != row["lean"][field]:
                failures.append("{}: {} no longer matches pinned Lean's".format(row_key(row), field))
                break
    print("checked {} matched file(s); {} skipped (corpus absent)".format(checked, skipped))
    for f in failures:
        print("FAIL: " + f)
    if failures:
        verdict_line("failed:{}-stopped-matching".format(len(failures)))
        return 1
    if skipped:
        return skip("corpus-absent", "{} matched row(s) were not re-run".format(skipped))
    verdict_line("checked")
    return 0


def cmd_summary(a: argparse.Namespace) -> int:
    with open(a.artifact, encoding="utf-8") as fh:
        artifact = json.load(fh)
    print(json.dumps(artifact["totals"], indent=1))
    classes = collections.Counter(mismatch_class(r) for r in artifact["rows"] if not r["match"])
    for cls, n in classes.most_common(a.top):
        print("{:5d}  {}".format(n, cls))
    return 0


def _selftest() -> int:
    lean = {"stdout": b"a\nb\n", "stderr": b""}
    clean = {"stdout": b"a\nc\n", "stderr": b""}
    d = first_diff(lean, clean)
    assert d == {"stream": "stdout", "line": 2, "lean": "b", "clean": "c"}, d
    assert first_diff(lean, lean) is None
    row = {"lean": {"exit": 0}, "clean": {"exit": 1},
           "first_diff": {"stream": "stdout", "lean": None, "clean": "f.lean:3:4-3:5: error: x 12"}}
    assert mismatch_class(row) == ("exit lean=0 clean=1 | stdout | lean: <missing> | clean: "
                                   "F:L:C: error: x N"), mismatch_class(row)
    res = run_capped([sys.executable, "-c", "import sys; print('o'); sys.stderr.write('e'); "
                      "sys.exit(3)"], ROOT, dict(os.environ), 30.0, DEFAULT_RSS_BYTES)
    assert res["exit"] == 3 and res["stdout"] == b"o\n" and res["stderr"] == b"e", res
    res = run_capped([sys.executable, "-c", "import time; time.sleep(5)"], ROOT,
                     dict(os.environ), 0.3, DEFAULT_RSS_BYTES)
    assert res["exit"] == "cap-wall", res
    _selftest_check_arms()
    print("selftest ok")
    return 0


def _selftest_check_arms() -> None:
    """The gate's own falsifiability, hermetically: an artifact recording one
    matched file, checked against a stand-in `clean` that prints exactly the
    recorded bytes (green), one that prints one byte more (red), and the file
    edited under the artifact (red)."""
    with tempfile.TemporaryDirectory() as tmp:
        os.makedirs(os.path.join(tmp, "elab"))
        lean_file = os.path.join(tmp, "elab", "x.lean")
        with open(lean_file, "w", encoding="utf-8") as fh:
            fh.write("#eval 1\n")
        good = os.path.join(tmp, "clean_good")
        bad = os.path.join(tmp, "clean_bad")
        for path, text in ((good, "1"), (bad, "1!")):
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("#!{}\nimport sys\nprint({!r})\n".format(sys.executable, text))
            os.chmod(path, 0o755)
        side = {"exit": 0, "stdout_sha256": sha256_bytes(b"1\n"), "stdout_bytes": 2,
                "stderr_sha256": sha256_bytes(b""), "stderr_bytes": 0, "wall_s": 0.1}
        row = {"corpus": "elab", "release": "4.30.0-rc2", "file": "elab/x.lean",
               "file_sha256": sha256_file(lean_file), "lean": dict(side), "clean": dict(side),
               "same_exit": True, "same_stdout": True, "same_stderr": True, "match": True}
        art = os.path.join(tmp, "art.json")
        with open(art, "w", encoding="utf-8") as fh:
            json.dump({"schema": SCHEMA, "rows": [row]}, fh)

        def check(clean_bin: str) -> int:
            ns = argparse.Namespace(clean=clean_bin, artifact=art, tests_root=tmp,
                                    wall_s=30.0, rss_bytes=DEFAULT_RSS_BYTES)
            return cmd_check(ns)
        assert not artifact_problems({"schema": SCHEMA, "rows": [row]})
        forged = dict(row, clean=dict(side, stdout_sha256="0" * 64))
        assert artifact_problems({"schema": SCHEMA, "rows": [forged]}), \
            "a row claiming a match its hashes deny must be refused"
        assert artifact_problems({"schema": SCHEMA, "rows": [row], "totals": {}}), \
            "totals that do not add up must be refused"
        assert check(good) == 0, "a matching stand-in must pass"
        assert check(bad) == 1, "a stand-in printing other bytes must fail the gate"
        with open(lean_file, "a", encoding="utf-8") as fh:
            fh.write("-- edited\n")
        assert check(good) == 1, "an edited corpus file must fail the gate"


def main(argv: Optional[List[str]] = None) -> int:
    if argv is None:
        argv = sys.argv[1:]
    if argv[:1] == ["--selftest"]:
        return _selftest()
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="mode", required=True)
    for name in ("measure", "check", "check-artifact", "summary"):
        s = sub.add_parser(name)
        s.add_argument("--artifact", default=ARTIFACT)
        s.add_argument("--clean")
        s.add_argument("--tests-root")
        s.add_argument("--wall-s", type=float, default=DEFAULT_WALL_S)
        s.add_argument("--rss-bytes", type=int, default=DEFAULT_RSS_BYTES)
        if name == "measure":
            s.add_argument("--corpus", default="elab,fixtures")
            s.add_argument("--jobs", type=int, default=4)
            s.add_argument("--limit", type=int, default=0)
            s.add_argument("--out")
            s.add_argument("--update", action="store_true",
                           help="write the measurement over the committed artifact")
            s.add_argument("--lean-only", action="store_true",
                           help="only run (and cache) pinned Lean; no clean binary needed")
        if name == "summary":
            s.add_argument("--top", type=int, default=40)
    a = p.parse_args(argv)
    return {"measure": cmd_measure, "check": cmd_check, "check-artifact": cmd_check_artifact,
            "summary": cmd_summary}[a.mode](a)


if __name__ == "__main__":
    sys.exit(main())
