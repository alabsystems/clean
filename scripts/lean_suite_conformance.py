#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Two-way Lean test-suite conformance ledger and gate.

WHY THIS EXISTS
---------------
Nothing in this repo asked Lean's own test suite what Lean does. The source-elab
ratchet counts ACCEPTANCES on five Mathlib files, so it cannot see Clean
accepting what Lean rejects -- the silent-acceptance face every soundness lane
here fears most. The 2026-09-24 critic (reports/lean4-replacement-audit-
2026-09-24/critic.json) ran the import-free files of the pinned toolchain's
`tests/elab` (Lean's contract: exit 0) and `tests/elab_fail` (contract: exit
non-zero) through the frozen binary and found Clean accepting 201 of 1,901
Lean-accepted files (by exit code alone; VERDICTS below says why this ledger
counts fewer of them as agreement) and ALSO accepting 34 of 282 files Lean must
reject; five
tiny prelude-only files drove Clean past 2.5 GB. This script productionizes that
driver (~/.cache/clean-lane/audit/critic/lean_suite_oracle.py) as a ledger and a
gate.

WHERE THE TESTS COME FROM
-------------------------
The pinned toolchain ships Lean's SOURCES (src/lean) but not its tests. They
come from a lean4 checkout at the pinned tag -- the critic's driver read
`$HOME/lean4-src/tests` at 3dc1a088b6d2 (`v4.30.0-rc2`). `--tests-root` /
`$LEAN4_TESTS_DIR` override; the ledger records the checkout's rev and a run
against a different one enforces nothing (`skipped:corpus-mismatch`), exactly
as the source-elab gate treats a foreign Mathlib. The two piles are 26 MB:
  git clone --depth 1 --filter=blob:none --sparse --branch v4.30.0-rc2 \
      https://github.com/leanprover/lean4.git <dir>
  git -C <dir> sparse-checkout set tests/elab tests/elab_fail

SELECTION: every `*.lean` in `tests/elab` and `tests/elab_fail` whose HEADER
names no `import` / `prelude` / `module` and that has no sibling
`<file>.*.sh` / `<file>.*.flags` (those set up an environment or arguments the
plain invocation below would not reproduce). The header test runs on the text
with Lean comments and string literals BLANKED (`blank_noncode_lean`): the
critic's rule matched raw lines, which excluded exactly one import-free file
(`elab/mathlibetaissue.lean`, whose doc comment quotes `import Mathlib`) --
measured 2026-09-25 over both directories, one file and no other difference.

VERDICTS
--------
* Lean's verdict is MEASURED, not assumed from the directory: the pinned binary
  run exactly as the suite's run_test.sh does (`lean --root=..
  -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true <file>`, cwd
  = the pile dir). A file whose measured verdict disagrees with its directory's
  contract is `lean-contract-mismatch` and is not an oracle row.
* Clean's verdict is `clean check --json <file>` (default flags, builtin
  prelude), cwd = the pile dir: non-zero exit = reject; exit 0 = `accept` ONLY
  when the check report it printed records no `parser_recovery`, and
  `accept-partial` otherwise (recovery notes, or no report to say there were
  none). `clean check` exits 0 over parser-recovery NOTES -- measured
  2026-09-25 on this suite, 12 of the 201 files the critic counted as agreeing
  with Lean did so with a tactic skipped (`elab/3022.lean`: "unsupported tactic
  `unfold` ... > `guard_target`: Unexpected token", status pass), i.e. Clean
  accepted a DIFFERENT text from the one Lean accepted. A parse recovery is a
  parse failure (CLAUDE.md), so `accept-partial` is never an agreement with a
  Lean acceptance; against a Lean REJECTION it is still a false accept, because
  Clean said yes. Without this split a parser regression that starts skipping
  text in an agreeing file stays green, and one that skips the failing part of
  a rejected file reads as an IMPROVEMENT that `--update` would ratchet in.
* A process that hits the per-file cap (60 s wall, 2 GiB RSS by default; the
  critic saw tiny files pass 2.5 GB, one of them in 0.63 s) is killed with its
  whole process group and recorded as `cap-wall` / `cap-rss` -- its OWN
  outcome, never a verdict. A cap hit is retried once, serially, before it is
  recorded, so box load alone does not mint one. RSS is polled every 0.1 s, so
  a fast allocator overshoots the cap before the kill -- measured 2026-09-25:
  elab/5818.lean reached 2.71 GB in 0.55 s against the 2 GiB cap. Size a
  heavy_gate reservation for about 3 GiB per job, not 2.

THE GATE
--------
Against the committed ledger (data/lean_suite_conformance.json), a measured run
FAILS on
  * any file the ledger records as AGREEING that no longer agrees (a new
    disagreement, or an agreement lost to a cap -- agreement only ratchets up);
  * any file newly in `clean-accepts-lean-rejects`, and any rise in that count;
  * any ledger file the run did not measure, and any selected file the ledger
    does not cover (the ledger no longer describes the selection).
Improvements are reported, and `--update` writes them into the ledger;
`--update` refuses to write over a regression unless `--rebase '<why>'` records
why it was accepted.

Usage:
  scripts/lean_suite_conformance.py                     measure + enforce
  scripts/lean_suite_conformance.py --update [--lean]   measure (+ Lean) and ratchet
  scripts/lean_suite_conformance.py --check-artifact    cheap: validate the ledger
  scripts/lean_suite_conformance.py --compare MEAS.json cheap: enforce a saved run
  scripts/lean_suite_conformance.py --selftest
  scripts/lean_suite_delta.py OLD [NEW]                 what a re-mint changed, row by row

Verdict line: LEAN_SUITE_CONFORMANCE=measured | artifact-ok | compared |
skipped:<why> | failed:<why>.  Exit 0 / 1 (failed) / 2 (usage).
LEAN_SUITE_REQUIRE_MEASURED=1 turns every skip into a failure.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as _dt
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
from typing import Dict, List, Optional, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCHEMA = "Clean-lean-suite-conformance-v1"
# The `clean check --json` report versions this reader accepts (it reads only
# `parser_recovery`, which v2 left unchanged).
CHECK_REPORT_SCHEMAS = ("Clean-check-report-v1", "Clean-check-report-v2")
LEDGER = os.path.join(ROOT, "data", "lean_suite_conformance.json")
DIRS = (("elab", "accept"), ("elab_fail", "reject"))
IMPORT_RE = re.compile(r"^\s*(import|prelude|module)\b", re.M)
LEAN_ARGS = ["--root=..", "-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true"]
DEFAULT_WALL_S = 60.0
DEFAULT_RSS_BYTES = 2 * 1024 ** 3
POLL_S = 0.1
CAPS = ("cap-wall", "cap-rss")
# Clean said yes without parsing the whole file (see VERDICTS in the docstring).
PARTIAL = "accept-partial"
LEAN_VERDICTS = ("accept", "reject") + CAPS
CLEAN_VERDICTS = ("accept", PARTIAL, "reject") + CAPS
AGREE = ("agree-accept", "agree-reject")
FALSE_ACCEPT = "clean-accepts-lean-rejects"
PARTIAL_ACCEPT = "clean-accepts-unparsed-text"
OUTCOMES = AGREE + ("clean-rejects-lean-accepts", PARTIAL_ACCEPT, FALSE_ACCEPT, "clean-cap-wall",
                    "clean-cap-rss", "lean-contract-mismatch", "lean-unmeasured")
def oracle_world() -> str:
    """Read the same registry as the importer, without a second oracle pin.

    This chooses a default executable, never re-labels an existing ledger or
    admits an artifact. The build and parser tests also bind this row to the
    checkout's lean-toolchain.
    """
    with open(os.path.join(ROOT, "crates/clean-olean/lean_worlds.tsv"), encoding="utf-8") as stream:
        rows = [line.rstrip("\n").split("\t") for line in stream
                if line.strip() and not line.startswith("#")]
    worlds = [row[0] for row in rows if len(row) == 4 and row[1] == "oracle"]
    if len(worlds) != 1:
        raise ValueError("lean_worlds.tsv must name exactly one oracle")
    return worlds[0]


LEAN_WORLD = oracle_world()
DEFAULT_LEAN = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---{}/bin/lean".format(LEAN_WORLD))


def git_env() -> Dict[str, str]:
    """The environment for every git call here, with GIT_* removed. A git hook
    runs with GIT_DIR (and a lane composing a commit over a temporary index,
    GIT_INDEX_FILE) exported; inherited, `git -C <tmp> add -A` in the
    self-test would stage into THAT repository and index, and `rev-parse` would
    name the wrong checkout."""
    return {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def verdict_line(v: str) -> None:
    print("LEAN_SUITE_CONFORMANCE=" + v)


def skip(why: str, text: str) -> int:
    """Nothing was measured. Green by default, red under REQUIRE_MEASURED."""
    print("SKIP: {}".format(text))
    verdict_line("skipped:" + why)
    return 1 if os.environ.get("LEAN_SUITE_REQUIRE_MEASURED") in ("1", "true", "yes") else 0


# ------------------------------------------------------------------ selection
def blank_noncode_lean(src: str) -> str:
    """Lean source with comments (`--`, nested `/- -/`) and string literals
    blanked, line geometry kept -- so a header keyword quoted in a doc comment
    is not read as a header."""
    out: List[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth, i = depth + 1, i + 2
            out.append("  ")
            continue
        if depth:
            if src.startswith("-/", i):
                depth, i = depth - 1, i + 2
                out.append("  ")
                continue
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            end = min(j + 1, n)
            out.append("".join("\n" if c == "\n" else " " for c in src[i:end]))
            i = end
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def select_files(tests_root: str) -> List[Tuple[str, str]]:
    """[(relative path 'elab/x.lean', contract)] in sorted order."""
    out: List[Tuple[str, str]] = []
    for d, contract in DIRS:
        dd = os.path.join(tests_root, d)
        sibs = set(os.listdir(dd))
        for f in sorted(sibs):
            if not f.endswith(".lean"):
                continue
            if any(s.startswith(f + ".") and (s.endswith(".sh") or s.endswith(".flags")) for s in sibs):
                continue
            with open(os.path.join(dd, f), encoding="utf-8", errors="replace") as fh:
                if IMPORT_RE.search(blank_noncode_lean(fh.read())):
                    continue
            out.append((d + "/" + f, contract))
    return out


UPSTREAM_REMOTE_RE = re.compile(r"^(https://github\.com/|git@github\.com:|ssh://git@github\.com/)"
                                r"leanprover/lean4(\.git)?/?$")


def tests_identity(tests_root: str) -> dict:
    src = os.path.dirname(os.path.abspath(tests_root))

    def git(*a: str) -> str:
        try:
            return subprocess.run(["git", "-C", src, *a], capture_output=True, text=True,
                                  check=True, env=git_env()).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            return ""
    # By rev and tag, never by where the checkout sits: a ledger minted on one
    # box would otherwise carry that box's home path.
    # The tree URL only when `origin` is Lean's own repository; another
    # remote is named by that fact, not by its URL (which can be a local path).
    rev, tag = git("rev-parse", "HEAD"), git("describe", "--tags", "--exact-match")
    upstream = bool(UPSTREAM_REMOTE_RE.match(git("remote", "get-url", "origin")))
    return {"git_rev": rev, "describe": git("describe", "--tags"),
            "upstream": "https://github.com/leanprover/lean4/tree/{}/tests".format(tag or rev)
                        if rev and upstream else "",
            "origin_is_upstream": upstream,
            "found_via": "--tests-root / $LEAN4_TESTS_DIR, else $HOME/lean4-src/tests (where the "
                         "2026-09-24 critic's driver read them); the pinned toolchain ships "
                         "src/lean but no tests"}


# ------------------------------------------------------------------- running
def _rss_bytes(pid: int) -> int:
    try:
        o = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True).stdout
        return int(o.strip() or 0) * 1024
    except (OSError, ValueError):
        return 0


def run_capped(cmd: List[str], cwd: str, wall_s: float, rss_bytes: int,
               stdout_path: Optional[str] = None) -> dict:
    """Run `cmd`, killing its whole process group at the wall or RSS cap. With
    `stdout_path` its stdout goes to that file (a file, not a pipe: the poll
    loop never reads, so a pipe could fill and stall the child)."""
    t0 = time.monotonic()
    out_f = open(stdout_path, "wb") if stdout_path else None
    try:
        p = subprocess.Popen(cmd, cwd=cwd, stdout=out_f or subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL, start_new_session=True)
    except BaseException:
        if out_f:
            out_f.close()
        raise
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
    if out_f:
        out_f.close()
    return {"rc": p.returncode, "wall_s": round(time.monotonic() - t0, 2),
            "peak_rss_bytes": peak, "killed": killed}


def verdict_of(res: dict) -> str:
    """A LEAN run's verdict: its exit code, or the cap it hit."""
    if res["killed"]:
        return res["killed"]
    return "accept" if res["rc"] == 0 else "reject"


def parser_recovery_of(stdout_text: str) -> Optional[int]:
    """How many parser-recovery notes the `clean check --json` report in
    `stdout_text` records; None when there is no such report to read."""
    i = (stdout_text or "").find("{")
    if i < 0:
        return None
    try:
        obj, _ = json.JSONDecoder().raw_decode(stdout_text[i:])
    except ValueError:
        return None
    # v2 (2026-09-28) changed only `trust_summary.sorry_axioms`, which this
    # reader does not use; v1 stays readable for committed artifacts.
    if not isinstance(obj, dict) or obj.get("schema_version") not in CHECK_REPORT_SCHEMAS:
        return None
    rec = obj.get("parser_recovery")
    return len(rec) if isinstance(rec, list) else None


def clean_verdict_of(res: dict, stdout_text: str) -> str:
    """A CLEAN run's verdict. Exit 0 is `accept` only when the report it printed
    says every byte was parsed; otherwise it is `accept-partial` -- Clean said
    yes about a text it did not fully read (module docstring, VERDICTS)."""
    v = verdict_of(res)
    if v != "accept":
        return v
    return "accept" if parser_recovery_of(stdout_text) == 0 else PARTIAL


def run_clean(clean_bin: str, f: str, cwd: str, wall_s: float, rss_bytes: int) -> dict:
    """`clean check --json <f>` under the caps, with its verdict and the
    number of parser-recovery notes its report carried (None: no report)."""
    fd, tmp = tempfile.mkstemp(prefix="lean_suite_clean.", suffix=".json")
    os.close(fd)
    try:
        # The world is named, not inferred: since G72 `clean check` selects the
        # world from the nearest lean-toolchain, and Lean's own tests/ carries
        # one naming `../build/release/stage1` (the stage1 Lean builds from the
        # tag this ledger pins), which no Clean world matches, so every file was
        # refused before elaboration. The ledger is measured in LEAN_WORLD.
        cr = run_capped([clean_bin, "check", "--json", "--lean-world", LEAN_WORLD, f],
                        cwd, wall_s, rss_bytes, stdout_path=tmp)
        with open(tmp, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass
    return {"clean": clean_verdict_of(cr, text), "clean_wall_s": cr["wall_s"],
            "clean_peak_rss_bytes": cr["peak_rss_bytes"],
            "clean_parser_recovery": parser_recovery_of(text) if not cr["killed"] else None}


def outcome_of(contract: str, lean: str, clean: str) -> str:
    if lean in CAPS:
        return "lean-unmeasured"
    if lean != contract:
        return "lean-contract-mismatch"
    if clean in CAPS:
        return "clean-" + clean
    if lean == "reject":
        # Clean said yes, whether or not it parsed the whole file.
        return "agree-reject" if clean == "reject" else FALSE_ACCEPT
    if clean == "accept":
        return "agree-accept"
    return PARTIAL_ACCEPT if clean == PARTIAL else "clean-rejects-lean-accepts"


def measure(files: List[Tuple[str, str]], tests_root: str, clean_bin: str, lean_bin: Optional[str],
            lean_for: Optional[set], jobs: int, wall_s: float, rss_bytes: int) -> Dict[str, dict]:
    """Clean on every file; Lean on every file when `lean_for` is None, else on
    those in it (the files the ledger has no Lean verdict for)."""
    def one(item: Tuple[str, str]) -> Tuple[str, dict]:
        rel, contract = item
        d, f = rel.split("/", 1)
        cwd = os.path.join(tests_root, d)
        row: dict = {"contract": contract}
        row.update(run_clean(clean_bin, f, cwd, wall_s, rss_bytes))
        if lean_bin and (lean_for is None or rel in lean_for):
            lr = run_capped([lean_bin, *LEAN_ARGS, f], cwd, max(wall_s, 120.0), max(rss_bytes, 3 * 1024 ** 3))
            row["lean"] = verdict_of(lr)
        return rel, row

    out: Dict[str, dict] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as ex:
        for rel, row in ex.map(one, files):
            out[rel] = row
    # A cap hit under load is retried ONCE, serially, before it is recorded.
    for rel, row in out.items():
        if row["clean"] in CAPS:
            d, f = rel.split("/", 1)
            row.update(run_clean(clean_bin, f, os.path.join(tests_root, d), wall_s, rss_bytes), retried=True)
    return out


# ------------------------------------------------------------------- ledger
def totals_of(files: Dict[str, dict]) -> dict:
    t = {o: 0 for o in OUTCOMES}
    for r in files.values():
        t[r["outcome"]] = t.get(r["outcome"], 0) + 1
    t["files"] = len(files)
    oracle_out = ("lean-contract-mismatch", "lean-unmeasured")
    for d, contract in DIRS:
        rows = [r for k, r in files.items() if k.startswith(d + "/") and r["outcome"] not in oracle_out]
        t[d + "_oracle_files"] = len(rows)
        t[d + "_clean_" + contract] = sum(1 for r in rows if r["clean"] == contract)
    return t


def validate_ledger(led: dict) -> List[str]:
    p: List[str] = []
    if led.get("schema_version") != SCHEMA:
        return ["schema_version is {!r}, expected {!r}".format(led.get("schema_version"), SCHEMA)]
    files = led.get("files")
    if not isinstance(files, dict) or not files:
        return ["`files` is empty or not an object -- a ledger of nothing enforces nothing"]
    if not str((led.get("tests_source") or {}).get("git_rev") or "").strip():
        p.append("tests_source.git_rev is empty -- the ledger must say which checkout its rows are OF")
    contracts = dict(DIRS)
    for k, r in files.items():
        d = k.split("/", 1)[0]
        if d not in contracts:
            p.append("{}: not under elab/ or elab_fail/".format(k))
            continue
        if not isinstance(r, dict):
            p.append("{}: row is not an object".format(k))
            continue
        if r.get("contract") != contracts[d]:
            p.append("{}: contract {!r} but {}/ is {!r}".format(k, r.get("contract"), d, contracts[d]))
        if r.get("lean") not in LEAN_VERDICTS or r.get("clean") not in CLEAN_VERDICTS:
            p.append("{}: verdicts lean={!r} clean={!r} not in {} / {}".format(
                k, r.get("lean"), r.get("clean"), LEAN_VERDICTS, CLEAN_VERDICTS))
            continue
        want = outcome_of(contracts[d], r["lean"], r["clean"])
        if r.get("outcome") != want:
            p.append("{}: outcome {!r} but lean={} clean={} derive {!r}".format(
                k, r.get("outcome"), r["lean"], r["clean"], want))
    if not p and led.get("totals") != totals_of(files):
        p.append("totals disagree with the rows they summarise: recorded {} vs derived {}".format(
            led.get("totals"), totals_of(files)))
    if "lean_world" in led and led.get("lean_toolchain") != "leanprover/lean4:{}".format(led["lean_world"]):
        p.append("lean_world {!r} is not the world of lean_toolchain {!r}".format(
            led["lean_world"], led.get("lean_toolchain")))
    for i, rb in enumerate(led.get("rebases") or []):
        if not isinstance(rb, dict) or len(str(rb.get("reason") or "").strip()) < 12 \
                or not re.match(r"^\d{4}-\d{2}-\d{2}$", str(rb.get("date") or "")):
            p.append("rebases[{}] needs a date and a real reason (>= 12 characters)".format(i))
    return p


def compare(led: dict, measured: Dict[str, dict]) -> dict:
    """Measured Clean verdicts against the ledger (Lean's verdict: the ledger's,
    unless this run re-measured it)."""
    res: dict = {"new_disagreements": [], "new_false_accepts": [], "improvements": [], "missing": [],
                 "extra": sorted(set(measured) - set(led["files"]))}
    now: Dict[str, dict] = {}
    for k, r in led["files"].items():
        m = measured.get(k)
        if m is None:
            res["missing"].append(k)
            continue
        lean = m.get("lean") or r["lean"]
        out = outcome_of(r["contract"], lean, m["clean"])
        now[k] = {"contract": r["contract"], "lean": lean, "clean": m["clean"], "outcome": out}
        if r["outcome"] in AGREE and out != r["outcome"]:
            res["new_disagreements"].append({"file": k, "was": r["outcome"], "now": out})
        if out == FALSE_ACCEPT and r["outcome"] != FALSE_ACCEPT:
            res["new_false_accepts"].append({"file": k, "was": r["outcome"]})
        if out in AGREE and r["outcome"] not in AGREE:
            res["improvements"].append({"file": k, "was": r["outcome"], "now": out})
    for k in res["extra"]:
        m = measured[k]
        if m.get("lean") in LEAN_VERDICTS:
            now[k] = {"contract": m["contract"], "lean": m["lean"], "clean": m["clean"],
                      "outcome": outcome_of(m["contract"], m["lean"], m["clean"])}
    res["false_accepts_before"] = sum(1 for r in led["files"].values() if r["outcome"] == FALSE_ACCEPT)
    res["false_accepts_now"] = sum(1 for r in now.values() if r["outcome"] == FALSE_ACCEPT)
    res["agree_before"] = sum(1 for r in led["files"].values() if r["outcome"] in AGREE)
    res["agree_now"] = sum(1 for r in now.values() if r["outcome"] in AGREE)
    res["rows"] = now
    res["regressed"] = bool(res["new_disagreements"] or res["new_false_accepts"] or res["missing"]
                           or res["extra"] or res["false_accepts_now"] > res["false_accepts_before"])
    return res


def rebase_record(res: dict, reason: str, date: str) -> dict:
    """What `--update --rebase` appends: every regression of `res` it accepts,
    by kind; an unledgered row with the outcome it was written at."""
    return {"date": date, "reason": reason.strip(), "new_disagreements": res["new_disagreements"],
            "new_false_accepts": res["new_false_accepts"], "missing": res["missing"],
            "extra": [{"file": k, "now": res["rows"][k]["outcome"]} for k in res["extra"] if k in res["rows"]]}


def render(res: dict) -> None:
    print("  agreement {} -> {}; clean-accepts-lean-rejects {} -> {}; {} improvement(s)".format(
        res["agree_before"], res["agree_now"], res["false_accepts_before"], res["false_accepts_now"],
        len(res["improvements"])))
    for r in res["improvements"]:
        print("  improved {} ({} -> {})".format(r["file"], r["was"], r["now"]))
    for r in res["new_disagreements"]:
        print("  NEW-DISAGREEMENT {} ({} -> {})".format(r["file"], r["was"], r["now"]), file=sys.stderr)
    for r in res["new_false_accepts"]:
        print("  NEW-FALSE-ACCEPT {}: Clean now ACCEPTS a file the pinned Lean rejects (was {})".format(
            r["file"], r["was"]), file=sys.stderr)
    for k in res["missing"]:
        print("  MISSING {}: in the ledger but not measured".format(k), file=sys.stderr)
    for k in res["extra"]:
        print("  UNLEDGERED {}: selected and measured, but the ledger has no row for it "
              "(re-run with --update --lean)".format(k), file=sys.stderr)


def _binary_identity(path: str) -> dict:
    """Where the measured binary is, relative to the repo when it is inside it,
    and what it is (sha256), so a ledger row can be traced to the program."""
    import hashlib
    h = hashlib.sha256()
    try:
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(1 << 20), b""):
                h.update(chunk)
        digest = h.hexdigest()
    except OSError:
        digest = ""
    rel = os.path.relpath(path, ROOT)
    return {"binary": path if rel.startswith("..") else rel, "binary_sha256": digest}


def build_ledger(prev: Optional[dict], rows: Dict[str, dict], ident: dict, clean_bin: str,
                 caps: dict, lean_measured: bool) -> dict:
    files = {k: {"contract": r["contract"], "lean": r["lean"], "clean": r["clean"],
                 "outcome": outcome_of(r["contract"], r["lean"], r["clean"])} for k, r in sorted(rows.items())}

    def git_head() -> str:
        """HEAD, marked `+dirty` when the sources a binary is built from
        differ from it -- a sha alone would claim a tree nobody measured."""
        try:
            head = subprocess.run(["git", "-C", ROOT, "rev-parse", "--short=9", "HEAD"],
                                  capture_output=True, text=True, check=True, env=git_env()).stdout.strip()
            dirty = subprocess.run(["git", "-C", ROOT, "status", "--porcelain", "--untracked-files=all",
                                    "--", "crates", "Cargo.toml", "Cargo.lock"],
                                   capture_output=True, text=True, check=True, env=git_env()).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            return "unknown"
        return head + ("+dirty" if dirty else "")
    return {
        "schema_version": SCHEMA,
        "generated": _dt.date.today().isoformat(),
        "what": ("Per-file two-way agreement between the pinned Lean and `clean check` on the "
                 "import-free files of Lean's own tests/elab (Lean accepts) and tests/elab_fail "
                 "(Lean rejects). Written by scripts/lean_suite_conformance.py --update; never "
                 "hand-edited. `clean-accepts-lean-rejects` rows are the silent-acceptance face "
                 "and may only fall."),
        "lean_toolchain": "leanprover/lean4:" + LEAN_WORLD,
        "lean_world": LEAN_WORLD,
        "tests_source": ident,
        "selection": ("every *.lean in elab/ and elab_fail/ whose text, with Lean comments and "
                      "string literals blanked, has no import/prelude/module line, and that has no "
                      "sibling <file>.*.sh or <file>.*.flags"),
        "lean": {"invocation": "lean " + " ".join(LEAN_ARGS) + " <file>  (cwd = the pile dir)",
                 # The date every Lean verdict was last MEASURED -- carried
                 # forward by an update that re-measures only Clean.
                 "verdicts_measured_on": (_dt.date.today().isoformat() if lean_measured else
                                          ((prev or {}).get("lean") or {}).get("verdicts_measured_on")),
                 "contract_held_on_every_file": all(
                     outcome_of(r["contract"], r["lean"], r["clean"]) != "lean-contract-mismatch"
                     for r in rows.values())},
        "clean": dict({"invocation": "clean check --json <file>  (cwd = the pile dir)",
                       "verdict_rule": ("non-zero exit = reject; exit 0 = accept only when the "
                                        "printed Clean-check-report-v1 records no parser_recovery, "
                                        "else accept-partial (never an agreement with a Lean "
                                        "acceptance; a false accept against a Lean rejection)"),
                       "tree_commit": git_head()}, **_binary_identity(clean_bin)),
        "caps": caps,
        "rebases": (prev or {}).get("rebases", []),
        "totals": totals_of(files),
        "files": files,
    }


# ----------------------------------------------------------------- self-test
def _selftest_e2e(check) -> None:
    """The MEASURE path end to end: a fake tests root, a fake `clean` that
    accepts everything and a fake `lean` that honours each directory's
    contract, through `main` itself."""
    with tempfile.TemporaryDirectory() as tmp:
        tests = os.path.join(tmp, "tests")
        for d in ("elab", "elab_fail"):
            os.makedirs(os.path.join(tests, d))
        for rel, text in (("elab/a.lean", "def a := 1\n"), ("elab_fail/b.lean", "def b : Nat := \"x\"\n"),
                          ("elab/quoted.lean", "/-! doc\nimport Mathlib\n-/\ndef q := 1\n"),
                          ("elab/hdr.lean", "import Lean\ndef h := 1\n"),
                          ("elab/rec.lean", "theorem r : True := by trivial\n")):
            with open(os.path.join(tests, rel), "w", encoding="utf-8") as f:
                f.write(text)
        for g in (["init", "-q"], ["add", "-A"],
                  ["-c", "user.email=selftest@example.invalid", "-c", "user.name=selftest",
                   "-c", "commit.gpgsign=false", "commit", "-q", "-m", "fixture"]):
            subprocess.run(["git", "-C", tmp, *g], check=False, capture_output=True, env=git_env())
        fake_clean = os.path.join(tmp, "clean")
        fake_lean = os.path.join(tmp, "lean")
        with open(fake_clean, "w", encoding="utf-8") as f:
            # A report like `clean check --json` prints; `rec.lean` carries a
            # parser-recovery note, as elab/3022.lean really does. The file is
            # the last argument, after `--lean-world <tag>`.
            f.write('#!/bin/sh\nfor F; do :; done\ncase "$F" in *rec*) R=\'["parser recovery [x]: at line 1"]\';; '
                    "*) R='[]';; esac\n"
                    'printf \'{"schema_version":"Clean-check-report-v1","parser_recovery":%s}\\n\' "$R"\n'
                    "exit ${FAKE_CLEAN_RC:-0}\n")
        with open(fake_lean, "w", encoding="utf-8") as f:
            f.write('#!/bin/sh\ncase "$(basename "$(pwd)")" in elab_fail) exit 1;; *) exit 0;; esac\n')
        os.chmod(fake_clean, 0o755)
        os.chmod(fake_lean, 0o755)
        ledger = os.path.join(tmp, "ledger.json")
        base = ["--tests-root", tests, "--clean", fake_clean, "--lean-bin", fake_lean, "--ledger", ledger,
                "--jobs", "1"]
        sel = [r for r, _ in select_files(tests)]
        check("selection keeps a doc-quoted `import` and drops a real header",
              sel == ["elab/a.lean", "elab/quoted.lean", "elab/rec.lean", "elab_fail/b.lean"])
        rc = main(base + ["--update", "--lean"])
        led = json.load(open(ledger, encoding="utf-8")) if os.path.exists(ledger) else {"files": {}}
        check("e2e: --update writes a valid ledger", rc == 0 and validate_ledger(led) == [])
        check("e2e: an accept-everything Clean is a recorded false accept",
              led.get("files", {}).get("elab_fail/b.lean", {}).get("outcome") == FALSE_ACCEPT)
        check("e2e: a Clean acceptance over a parser recovery is not an agreement",
              led.get("files", {}).get("elab/rec.lean", {}).get("outcome") == PARTIAL_ACCEPT
              and led.get("files", {}).get("elab/a.lean", {}).get("outcome") == "agree-accept"
              and led.get("totals", {}).get("elab_clean_accept") == 2)
        check("e2e: an identical re-run passes", main(base) == 0)
        # The ledger had rec.lean AGREEING; the same binary now accepts it only
        # over a parser recovery -- a parser regression that starts skipping
        # text in an agreeing file, which the exit code alone cannot see.
        led2 = json.loads(json.dumps(led))
        led2["files"]["elab/rec.lean"].update(clean="accept", outcome="agree-accept")
        led2["totals"] = totals_of(led2["files"])
        ledger2 = os.path.join(tmp, "ledger2.json")
        with open(ledger2, "w", encoding="utf-8") as f:
            json.dump(led2, f)
        check("e2e: an agreement lost to a parser recovery fails although the exit code held",
              main([a if a != ledger else ledger2 for a in base]) == 1)
        led["files"].setdefault("elab_fail/b.lean", {}).update(
            contract="reject", lean="reject", clean="reject", outcome="agree-reject")
        led["totals"] = totals_of(led["files"])
        with open(ledger, "w", encoding="utf-8") as f:
            json.dump(led, f)
        check("e2e: the same binary against a ledger that had it AGREEING fails", main(base) == 1)


def _selftest() -> int:
    fails = 0

    def check(name: str, cond: bool) -> None:
        nonlocal fails
        print("  {}: {}".format("PASS" if cond else "FAIL", name))
        fails += 0 if cond else 1

    rows = {
        "elab/a.lean": {"contract": "accept", "lean": "accept", "clean": "accept"},
        "elab/b.lean": {"contract": "accept", "lean": "accept", "clean": "reject"},
        "elab_fail/c.lean": {"contract": "reject", "lean": "reject", "clean": "reject"},
        "elab_fail/d.lean": {"contract": "reject", "lean": "reject", "clean": "accept"},
        "elab/e.lean": {"contract": "accept", "lean": "reject", "clean": "reject"},
    }
    led = build_ledger(None, rows, {"root": "t", "git_rev": "abc"}, "clean", {}, True)
    check("a built ledger validates", validate_ledger(led) == [])
    check("the derived outcomes", [r["outcome"] for r in led["files"].values()] == [
        "agree-accept", "clean-rejects-lean-accepts", "lean-contract-mismatch", "agree-reject",
        FALSE_ACCEPT])
    same = {k: {"clean": r["clean"]} for k, r in rows.items()}
    check("an identical run does not regress", not compare(led, same)["regressed"])
    lost = dict(same, **{"elab/a.lean": {"clean": "reject"}})
    r = compare(led, lost)
    check("a lost agreement is a NEW disagreement",
          r["regressed"] and [x["file"] for x in r["new_disagreements"]] == ["elab/a.lean"])
    capped = dict(same, **{"elab/a.lean": {"clean": "cap-wall"}})
    check("an agreement lost to a CAP regresses (a cap is not a verdict, and not a pass)",
          compare(led, capped)["regressed"])
    fa = dict(same, **{"elab_fail/c.lean": {"clean": "accept"}})
    r = compare(led, fa)
    check("a new false accept regresses",
          r["regressed"] and [x["file"] for x in r["new_false_accepts"]] == ["elab_fail/c.lean"])
    better = dict(same, **{"elab/b.lean": {"clean": "accept"}, "elab_fail/d.lean": {"clean": "reject"}})
    r = compare(led, better)
    check("improvements ratchet up without regressing", not r["regressed"] and len(r["improvements"]) == 2)
    check("a missing file regresses", compare(led, {k: v for k, v in same.items() if k != "elab/a.lean"})["regressed"])
    ext = dict(same, **{"elab/z.lean": {"contract": "accept", "lean": "accept", "clean": "accept"}})
    r = compare(led, ext)
    check("a selected file the ledger does not cover regresses, and is kept for --update",
          r["regressed"] and r["extra"] == ["elab/z.lean"] and "elab/z.lean" in r["rows"])
    check("a Lean cap is not a contract verdict", outcome_of("accept", "cap-wall", "accept") == "lean-unmeasured")
    ok0, rep = {"killed": None, "rc": 0}, '{"schema_version":"Clean-check-report-v1","parser_recovery":%s}'
    check("clean verdicts: exit 0 with a clean parse accepts; a recovery note or no report is partial; "
          "non-zero rejects",
          clean_verdict_of(ok0, "noise\n" + rep % "[]") == "accept"
          and clean_verdict_of(ok0, rep % '["parser recovery [p]: at line 7"]') == PARTIAL
          and clean_verdict_of(ok0, "") == PARTIAL
          and clean_verdict_of({"killed": None, "rc": 1}, rep % "[]") == "reject"
          and clean_verdict_of({"killed": "cap-rss", "rc": -9}, "") == "cap-rss")
    check("a partial acceptance never agrees with Lean, and is a false accept against a rejection",
          outcome_of("accept", "accept", PARTIAL) == PARTIAL_ACCEPT
          and outcome_of("reject", "reject", PARTIAL) == FALSE_ACCEPT)
    r = compare(led, dict(same, **{"elab/a.lean": {"clean": PARTIAL}}))
    check("an agreeing file accepted only over a parser recovery is a NEW disagreement",
          r["regressed"] and [x["file"] for x in r["new_disagreements"]] == ["elab/a.lean"])
    bad = json.loads(json.dumps(led))
    bad["files"]["elab/a.lean"]["outcome"] = "agree-reject"
    check("an outcome that does not follow from its verdicts is refused", bool(validate_ledger(bad)))
    bad = json.loads(json.dumps(led))
    bad["totals"]["agree-accept"] += 1
    check("totals that do not add up are refused", bool(validate_ledger(bad)))
    bad = json.loads(json.dumps(led))
    bad["files"]["elab_fail/c.lean"]["contract"] = "accept"
    check("a contract that contradicts its directory is refused", bool(validate_ledger(bad)))
    bad = json.loads(json.dumps(led))
    world = json.loads(json.dumps(led))
    world["lean_world"] = "v4.29.0"
    check("validate: a lean_world that is not lean_toolchain's is refused",
          any("lean_world" in x for x in validate_ledger(world)) and not validate_ledger(led))
    check("tests identity: the tree URL only for Lean's own origin",
          all(bool(UPSTREAM_REMOTE_RE.match(u)) == ok for u, ok in (
              ("https://github.com/leanprover/lean4.git", True), ("git@github.com:leanprover/lean4.git", True),
              ("https://github.com/leanprover/lean4", True), ("https://github.com/someone/lean4.git", False),
              ("$HOME/lean4", False), ("https://github.com/leanprover/lean4-nightly.git", False), ("", False))))
    bad["rebases"] = [{"date": "2026-09-25", "reason": "x"}]
    check("a rebase without a real reason is refused", bool(validate_ledger(bad)))
    _src = 'a -- import X\n/- /- import -/ -/ "import"\nimport Y -- real'
    _bl = blank_noncode_lean(_src)
    check("comments and strings are blanked, geometry kept, code untouched",
          len(_bl) == len(_src) and [i for i, c in enumerate(_bl) if c == "\n"]
          == [i for i, c in enumerate(_src) if c == "\n"]
          and _bl.count("import") == 1 and _bl.startswith("a ") and "import Y" in _bl)
    _selftest_e2e(check)
    with open(os.path.join(ROOT, "crates/clean-olean/lean_worlds.tsv"), encoding="utf-8") as f:
        check("LEAN_WORLD is the oracle row of crates/clean-olean/lean_worlds.tsv",
              any(ln.split("\t")[:2] == [LEAN_WORLD, "oracle"] for ln in f if not ln.startswith("#")))
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import lean_suite_delta  # noqa: E402 -- it imports this module; a cycle at import time
    lean_suite_delta.selftest_checks(check)
    print("LEAN_SUITE_CONFORMANCE_SELFTEST={} failed={}".format("ok" if fails == 0 else "fail", fails))
    return 0 if fails == 0 else 1


# --------------------------------------------------------------------- main
def _load(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def _write(path: str, obj: dict) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=1, sort_keys=False)
        f.write("\n")


def _check_artifact(led: Optional[dict]) -> int:
    if led is None:
        verdict_line("failed:no-ledger")
        return 1
    probs = validate_ledger(led)
    for p in probs:
        print("  LEAN-SUITE ledger: " + p, file=sys.stderr)
    if probs:
        verdict_line("failed:ledger-inconsistent")
        return 1
    t = led["totals"]
    print("  LEAN-SUITE ledger OK: {} files; elab accepted {}/{}; elab_fail rejected {}/{}; "
          "clean-accepts-lean-rejects {}".format(t["files"], t["elab_clean_accept"], t["elab_oracle_files"],
                                                  t["elab_fail_clean_reject"], t["elab_fail_oracle_files"],
                                                  t[FALSE_ACCEPT]))
    verdict_line("artifact-ok")
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ledger", default=LEDGER)
    ap.add_argument("--tests-root", default=os.environ.get("LEAN4_TESTS_DIR")
                    or os.path.expanduser("~/lean4-src/tests"))
    ap.add_argument("--clean", default=os.environ.get("CLEAN_BIN") or os.path.join(ROOT, "target/release/clean"))
    ap.add_argument("--lean-bin", default=DEFAULT_LEAN)
    ap.add_argument("--lean", action="store_true", help="also re-measure Lean's verdict on every file")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--wall", type=float, default=DEFAULT_WALL_S)
    ap.add_argument("--rss-bytes", type=int, default=DEFAULT_RSS_BYTES)
    ap.add_argument("--only", action="append", default=[], help="restrict to these relative paths")
    ap.add_argument("--out", help="write the raw measurement (walls, peak RSS) here")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--rebase", default="", help="with --update: accept regressions, recording why")
    ap.add_argument("--check-artifact", action="store_true")
    ap.add_argument("--compare", metavar="MEASURED_JSON")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return _selftest()
    if a.update and a.only:
        ap.error("--update measures the whole selection; --only would write a partial ledger")

    led: Optional[dict] = None
    if os.path.exists(a.ledger):
        try:
            led = _load(a.ledger)
        except (OSError, ValueError) as exc:
            print("unreadable ledger {}: {}".format(a.ledger, exc), file=sys.stderr)
            verdict_line("failed:ledger-unreadable")
            return 1
    if a.check_artifact:
        return _check_artifact(led)
    if led is not None and validate_ledger(led):
        for p in validate_ledger(led):
            print("  LEAN-SUITE ledger: " + p, file=sys.stderr)
        verdict_line("failed:ledger-inconsistent")
        return 1
    if a.compare:
        if led is None:
            verdict_line("failed:no-ledger")
            return 1
        res = compare(led, _load(a.compare))
        render(res)
        verdict_line("failed:conformance-regression" if res["regressed"] else "compared")
        return 1 if res["regressed"] else 0

    if not os.path.isdir(os.path.join(a.tests_root, "elab")):
        return skip("no-tests", "no Lean tests checkout at {} (set --tests-root / LEAN4_TESTS_DIR)".format(
            a.tests_root))
    if not (os.path.isfile(a.clean) and os.access(a.clean, os.X_OK)):
        return skip("no-binary", "no clean binary at {}".format(a.clean))
    ident = tests_identity(a.tests_root)
    if led is not None and (led.get("tests_source") or {}).get("git_rev") != ident["git_rev"]:
        print("  tests checkout is {} but the ledger's rows are of {}; not comparable".format(
            ident["git_rev"] or "<no rev>", (led.get("tests_source") or {}).get("git_rev")))
        if not a.update:
            return skip("corpus-mismatch", "the Lean tests checkout is not the one the ledger was minted on")
        print("  --update on a different checkout re-mints the whole ledger (Lean re-measured)")
        led, a.lean = None, True
    files = select_files(a.tests_root)
    if a.only:
        files = [f for f in files if f[0] in set(a.only)]
    lean_for = None if (a.lean or led is None) else {k for k, _ in files if k not in led["files"]}
    lean_bin = a.lean_bin if (lean_for is None or lean_for) else None
    if lean_bin and not (os.path.isfile(lean_bin) and os.access(lean_bin, os.X_OK)):
        print("the pinned lean is required for this run and is absent at {}".format(lean_bin), file=sys.stderr)
        verdict_line("failed:no-lean")
        return 1
    t0 = time.monotonic()
    measured = measure(files, a.tests_root, os.path.abspath(a.clean), lean_bin, lean_for, a.jobs,
                       a.wall, a.rss_bytes)
    print("  measured {} files in {:.0f}s".format(len(measured), time.monotonic() - t0))
    if a.out:
        _write(a.out, measured)
    if led is None:
        if not a.update:
            verdict_line("failed:no-ledger")
            return 1
        rows = measured
    else:
        cmp_in = measured if not a.only else \
            {k: measured.get(k, {"clean": led["files"][k]["clean"]}) for k in led["files"]}
        res = compare(led, cmp_in)
        render(res)
        rebase_ok = a.update and len(a.rebase.strip()) >= 12
        if res["regressed"] and not rebase_ok:
            verdict_line("failed:conformance-regression")
            return 1
        if not a.update:
            verdict_line("measured")
            return 0
        rows = res["rows"]
        if res["regressed"]:
            led.setdefault("rebases", []).append(rebase_record(res, a.rebase, _dt.date.today().isoformat()))
    caps = {"wall_s": a.wall, "rss_bytes": a.rss_bytes, "poll_s": POLL_S, "retry_cap_hits": 1}
    new = build_ledger(led, rows, ident, os.path.abspath(a.clean), caps, lean_for is None)
    probs = validate_ledger(new)
    if probs:
        for p in probs:
            print("  LEAN-SUITE ledger: " + p, file=sys.stderr)
        verdict_line("failed:ledger-inconsistent")
        return 1
    _write(a.ledger, new)
    print("  ledger written: {}".format(a.ledger))
    verdict_line("measured")
    return 0


if __name__ == "__main__":
    sys.exit(main())
