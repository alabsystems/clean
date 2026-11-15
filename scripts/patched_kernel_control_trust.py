#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Run P3's patched-kernel control through Trust's island door and E9 lane (the Trust leg).

    scripts/heavy_gate.sh run 26 p3-trust-leg -- \\
        python3 scripts/patched_kernel_control_trust.py [--trust-repo DIR] \\
            [--trust-ref REF] [--work-dir DIR] [--keep] [--write-record]

`scripts/patched_kernel_control.py` measures Clean's own mint sites and the
`clean-kernel` calls Trust makes; this script measures Trust's code on top of
them: `trust-certify`'s island door, the island's reference gate and the E9
lane, from the audited judgment through the fenced entry to the certificate
the compiler's `Certified` mint reads back
(`trust_certify::reference_certificate_for`). The test it runs is
`scripts/p3_trust_leg/p3_planted_e9.rs` (its docs state the sites and the
contract). The weight above is 1.3 times the 19.61 GB peak of one cold build
of that test (2026-11-15); `scripts/heavy_gate.sh peaks` has the current one.

It never edits Trust's checkout or this repository's sources. It builds a
scratch copy of Trust's tree at `--trust-ref` (`git archive`, every file stamped
now) with each `first-party/*` gitlink filled from a local repository that
holds the pinned commit (this repository for `first-party/clean`, then Trust's
own submodule store, then a sibling checkout `../<name>`; a partial clone is
skipped and no git call here may fetch: `GIT_NO_LAZY_FETCH=1`), copies the test
into `crates/trust-certify/tests/`, and clones the tree once more with P3's
mutant M1 applied to `first-party/clean`'s `infer.rs` (the anchor and the
replacement are `patched_kernel_control.py`'s). Three legs, each tree with its
own fresh target directory (never shared: P3's 2026-11-13 finding):

  unmodified  the pinned Clean: every site refuses the planted pair;
  mutant      M1 with CLEAN_P3_KERNEL_UNDER_TEST naming it: each site's
              outcome must match its pin;
  undeclared  M1 again without the variable: must fail with `P3 WRONG ACCEPT`.

A leg passes only when its exit status is the required one AND its printed
rows name exactly the pinned sites, its controls all mint, and its kernel line
declares the leg's kernel. The scratch root is deleted on exit, failure and
SIGTERM/SIGHUP/SIGINT included, unless `--keep`. With `--write-record` (this
runner, P3's runner and the test committed and unmodified, before and after)
the measurement is written to RECORD.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import patched_kernel_control as p3  # noqa: E402  (the mutant and the targo resolution are P3's)

ROOT = p3.ROOT
RECORD = "reports/self-proof-p3-2026-11-12/patched_kernel_control_trust.json"
FIXTURE = "scripts/p3_trust_leg/p3_planted_e9.rs"
RUNNER = "scripts/patched_kernel_control_trust.py"
COMMITTED = [FIXTURE, RUNNER, "scripts/patched_kernel_control.py"]
PACKAGE = "trust-certify"
TEST = "p3_planted_e9"
TEST_FN = "p3_planted_false_through_trust_certify_e9_lane"
TEST_DEST = "crates/trust-certify/tests/p3_planted_e9.rs"
CLEAN_GITLINK = "first-party/clean"
CONTROL_STAGES = ["island", "audited", "reference", "registered"]
# leg -> (declare the mutant, required exit 0, kernel line printed by the test)
LEGS = {
    "unmodified": (False, True, "declared=Unmodified\tlive=false"),
    "mutant": (True, True, "declared=Mutant\tlive=true"),
    "undeclared": (False, False, "declared=Unmodified\tlive=true"),
}
NO_FETCH = {**os.environ, "GIT_NO_LAZY_FETCH": "1"}

_children: list[subprocess.Popen] = []


def fail(message: str) -> None:
    print(f"patched_kernel_control_trust: {message}", file=sys.stderr)
    raise SystemExit(1)


def on_signal(signum: int, _frame: object) -> None:
    raise SystemExit(128 + signum)


def run(*args: str) -> str:
    out = subprocess.run(list(args), capture_output=True, text=True, env=NO_FETCH)
    if out.returncode != 0:
        fail(f"`{' '.join(args)}` exited {out.returncode}: {out.stderr.strip()}")
    return out.stdout


def is_partial_clone(repo: Path) -> bool:
    probe = subprocess.run(["git", "-C", str(repo), "config", "--get-regexp", r"^remote\..*\.(promisor|partialclonefilter)$"],
                           capture_output=True, text=True, env=NO_FETCH)
    return bool(probe.stdout.strip())


def has_commit(repo: Path, sha: str) -> bool:
    if not (repo / ".git").exists() or is_partial_clone(repo):
        return False
    probe = subprocess.run(["git", "-C", str(repo), "cat-file", "-e", f"{sha}^{{commit}}"], capture_output=True, env=NO_FETCH)
    return probe.returncode == 0


def gitlinks(trust: Path, sha: str) -> dict[str, str]:
    links = {}
    for line in run("git", "-C", str(trust), "ls-tree", sha, "first-party/").splitlines():
        meta, path = line.split("\t", 1)
        mode, kind, commit = meta.split()
        if mode == "160000" and kind == "commit":
            links[path] = commit
    if CLEAN_GITLINK not in links:
        fail(f"Trust {sha} has no {CLEAN_GITLINK} gitlink")
    return links


def source_for(path: str, commit: str, trust: Path) -> Path:
    """A complete local repository holding `commit`. Nothing is fetched."""
    name = path.removeprefix("first-party/")
    candidates = list(dict.fromkeys(([ROOT] if path == CLEAN_GITLINK else []) + [trust / path, ROOT.parent / name, trust.parent / name]))
    for repo in candidates:
        if has_commit(repo, commit):
            return repo
    fail(f"no complete local repository holds {path} at {commit} (looked in {', '.join(map(str, candidates))}; partial clones are skipped)")
    raise AssertionError


def shown_path(repo: Path, trust: Path) -> str:
    """Where a source came from, without a machine-specific prefix."""
    if repo == ROOT:
        return "this repository"
    return os.path.relpath(repo, trust.parent)


def extract(repo: Path, commit: str, dest: Path) -> None:
    """`commit` of `repo` into `dest`, every file stamped now (`tar -m`)."""
    dest.mkdir(parents=True, exist_ok=True)
    pack = subprocess.Popen(["git", "-C", str(repo), "archive", "--format=tar", commit], stdout=subprocess.PIPE, env=NO_FETCH)
    unpack = subprocess.Popen(["tar", "-x", "-m", "-f", "-", "-C", str(dest)], stdin=pack.stdout)
    assert pack.stdout is not None
    pack.stdout.close()  # tar holds the read end; git sees EPIPE if tar dies
    if unpack.wait() != 0 or pack.wait() != 0:
        fail(f"extracting {repo} at {commit} into {dest} failed")


def build_tree(dest: Path, trust: Path, sha: str, links: dict[str, str]) -> dict[str, dict[str, str]]:
    extract(trust, sha, dest)
    sources = {}
    for path, commit in sorted(links.items()):
        repo = source_for(path, commit, trust)
        target = dest / path
        if target.exists():
            shutil.rmtree(target)
        extract(repo, commit, target)
        sources[path] = {"commit": commit, "from": shown_path(repo, trust)}
    installed = dest / TEST_DEST
    if installed.exists():
        fail(f"Trust already has {TEST_DEST}; this runner would overwrite it")
    shutil.copyfile(ROOT / FIXTURE, installed)
    return sources


def clone_tree(src: Path, dest: Path) -> None:
    # APFS clone where available (copy-on-write: no data copied, writes stay
    # private to the clone); a plain copy elsewhere.
    if subprocess.run(["cp", "-c", "-R", str(src), str(dest)], capture_output=True).returncode != 0:
        shutil.rmtree(dest, ignore_errors=True)
        shutil.copytree(src, dest, symlinks=True)


def run_leg(leg: str, tree: Path, target: Path, logs: Path, targo: str) -> dict:
    declare, _, _ = LEGS[leg]
    command = [targo, "--unverified", "test", "--locked", "-p", PACKAGE, "--test", TEST, "--", "--exact", TEST_FN, "--nocapture"]
    env = {k: v for k, v in os.environ.items() if k != p3.MODE_ENV}
    env["CARGO_TARGET_DIR"] = str(target)
    if declare:
        env[p3.MODE_ENV] = p3.MUTANT_ID
    log = logs / f"{leg}.log"
    print(f"patched_kernel_control_trust: {leg} leg (log {log})", flush=True)
    with log.open("w") as out:
        child = subprocess.Popen(command, cwd=tree, env=env, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
        _children.append(child)
        status = child.wait()
        _children.remove(child)
    text = log.read_text(errors="replace")
    rows, control, pins, kernel = [], [], [], None
    for line in text.splitlines():
        cells = line.split("\t")
        if cells[0] == "P3_TRUST" and len(cells) == 4:
            rows.append({"site": cells[1], "outcome": cells[2], "detail": cells[3]})
        elif cells[0] == "P3_TRUST_CONTROL" and len(cells) == 4:
            control.append({"stage": cells[1], "outcome": cells[2], "detail": cells[3]})
        elif cells[0] == "P3_TRUST_PIN" and len(cells) == 4:
            pins.append({"site": cells[1], "unmodified": cells[2], "mutant": cells[3]})
        elif cells[0] == "P3_TRUST_KERNEL":
            kernel = "\t".join(cells[1:])
    shown = ["targo", *command[1:]]
    if declare:
        shown = [f"{p3.MODE_ENV}={p3.MUTANT_ID}", *shown]
    return {"leg": leg, "command": " ".join(shown), "exit_status": status, "kernel": kernel,
            "wrong_accept_reported": p3.WRONG_ACCEPT in text, "pins": pins, "control": control, "rows": rows, "log": text}


def judge(leg: dict) -> list[str]:
    """Why `leg` did not end as its contract requires (empty when it did)."""
    declare, passes, kernel = LEGS[leg["leg"]]
    problems = []
    if (leg["exit_status"] == 0) != passes:
        problems.append(f"exit status {leg['exit_status']}, required {'0' if passes else 'non-zero'}")
    if leg["kernel"] != kernel:
        problems.append(f"kernel line {leg['kernel']!r}, required {kernel!r}")
    pinned = [pin["site"] for pin in leg["pins"]]
    if not pinned or [row["site"] for row in leg["rows"]] != pinned:
        problems.append(f"measured sites {[row['site'] for row in leg['rows']]} are not the pinned sites {pinned}")
    if [c["stage"] for c in leg["control"]] != CONTROL_STAGES or any(c["outcome"] != "Minted" for c in leg["control"]):
        problems.append(f"controls {[(c['stage'], c['outcome']) for c in leg['control']]} are not all minted")
    if passes:
        column = "mutant" if declare else "unmodified"
        for row, pin in zip(leg["rows"], leg["pins"]):
            if row["outcome"] != pin[column]:
                problems.append(f"{row['site']}: {row['outcome']}, pinned {pin[column]}")
    elif not leg["wrong_accept_reported"]:
        problems.append("no `P3 WRONG ACCEPT` in the output")
    return problems


def committed_unmodified(paths: list[str]) -> bool:
    out = subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain", "--", *paths], capture_output=True, text=True)
    return out.returncode == 0 and not out.stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--trust-repo", type=Path, default=ROOT.parent / "trust")
    parser.add_argument("--trust-ref", default="origin/main")
    parser.add_argument("--work-dir", type=Path, help="scratch root; must not exist (default: a new temporary directory)")
    parser.add_argument("--keep", action="store_true", help="keep the scratch root")
    parser.add_argument("--write-record", action="store_true", help=f"write {RECORD}")
    args = parser.parse_args()

    if not os.environ.get("HEAVY_GATE_HELD"):
        fail("run me under scripts/heavy_gate.sh run 26 p3-trust-leg -- python3 scripts/patched_kernel_control_trust.py ...")
    if args.write_record and not committed_unmodified(COMMITTED):
        fail(f"--write-record needs {', '.join(COMMITTED)} committed and unmodified")
    clean_commit = run("git", "-C", str(ROOT), "rev-parse", "HEAD").strip()
    fixture_sha = p3.sha256(ROOT / FIXTURE)
    trust = args.trust_repo.resolve()
    trust_sha = run("git", "-C", str(trust), "rev-parse", f"{args.trust_ref}^{{commit}}").strip()
    links = gitlinks(trust, trust_sha)
    clean_pin = links[CLEAN_GITLINK]
    pinned_infer = run("git", "-C", str(ROOT), "show", f"{clean_pin}:{p3.MUTATION_FILE}")
    if pinned_infer.count(p3.ANCHOR) != 1:
        fail(f"the mutation anchor occurs {pinned_infer.count(p3.ANCHOR)} times in {p3.MUTATION_FILE} at Trust's Clean pin {clean_pin}")
    targo = p3.resolve_targo()

    for signum in (signal.SIGTERM, signal.SIGHUP, signal.SIGINT):
        signal.signal(signum, on_signal)
    work: Path | None = None
    try:
        if args.work_dir is not None:
            work = args.work_dir.resolve()
            if work.exists():
                work = None
                fail(f"{args.work_dir} exists; the runner owns a fresh scratch root and refuses one it did not make")
            work.mkdir(parents=True)
        else:
            work = Path(tempfile.mkdtemp(prefix="p3-trust-leg-"))
        (work / ".metadata_never_index").touch()
        logs = work / "logs"
        logs.mkdir()

        base = work / "unmodified" / "trust"
        sources = build_tree(base, trust, trust_sha, links)
        if p3.sha256(base / TEST_DEST) != fixture_sha:
            fail("the installed test is not the fixture this run started from")
        mutant = work / "mutant" / "trust"
        mutant.parent.mkdir(parents=True)
        clone_tree(base, mutant)
        base_infer = p3.sha256(base / CLEAN_GITLINK / p3.MUTATION_FILE)
        mutation = p3.mutate(mutant / CLEAN_GITLINK)
        if mutation["original_sha256"] != base_infer or p3.sha256(base / CLEAN_GITLINK / p3.MUTATION_FILE) != base_infer:
            fail("the mutant's infer.rs did not start as the unmodified tree's, or patching it moved the unmodified tree's")

        legs = [
            run_leg("unmodified", base, work / "target-unmodified", logs, targo),
            run_leg("mutant", mutant, work / "target-mutant", logs, targo),
            run_leg("undeclared", mutant, work / "target-mutant", logs, targo),
        ]
        if p3.sha256(base / CLEAN_GITLINK / p3.MUTATION_FILE) != base_infer:
            fail("the unmodified tree's infer.rs moved during the run")

        verdicts = [judge(leg) for leg in legs]
        for leg, problems in zip(legs, verdicts):
            print(f"patched_kernel_control_trust: {leg['leg']}: exit {leg['exit_status']} "
                  f"({'as required' if not problems else 'NOT as required: ' + '; '.join(problems)})")
            for row in leg["rows"]:
                print(f"    {row['site']}: {row['outcome']} -- {row['detail'][:200]}")
        if any(verdicts):
            for leg, problems in zip(legs, verdicts):
                if problems:
                    print(leg["log"][-6000:], file=sys.stderr)
            fail("a leg did not end as required")
        if legs[0]["pins"] != legs[1]["pins"] or legs[1]["pins"] != legs[2]["pins"]:
            fail("the legs printed different pins")

        if args.write_record:
            if not committed_unmodified(COMMITTED) or run("git", "-C", str(ROOT), "rev-parse", "HEAD").strip() != clean_commit:
                fail("the runner, P3's runner or the test moved during the run; nothing recorded")
            record = {
                "schema": "clean.p3-trust-leg/v1",
                "what_this_is": "P3's planted proof of False through trust-certify's island door, its reference gate and its E9 lane, measured by " + RUNNER,
                "measured_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "clean_commit": clean_commit,
                "trust": {"ref": args.trust_ref, "commit": trust_sha, "gitlinks": sources},
                "clean_pin_in_trust": clean_pin,
                "mutation": {"id": p3.MUTANT_ID, "file": f"{CLEAN_GITLINK}/{p3.MUTATION_FILE}", **mutation},
                "fixture": {"path": FIXTURE, "installed_as": TEST_DEST, "sha256": fixture_sha},
                "pins": legs[0]["pins"],
                "legs": [{k: v for k, v in leg.items() if k not in ("log", "pins")} for leg in legs],
            }
            (ROOT / RECORD).write_text(json.dumps(record, indent=2) + "\n")
            print(f"patched_kernel_control_trust: wrote {RECORD}")
        return 0
    finally:
        for child in list(_children):
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
        if work is not None:
            if args.keep:
                print(f"patched_kernel_control_trust: kept {work}")
            else:
                shutil.rmtree(work, ignore_errors=True)
                if work.exists():
                    print(f"patched_kernel_control_trust: could not delete all of {work}; remove it by hand", file=sys.stderr)


if __name__ == "__main__":
    raise SystemExit(main())
