#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Run P3's patched-kernel control through Trust's trust-certify mint sites and its temporal
source certification (the Trust leg).

    scripts/heavy_gate.sh run 52 p3-trust-leg -- \\
        python3 scripts/patched_kernel_control_trust.py [--trust-repo DIR] \\
            [--trust-ref REF] [--gitlink-source first-party/NAME=DIR]... \\
            [--work-dir DIR] [--keep] [--write-record]

`scripts/patched_kernel_control.py` measures Clean's own mint sites and the
`clean-kernel` calls Trust makes; this script measures Trust's code on top of
them: `trust-certify`'s island doors (single and batched), the island's
reference gate and judgment check, the E9 mints (the scalar one the compiler
calls and the exact-domain one) with the grade the compiler reads, from the
audited judgment through the fenced entry to the certificate the compiler's
`Certified` mint reads back (`trust_certify::reference_certificate_for`), a
calculus row over a stand-in VF5 family, presented violation-refutation
evidence, and the planted pair from island source through a term-level
`let rec` (both doors, then the helper and the parent cited through the E9
lane on the batched door's session environment); and, in the separate
`trust-spec-temporal` workspace, `certify_clean_temporal_source` and
`recheck_clean_temporal_certificate` on the plain and the `let rec` source. The
tests it runs are `scripts/p3_trust_leg/p3_planted_e9.rs` (built with Trust's
`calculus-row-test-support` feature, a test door that gates only
`calculus_row::test_support`) and `scripts/p3_trust_leg/p3_planted_temporal.rs`;
their docs state the sites. Both trees give Clean's clean-tla the two `Expr::BuiltinSet` match
arms of Clean's commit 7253ee4957, without which `trust-spec-temporal` does not compile from
Trust's own pins (`shim_clean_tla`, which states why and refuses once either pin makes the
arms wrong); the record carries the shim. `scripts/p3_trust_leg/` mirrors the `tests/`
directory each is installed into, with its modules and the contract both share
(`p3_contract/contract.rs`); the runner installs every file there, refuses a
file in it that no test installs, and records each installed file's digest. The weight above is 1.3 times the class's largest
completed peak, 39.65 GB (2026-11-15; the same command has also peaked under
20 GB, and the cause of the difference was not determined); the gate raises a
lower weight to it, and `scripts/heavy_gate.sh peaks` has the current one.

Trust's tree is taken at `--trust-ref`. Every `first-party/*` gitlink there
must be held by a complete local repository: when Trust's main pins a commit
only a partial clone (or nobody) here holds, name an older `--trust-ref` whose
gitlinks resolve and state why in the record's README.

It never edits Trust's checkout or this repository's sources. It builds a
scratch copy of Trust's tree at `--trust-ref` (`git archive`, every file stamped
now) with each `first-party/*` gitlink filled from a local repository that
holds the pinned commit (this repository for `first-party/clean`, then Trust's
own submodule store, then a sibling checkout `../<name>`, then any repository
named for that path with `--gitlink-source PATH=DIR`; a partial clone is
skipped wherever it is named and no git call here may fetch:
`GIT_NO_LAZY_FETCH=1`; the record says which source was named), installs each
test with its modules and the shared contract into its crate's `tests/`
(`crates/trust-certify/tests/`, `crates/trust-spec-temporal/tests/`), gives
clean-tla the shim's two arms, and clones the tree once more with P3's
mutant M1 applied to `first-party/clean`'s `infer.rs` (the anchor and the
replacement are `patched_kernel_control.py`'s). Three legs, each tree and each
workspace with its own fresh target directory (never shared: P3's 2026-11-13
finding), each running both tests:

  unmodified  the pinned Clean: every site refuses the planted pair;
  mutant      M1 with CLEAN_P3_KERNEL_UNDER_TEST naming it: each site's
              outcome must match its pin;
  undeclared  M1 again without the variable: must fail with `P3 WRONG ACCEPT`.

A test's leg passes only when its exit status is the required one AND its printed
rows name exactly the pinned sites with its binary's pinned outcomes (the
undeclared leg runs the mutant's), its controls all mint, and its kernel line
declares the leg's kernel. The undeclared leg must report `P3 WRONG ACCEPT` at
the liveness check and at exactly the sites pinned to mint only under the
mutant, and fail in no other way. The test runs with `TRUST_KR0_DEBUG=1`,
Trust's measurement-only report of each reference-entry refusal: on the mutant
binary the refutation's entry (lane `int`) must refuse exactly once, by a type
mismatch, and on the unmodified binary it must not be reached (the open-term
check refuses first). That rule is the E9 test's; the temporal test reaches no
reference entry and must report no miss. The scratch root is deleted on exit, failure and
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
from patched_kernel_control_trust_tree import (  # noqa: E402  (the scratch tree)
    CLEAN_GITLINK, clone_tree, extract, fail, gitlinks, named_sources, run, shim_clean_tla, shown_path, source_for,
)

ROOT = p3.ROOT
RECORD = "reports/self-proof-p3-2026-11-12/patched_kernel_control_trust.json"
FIXTURE_DIR = "scripts/p3_trust_leg"
RUNNER = "scripts/patched_kernel_control_trust.py"
CONTRACT = "p3_contract/contract.rs"
E9_CONTROL_STAGES = [
    "island", "audited", "reference", "registered",
    "domains.audited", "domains.reference", "domains.registered",
    "grade", "island_judgment_universe", "calculus.certify", "calculus.registered",
    "island_example", "batch_example",
    "refutation.certify_vc", "refutation.replay", "refutation.linear_int",
    "let_rec.island", "let_rec.batch", "let_rec.audited", "let_rec.reference",
    "let_rec.registered", "let_rec.grade", "let_rec_parent.audited",
    "let_rec_parent.reference", "let_rec_parent.registered", "let_rec_parent.grade",
]
# Each test: where it is installed (paths under FIXTURE_DIR keep their place under
# `tests`), the workspace it is built in, the `targo test` selection, the one
# test function, its control stages, and whether the refutation's `int` miss rule
# applies (the E9 test's; the temporal test must report no miss at all). The E9
# test is built with the test door the calculus rows need (it gates only
# `calculus_row::test_support`).
TESTS = [
    {
        "name": "p3_planted_e9",
        "workspace": ".",
        "tests": "crates/trust-certify/tests",
        "files": ["p3_planted_e9.rs", "p3_planted_e9/controls.rs", "p3_planted_e9/evidence.rs",
                  "p3_planted_e9/lanes.rs", "p3_planted_e9/planted.rs", CONTRACT],
        "select": ["-p", "trust-certify", "--features", "calculus-row-test-support", "--test", "p3_planted_e9"],
        "test_fn": "p3_planted_false_through_trust_certify_e9_lane",
        "controls": E9_CONTROL_STAGES,
        "int_miss_rule": True,
    },
    {
        "name": "p3_planted_temporal",
        "workspace": "crates/trust-spec-temporal",
        "tests": "crates/trust-spec-temporal/tests",
        "files": ["p3_planted_temporal.rs", CONTRACT],
        "select": ["--test", "p3_planted_temporal"],
        "test_fn": "p3_planted_false_through_temporal_certification",
        "controls": ["temporal.honest.certify", "temporal.honest.recheck",
                     "temporal.let_rec.certify", "temporal.let_rec.recheck"],
        "int_miss_rule": False,
    },
]
SPEC = {test["name"]: test for test in TESTS}
FIXTURE_FILES = sorted({f"{FIXTURE_DIR}/{name}" for test in TESTS for name in test["files"]})
COMMITTED = [*FIXTURE_FILES, RUNNER, "scripts/patched_kernel_control_trust_tree.py", "scripts/patched_kernel_control.py"]
# leg -> (declare the mutant, required exit 0, kernel line printed by the test)
LEGS = {
    "unmodified": (False, True, "declared=Unmodified\tlive=false"),
    "mutant": (True, True, "declared=Mutant\tlive=true"),
    "undeclared": (False, False, "declared=Unmodified\tlive=true"),
}
# The legs that run the mutant binary (the undeclared leg reuses the mutant's).
MUTANT_BINARY = {"unmodified": False, "mutant": True, "undeclared": True}
WRONG_ACCEPT = "P3 WRONG ACCEPT: "
LIVENESS = WRONG_ACCEPT + p3.MODE_ENV + " is unset"
# Trust's measurement-only report of a reference-entry refusal
# (`reference_mint::note_miss`, on when `TRUST_KR0_DEBUG` is set; it never changes
# a verdict). The refutation replay reports its entry's refusal as lane `int`.
MISS_PREFIX = "TRUST_KR0_DEBUG REFERENCE-MISS lane="

_children: list[subprocess.Popen] = []


def on_signal(signum: int, _frame: object) -> None:
    raise SystemExit(128 + signum)


def build_tree(dest: Path, trust: Path, sha: str, links: dict[str, str],
               named: dict[str, list[Path]] | None = None) -> dict[str, dict[str, object]]:
    extract(trust, sha, dest)
    sources: dict[str, dict[str, object]] = {}
    for path, commit in sorted(links.items()):
        repo, was_named = source_for(path, commit, trust, named)
        target = dest / path
        if target.exists():
            shutil.rmtree(target)
        extract(repo, commit, target)
        sources[path] = {"commit": commit, "from": shown_path(repo, trust)}
        if was_named:
            sources[path]["named_by"] = "--gitlink-source"
    for source, installed in installs():
        if (dest / installed).exists():
            fail(f"Trust already has {installed}; this runner would overwrite it")
        (dest / installed).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / source, dest / installed)
    return sources


def installs() -> list[tuple[str, str]]:
    """(file under FIXTURE_DIR, where it is installed in Trust's tree), for every test."""
    return [(f"{FIXTURE_DIR}/{name}", f"{test['tests']}/{name}") for test in TESTS for name in test["files"]]


def fixture_files_unclaimed() -> list[str]:
    """Files under FIXTURE_DIR that no test installs (a module nothing builds)."""
    present = {str(path.relative_to(ROOT)) for path in (ROOT / FIXTURE_DIR).rglob("*") if path.is_file()}
    return sorted(present - set(FIXTURE_FILES))


def run_leg(leg: str, test: dict, tree: Path, target: Path, logs: Path, targo: str) -> dict:
    declare, _, _ = LEGS[leg]
    command = [targo, "--unverified", "test", "--locked", *test["select"],
               "--", "--exact", test["test_fn"], "--nocapture"]
    env = {k: v for k, v in os.environ.items() if k != p3.MODE_ENV}
    env["CARGO_TARGET_DIR"] = str(target)
    env["TRUST_KR0_DEBUG"] = "1"
    if declare:
        env[p3.MODE_ENV] = p3.MUTANT_ID
    log = logs / f"{leg}-{test['name']}.log"
    print(f"patched_kernel_control_trust: {leg} leg, {test['name']} (log {log})", flush=True)
    with log.open("w") as out:
        child = subprocess.Popen(command, cwd=tree / test["workspace"], env=env, stdout=out,
                                 stderr=subprocess.STDOUT, start_new_session=True)
        _children.append(child)
        status = child.wait()
        _children.remove(child)
    text = log.read_text(errors="replace")
    rows, control, pins, kernel, failures, misses = [], [], [], None, [], []
    for line in text.splitlines():
        if line.startswith("P3 "):
            failures.append(line)
        elif line.startswith(MISS_PREFIX):
            lane, _, miss = line[len(MISS_PREFIX):].partition(" ")
            misses.append({"lane": lane, "miss": miss})
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
    return {"leg": leg, "test": test["name"], "workspace": test["workspace"], "command": " ".join(shown),
            "exit_status": status, "kernel": kernel, "failures": failures, "reference_misses": misses,
            "pins": pins, "control": control, "rows": rows, "log": text}


def judge(leg: dict) -> list[str]:
    """Why one test's `leg` did not end as its contract requires (empty when it did)."""
    declare, passes, kernel = LEGS[leg["leg"]]
    test = SPEC.get(leg.get("test", ""))
    if test is None:
        return [f"no test named {leg.get('test')!r}"]
    problems = []
    if (leg["exit_status"] == 0) != passes:
        problems.append(f"exit status {leg['exit_status']}, required {'0' if passes else 'non-zero'}")
    if leg["kernel"] != kernel:
        problems.append(f"kernel line {leg['kernel']!r}, required {kernel!r}")
    pinned = [pin["site"] for pin in leg["pins"]]
    if not pinned or [row["site"] for row in leg["rows"]] != pinned:
        problems.append(f"measured sites {[row['site'] for row in leg['rows']]} are not the pinned sites {pinned}")
    if [c["stage"] for c in leg["control"]] != test["controls"] or any(c["outcome"] != "Minted" for c in leg["control"]):
        problems.append(f"controls {[(c['stage'], c['outcome']) for c in leg['control']]} are not all minted")
    # Every leg's rows are its binary's pins: the undeclared leg runs the mutant's.
    column = "mutant" if MUTANT_BINARY[leg["leg"]] else "unmodified"
    for row, pin in zip(leg["rows"], leg["pins"]):
        if row["outcome"] != pin[column]:
            problems.append(f"{row['site']}: {row['outcome']}, pinned {pin[column]}")
    if passes:
        if leg["failures"]:
            problems.append(f"failures printed: {leg['failures'][:3]}")
    else:
        # Exactly the liveness check and every site pinned to mint only under
        # the mutant report `P3 WRONG ACCEPT`, and nothing else fails.
        expected = {pin["site"] for pin in leg["pins"] if (pin["unmodified"], pin["mutant"]) == ("Refused", "Minted")}
        reported, liveness, other = set(), False, []
        for line in leg["failures"]:
            site = line[len(WRONG_ACCEPT):].split(": ", 1)[0] if line.startswith(WRONG_ACCEPT) else None
            if line.startswith(LIVENESS):
                liveness = True
            elif site in expected:
                reported.add(site)
            else:
                other.append(line)
        if not liveness:
            problems.append("no `P3 WRONG ACCEPT` at the liveness check")
        if reported != expected:
            problems.append(f"`P3 WRONG ACCEPT` at {sorted(reported)}, required at {sorted(expected)}")
        if other:
            problems.append(f"other failures: {other[:3]}")
    if not test["int_miss_rule"]:
        if leg["reference_misses"]:
            problems.append(f"a test that reaches no reference entry reported misses: {leg['reference_misses'][:3]}")
        return problems
    # Where the presented refutation evidence is refused: by the reference entry
    # (one kernel type mismatch) on the mutant binary, before it otherwise.
    int_misses = [miss["miss"] for miss in leg["reference_misses"] if miss["lane"] == "int"]
    if MUTANT_BINARY[leg["leg"]]:
        if len(int_misses) != 1 or not ("Refused(Kernel(" in int_misses[0] and "TypeMismatch" in int_misses[0]):
            problems.append(f"the refutation's reference entry did not refuse exactly once by a type mismatch: {int_misses[:3]}")
    elif int_misses:
        problems.append(f"the refutation reached its reference entry on the unmodified binary: {int_misses[:3]}")
    return problems


def committed_unmodified(paths: list[str]) -> bool:
    out = subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain", "--", *paths], capture_output=True, text=True)
    return out.returncode == 0 and not out.stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--trust-repo", type=Path, default=ROOT.parent / "trust")
    parser.add_argument("--trust-ref", default="origin/main")
    parser.add_argument("--gitlink-source", action="append", default=[], metavar="PATH=DIR",
                        help="also look for first-party/<name> in DIR (complete clones only; recorded)")
    parser.add_argument("--work-dir", type=Path, help="scratch root; must not exist (default: a new temporary directory)")
    parser.add_argument("--keep", action="store_true", help="keep the scratch root")
    parser.add_argument("--write-record", action="store_true", help=f"write {RECORD}")
    args = parser.parse_args()

    if not os.environ.get("HEAVY_GATE_HELD"):
        fail("run me under scripts/heavy_gate.sh run 52 p3-trust-leg -- python3 scripts/patched_kernel_control_trust.py ...")
    if args.write_record and not committed_unmodified(COMMITTED):
        fail(f"--write-record needs {', '.join(COMMITTED)} committed and unmodified")
    unclaimed = fixture_files_unclaimed()
    if unclaimed:
        fail(f"{', '.join(unclaimed)} under {FIXTURE_DIR} would be installed by no test")
    clean_commit = run("git", "-C", str(ROOT), "rev-parse", "HEAD").strip()
    fixture_shas = {source: p3.sha256(ROOT / source) for source in FIXTURE_FILES}
    trust = args.trust_repo.resolve()
    trust_sha = run("git", "-C", str(trust), "rev-parse", f"{args.trust_ref}^{{commit}}").strip()
    links = gitlinks(trust, trust_sha)
    named = named_sources(args.gitlink_source)
    unknown = sorted(set(named) - set(links))
    if unknown:
        fail(f"--gitlink-source names {', '.join(unknown)}, which Trust {trust_sha} does not pin")
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
        sources = build_tree(base, trust, trust_sha, links, named)
        shim = shim_clean_tla(base)
        if any(p3.sha256(base / installed) != fixture_shas[source] for source, installed in installs()):
            fail("an installed test file is not the fixture this run started from")
        mutant = work / "mutant" / "trust"
        mutant.parent.mkdir(parents=True)
        clone_tree(base, mutant)
        base_infer = p3.sha256(base / CLEAN_GITLINK / p3.MUTATION_FILE)
        mutation = p3.mutate(mutant / CLEAN_GITLINK)
        if mutation["original_sha256"] != base_infer or p3.sha256(base / CLEAN_GITLINK / p3.MUTATION_FILE) != base_infer:
            fail("the mutant's infer.rs did not start as the unmodified tree's, or patching it moved the unmodified tree's")
        if any(p3.sha256(tree / shim["file"]) != shim["patched_sha256"] for tree in (base, mutant)):
            fail("a tree's clean-tla is not the shimmed file")

        # Every test in each leg; the undeclared leg reuses the mutant's targets.
        legs = [
            run_leg(leg, test, tree, work / f"target-{target}-{test['name']}", logs, targo)
            for leg, tree, target in (("unmodified", base, "unmodified"), ("mutant", mutant, "mutant"),
                                      ("undeclared", mutant, "mutant"))
            for test in TESTS
        ]
        if p3.sha256(base / CLEAN_GITLINK / p3.MUTATION_FILE) != base_infer:
            fail("the unmodified tree's infer.rs moved during the run")

        verdicts = [judge(leg) for leg in legs]
        for leg, problems in zip(legs, verdicts):
            print(f"patched_kernel_control_trust: {leg['leg']}, {leg['test']}: exit {leg['exit_status']} "
                  f"({'as required' if not problems else 'NOT as required: ' + '; '.join(problems)})")
            for row in leg["rows"]:
                print(f"    {row['site']}: {row['outcome']} -- {row['detail'][:200]}")
        if any(verdicts):
            for leg, problems in zip(legs, verdicts):
                if problems:
                    print(leg["log"][-6000:], file=sys.stderr)
            fail("a leg did not end as required")
        pins = {test["name"]: [leg["pins"] for leg in legs if leg["test"] == test["name"]] for test in TESTS}
        if any(any(each != printed[0] for each in printed) for printed in pins.values()):
            fail("the legs of a test printed different pins")

        if args.write_record:
            if not committed_unmodified(COMMITTED) or run("git", "-C", str(ROOT), "rev-parse", "HEAD").strip() != clean_commit:
                fail("the runner, P3's runner or the test moved during the run; nothing recorded")
            record = {
                "schema": "clean.p3-trust-leg/v2",
                "what_this_is": "P3's planted proof of False through trust-certify's island doors, reference gate and judgment check, the E9 mints and grade, a calculus row over a stand-in family and presented refutation evidence, and through trust-spec-temporal's source certification and its recheck (the sites are each test's pins), measured by " + RUNNER,
                "measured_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "clean_commit": clean_commit,
                "trust": {"ref": args.trust_ref, "commit": trust_sha, "gitlinks": sources},
                "clean_pin_in_trust": clean_pin,
                "mutation": {"id": p3.MUTANT_ID, "file": f"{CLEAN_GITLINK}/{p3.MUTATION_FILE}", **mutation},
                "clean_tla_shim": shim,
                "fixture": [{"path": source, "installed_as": installed, "sha256": fixture_shas[source]}
                            for source, installed in installs()],
                "pins": {name: printed[0] for name, printed in pins.items()},
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
