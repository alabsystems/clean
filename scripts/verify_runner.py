#!/usr/bin/env python3
"""Persistent, resumable, per-target test runner for the Clean workspace.

WHY THIS EXISTS
---------------
`cargo test --locked -p clean-verify` is not completable inside one agent
session: the lib target alone declares thousands of tests and 39 integration
targets follow it, several measured in the tens of minutes each. The observed
consequence was that nobody could state the repo's test state, so commits
landed on top of an unknown, and each new agent re-derived the same partial
answer and ran out of time in the same place.

This runner makes greenness a durable, incrementally-maintained *fact*:

  * every target runs INDIVIDUALLY, detached, so it outlives the agent harness
    process reaper (see scripts/daemonize.py);
  * every completed run appends a durable per-target record under
    `data/suite_state/` carrying the commit sha, the exact command, the exit
    code and the verbatim final line of output;
  * re-invoking skips targets already GREEN *at the current input digest* and
    re-runs everything else;
  * a target that has never run is reported UNKNOWN -- never as a pass.

WHAT "INPUTS CHANGED" MEANS -- READ THIS BEFORE TRUSTING A GREEN
----------------------------------------------------------------
A stored result is honoured only when its `input_digest` still matches the
digest computed now. The digest is a SHA-256 over, in sorted order:

  1. the *working-tree* content of every git-visible file (tracked, plus
     untracked-and-not-ignored) under the target package's directory and under
     the directory of every workspace path-dependency in its transitive
     closure, dev-dependencies included;
  2. the workspace root `Cargo.toml` and `Cargo.lock`;
  3. the `rustc -vV` release/host/commit-hash string;
  4. the exact argv the target is run with.

It is therefore strictly stronger than a commit sha: an uncommitted edit to a
source file in the closure invalidates the green, and a commit that touches
only unrelated crates does not. The commit sha is recorded alongside for
attribution but is NOT what freshness is decided on.

The digest deliberately does NOT cover, and a matching digest therefore does
NOT rule out drift in:

  * the contents of the cargo registry / vendored crate sources (only
    `Cargo.lock` is hashed, so a *pin* change is caught but a mutated
    `~/.cargo` checkout is not);
  * files outside the repository that a test reads -- `.olean` corpora,
    `data/corpora/`, `$HOME` configuration, network services;
  * environment variables, feature flags supplied outside the recorded argv,
    and the state of the shared `target/` directory;
  * anything nondeterministic in the test itself (time, threads, ports).

Those exclusions are the honest boundary of this tool. A GREEN here means
"this exact command exited 0 on this machine against this source closure",
not "this target is correct".

TIMEOUTS ARE PER-TARGET AND DERIVED, NEVER A FLAT NUMBER
--------------------------------------------------------
This inventory spans four orders of magnitude of runtime: `gate::fmt` finishes
in 45s, `clean-verify::test::axiom_refutation_gate` took 4813s here, and
`clean-verify::lib` is a multi-hour target. No single budget fits it. On
2026-08-12 a flat 25s killed `clean-verify::test::whnf_lemma_wrapper_defs` at
"running 2 tests" and recorded ERROR -- the artifact behaving exactly as
designed, because an unfinished run is neither a pass nor a failure, but a
measurement thrown away. That target was later measured at 1761.1s.

So each target's budget is now derived from what that target has actually cost
here: HEADROOM x its last completed duration, floored by its kind, doubled if
its previous run was killed, and clamped to a hard ceiling. `timeout_for` holds
the rules and every record carries a `timeout_basis` explaining its number.
Run `scripts/verify_runner.sh policy` to see the table before launching a queue.

The one thing the policy will not do is stop enforcing a limit. There is no
unlimited setting and `--timeout` is an explicit override, not the default: a
target that cannot finish inside its budget is a defect to report, not a
number to raise.

SHARDING -- WHEN ONE TARGET CANNOT FINISH AS ONE UNIT
-----------------------------------------------------
`clean-verify::lib` is a single test binary declaring thousands of tests, and on
2026-08-13 it was killed at 43200s with 6361 of 6900 done and 0 failures: not a
pass, not a failure, twelve hours of electricity converted into no information.
Raising the budget only moves the wall, so the target is instead SPLIT into
shards, each of which is a first-class target with its own record, its own input
digest and its own budget.

The shard key is a total function on a test's name -- see `shard_key` -- so the
shards partition the tests *by construction*. That is not taken on faith:
`shards plan` re-derives each shard's membership from libtest's own `--list`
filtering and refuses to write a plan unless the observed sets are pairwise
disjoint, cover every declared test, and sum to the declared total.

Three separate defences stop a shard scheme from silently losing tests, which
would be strictly worse than the unmeasured status quo:

  1. plan time -- the `--list` partition proof above, stored in the plan;
  2. run time -- a shard is GREEN only if the tests it actually ran equal the
     count its plan entry promised. A filter that stops matching reports
     "0 passed" and exits 0, which would otherwise read as a pass;
  3. roll-up time -- the parent is GREEN only when EVERY shard is GREEN at the
     current digest *and* the shards' own measured test counts re-sum to the
     declared total. Any missing, stale, running or unmeasured shard makes the
     parent UNKNOWN. It is never GREEN on a partial set.

WHY THE SHARDS ARE PACKED COARSELY -- THE COST MOVED, SO THE CUT MOVED
----------------------------------------------------------------------
The first cut answered the question "how do I keep each shard under a time
budget?", and the answer was 395 shards on module prefixes. That question was
the right one while EVERY `spec::*` test rebuilt the whole specification: cost
was proportional to tests, so cutting by tests cut cost.

`perf(verify): build each spec flavour once per process` (6dbe7955b) changed the
cost function underneath the cut. Each specification flavour is now built once
per PROCESS behind a `OnceLock` and every caller gets a `clone()`. Measured on
one 4-test shard, same argv, concurrent runs: 13156s -> 4007s wall and 8077 ->
2085 CPU-s; per-test marginal cost fell from ~2019 CPU-s to 0.017-0.053s. In the
cached run the single build was 4007.5s of the shard's 4007.62s -- the four
tests' own work was 0.12s.

Cost is therefore no longer proportional to tests. It is proportional to
PROCESSES, and each shard is one process. 395 shards, 137 of them holding
`spec::*` tests, pays ~137 builds where one process would pay at most four. So
the objective changed with the economics:

    minimise the number of builds, subject to each shard staying inside its
    budget and the set staying resumable

and the lever is bin-packing many module keys into one shard: libtest takes
multiple positional filters, so the `--list` partition proof extends to a packed
shard unchanged. Packing is the DEFAULT; `--no-pack` restores the per-key cut.

Nothing about the three defences changes. A packed shard is still proved by
`--list` against the binary, still refuses to be GREEN unless it RAN its planned
count, and still rolls up only on a complete set. Packing chooses how many
processes to pay for; it has no vote on what is true.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import shutil
import signal
import socket
import math
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCHEMA = "clean.suite_state/v1"
PLAN_SCHEMA = "clean.suite_shard_plan/v1"

REPO_ROOT = Path(__file__).resolve().parent.parent
# VERIFY_RUNNER_STATE_DIR exists so the runner's own behaviour can be exercised
# against a throwaway artifact. Never point it at the real directory in a test:
# a synthetic GREEN written into data/suite_state/ is indistinguishable from a
# measured one to every later reader.
STATE_DIR = Path(os.environ.get("VERIFY_RUNNER_STATE_DIR", REPO_ROOT / "data" / "suite_state"))
# Shard PLANS are inventory, not evidence: a plan says how a target is cut up,
# a record says what happened when a piece of it ran. They live apart so that
# nothing walking data/suite_state/ can mistake a plan for a measurement.
PLAN_DIR = Path(os.environ.get("VERIFY_RUNNER_PLAN_DIR", REPO_ROOT / "data" / "suite_plans"))
DEFAULT_TARGET_DIR = REPO_ROOT / "target" / "verify-runner"
# Everything the runner writes lives beside the build it describes, so that
# overriding VERIFY_RUNNER_TARGET_DIR gives a fully independent runner --
# separate logs, separate pidfile, no false "a worker is already running".
_TARGET_DIR = Path(os.environ["VERIFY_RUNNER_TARGET_DIR"]).resolve() \
    if os.environ.get("VERIFY_RUNNER_TARGET_DIR") else DEFAULT_TARGET_DIR
RUN_DIR = _TARGET_DIR / "suite-runner"
LOG_DIR = RUN_DIR / "logs"
WORKER_PIDFILE = RUN_DIR / "worker.pid"
WORKER_LOG = RUN_DIR / "worker.log"
QUEUE_FILE = RUN_DIR / "queue.json"

# Statuses that can appear in a stored record.
STATUS_GREEN = "GREEN"
STATUS_RED = "RED"
STATUS_RUNNING = "RUNNING"
STATUS_ERROR = "ERROR"

# Derived buckets reported to a human.
BUCKET_GREEN = "GREEN"
BUCKET_RED = "RED"
BUCKET_UNKNOWN = "UNKNOWN"
BUCKET_RUNNING = "RUNNING"


# --------------------------------------------------------------------------
# THE MEASURED COST OF A SHARD -- every shard budget below derives from these
# --------------------------------------------------------------------------
# Re-measured on this host on 2026-08-13, AFTER `perf(verify): build each spec
# flavour once per process` (6dbe7955b). These five numbers, and nothing else,
# are what the shard floors are computed from. None is carried over from the
# pre-cache regime; the 3659s-per-test figure that produced the old 10800s
# lib-shard floor describes a program that no longer exists.
#
# ONE_FLAVOUR_BUILD_S -- on a 4-test shard run concurrently with three siblings,
#   the single process-wide build accounted for 4007.5s of the shard's 4007.62s
#   total. This is a CONTENDED measurement, so using it as the per-build term
#   is conservative in the right direction.
# SPEC_FLAVOURS -- crates/clean-verify/src/test_utils.rs holds four independent
#   `OnceLock`s (FULL, EVAL_IR, IMPL_SOUNDNESS, SUBSTITUTION). A process pays at
#   most four builds no matter how many tests it runs; that is the whole reason
#   packing works, and it is also the worst case a packed shard must survive.
# MARGINAL_PER_TEST_S -- 0.053s, the slowest of the four per-test costs measured
#   once the build is cached (range 0.017-0.053s).
# CHEAP_POPULATION_S -- 242.5s: the summed wall time of EVERY non-spec shard
#   that completed under the 395-shard cut (120 records, largest single 3.6s),
#   each figure including that shard's own `cargo test` startup. It is an upper
#   bound on what the entire non-spec population of this target costs.
# DECLARED_TESTS -- 6927, MEASURED from the binary's own `--list` at 6dbe7955b,
#   not taken on report. Reconciled by commit with no test removed anywhere in
#   the range: 9ec362dbb declared 6910 (what the 395-shard cut was verified
#   against), 9ec362dbb..25f7e30bb adds 14 `#[test]`s under crates/clean-verify/
#   src, and 6dbe7955b adds 3 more (the cache's own isolation and equivalence
#   tests). 6910 + 14 + 3 = 6927. A 6913 figure was reported alongside this
#   lane; it matches no commit in that range and does not reproduce here.
ONE_FLAVOUR_BUILD_S = 4_007.5
SPEC_FLAVOURS = 4
MARGINAL_PER_TEST_S = 0.053
CHEAP_POPULATION_S = 242.5
DECLARED_TESTS = 6_927

# A shard whose keys are classified spec-paying must survive the worst case its
# own classification admits: all four flavours built in one process with no
# overlap, plus the marginal cost of every test in the target.
#   4 x 4007.5 + 6927 x 0.053 = 16030.0 + 367.1 = 16397.1s
_SPEC_SHARD_DERIVED_S = SPEC_FLAVOURS * ONE_FLAVOUR_BUILD_S + DECLARED_TESTS * MARGINAL_PER_TEST_S

# A shard classified cheap gets 4x the measured cost of the ENTIRE non-spec
# population, plus one flavour build. That last term is not slack: the
# spec/cheap split is a source-scan HINT (see `spec_paying_roots`), so a cheap
# shard that turns out to hold one spec-building test must still be able to
# finish and report, rather than being killed and reported UNKNOWN. A shard
# needing a SECOND build is a classification error worth hearing about as a
# kill.
#   4 x 242.5 + 4007.5 = 970.0 + 4007.5 = 4977.5s
_CHEAP_SHARD_DERIVED_S = 4.0 * CHEAP_POPULATION_S + ONE_FLAVOUR_BUILD_S


# --------------------------------------------------------------------------
# per-target timeout policy
# --------------------------------------------------------------------------
# ONE flat number cannot serve this inventory. Measured on this workspace:
# `clean-verify::test::whnf_lemma_wrapper_defs` needs 1761s of spec building
# before its two tests report, while `gate::fmt` finishes in seconds. A single
# budget is therefore either absurdly short for the spec-building targets --
# 2026-08-12, a 25s budget killed that target at "running 2 tests" and recorded
# ERROR (correct behaviour for the artifact: an unfinished run is neither a pass
# nor a failure, but a useless measurement) -- or so long for the cheap ones
# that a genuinely hung target burns a day before anyone hears about it.
#
# The policy below derives each target's budget from what that target has
# actually cost here, and it is deliberately NOT "no timeout":
#
#   1. A target that completed before gets HEADROOM x its measured duration.
#      Adaptive, and it tightens as well as loosens.
#   2. A target that has never completed here gets its KIND's floor. The floors
#      encode the shape of this inventory, not a guess at any one target.
#   3. A target whose last run was KILLED by the timeout gets DOUBLE the budget
#      that killed it. A kill is evidence the budget was too small, so it
#      escalates -- but geometrically and from a recorded number, not by being
#      switched off.
#   4. Everything is clamped to HARD_CEILING. There is no unlimited setting.
#      A target that cannot finish in a day is a defect to report, not a budget
#      to raise.
#
# Every record carries `timeout_basis` alongside `timeout_s`, so the number in
# an artifact can always be explained without re-deriving it.
TIMEOUT_HEADROOM = 4.0
TIMEOUT_HARD_CEILING = 86_400          # 24h. Never exceeded, never disabled.
TIMEOUT_FLOOR_BY_KIND = {
    # Workspace-wide check/clippy/fmt over 27 crates and 521 targets.
    "gate": 3_600,
    # The clean-verify integration targets. These are the SPEC-BUILDING ones:
    # several routinely sit in the 2000-2500s range before their first test
    # line, which is what the 25s budget ran into.
    "test": 7_200,
    # The known multi-hour target: thousands of declared tests in one binary.
    "lib": 43_200,
    # One packed slice of a sharded lib target that the source scan says holds
    # NO spec-building test. Derived just above:
    #   4 x 242.5s (every non-spec shard measured under the old cut) + 4007.5s
    #   (one flavour build, the cost of a classification miss) = 4977.5s,
    # rounded up to the next half hour.
    #
    # RETIRED, and deliberately not carried forward: the previous 10800s figure
    # was derived from a 3659s single-test measurement of `Specification::new()`
    # rebuilt per test. The spec cache deleted that cost function; re-using its
    # number would be quoting a retired program.
    "lib-shard": 5_400,
    # One packed slice whose keys are classified spec-paying. Derived just
    # above: 4 x 4007.5s + 6927 x 0.053s = 16397.1s, rounded up to the next
    # whole hour.
    #
    # Concurrency is NOT covered by this number -- three spec shards at once on
    # this host measured ~385% CPU each rather than 1800%. Under the cache there
    # is normally only one spec-paying shard, so that is an argument for keeping
    # it that way rather than for a larger number here.
    #
    # This is a floor for a target that has never run, not a limit raised to
    # make something pass: once a shard completes, its budget comes from its own
    # measured duration, and a shard that blows this budget is KILLED and
    # reported UNKNOWN exactly like any other.
    "lib-shard-spec": 18_000,
}
TIMEOUT_FLOOR_DEFAULT = 3_600

# A roll-up target executes nothing; it is a reading of its shards' records.
KIND_ROLLUP = "lib-rollup"
KIND_SHARD = "lib-shard"
KIND_SHARD_SPEC = "lib-shard-spec"
# Separates a parent target id from the shard key inside a shard target id.
SHARD_SEP = "::shard::"


def _record_was_killed(record: dict[str, Any]) -> bool:
    """Did this record come from a run the runner killed on its own timeout?

    `timed_out` is authoritative; the string sniff exists only for records
    written before that field did, and it must stay narrow enough that a test
    which legitimately prints the phrase cannot be mistaken for one.
    """
    if record.get("timed_out") is not None:
        return bool(record["timed_out"])
    return record.get("status") == STATUS_ERROR and str(
        record.get("final_line") or ""
    ).startswith("<timed out after ")


def timeout_for(
    entry: dict[str, Any],
    record: dict[str, Any] | None,
    override: int | None = None,
) -> tuple[int, str]:
    """(budget in seconds, one-line basis). See the policy note above."""
    if override is not None:
        return max(1, int(override)), f"explicit --timeout {int(override)}s override of the policy"

    kind = entry.get("kind", "")
    floor = TIMEOUT_FLOOR_BY_KIND.get(kind, TIMEOUT_FLOOR_DEFAULT)

    if record and record.get("source") == "measured":
        if _record_was_killed(record) and record.get("timeout_s"):
            prev = int(record["timeout_s"])
            budget = min(max(prev * 2, floor), TIMEOUT_HARD_CEILING)
            return budget, f"previous run was KILLED at {prev}s; doubled, floored at the {kind} floor {floor}s"
        duration = record.get("duration_s")
        if record.get("status") in (STATUS_GREEN, STATUS_RED) and isinstance(duration, (int, float)):
            scaled = int(duration * TIMEOUT_HEADROOM) + 1
            budget = min(max(scaled, floor), TIMEOUT_HARD_CEILING)
            return budget, (
                f"{TIMEOUT_HEADROOM:g}x the {duration:.1f}s this target last took here, "
                f"floored at the {kind} floor {floor}s"
            )

    return min(floor, TIMEOUT_HARD_CEILING), f"never completed here; {kind or 'default'} floor"


# --------------------------------------------------------------------------
# small helpers
# --------------------------------------------------------------------------


def now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run_capture(argv: list[str], cwd: Path | None = None, timeout: int | None = None) -> tuple[int, str]:
    proc = subprocess.run(
        argv,
        cwd=str(cwd or REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=timeout,
        check=False,
    )
    return proc.returncode, proc.stdout


def git_head() -> str:
    code, out = run_capture(["git", "rev-parse", "HEAD"])
    return out.strip() if code == 0 else "unknown"


def git_tree_dirty() -> bool:
    code, out = run_capture(["git", "status", "--porcelain"])
    return bool(out.strip()) if code == 0 else True


def target_dir() -> Path:
    return _TARGET_DIR


def safe_name(target_id: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", target_id)


def pid_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


# --------------------------------------------------------------------------
# inventory
# --------------------------------------------------------------------------


def cargo_metadata() -> dict[str, Any]:
    code, out = run_capture(
        ["cargo", "metadata", "--locked", "--format-version", "1", "--no-deps"],
        timeout=600,
    )
    if code != 0:
        raise SystemExit(f"cargo metadata failed:\n{out}")
    return json.loads(out)


def path_dep_closure(meta: dict[str, Any], package: str) -> list[Path]:
    """Directories of `package` plus every workspace path-dependency it reaches.

    Dev-dependencies are included: they are compiled into the test binaries and
    a change in one genuinely invalidates a stored result.
    """
    by_name = {p["name"]: p for p in meta["packages"]}
    seen: set[str] = set()
    stack = [package]
    dirs: list[Path] = []
    while stack:
        name = stack.pop()
        if name in seen or name not in by_name:
            continue
        seen.add(name)
        pkg = by_name[name]
        dirs.append(Path(pkg["manifest_path"]).parent)
        for dep in pkg.get("dependencies", []):
            dep_name = dep.get("name")
            # Only workspace-local packages matter; registry deps are pinned by
            # Cargo.lock, which is hashed separately.
            if dep_name in by_name:
                stack.append(dep_name)
    return sorted(set(dirs))


def package_targets(meta: dict[str, Any], package: str) -> list[dict[str, Any]]:
    """Enumerate the runnable test targets of a package, from cargo itself.

    A lib target with a stored shard plan is replaced by its shards plus a
    non-executing roll-up under the original id, so that every reader of
    `clean-verify::lib` keeps asking the same question and gets an answer that
    is now derived from the pieces rather than from one unfinishable run.
    """
    pkg = next((p for p in meta["packages"] if p["name"] == package), None)
    if pkg is None:
        raise SystemExit(f"package not found in workspace metadata: {package}")
    out: list[dict[str, Any]] = []
    for tgt in pkg["targets"]:
        kinds = tgt.get("kind", [])
        if "lib" in kinds and tgt.get("test", True):
            base = ["cargo", "test", "--locked", "-p", package, "--lib"]
            plan = load_plan(f"{package}::lib")
            if plan:
                out.extend(shard_entries(plan))
                out.append(
                    {
                        "id": f"{package}::lib",
                        "package": package,
                        "kind": KIND_ROLLUP,
                        "argv": base,
                        "_plan": plan,
                    }
                )
            else:
                out.append(
                    {
                        "id": f"{package}::lib",
                        "package": package,
                        "kind": "lib",
                        "argv": base,
                    }
                )
        elif "test" in kinds:
            out.append(
                {
                    "id": f"{package}::test::{tgt['name']}",
                    "package": package,
                    "kind": "test",
                    "argv": [
                        "cargo",
                        "test",
                        "--locked",
                        "-p",
                        package,
                        "--test",
                        tgt["name"],
                    ],
                }
            )
    return sorted(out, key=lambda t: t["id"])


# The workspace gates, spelled exactly as CLAUDE.md's "Before pushing --
# the real gate" spells them. `--workspace --all-targets` is load-bearing:
# `default-members` narrows a bare `cargo check`/`clippy` to 8 of 27 crates and
# 85 of 521 targets, so the bare forms are an inner loop, never a coverage claim.
WORKSPACE_GATES = [
    {
        "id": "gate::check",
        "package": "__workspace__",
        "kind": "gate",
        "argv": ["cargo", "check", "--locked", "--workspace", "--all-targets"],
    },
    # `scripts/rust_frontend.sh` rather than a bare `cargo`, and ONLY for these
    # two: `rust-toolchain.toml` pins `channel = "trust"`, whose stage2 ships
    # the lint and format frontends as `targo-tippy` / `targo-fmt`. Cargo
    # resolves `cargo <sub>` by looking for a `cargo-<sub>` sibling, so on this
    # toolchain BOTH gates died before running a single unit -- measured at
    # fa691b5a9, 2026-08-20: `error: 'cargo-clippy' is not installed for the
    # custom toolchain 'trust'`. `cargo check` needs no such help; it is a
    # built-in subcommand, which is why gate::check is spelled plainly.
    #
    # The resolver changes the DRIVER, never the check: the flags below are the
    # same `--workspace --all-targets ... -D warnings` the pre-push gate has
    # always run, and on an upstream toolchain the resolver execs `cargo <sub>`
    # unchanged.
    {
        "id": "gate::clippy",
        "package": "__workspace__",
        "kind": "gate",
        "argv": ["scripts/rust_frontend.sh", "clippy", "--locked", "--workspace", "--all-targets", "--", "-D", "warnings"],
        "_extra_paths": ["scripts/rust_frontend.sh"],
    },
    {
        "id": "gate::fmt",
        "package": "__workspace__",
        "kind": "gate",
        "argv": ["scripts/rust_frontend.sh", "fmt", "--all", "--check"],
        "_extra_paths": ["scripts/rust_frontend.sh"],
    },
    # The paragon quality ratchet, added 2026-08-17 because NOTHING ROUTINE RAN
    # IT. It is a leg of `scripts/local_gate.sh` (both modes -- it sits above
    # the `if [[ $FAST -eq 0 ]]` block, so `--fast` runs it too), and
    # `scripts/hooks/pre-push` runs `local_gate.sh --fast`. But that hook is
    # installed only by `just install-hooks` setting `core.hooksPath`, and on
    # the box that produced the 2026-08-16 suite pass it was not installed:
    # `core.hooksPath` still pointed at `.git/hooks`, which holds nothing but
    # git's `.sample` files. So the only thing that ran routinely was this
    # runner, and this ratchet was not one of its rows. `files_over_500` grew
    # 1410 -> 1416 across four commits behind honestly-green lane gates, and
    # the growth was found by a human reading a report rather than by a gate.
    #
    # It belongs here rather than anywhere else for the reason the other three
    # do: this runner is what actually runs, it records to data/suite_state/,
    # and `status --gate` exits non-zero on a RED row. Cost is ~27 s of file
    # I/O and NO BUILD AT ALL (measured on an 18-core box, nine runs across two
    # load levels, 24.5-29.8 s; the row this runner recorded itself came in at
    # 25.7 s). The suite's next-cheapest row is minutes and its four heavy
    # clean-verify rows are 47-63 min each, so there is no argument for making
    # this one non-blocking.
    {
        "id": "gate::paragon",
        "package": "__workspace__",
        "kind": "gate",
        "argv": ["scripts/paragon_ratchet.sh"],
        # The ratchet MEASURES crates/ (covered by the workspace dirs) but
        # DECIDES against data/paragon_ratchet.json, using the heuristics in
        # scripts/paragon_ratchet.sh. Neither of those is inside a crate dir,
        # so without this a baseline edit or a heuristic edit would leave a
        # recorded green reading fresh -- the precise failure mode
        # `_dir_content_digest` exists to prevent.
        "_extra_paths": ["data/paragon_ratchet.json", "scripts/paragon_ratchet.sh"],
    },
]


# A PACKAGE TARGET whose verdict depends on files outside every crate dir.
#
# Same mechanism as `WORKSPACE_GATES`' `_extra_paths`, which until now only
# existed for gates. `crystal_a1_lineage` needs it because its `freshness` module
# decides against the committed result of the only check that compares a chain
# fixture to a LIVE trustc dump -- a `data/` record and a `scripts/` comparator,
# neither of which is inside any crate directory. `freshness.rs` names that gap
# in its own module doc; this closes it, so editing a record or the script
# DEMOTES the recorded green to UNKNOWN instead of leaving it reading fresh.
#
# It does not schedule the trustc run itself -- nothing in this suite can, the
# comparison needs the Trust compiler -- and that remains a manual duty.
TARGET_EXTRA_PATHS: dict[str, list[str]] = {
    # `crystal_a1_lineage` reaches OUTSIDE every crate directory at run time: its
    # freshness lanes read committed revalidation records, the head-measurement
    # record a head-measured chain names, and the freshness-scope pin. Every one of
    # those is an INPUT to the verdict, so every one has to be in the digest or
    # the row's GREEN survives an edit to the evidence it read.
    #
    # The three 2026-08-19 records were added on discovery (141f2662b, "the record
    # inside the input digest"). The 2026-08-20 lane-13 record and the scope files
    # landed afterwards and were NOT added -- measured 2026-08-20 by lane V, by
    # enumerating this entry's digest pathspecs: all three read NOT COVERED, so a
    # green `crystal_a1_lineage` stood while
    # `data/crystal_fixture_freshness_2026-08-20_lane13.json` -- the ONLY live-dump
    # record backing chains 11-14, and the file `freshness_head.rs` reads -- could
    # be edited underneath it. Same class as the hole
    # `crystal_fixture_freshness.py` exists to close, one level up in the
    # bookkeeping. `data/crystal_chain_verification_2026-08-20_laneV.json`, D3.
    #
    # Adding a path MOVES the digest, so the row correctly demotes to UNKNOWN once
    # and is re-measured. That is the intended cost.
    "clean-verify::test::crystal_a1_lineage": [
        "data/crystal_chain_revalidation_2026-08-19.json",
        "data/crystal_chain_revalidation_2026-08-19_ccf52b40c3.json",
        "data/crystal_chain_revalidation_2026-08-19_28fb5dd812.json",
        "data/crystal_chain_revalidation_2026-08-20_8ea683678.json",
        "data/crystal_chain_revalidation_2026-08-20_a152ab39e.json",
        "data/crystal_fixture_rebaseline_2026-08-20_a152ab39e.json",
        "data/crystal_fixture_rebaseline_bindings_2026-08-20_a152ab39e.json",
        "crates/clean-verify/src/spec/core_spec/generated/ir_lz.a152.prov.json",
        "data/crystal_chain_revalidation_2026-08-21_b03937e74.json",
        "data/crystal_fixture_rebaseline_2026-08-21_b03937e74.json",
        "data/crystal_fixture_rebaseline_bindings_2026-08-21_b03937e74.json",
        "crates/clean-verify/src/spec/core_spec/generated/ir_lz.b039.prov.json",
        "data/crystal_fixture_freshness_2026-08-20_lane13.json",
        "data/crystal_freshness_scope.json",
        "scripts/crystal_chain_revalidation.py",
        "scripts/crystal_fixture_freshness.py",
        "scripts/crystal_fixture_rebaseline.py",
        "scripts/crystal_freshness_scope.py",
        "scripts/trust_ir_build.sh",
    ],
}


def build_inventory(packages: list[str], with_gates: bool = True) -> list[dict[str, Any]]:
    meta = cargo_metadata()
    inv: list[dict[str, Any]] = []
    if with_gates:
        inv.extend(WORKSPACE_GATES)
    for package in packages:
        inv.extend(package_targets(meta, package))
    # attach the digest scope directories
    ws_dirs = sorted({Path(p["manifest_path"]).parent for p in meta["packages"]})
    for entry in inv:
        if entry["package"] == "__workspace__":
            entry["_dirs"] = ws_dirs
        else:
            entry["_dirs"] = path_dep_closure(meta, entry["package"])
        # A gate whose verdict depends on files outside every crate dir declares
        # them here; `_dir_content_digest` accepts file pathspecs as readily as
        # directories, so they widen the scope rather than replacing it. Read
        # non-destructively: `_dirs` is rebuilt on every call, but the entry
        # dicts are the module-level ones, so popping the key would silently
        # narrow the digest on the second call.
        extra = tuple(entry.get("_extra_paths") or ()) + tuple(
            TARGET_EXTRA_PATHS.get(entry["id"], ())
        )
        if extra:
            entry["_dirs"] = list(entry["_dirs"]) + [REPO_ROOT / p for p in extra]
    return inv


# --------------------------------------------------------------------------
# sharding
# --------------------------------------------------------------------------
#
# THE KEY, AND WHY IT PARTITIONS
# ------------------------------
# Every Rust test has a name of the form `mod1::mod2::...::modk::test_fn` with
# k >= 0. `shard_key` walks that name from the left and stops at the first
# module prefix that is NOT marked for splitting, never consuming the final
# component (the function name itself). It is a *function* of the name alone:
# total (every name yields exactly one key) and deterministic (no ordering, no
# counters, no state). Tests therefore fall into the equivalence classes of that
# function, and equivalence classes of a total function on a set ARE a partition
# of it. One shard per class, so no test can land in two shards or in none.
#
# The split set is derived mechanically, not curated: deepen any key holding
# more than `max_tests` tests, as long as some test under it has another module
# level to descend into, and repeat to fixpoint. A key that cannot be deepened
# stays oversized and is reported as such rather than being quietly dropped.
#
# WHY THE KEY ALONE IS NOT THE PROOF
# ----------------------------------
# The key partitions test NAMES. What actually decides which tests a shard runs
# is libtest's SUBSTRING filter, which is a different function -- `eval_ir::`
# matches `spec::core_spec::eval_ir::x` as happily as `eval_ir::x`. So the key
# is only the intent; `verify_partition` measures the realisation by asking the
# test binary itself, with `--list`, exactly which tests each shard's argv
# selects, and compares the observed sets. A plan is written only if the
# observed sets are pairwise disjoint and their union is every declared test.

SHARD_MAX_TESTS_DEFAULT = 100


def shard_key(name: str, splits: set[str]) -> str:
    """The shard a test name belongs to. Total, deterministic, name-only."""
    parts = name.split("::")
    if len(parts) == 1:
        # A test at the crate root has no module path; it is its own class.
        return parts[0]
    key = parts[0]
    index = 1
    while key in splits and index < len(parts) - 1:
        key = f"{key}::{parts[index]}"
        index += 1
    return key


def derive_splits(names: list[str], max_tests: int) -> set[str]:
    """Smallest fixpoint split set that keeps every *divisible* key under the cap."""
    splits: set[str] = set()
    while True:
        buckets: dict[str, list[str]] = {}
        for name in names:
            buckets.setdefault(shard_key(name, splits), []).append(name)
        grew = False
        for key, members in buckets.items():
            if len(members) <= max_tests or key in splits:
                continue
            depth = len(key.split("::"))
            # Divisible only if some member still has a module level below `key`.
            if any(len(m.split("::")) - 1 > depth for m in members):
                splits.add(key)
                grew = True
        if not grew:
            return splits


def shard_filters(key: str, keys: list[str]) -> tuple[list[str], list[str]]:
    """(include filters, --skip filters) realising `key` under substring matching.

    The include filter is the key's module prefix. Skips exist for the one case
    the key function permits: a test sitting directly in a module that was split
    (`a::b::t` where `a::b` is a split prefix) keys on `a::b`, which is a strict
    prefix of the sibling keys `a::b::c`. Without the skips those siblings'
    tests would be swept into this shard as well as their own.
    """
    include = f"{key}::"
    skips = sorted(f"{other}::" for other in keys if other != key and other.startswith(include))
    return [include], skips


def shard_realisation(
    key: str, keys: list[str], intended: set[str], declared: list[str]
) -> tuple[str, list[str], list[str]]:
    """(mode, filters, skips) that make libtest select EXACTLY `intended`.

    A module prefix is the natural filter and the readable one, but libtest
    matches substrings with no anchor, so a prefix is only correct when nothing
    else in the target contains it. Measured here: the key `tests` (five tests at
    the crate root) has the prefix `tests::`, which selects 3501 of the 6900
    tests in this binary, and `proofs::` sweeps in `nn_verify::ibp_crown::
    crown_proofs::tests::*`. Three keys overreached that way, double-counting
    3600 tests.

    So the prefix is used only where it is *checked* to select exactly the
    intended set, and every remaining key falls back to `--exact` with its
    members named individually -- verbose in the argv, but exact by construction
    and immune to any future name that happens to embed the prefix. Both modes
    are then re-verified against the binary by `verify_partition`; this function
    chooses, it does not certify.
    """
    filters, skips = shard_filters(key, keys)
    include = filters[0]
    selected = {
        test
        for test in declared
        if include in test and not any(skip in test for skip in skips)
    }
    if selected == intended:
        return "prefix", filters, skips
    return "exact", sorted(intended), []


# --------------------------------------------------------------------------
# PACKING -- many keys into one shard, because cost is per PROCESS now
# --------------------------------------------------------------------------
#
# See the module docstring. A packed shard is a set of module keys run by ONE
# `cargo test` invocation, which is one process, which pays each specification
# flavour's build at most once. The packing decides how many processes the suite
# buys; the `--list` partition proof still decides what is true.

PACK_MAX_TESTS_DEFAULT = 1_500
PACK_GROUP_MIN_TESTS_DEFAULT = 100

# An `--exact` bin names every one of its tests in argv. macOS caps arguments
# plus environment at 1 MiB; 200 KiB of names stays an order of magnitude clear
# of that, and a bin that cannot fit is split rather than truncated.
EXACT_ARGV_BUDGET_BYTES = 200_000

# The calls that make a test pay a specification build. Kept as literal source
# fragments because that is what the scan can actually check.
SPEC_BUILDER_CALLS = (
    "build_spec_with_stack",
    "shared_spec()",
    "build_eval_ir_spec_with_stack",
    "build_implementation_soundness_spec_with_stack",
    "build_substitution_spec_with_stack",
)


def spec_paying_roots(src_dir: Path) -> tuple[set[str], list[str]]:
    """Top-level module names under `src_dir` whose sources build a specification.

    A COST HINT AND NOTHING MORE. Getting this wrong cannot make the cut wrong:
    a spec-building test misfiled into a cheap shard makes that shard pay one
    build (which its floor covers, and which shows up in its log as
    `[clean-verify test_utils] ...: one process-wide build took Ns`), and a
    cheap test filed into the spec shard costs 0.053s. Coverage and disjointness
    are decided by `verify_partition` against the binary, never by this scan.

    Returns (roots, evidence-paths). `lib.rs` maps to the crate-root key
    `tests`, because the crate root's own `mod tests` is what the tests named
    `tests::*` live in.
    """
    roots: set[str] = set()
    evidence: list[str] = []
    if not src_dir.is_dir():
        return roots, evidence
    for path in sorted(src_dir.rglob("*.rs")):
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        if not any(call in text for call in SPEC_BUILDER_CALLS):
            continue
        rel = path.relative_to(src_dir)
        evidence.append(str(rel))
        head = rel.parts[0]
        roots.add("tests" if head == "lib.rs" else head[:-3] if head.endswith(".rs") else head)
    return roots, evidence


def pack_group_of(key: str, root_sizes: dict[str, int], spec_roots: set[str],
                  group_min_tests: int) -> str:
    """Which packing group a key belongs to.

    Three groups only, and each exists for a cost reason:

      * `spec_paying`  -- keys whose root builds a specification. Putting all of
        them in one group is the entire point: they then share one process, so
        the suite pays the flavour builds ONCE instead of once per shard.
      * `<root>`       -- a root big enough to be worth its own resumable unit.
        Keeping them apart costs nothing (they build no specification) and buys
        a failure in one subtree that does not hide another subtree's result.
      * `misc`         -- every remaining small root, swept together so the tail
        does not become dozens of processes for a few seconds of work each.
    """
    root = key.split("::")[0]
    if root in spec_roots:
        return "spec_paying"
    if root_sizes.get(root, 0) >= group_min_tests:
        return root
    return "misc"


def pack_bins(buckets: dict[str, list[str]], groups: dict[str, str],
              max_tests: int) -> list[dict[str, Any]]:
    """Greedily pack each group's keys, in name order, into bins of <= max_tests.

    Name order rather than first-fit-decreasing: the bins come out as contiguous
    runs of the module namespace, so a bin's name range describes its contents
    and a human can predict which bin a test is in. Packing tighter would save
    nothing -- the cost of a bin is its process, not its test count.

    A single key larger than the cap becomes its own bin. It is already
    indivisible at this level; the cap is a packing limit, not a claim.
    """
    by_group: dict[str, list[str]] = {}
    for key in sorted(buckets):
        by_group.setdefault(groups[key], []).append(key)

    raw: list[tuple[str, list[str]]] = []
    for group in sorted(by_group):
        current: list[str] = []
        count = 0
        for key in by_group[group]:
            size = len(buckets[key])
            if current and count + size > max_tests:
                raw.append((group, current))
                current, count = [], 0
            current.append(key)
            count += size
        if current:
            raw.append((group, current))

    totals: dict[str, int] = {}
    for group, _ in raw:
        totals[group] = totals.get(group, 0) + 1
    seq: dict[str, int] = {}
    bins: list[dict[str, Any]] = []
    for group, keys in raw:
        seq[group] = seq.get(group, 0) + 1
        name = group if totals[group] == 1 else f"{group}_{seq[group]:02d}"
        bins.append({"key": name, "group": group, "keys": keys})
    return bins


def libtest_select(declared: list[str], filters: list[str], skips: list[str],
                   exact: bool = False) -> set[str]:
    """What libtest's own filtering would select, reproduced here.

    libtest keeps a test when it matches SOME positional filter and NO `--skip`
    filter, matching by substring unless `--exact` is given (see `filter_tests`
    in libtest). Skips are applied after includes, so a skip beats an include.
    This mirror is what lets a candidate realisation be rejected before the
    binary is asked; the binary still has the last word in `verify_partition`.
    """
    if exact:
        wanted = set(filters)
        selected = {name for name in declared if name in wanted}
    else:
        selected = {name for name in declared if any(f in name for f in filters)}
    return {name for name in selected if not any(s in name for s in skips)}


def bin_realisation(
    keys: list[str], all_keys: list[str], intended: set[str], declared: list[str]
) -> tuple[str, list[str], list[str]] | None:
    """(mode, filters, skips) making libtest select EXACTLY a bin's tests.

    The include filters are the members' own module prefixes. The skip set is
    the union of the members' individual skips MINUS any skip that is itself a
    member's include: those exist to fence a key off from a deeper sibling, and
    when the sibling has been packed into the same bin the fence must come down
    or the bin would exclude its own members.

    Returns None when neither a prefix nor an `--exact` realisation works, which
    is the caller's signal to split the bin rather than ship an unproved one.
    """
    includes = sorted({f"{key}::" for key in keys})
    member_includes = set(includes)
    skips = sorted(
        {skip for key in keys for skip in shard_filters(key, all_keys)[1]} - member_includes
    )
    if libtest_select(declared, includes, skips) == intended:
        return "prefix", includes, skips

    names = sorted(intended)
    if sum(len(name) + 1 for name in names) <= EXACT_ARGV_BUDGET_BYTES:
        if libtest_select(declared, names, [], exact=True) == intended:
            return "exact", names, []
    return None


def shard_binary_args(shard: dict[str, Any]) -> list[str]:
    """The arguments handed to the test binary for one shard."""
    args = ["--exact"] if shard.get("mode") == "exact" else []
    args += list(shard["filters"])
    for skip in shard.get("skip", []):
        args += ["--skip", skip]
    return args


def shard_target_id(parent: str, key: str) -> str:
    return f"{parent}{SHARD_SEP}{key}"


def shard_entries(plan: dict[str, Any], dirs: list[Path] | None = None) -> list[dict[str, Any]]:
    """Inventory entries for a stored plan's shards.

    `dirs` is the digest scope, normally attached by `build_inventory`. It is
    threaded through here as well so a roll-up can derive a shard's row without
    a second trip through the inventory.
    """
    out = []
    for shard in plan["shards"]:
        argv = list(plan["base_argv"]) + ["--"] + shard_binary_args(shard)
        entry = {
            "id": shard["id"],
            "package": plan["package"],
            # A packed shard carries its own kind, because a spec-paying shard
            # and a cheap one have budgets an order of magnitude apart. Plans
            # written before packing have no `kind` and are all `lib-shard`.
            "kind": shard.get("kind", KIND_SHARD),
            "argv": argv,
            "_shard": shard,
            "_parent": plan["parent"],
        }
        if dirs is not None:
            entry["_dirs"] = dirs
        out.append(entry)
    return out


def plan_path(parent_id: str) -> Path:
    return PLAN_DIR / f"{safe_name(parent_id)}.json"


def repo_relative(path: Path) -> str:
    """Repo-relative when it can be, absolute otherwise.

    In pinned mode `REPO_ROOT` is the throwaway worktree while the state and
    plan directories point back at the real repo, so several paths recorded in
    an artifact are genuinely outside the tree the runner is executing from.
    `Path.relative_to` raises there; recording the absolute path is right.
    """
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def load_plan(parent_id: str) -> dict[str, Any] | None:
    path = plan_path(parent_id)
    if not path.exists():
        return None
    try:
        plan = json.loads(path.read_text())
    except json.JSONDecodeError:
        return None
    return plan if plan.get("schema") == PLAN_SCHEMA else None


_LIST_RE = re.compile(r"^(\S+): test$")


def parse_list_output(text: str) -> list[str]:
    return sorted(m.group(1) for m in (_LIST_RE.match(line) for line in text.splitlines()) if m)


def test_binary_for(package: str) -> Path:
    """Build the package's lib test binary and return its path, from cargo's JSON.

    `--no-run` still compiles; on a cold target directory this is the expensive
    part of planning. The path comes from cargo rather than a glob so it cannot
    silently pick up a stale binary from an earlier build.
    """
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = str(target_dir())
    env.setdefault("CARGO_TERM_COLOR", "never")
    proc = subprocess.run(
        ["cargo", "test", "--locked", "-p", package, "--lib", "--no-run", "--message-format=json"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        check=False,
    )
    if proc.returncode != 0:
        raise SystemExit(f"cargo test --no-run failed for {package}:\n{proc.stderr[-4000:]}")
    executables = []
    for line in proc.stdout.splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("reason") != "compiler-artifact" or not msg.get("executable"):
            continue
        target = msg.get("target", {})
        if target.get("name") == package.replace("-", "_") and "lib" in target.get("kind", []):
            executables.append(Path(msg["executable"]))
    if len(executables) != 1:
        raise SystemExit(
            f"expected exactly one lib test binary for {package}, cargo reported {len(executables)}: "
            f"{executables}. Refusing to plan shards against an ambiguous binary."
        )
    return executables[0]


def list_tests(binary: Path, args: list[str] | None = None) -> list[str]:
    code, out = run_capture([str(binary), "--list"] + (args or []), timeout=600)
    if code != 0:
        raise SystemExit(f"{binary.name} --list failed (exit {code}):\n{out[-4000:]}")
    return parse_list_output(out)


def verify_partition(
    binary: Path, shards: list[dict[str, Any]], declared: list[str]
) -> dict[str, Any]:
    """Ask libtest which tests each shard's argv really selects, and check it.

    Returns the proof. `verified` is true only when the observed sets are
    pairwise disjoint, cover every declared test, and sum to the declared total.
    """
    declared_set = set(declared)
    seen: dict[str, str] = {}
    duplicated: list[str] = []
    observed_total = 0
    mismatched: list[dict[str, Any]] = []

    for shard in shards:
        observed = list_tests(binary, shard_binary_args(shard))
        shard["observed_count"] = len(observed)
        shard["names_sha256"] = hashlib.sha256("\n".join(observed).encode()).hexdigest()
        observed_total += len(observed)
        if len(observed) != shard["test_count"] or set(observed) != set(shard["_intended"]):
            mismatched.append(
                {
                    "shard": shard["id"],
                    "intended": shard["test_count"],
                    "observed": len(observed),
                    "only_intended": sorted(set(shard["_intended"]) - set(observed))[:5],
                    "only_observed": sorted(set(observed) - set(shard["_intended"]))[:5],
                }
            )
        for name in observed:
            if name in seen:
                duplicated.append(f"{name} in {seen[name]} and {shard['id']}")
            seen[name] = shard["id"]

    dropped = sorted(declared_set - set(seen))
    alien = sorted(set(seen) - declared_set)
    return {
        "method": (
            "each shard's exact argv replayed through the test binary's own --list, "
            "then the observed name sets compared for coverage and disjointness"
        ),
        "declared_total": len(declared),
        "sum_of_shard_counts": observed_total,
        "union_size": len(seen),
        "dropped_count": len(dropped),
        "dropped_examples": dropped[:10],
        "duplicated_count": len(duplicated),
        "duplicated_examples": duplicated[:10],
        "alien_count": len(alien),
        "alien_examples": alien[:10],
        "mismatched_shards": mismatched[:10],
        "mismatched_shard_count": len(mismatched),
        "shards_verified": len(shards),
        "all_names_sha256": hashlib.sha256("\n".join(sorted(declared)).encode()).hexdigest(),
        "verified": (
            not dropped
            and not duplicated
            and not alien
            and not mismatched
            and observed_total == len(declared)
            and len(seen) == len(declared)
        ),
    }


# --------------------------------------------------------------------------
# input digest
# --------------------------------------------------------------------------

_TOOLCHAIN_CACHE: str | None = None


def toolchain_id() -> str:
    global _TOOLCHAIN_CACHE
    if _TOOLCHAIN_CACHE is None:
        code, out = run_capture(["rustc", "-vV"])
        keep = [
            line
            for line in out.splitlines()
            if line.startswith(("rustc ", "commit-hash:", "host:", "release:"))
        ]
        _TOOLCHAIN_CACHE = "|".join(keep) if code == 0 else "rustc-unavailable"
    return _TOOLCHAIN_CACHE


_DIGEST_CACHE: dict[tuple[str, ...], str] = {}


def _dir_content_digest(dirs: list[Path], fresh: bool = False) -> str:
    """SHA-256 over the working-tree content of every git-visible file in `dirs`.

    "git-visible" = tracked (`-c`) plus untracked-but-not-ignored (`-o
    --exclude-standard`). Ignored build output is excluded, which is what makes
    this stable across builds.

    `fresh=True` bypasses the memo. Read-only commands want the memo -- it gives
    every row of one `status` table a single consistent snapshot of a tree that
    other lanes are editing underneath us. A run about to be recorded wants the
    truth at that instant instead.
    """
    key = tuple(str(d) for d in dirs)
    if not fresh and key in _DIGEST_CACHE:
        return _DIGEST_CACHE[key]

    rel = []
    for d in dirs:
        try:
            rel.append(str(d.relative_to(REPO_ROOT)))
        except ValueError:
            # A path dependency outside the repo cannot be hashed by this git
            # enumeration. Fail loudly rather than silently narrowing the digest
            # scope -- a digest that quietly stops covering an input is worse
            # than no digest, because it makes stale greens look fresh.
            raise SystemExit(
                f"path dependency outside the repository is not covered by the input "
                f"digest: {d}. Refusing to record results whose freshness cannot be decided."
            ) from None
    code, out = run_capture(
        ["git", "ls-files", "-c", "-o", "--exclude-standard", "-z", "--"] + rel,
        timeout=600,
    )
    if code != 0:
        raise SystemExit(f"git ls-files failed:\n{out}")
    files = sorted(f for f in out.split("\0") if f)

    # Hash working-tree content (not the index) so uncommitted edits count.
    hasher = hashlib.sha256()
    proc = subprocess.Popen(
        ["git", "hash-object", "--stdin-paths"],
        cwd=str(REPO_ROOT),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    stdout, stderr = proc.communicate("\n".join(files) + "\n" if files else "")
    if proc.returncode != 0:
        raise SystemExit(f"git hash-object failed:\n{stderr}")
    blobs = stdout.split()
    if len(blobs) != len(files):
        raise SystemExit(
            f"digest mismatch: {len(files)} paths but {len(blobs)} hashes returned"
        )
    for path, blob in zip(files, blobs):
        hasher.update(path.encode())
        hasher.update(b"\0")
        hasher.update(blob.encode())
        hasher.update(b"\n")
    digest = hasher.hexdigest()
    if not fresh:
        # A fresh read must not poison the shared memo: worker threads compute
        # digests concurrently, and one thread's instant-in-time answer is not a
        # valid snapshot for another's.
        _DIGEST_CACHE[key] = digest
    return digest


def input_digest(entry: dict[str, Any], fresh: bool = False) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"schema=" + SCHEMA.encode() + b"\n")
    hasher.update(b"sources=" + _dir_content_digest(entry["_dirs"], fresh).encode() + b"\n")
    for extra in ("Cargo.toml", "Cargo.lock"):
        path = REPO_ROOT / extra
        blob = hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else "absent"
        hasher.update(f"{extra}={blob}\n".encode())
    hasher.update(b"toolchain=" + toolchain_id().encode() + b"\n")
    hasher.update(b"argv=" + " ".join(entry["argv"]).encode() + b"\n")
    return "sha256:" + hasher.hexdigest()


# --------------------------------------------------------------------------
# records
# --------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Memory admission. WHY: this runner's concurrency unit was TARGETS, but the
# binding resource is MEMORY, and targets range from ~50 MB to 8.8 GB (a
# clean-verify spec binary, measured). `--jobs 8` could therefore mean 70 GB or
# 400 MB with no way to tell in advance. On 2026-08-19 that, combined with
# concurrent driver builds from other lanes, exhausted the macOS compressor's
# SEGMENT table (100% segments, pages only 44%) and the kernel watchdog panicked
# the machine -- see reports/kernel-panic-rca-2026-08-19.md.
#
# So each target now acquires GB from the machine-wide gate before it runs, and
# MEASURES its own peak RSS while running. The measurement is written to the
# record, so the next run of that target admits at its true cost: the runner
# tunes its own weights instead of trusting a hand-written table.
HEAVY_GATE = REPO_ROOT / "scripts" / "heavy_gate.sh"
DEFAULT_TARGET_GB = 12                 # unmeasured target: above the 8.8 GB spec binary
MIN_TARGET_GB = 1


def _peak_rss_gb(pgid: int, stop: threading.Event) -> float:
    """Poll the child's whole process group and keep the maximum total RSS.

    Polling rather than getrusage: cargo spawns rustc and the test binary into
    the group, and the peak we care about is the SUM across the group at one
    instant, which getrusage(RUSAGE_CHILDREN) cannot give.
    """
    peak = 0.0
    while not stop.is_set():
        try:
            out = subprocess.run(["ps", "-o", "rss=", "-g", str(pgid)],
                                 capture_output=True, text=True, timeout=5).stdout
            total_kb = sum(int(x) for x in out.split() if x.isdigit())
            peak = max(peak, total_kb / 1048576.0)
        except Exception:
            pass
        stop.wait(2.0)
    return peak


def _gate_weight_gb(target_id: str) -> int:
    prior = load_record(target_id) or {}
    measured = prior.get("peak_rss_gb")
    if isinstance(measured, (int, float)) and measured > 0:
        # +50% headroom: peak RSS is sampled, so the true peak can fall between
        # samples, and a target's cost grows as the spec does.
        return max(MIN_TARGET_GB, math.ceil(measured * 1.5))
    return DEFAULT_TARGET_GB


# A FAILED ACQUIRE IS NOT A FREE PASS, AND IT MUST NOT BE SILENT.
#
# `heavy_gate.sh acquire` blocks until it fits, so the only way it returns
# without a token is an ERROR -- in practice `_lock` starving out (its mkdir
# mutex is unfair and gives up after 180 s) when a dozen threads and half a
# dozen other lanes storm it at once. The runner then proceeds anyway, on the
# deliberate principle that the gate must never stop the suite from running.
#
# That principle stands. What was wrong is that it happened INVISIBLY: measured
# 2026-08-20 at fa691b5a9, a `--jobs 8` sweep had EIGHT `cargo test` children
# alive under the worker and TWO gate tokens to its name -- six targets running
# with no reservation at all, on a machine whose kernel panicked on 2026-08-19
# from exactly that kind of unaccounted concurrency. Nothing in the artifact
# said so.
#
# So: retry a failed acquire a few times before giving up, and RECORD which way
# it went. `gate_admitted: false` in a record means "this row's memory was never
# reserved" -- the number a reader needs to judge whether a pass was gated.
GATE_ACQUIRE_ATTEMPTS = 3
GATE_ACQUIRE_BACKOFF_S = 5.0


def _gate_acquire(weight_gb: int, label: str) -> tuple[str | None, bool]:
    """Reserve `weight_gb` from the machine-wide gate.

    Returns `(token, admitted)`. `admitted` is False when the gate could not
    admit us and the caller is proceeding UNGATED -- never a reason to skip the
    target, always a reason to say so in the record.
    """
    if not HEAVY_GATE.exists():
        return None, False
    for attempt in range(GATE_ACQUIRE_ATTEMPTS):
        try:
            env = dict(os.environ, HEAVY_GATE_OWNER_PID=str(os.getpid()))
            proc = subprocess.run([str(HEAVY_GATE), "acquire", str(weight_gb), label],
                                  capture_output=True, text=True, env=env)
            token = proc.stdout.strip()
            if proc.returncode == 0 and token:
                return token, True
        except Exception:
            pass         # never let the gate stop the suite from running
        if attempt + 1 < GATE_ACQUIRE_ATTEMPTS:
            time.sleep(GATE_ACQUIRE_BACKOFF_S * (attempt + 1))
    return None, False


def _gate_release(token: str | None) -> None:
    if token and HEAVY_GATE.exists():
        try:
            subprocess.run([str(HEAVY_GATE), "release", token],
                           capture_output=True, timeout=10)
        except Exception:
            pass


def record_path(target_id: str) -> Path:
    """Where a target's record lives.

    Shard records go into a per-parent subdirectory. There are hundreds of them
    and they are subordinate evidence; leaving them in the top level would bury
    the four dozen rows a human actually scans.
    """
    if SHARD_SEP in target_id:
        parent = target_id.split(SHARD_SEP, 1)[0]
        return STATE_DIR / "shards" / safe_name(parent) / f"{safe_name(target_id)}.json"
    return STATE_DIR / f"{safe_name(target_id)}.json"


def load_record(target_id: str) -> dict[str, Any] | None:
    path = record_path(target_id)
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text())
    except json.JSONDecodeError:
        return {"status": STATUS_ERROR, "notes": "record file is not valid JSON"}


def write_record(record: dict[str, Any]) -> None:
    path = record_path(record["target"])
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def rollup(
    entry: dict[str, Any], digest: str, shard_rows: list[dict[str, Any]]
) -> dict[str, Any]:
    """Derive a sharded parent's bucket from its shards. Never executes anything.

    GREEN demands all four of: a plan that still matches the current inputs, a
    plan whose `--list` partition proof passed, every shard GREEN at its own
    current digest, and the shards' *measured* test counts re-summing to the
    declared total. Anything less is UNKNOWN, except a RED shard, which is RED.
    Rolling an incomplete set up to GREEN is the exact failure this artifact
    exists to prevent, so every early return below is UNKNOWN or RED.
    """
    base = {"target": entry["id"], "kind": entry["kind"], "package": entry["package"],
            "last_known": None}
    plan = entry.get("_plan") or load_plan(entry["id"])
    if plan is None:
        return {**base, "bucket": BUCKET_UNKNOWN, "reason": "no shard plan: run `shards plan`"}

    proof = plan.get("partition_proof") or {}
    if not proof.get("verified"):
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": "shard plan's partition proof did not pass; the shards are not known to cover the target",
        }
    if plan.get("input_digest") != digest:
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": "stale: the shard plan was computed against different inputs; re-run `shards plan`",
        }

    # The PLAN is the authority on which shards exist, not whatever the caller
    # happened to enumerate: `--only clean-verify::lib` selects the parent and
    # no shards, and answering that query from an empty list would be answering
    # a different question. Rows already derived by the caller are reused;
    # anything missing is derived here from the plan.
    have = {row["target"]: row for row in (shard_rows or [])}
    rows = [
        have.get(shard_entry["id"])
        or derive(shard_entry, load_record(shard_entry["id"]), input_digest(shard_entry))
        for shard_entry in shard_entries(plan, entry.get("_dirs"))
    ]
    counts = {b: 0 for b in (BUCKET_GREEN, BUCKET_RED, BUCKET_RUNNING, BUCKET_UNKNOWN)}
    for row in rows:
        counts[row["bucket"]] += 1
    total = len(plan["shards"])
    if len(rows) != total:
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": f"only {len(rows)} of {total} planned shards could be derived",
        }
    detail = (
        f"{counts[BUCKET_GREEN]}/{total} shards GREEN, {counts[BUCKET_RED]} RED, "
        f"{counts[BUCKET_RUNNING]} RUNNING, {counts[BUCKET_UNKNOWN]} UNKNOWN"
    )
    if counts[BUCKET_RED]:
        return {**base, "bucket": BUCKET_RED, "reason": detail}
    if counts[BUCKET_UNKNOWN] or counts[BUCKET_RUNNING]:
        return {**base, "bucket": BUCKET_UNKNOWN, "reason": detail}

    # Every shard is GREEN. Re-prove the partition from what actually RAN, not
    # from the plan: a green shard that executed fewer tests than planned is
    # caught per-shard below, and this catches the aggregate.
    observed = 0
    for shard in plan["shards"]:
        shard_record = load_record(shard["id"]) or {}
        shard_counts = shard_record.get("counts") or {}
        observed += (
            int(shard_counts.get("passed", 0))
            + int(shard_counts.get("failed", 0))
            + int(shard_counts.get("ignored", 0))
        )
    declared = int(proof.get("declared_total", -1))
    if observed != declared:
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": (
                f"{detail}, but the shards ran {observed} tests where the plan declares "
                f"{declared}: the run-time partition does not close"
            ),
        }
    return {
        **base,
        "bucket": BUCKET_GREEN,
        "reason": f"{detail}; {observed} tests ran, matching the {declared} declared",
    }


def shard_count_mismatch(entry: dict[str, Any], record: dict[str, Any]) -> str | None:
    """Did a GREEN shard actually run the tests its plan entry promised?

    A filter that stops matching anything makes libtest print "0 passed" and
    exit 0. Without this check that reads as a pass, and the sharding would have
    quietly deleted tests from the suite -- worse than not measuring at all.
    """
    shard = entry.get("_shard")
    if not shard:
        return None
    counts = record.get("counts") or {}
    ran = (
        int(counts.get("passed", 0))
        + int(counts.get("failed", 0))
        + int(counts.get("ignored", 0))
    )
    expected = int(shard.get("test_count", -1))
    if ran != expected:
        return f"ran {ran} tests, the shard plan declares {expected}"
    return None


def derive(
    entry: dict[str, Any],
    record: dict[str, Any] | None,
    digest: str,
    shard_rows: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Map (inventory entry, stored record, current digest) -> reported bucket.

    This is the only place a bucket is decided, and it defaults to UNKNOWN.
    """
    target = entry["id"]
    base = {"target": target, "kind": entry["kind"], "package": entry["package"]}

    if entry["kind"] == KIND_ROLLUP:
        return rollup(entry, digest, shard_rows or [])

    if record is None:
        return {**base, "bucket": BUCKET_UNKNOWN, "reason": "never run by this runner", "last_known": None}

    commit = record.get("commit")
    last_known = f"{record.get('status', '?')}@{commit[:9] if commit else 'no-sha'}"

    if record.get("source") == "seeded":
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": f"seeded report, not verified here ({record.get('seed_note', 'no note')})",
            "last_known": last_known,
        }

    if record.get("status") == STATUS_RUNNING:
        pid = int(record.get("pid", 0) or 0)
        if pid_alive(pid):
            return {**base, "bucket": BUCKET_RUNNING, "reason": f"in flight, pid {pid}", "last_known": last_known}
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": f"abandoned: recorded RUNNING at pid {pid}, process is gone",
            "last_known": last_known,
        }

    if record.get("input_digest") != digest:
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": "stale: inputs changed since the recorded run",
            "last_known": last_known,
        }

    if record.get("status") == STATUS_GREEN:
        mismatch = shard_count_mismatch(entry, record)
        if mismatch:
            return {
                **base,
                "bucket": BUCKET_UNKNOWN,
                "reason": f"shard exited 0 but {mismatch}; its filter no longer selects its planned tests",
                "last_known": last_known,
            }
        return {**base, "bucket": BUCKET_GREEN, "reason": record.get("final_line", ""), "last_known": last_known}
    if record.get("status") == STATUS_RED:
        return {**base, "bucket": BUCKET_RED, "reason": record.get("final_line", ""), "last_known": last_known}
    return {
        **base,
        "bucket": BUCKET_UNKNOWN,
        "reason": f"recorded status {record.get('status')!r}: {record.get('notes', '')}",
        "last_known": last_known,
    }


# --------------------------------------------------------------------------
# execution
# --------------------------------------------------------------------------

_RESULT_RE = re.compile(r"^test result: ")

# Live child process groups, so a SIGTERM to the worker takes its cargo
# invocations (and the test binaries they spawned) down with it. Without this,
# `run --restart` orphans the previous run's children to PID 1, where they keep
# burning cores and writing logs that nothing will ever turn into a record.
_LIVE_CHILDREN: set[int] = set()
_LIVE_LOCK = threading.Lock()


def _reap_children(signum: int, _frame: Any) -> None:
    with _LIVE_LOCK:
        pids = sorted(_LIVE_CHILDREN)
    for pid in pids:
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    print(f"[worker] received signal {signum}; killed {len(pids)} child group(s)", flush=True)
    os._exit(143)


def install_signal_handlers() -> None:
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, _reap_children)


def summarize_output(text: str, exit_code: int) -> tuple[str, dict[str, int]]:
    """Verbatim final meaningful line plus parsed counts where cargo gives them."""
    lines = [line.rstrip("\n") for line in text.splitlines() if line.strip()]
    result_lines = [line for line in lines if _RESULT_RE.match(line.strip())]
    counts = {"passed": 0, "failed": 0, "ignored": 0, "result_lines": len(result_lines)}
    for line in result_lines:
        for field in ("passed", "failed", "ignored"):
            match = re.search(rf"(\d+) {field}", line)
            if match:
                counts[field] += int(match.group(1))
    if result_lines:
        final = result_lines[-1].strip()
    elif lines:
        final = lines[-1].strip()
    else:
        final = f"<no output; exit {exit_code}>"
    return final[:600], counts


# A packed `--exact` shard names every test it runs in argv -- 935 names and
# ~61KB for the spec shard of the current cut. That is fine to EXECUTE (argv is
# passed as a list, never through a shell, and macOS allows 1MiB) but writing it
# verbatim into a JSON record makes the record unreadable for no gain, since the
# plan already holds the authoritative filters. So the record's `command` is
# rendered with an explicit, unmistakable truncation marker rather than silently
# cut: a reader must not be able to copy a shortened command and believe it is
# the one that ran.
COMMAND_RENDER_LIMIT = 2_000


def render_command(argv: list[str]) -> str:
    text = " ".join(argv)
    if len(text) <= COMMAND_RENDER_LIMIT:
        return text
    return (
        f"{text[:COMMAND_RENDER_LIMIT]} "
        f"<<TRUNCATED: {len(argv)} argv items, {len(text)} chars. This string is NOT runnable; "
        f"the authoritative argv is this shard's entry in the shard plan.>>"
    )


def run_one(entry: dict[str, Any], timeout: int, timeout_basis: str = "caller-supplied") -> dict[str, Any]:
    # Digest immediately before launch -- NOT at queue-planning time. With a job
    # pool, the last target in a queue can start hours after planning, and other
    # lanes commit to this repo concurrently; stamping a record with a digest
    # measured hours before the command ran would attribute the result to a tree
    # state that was never tested.
    digest = input_digest(entry, fresh=True)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = LOG_DIR / f"{safe_name(entry['id'])}.log"
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = str(target_dir())
    env.setdefault("CARGO_TERM_COLOR", "never")

    # Weight from what this target ACTUALLY cost here last time. Read BEFORE the
    # RUNNING template below overwrites the record -- otherwise it reads its own
    # blank `peak_rss_gb` and every target admits at the default forever. That
    # bug was live for one commit; the test below pins it.
    gate_weight = _gate_weight_gb(entry["id"])

    started = time.time()
    record = {
        "schema": SCHEMA,
        "target": entry["id"],
        "package": entry["package"],
        "kind": entry["kind"],
        "status": STATUS_RUNNING,
        "command": render_command(entry["argv"]),
        "argv_items": len(entry["argv"]),
        "commit": git_head(),
        "tree_dirty": git_tree_dirty(),
        "input_digest": digest,
        "digest_scope": "path-dep-closure(working tree) + root Cargo.toml + Cargo.lock + rustc -vV + argv",
        "started_at": now_iso(),
        "finished_at": None,
        "duration_s": None,
        "exit_code": None,
        "final_line": None,
        "counts": None,
        "log": repo_relative(log_path),
        "source": "measured",
        "runner_host": socket.gethostname(),
        "runner_target_dir": str(target_dir()),
        "pid": os.getpid(),
        "timeout_s": timeout,
        # Why this budget and not another. Without it, a reader of the artifact
        # cannot tell a policy-derived number from an ad-hoc `--timeout 25`, and
        # the 2026-08-12 ERROR row is exactly the case where that mattered.
        "timeout_basis": timeout_basis,
        "timed_out": None,
        # Peak RSS of the child's whole process group, sampled at 2 s. Feeds the
        # NEXT run's gate weight, so the runner learns each target's real cost.
        "peak_rss_gb": None,
        "gate_weight_gb": gate_weight,
        # Whether the machine-wide gate actually reserved that weight. False
        # means the row ran with NO reservation -- see _gate_acquire.
        "gate_admitted": None,
        "notes": "",
    }
    write_record(record)

    gate_token, gate_admitted = _gate_acquire(gate_weight, entry["id"])
    record["gate_admitted"] = gate_admitted
    if not gate_admitted:
        record["notes"] = (
            (record["notes"] + " | ") if record["notes"] else ""
        ) + f"ran UNGATED: heavy_gate did not reserve {gate_weight} GB "\
            f"(script absent, or acquire failed {GATE_ACQUIRE_ATTEMPTS} times)"
        write_record(record)
    rss_stop = threading.Event()
    rss_future: list[float] = []

    try:
        with open(log_path, "w", encoding="utf-8") as handle:
            # start_new_session: give the child its own process group so both
            # the timeout path and the SIGTERM handler can kill cargo *and* the
            # test binary it spawns, rather than just cargo.
            proc = subprocess.Popen(
                entry["argv"],
                cwd=str(REPO_ROOT),
                stdout=handle,
                stderr=subprocess.STDOUT,
                env=env,
                text=True,
                start_new_session=True,
            )
            with _LIVE_LOCK:
                _LIVE_CHILDREN.add(proc.pid)
            sampler = threading.Thread(
                target=lambda: rss_future.append(_peak_rss_gb(proc.pid, rss_stop)),
                daemon=True,
            )
            sampler.start()
            try:
                exit_code = proc.wait(timeout=timeout)
                timed_out = False
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    proc.kill()
                proc.wait()
                exit_code = -1
                timed_out = True
            finally:
                rss_stop.set()
                sampler.join(timeout=5)
                with _LIVE_LOCK:
                    _LIVE_CHILDREN.discard(proc.pid)
    except OSError as exc:
        rss_stop.set()
        _gate_release(gate_token)
        record.update(
            status=STATUS_ERROR,
            finished_at=now_iso(),
            duration_s=round(time.time() - started, 1),
            exit_code=None,
            final_line=f"<launch failed: {exc}>",
            notes="runner could not start the command",
        )
        write_record(record)
        return record

    _gate_release(gate_token)
    if rss_future:
        record["peak_rss_gb"] = round(rss_future[0], 2)

    text = log_path.read_text(errors="replace")
    final_line, counts = summarize_output(text, exit_code)

    # Did another lane edit the source closure while this target was running?
    # If so the record's start-digest no longer describes the current tree, and
    # the derived status will report the record stale -- i.e. UNKNOWN, not a
    # pass. Recording the fact explicitly turns a silent staleness into a stated
    # one. Known residual race: the tree can move in the seconds between the
    # start digest and cargo actually reading the sources; nothing here closes
    # that window.
    digest_at_finish = input_digest(entry, fresh=True)
    record["input_digest_at_finish"] = digest_at_finish
    record["inputs_moved_during_run"] = digest_at_finish != digest

    record["timed_out"] = timed_out

    if timed_out:
        status = STATUS_ERROR
        notes = (
            f"KILLED after the runner timeout of {timeout}s ({timeout_basis}) -- this is NOT a pass "
            f"and NOT a failure. The next run of this target gets {min(timeout * 2, TIMEOUT_HARD_CEILING)}s "
            f"by policy; if it is still killed there, investigate the target, do not raise the budget by hand."
        )
        final_line = f"<timed out after {timeout}s; last line: {final_line}>"
    elif exit_code == 0:
        status = STATUS_GREEN
        notes = ""
    else:
        status = STATUS_RED
        notes = ""

    record.update(
        status=status,
        finished_at=now_iso(),
        duration_s=round(time.time() - started, 1),
        exit_code=exit_code,
        final_line=final_line,
        counts=counts,
        notes=notes,
    )
    write_record(record)
    return record


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------


def select(inventory: list[dict[str, Any]], patterns: list[str]) -> list[dict[str, Any]]:
    if not patterns:
        return inventory
    out = []
    for entry in inventory:
        if any(fnmatch.fnmatch(entry["id"], pat) for pat in patterns):
            out.append(entry)
    return out


def derive_all(inventory: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Bucket every entry, resolving roll-ups after the shards they read."""
    rows: list[dict[str, Any]] = []
    shards_by_parent: dict[str, list[dict[str, Any]]] = {}
    rollups: list[dict[str, Any]] = []
    for entry in inventory:
        if entry["kind"] == KIND_ROLLUP:
            rollups.append(entry)
            continue
        row = derive(entry, load_record(entry["id"]), input_digest(entry))
        if entry["kind"] == KIND_SHARD:
            row["parent"] = entry["_parent"]
            shards_by_parent.setdefault(entry["_parent"], []).append(row)
        rows.append(row)
    for entry in rollups:
        rows.append(derive(entry, None, input_digest(entry), shards_by_parent.get(entry["id"], [])))
    return rows


def cmd_status(args: argparse.Namespace) -> int:
    inventory = select(build_inventory(args.packages), args.only)
    rows = derive_all(inventory)

    counts = {b: 0 for b in (BUCKET_GREEN, BUCKET_RED, BUCKET_RUNNING, BUCKET_UNKNOWN)}
    for row in rows:
        counts[row["bucket"]] += 1

    if args.json:
        print(
            json.dumps(
                {
                    "schema": SCHEMA,
                    "generated_at": now_iso(),
                    "commit": git_head(),
                    "tree_dirty": git_tree_dirty(),
                    "counts": counts,
                    "targets": rows,
                },
                indent=2,
            )
        )
        return 0

    # Hundreds of shard rows would bury the four dozen a human scans, so they
    # collapse into their roll-up unless asked for -- or unless they are not
    # GREEN, because a shard that is RED or unmeasured is precisely the row
    # nobody should have to opt in to see.
    shown = [
        row
        for row in rows
        if args.shards or row["kind"] != KIND_SHARD or row["bucket"] != BUCKET_GREEN
    ]
    hidden = len(rows) - len(shown)
    width = max((len(r["target"]) for r in shown), default=10)
    order = {BUCKET_RED: 0, BUCKET_UNKNOWN: 1, BUCKET_RUNNING: 2, BUCKET_GREEN: 3}
    print(f"suite state @ {git_head()[:9]}{'  (DIRTY TREE)' if git_tree_dirty() else ''}")
    print(f"{'TARGET':<{width}}  BUCKET    DETAIL")
    for row in sorted(shown, key=lambda r: (order[r["bucket"]], r["target"])):
        detail = row["reason"]
        if row["bucket"] != BUCKET_GREEN and row.get("last_known"):
            detail = f"{detail} [last_known={row['last_known']}]"
        print(f"{row['target']:<{width}}  {row['bucket']:<8}  {detail[:150]}")
    total = len(rows)
    print()
    if hidden:
        print(f"({hidden} GREEN shard row(s) collapsed into their roll-up; --shards to list them)")
    print(
        f"GREEN {counts[BUCKET_GREEN]}   RED {counts[BUCKET_RED]}   "
        f"RUNNING {counts[BUCKET_RUNNING]}   UNKNOWN {counts[BUCKET_UNKNOWN]}   (of {total})"
    )
    if counts[BUCKET_UNKNOWN] or counts[BUCKET_RUNNING]:
        print("The suite is NOT known green: UNKNOWN is not a pass.")
    elif counts[BUCKET_RED]:
        print("The suite is RED.")
    else:
        print("Every enumerated target is GREEN at the current input digest.")
    return gate_exit_code(counts) if args.gate else 0


def gate_exit_code(counts: dict[str, int]) -> int:
    """Exit status for `--gate`, so this composes with the other pre-push gates.

    Fail-closed and distinguishable: RED outranks UNKNOWN because a known
    failure is more actionable than an absence of information, but an absence of
    information is still a failure. Only an all-GREEN board exits 0.
    """
    if counts[BUCKET_RED]:
        return 1
    if counts[BUCKET_UNKNOWN] or counts[BUCKET_RUNNING]:
        return 2
    return 0


def cmd_inventory(args: argparse.Namespace) -> int:
    for entry in select(build_inventory(args.packages), args.only):
        print(f"{entry['id']}\t{' '.join(entry['argv'])}")
    return 0


def cmd_worker(args: argparse.Namespace) -> int:
    """In-process queue walker. Launched detached by `run`; not for direct use.

    Runs up to `jobs` targets concurrently. Safe on a shared CARGO_TARGET_DIR,
    but concurrency only pays once the target dir is warm: cargo holds the
    build-directory lock for the build phase and releases it before executing
    the test binary, so concurrent invocations serialize while building and
    overlap only while running. Both halves measured on this workspace -- a
    second `cargo test --test X` started immediately beside a target past its
    build, and a second cold `cargo clippy` blocked on the build-directory lock.
    """
    install_signal_handlers()
    queue = json.loads(Path(args.queue).read_text())
    inventory = {e["id"]: e for e in build_inventory(queue["packages"])}
    jobs = max(1, int(queue.get("jobs", 1)))
    print(
        f"[worker] pid={os.getpid()} targets={len(queue['targets'])} jobs={jobs} "
        f"start={now_iso()} commit={git_head()[:9]}",
        flush=True,
    )

    pending: list[tuple[dict[str, Any], str]] = []
    for target_id in queue["targets"]:
        entry = inventory.get(target_id)
        if entry is None:
            print(f"[worker] SKIP {target_id}: not in inventory", flush=True)
            continue
        if entry["kind"] == KIND_ROLLUP:
            print(f"[worker] SKIP {target_id}: roll-up target, nothing to execute", flush=True)
            continue
        digest = input_digest(entry)
        # Ask `derive`, not the raw record: it is the single place a bucket is
        # decided, and it knows things a status field does not -- e.g. that a
        # shard which exited 0 while running the wrong number of tests is not a
        # pass and must be re-run rather than skipped.
        if not queue.get("force") and derive(entry, load_record(target_id), digest)["bucket"] == BUCKET_GREEN:
            print(f"[worker] SKIP {target_id}: already GREEN at this digest", flush=True)
            continue
        pending.append((entry, digest))

    def execute(item: tuple[dict[str, Any], str]) -> dict[str, Any]:
        entry, _planning_digest = item
        # Budget decided HERE, from the record as it stands at dispatch, not at
        # queue-planning time: with a job pool the last target can start hours
        # later, and by then this target may have a completed run to size from.
        budget, basis = timeout_for(entry, load_record(entry["id"]), queue.get("timeout_override"))
        print(f"[worker] RUN  {entry['id']} at {now_iso()} (timeout {budget}s: {basis})", flush=True)
        return run_one(entry, budget, basis)

    done = 0
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(execute, item): item[0]["id"] for item in pending}
        for future in as_completed(futures):
            target_id = futures[future]
            done += 1
            try:
                result = future.result()
            except Exception as exc:  # pragma: no cover - defensive
                print(f"[worker] DONE {target_id} -> runner exception: {exc}", flush=True)
                continue
            print(
                f"[worker] DONE ({done}/{len(pending)}) {target_id} -> {result['status']} "
                f"({result['duration_s']}s) {result['final_line']}",
                flush=True,
            )
    print(f"[worker] finished {now_iso()}", flush=True)
    return 0


def cmd_run(args: argparse.Namespace) -> int:
    if WORKER_PIDFILE.exists():
        try:
            existing = int(WORKER_PIDFILE.read_text().strip())
        except ValueError:
            existing = 0
        if pid_alive(existing) and not args.restart:
            print(
                f"a worker is already running (pid {existing}); "
                f"follow {WORKER_LOG}, or pass --restart to replace it",
                file=sys.stderr,
            )
            return 3
        if pid_alive(existing) and args.restart:
            os.kill(existing, 15)
            time.sleep(2)

    inventory = select(build_inventory(args.packages), args.only)
    rows = {row["target"]: row for row in derive_all(inventory)}
    chosen: list[dict[str, Any]] = []
    for entry in inventory:
        # A roll-up executes nothing: queueing it would be queueing a reading.
        if entry["kind"] == KIND_ROLLUP:
            continue
        row = rows[entry["id"]]
        if args.force or row["bucket"] in (BUCKET_UNKNOWN, BUCKET_RED):
            chosen.append(entry)

    # Integration targets, then workspace gates, then the lib target or its
    # shards. The lib work is the known multi-hour part; dispatching it first
    # would starve every cheaper target and reproduce the exact "ran out of time
    # with nothing to show" failure this runner exists to end.
    #
    # Within the shards it is still longest-processing-time-first, but the
    # estimate of "longest" changed with the cost model. Test count WAS the
    # proxy, because every spec test rebuilt the specification. Under the
    # per-process cache a shard's cost is dominated by whether it pays a build
    # at all: the 935-test spec shard is hours and the 1499-test sat_verify
    # shard is seconds. So spec-paying shards are dispatched first and test
    # count only breaks ties among equals.
    kind_rank = {"test": 0, "gate": 1, "lib": 2, KIND_SHARD_SPEC: 2, KIND_SHARD: 3}
    chosen.sort(
        key=lambda e: (
            kind_rank.get(e["kind"], 4),
            -int((e.get("_shard") or {}).get("test_count", 0)),
            e["id"],
        )
    )
    chosen = [e["id"] for e in chosen]

    if not chosen:
        print("nothing to do: every selected target is GREEN at its current input digest")
        return 0

    RUN_DIR.mkdir(parents=True, exist_ok=True)
    QUEUE_FILE.write_text(
        json.dumps(
            {
                "targets": chosen,
                "packages": args.packages,
                # None => the per-target policy decides at dispatch. A number
                # here is an explicit operator override for the whole queue.
                "timeout_override": args.timeout,
                "jobs": args.jobs,
                "force": args.force,
                "queued_at": now_iso(),
                "commit": git_head(),
            },
            indent=2,
        )
    )

    if args.foreground:
        args.queue = str(QUEUE_FILE)
        return cmd_worker(args)

    argv = [
        sys.executable,
        str(REPO_ROOT / "scripts" / "daemonize.py"),
        "--log",
        str(WORKER_LOG),
        "--pidfile",
        str(WORKER_PIDFILE),
        "--cwd",
        str(REPO_ROOT),
        "--",
        sys.executable,
        str(REPO_ROOT / "scripts" / "verify_runner.py"),
        "worker",
        "--queue",
        str(QUEUE_FILE),
    ]
    code, out = run_capture(argv)
    if code != 0:
        print(out, file=sys.stderr)
        return code
    pid = out.strip()
    print(f"worker daemon pid {pid}; {len(chosen)} target(s) queued")
    print(f"  log:    {WORKER_LOG}")
    print(f"  state:  {STATE_DIR}")
    print(f"  status: scripts/verify_runner.sh status")
    return 0


def cmd_shards(args: argparse.Namespace) -> int:
    """Plan / inspect the shard cut of a lib target.

    `plan` is the only thing that writes a plan, and it refuses to write one
    whose partition proof did not pass. That refusal is the point: an unproved
    cut is how a suite silently loses tests, which is strictly worse than the
    single unmeasurable target it replaces.
    """
    parent = args.parent
    package = parent.split("::")[0]

    if args.action == "show":
        plan = load_plan(parent)
        if plan is None:
            print(f"no shard plan for {parent} at {plan_path(parent)}", file=sys.stderr)
            return 2
        if args.json:
            print(json.dumps(plan, indent=2))
            return 0
        proof = plan["partition_proof"]
        packing = plan.get("packing") or {"enabled": False}
        print(f"shard plan for {parent} @ {plan['commit'][:9]} ({plan['generated_at']})")
        print(f"  key           : module prefix, split while a key exceeds {plan['max_tests_per_shard']} tests")
        print(f"  split prefixes: {len(plan['split_prefixes'])}")
        if packing.get("enabled"):
            print(f"  packing       : {packing['module_keys']} module keys -> {packing['bins']} bins "
                  f"(<= {packing['max_tests_per_bin']} tests, groups >= {packing['group_min_tests']})")
            print(f"  spec-paying   : roots {', '.join(packing['spec_paying_roots'])} "
                  f"(source scan, cost hint only)")
            spec_shards = [s for s in plan["shards"] if s.get("kind") == KIND_SHARD_SPEC]
            print(f"  builds paid   : <= {len(spec_shards)} process(es) x {SPEC_FLAVOURS} flavours "
                  f"= <= {len(spec_shards) * SPEC_FLAVOURS} specification builds")
            for item in packing.get("unpackable_bins") or []:
                print(f"  UNPACKABLE    : {item['bin']} fell back to {len(item['keys'])} per-key shards")
        else:
            print("  packing       : disabled (one shard per module key)")
        modes = {}
        for shard in plan["shards"]:
            modes[shard.get("mode", "prefix")] = modes.get(shard.get("mode", "prefix"), 0) + 1
        print(f"  shards        : {len(plan['shards'])} "
              f"({modes.get('prefix', 0)} by module prefix, {modes.get('exact', 0)} by --exact name list)")
        print(f"  declared tests: {proof['declared_total']}")
        print(f"  partition     : sum={proof['sum_of_shard_counts']} union={proof['union_size']} "
              f"dropped={proof['dropped_count']} duplicated={proof['duplicated_count']} "
              f"alien={proof['alien_count']} -> {'VERIFIED' if proof['verified'] else 'NOT VERIFIED'}")
        oversized = plan.get("oversized_indivisible") or []
        if oversized:
            print(f"  OVER CAP      : {len(oversized)} key(s) exceed {plan['max_tests_per_shard']} "
                  f"and cannot be split further without a source change:")
            for item in oversized:
                print(f"                  {item['test_count']:>5}  {item['key']}")
        print()
        for shard in sorted(plan["shards"], key=lambda s: -s["test_count"])[: args.top]:
            budget, _ = timeout_for({"kind": shard.get("kind", KIND_SHARD)},
                                    load_record(shard["id"]))
            print(f"  {shard['test_count']:>5}  {shard['key']:<28} "
                  f"{shard.get('kind', KIND_SHARD):<15} {len(shard.get('keys') or [shard['key']]):>4} keys "
                  f"budget {budget}s")
        return 0

    # --- plan ------------------------------------------------------------
    entry = next(
        (e for e in build_inventory([package], with_gates=False)
         if e["id"] == parent and e["kind"] in ("lib", KIND_ROLLUP)),
        None,
    )
    if entry is None:
        print(f"{parent} is not a lib target of {package}", file=sys.stderr)
        return 2
    base_argv = ["cargo", "test", "--locked", "-p", package, "--lib"]
    # The plan's freshness is the freshness of the UNSHARDED target: that is the
    # command whose inputs the shards collectively stand in for.
    parent_entry = dict(entry, argv=base_argv, kind="lib")
    digest = input_digest(parent_entry, fresh=True)

    print(f"building {package} lib test binary ...", flush=True)
    binary = test_binary_for(package)
    declared = list_tests(binary)
    print(f"{len(declared)} declared tests in {binary.name}", flush=True)
    if not declared:
        print("the target declares no tests; refusing to write an empty plan", file=sys.stderr)
        return 2

    splits = derive_splits(declared, args.max_tests)
    buckets: dict[str, list[str]] = {}
    for name in declared:
        buckets.setdefault(shard_key(name, splits), []).append(name)
    keys = sorted(buckets)

    # A key can exceed the cap and still be un-splittable: every test under it
    # sits at the same module depth, so there is no deeper level to cut on.
    # Stating those in the plan is the difference between "the cut is uneven"
    # and "this shard cannot be made smaller without a source change".
    oversized = sorted(
        (
            {
                "key": key,
                "test_count": len(members),
                "reason": "every test under this key is at the key's own module depth; "
                          "no deeper module level exists to split on",
            }
            for key, members in buckets.items()
            if len(members) > args.max_tests
        ),
        key=lambda item: -item["test_count"],
    )

    def per_key_shard(key: str) -> dict[str, Any]:
        mode, filters, skips = shard_realisation(key, keys, set(buckets[key]), declared)
        return {
            "key": key,
            "id": shard_target_id(parent, key),
            "kind": KIND_SHARD_SPEC if key.split("::")[0] in spec_roots else KIND_SHARD,
            "mode": mode,
            "filters": filters,
            "skip": skips,
            "keys": [key],
            "test_count": len(buckets[key]),
            "_intended": sorted(buckets[key]),
        }

    src_dir = REPO_ROOT / "crates" / package / "src"
    spec_roots, spec_evidence = spec_paying_roots(src_dir)
    root_sizes: dict[str, int] = {}
    for key, members in buckets.items():
        root_sizes[key.split("::")[0]] = root_sizes.get(key.split("::")[0], 0) + len(members)

    shards: list[dict[str, Any]] = []
    unpackable: list[dict[str, Any]] = []
    if args.no_pack:
        packing = {"enabled": False, "reason": "--no-pack: one shard per module key"}
        shards = [per_key_shard(key) for key in keys]
    else:
        groups = {
            key: pack_group_of(key, root_sizes, spec_roots, args.group_min_tests)
            for key in keys
        }
        bins = pack_bins(buckets, groups, args.pack_max_tests)
        for item in bins:
            intended = {name for key in item["keys"] for name in buckets[key]}
            realised = bin_realisation(item["keys"], keys, intended, declared)
            if realised is None:
                # Never ship a bin whose filter cannot be made to select exactly
                # its members: fall back to the per-key shards, which are the
                # already-proved unit, and say so in the plan.
                unpackable.append({"bin": item["key"], "keys": item["keys"],
                                   "reason": "no prefix or --exact realisation selects exactly this bin"})
                shards.extend(per_key_shard(key) for key in item["keys"])
                continue
            mode, filters, skips = realised
            shards.append(
                {
                    "key": item["key"],
                    "id": shard_target_id(parent, item["key"]),
                    "kind": KIND_SHARD_SPEC if item["group"] == "spec_paying" else KIND_SHARD,
                    "group": item["group"],
                    "mode": mode,
                    "filters": filters,
                    "skip": skips,
                    "keys": item["keys"],
                    "test_count": len(intended),
                    "_intended": sorted(intended),
                }
            )
        packing = {
            "enabled": True,
            "objective": (
                "minimise the number of PROCESSES that pay a specification build, "
                "subject to each shard staying inside its derived budget and the set "
                "staying resumable"
            ),
            "max_tests_per_bin": args.pack_max_tests,
            "group_min_tests": args.group_min_tests,
            "module_keys": len(keys),
            "bins": len(bins),
            "spec_paying_roots": sorted(spec_roots),
            "spec_paying_evidence": spec_evidence,
            "spec_paying_scan": (
                "source scan of crates/%s/src for %s; a COST HINT ONLY -- coverage and "
                "disjointness are decided by the --list partition proof, not by this scan"
                % (package, "/".join(SPEC_BUILDER_CALLS))
            ),
            "unpackable_bins": unpackable,
            "cost_model": {
                "one_flavour_build_s": ONE_FLAVOUR_BUILD_S,
                "spec_flavours": SPEC_FLAVOURS,
                "marginal_per_test_s": MARGINAL_PER_TEST_S,
                "cheap_population_s": CHEAP_POPULATION_S,
                "spec_shard_floor_s": TIMEOUT_FLOOR_BY_KIND[KIND_SHARD_SPEC],
                "cheap_shard_floor_s": TIMEOUT_FLOOR_BY_KIND[KIND_SHARD],
            },
        }

    # Sanitised ids must stay distinct: two different keys collapsing to one
    # record filename would have one shard overwrite the other's evidence.
    by_file = {}
    for shard in shards:
        name = safe_name(shard["id"])
        if name in by_file:
            print(f"shard id collision after sanitisation: {shard['id']} and {by_file[name]}",
                  file=sys.stderr)
            return 2
        by_file[name] = shard["id"]

    print(f"{len(shards)} shards; replaying each through --list to prove the partition ...", flush=True)
    proof = verify_partition(binary, shards, declared)
    for shard in shards:
        shard.pop("_intended", None)

    plan = {
        "schema": PLAN_SCHEMA,
        "parent": parent,
        "package": package,
        "base_argv": base_argv,
        "generated_at": now_iso(),
        "commit": git_head(),
        "tree_dirty": git_tree_dirty(),
        "input_digest": digest,
        "digest_scope": "path-dep-closure(working tree) + root Cargo.toml + Cargo.lock + rustc -vV + argv",
        "runner_host": socket.gethostname(),
        "test_binary": binary.name,
        "max_tests_per_shard": args.max_tests,
        "oversized_indivisible": oversized,
        "split_prefixes": sorted(splits),
        "shard_key_rule": (
            "longest module prefix whose parent chain is entirely in split_prefixes, "
            "never consuming the test function name; total and deterministic on test names"
        ),
        "packing": packing,
        "partition_proof": proof,
        "shards": shards,
    }

    if not proof["verified"]:
        # A rejected plan is a debugging aid, not part of the artifact: it goes
        # beside the build it describes, never into the committed plan
        # directory where a later reader could mistake it for the live cut.
        failed = RUN_DIR / f"{safe_name(parent)}.REJECTED.json"
        RUN_DIR.mkdir(parents=True, exist_ok=True)
        failed.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
        print(
            "PARTITION PROOF FAILED -- no plan written.\n"
            f"  declared={proof['declared_total']} sum={proof['sum_of_shard_counts']} "
            f"union={proof['union_size']} dropped={proof['dropped_count']} "
            f"duplicated={proof['duplicated_count']} alien={proof['alien_count']} "
            f"mismatched_shards={proof['mismatched_shard_count']}\n"
            f"  rejected plan kept for inspection at {failed}",
            file=sys.stderr,
        )
        return 1

    PLAN_DIR.mkdir(parents=True, exist_ok=True)
    path = plan_path(parent)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)
    supersede_monolith_record(parent, plan)
    print(
        f"wrote {path}\n"
        f"  {len(shards)} shards, {proof['declared_total']} tests, partition VERIFIED "
        f"(sum={proof['sum_of_shard_counts']}, union={proof['union_size']}, "
        f"dropped=0, duplicated=0)"
    )
    return 0


def supersede_monolith_record(parent: str, plan: dict[str, Any]) -> None:
    """Retire the parent's old whole-target record without deleting its content.

    Once a target is sharded its bucket is DERIVED from the shards, so a stored
    status under the parent's id is no longer evidence of anything -- but the
    run that produced it is still a measurement worth keeping, and in this case
    it is the measurement that motivated sharding at all. So the old record is
    carried inside the new one rather than being overwritten or removed.
    """
    previous = load_record(parent)
    if previous is not None and previous.get("source") == "derived":
        previous = previous.get("superseded_run")
    write_record(
        {
            "schema": SCHEMA,
            "target": parent,
            "package": plan["package"],
            "kind": KIND_ROLLUP,
            "status": "SUPERSEDED",
            "source": "derived",
            "command": " ".join(plan["base_argv"]),
            "shard_plan": repo_relative(plan_path(parent)),
            "shard_count": len(plan["shards"]),
            "declared_tests": plan["partition_proof"]["declared_total"],
            "notes": (
                "This target is SHARDED. Its bucket is derived by the runner from the shard "
                "records under data/suite_state/shards/, never from this file; this file exists "
                "so a reader of the parent id finds the plan and the superseded run instead of a "
                "stale status. GREEN requires every shard GREEN at the current digest and the "
                "shards' measured test counts to re-sum to the declared total."
            ),
            "superseded_run": previous,
        }
    )


def cmd_policy(args: argparse.Namespace) -> int:
    """Show the budget each target would get and the basis for it.

    A timeout policy nobody can inspect is a magic number with extra steps. This
    makes the derivation auditable before a multi-hour queue is launched.
    """
    inventory = [e for e in select(build_inventory(args.packages), args.only)
                 if e["kind"] != KIND_ROLLUP]
    rows = []
    for entry in inventory:
        record = load_record(entry["id"])
        budget, basis = timeout_for(entry, record)
        rows.append(
            {
                "target": entry["id"],
                "kind": entry["kind"],
                "timeout_s": budget,
                "basis": basis,
                "last_duration_s": (record or {}).get("duration_s"),
            }
        )
    if args.json:
        print(json.dumps({"schema": SCHEMA, "generated_at": now_iso(), "targets": rows}, indent=2))
        return 0
    width = max((len(r["target"]) for r in rows), default=10)
    print(f"{'TARGET':<{width}}  TIMEOUT   BASIS")
    for row in sorted(rows, key=lambda r: (-r["timeout_s"], r["target"])):
        print(f"{row['target']:<{width}}  {row['timeout_s']:>7}s  {row['basis']}")
    print()
    print(f"hard ceiling {TIMEOUT_HARD_CEILING}s; there is no unlimited setting.")
    return 0


def cmd_seed(args: argparse.Namespace) -> int:
    """Import an externally-reported result WITHOUT claiming it as verified.

    Seeded records are always reported UNKNOWN until this runner measures the
    target itself. That is deliberate: a result whose sha and command were not
    observed here is not evidence, and silently promoting it to GREEN is the
    exact failure mode this artifact exists to prevent.
    """
    payload = json.loads(Path(args.file).read_text())
    written = 0
    for item in payload["seeds"]:
        record = {
            "schema": SCHEMA,
            "target": item["target"],
            "package": item.get("package", "unknown"),
            "kind": item.get("kind", "unknown"),
            "status": item.get("status", STATUS_GREEN),
            "command": item.get("command", "unrecorded"),
            "commit": item.get("commit"),
            "tree_dirty": item.get("tree_dirty"),
            "input_digest": None,
            "digest_scope": None,
            "started_at": None,
            "finished_at": item.get("measured_at"),
            "duration_s": None,
            "exit_code": None,
            "final_line": item.get("final_line"),
            "counts": item.get("counts"),
            "log": None,
            "source": "seeded",
            "seed_note": item["seed_note"],
            "runner_host": None,
            "notes": "SEEDED: reported by another lane, not observed by this runner. "
                     "Reported UNKNOWN until measured here.",
        }
        write_record(record)
        written += 1
    print(f"seeded {written} record(s) into {STATE_DIR} (all still reported UNKNOWN)")
    return 0


def cmd_stop(_args: argparse.Namespace) -> int:
    if not WORKER_PIDFILE.exists():
        print("no worker pidfile")
        return 0
    pid = int(WORKER_PIDFILE.read_text().strip())
    if pid_alive(pid):
        os.kill(pid, 15)
        print(f"sent SIGTERM to worker {pid}")
    else:
        print(f"worker {pid} is not running")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(prog="verify_runner", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    # Single-valued and repeatable rather than nargs="*": a greedy list argument
    # sitting in front of a subcommand swallows the subcommand's own flags.
    parser.add_argument("--packages", action="append", default=None,
                        help="workspace package to enumerate; repeatable, or comma-separated "
                             "(default: clean-verify)")
    parser.add_argument("--only", action="append", default=None,
                        help="glob restricting the target ids acted on; repeatable, or comma-separated")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_status = sub.add_parser("status", help="print the derived GREEN/RED/UNKNOWN table")
    p_status.add_argument("--json", action="store_true")
    p_status.add_argument("--gate", action="store_true",
                          help="exit 1 if any target is RED, 2 if any is UNKNOWN/RUNNING, "
                               "0 only when every enumerated target is GREEN")
    p_status.add_argument("--shards", action="store_true",
                          help="list GREEN shard rows too (non-green shards always show)")
    p_status.set_defaults(func=cmd_status)

    p_inv = sub.add_parser("inventory", help="print the enumerated targets and commands")
    p_inv.set_defaults(func=cmd_inventory)

    p_run = sub.add_parser("run", help="launch the detached worker over stale/unknown targets")
    p_run.add_argument(
        "--timeout", type=int, default=None,
        help="OVERRIDE the per-target timeout policy with one flat budget (seconds). "
             "Omit it -- the policy sizes each target from what that target has actually "
             "cost here. See `policy` for the table it would use.",
    )
    p_run.add_argument("--jobs", type=int, default=4, help="targets to run concurrently (default 4)")
    p_run.add_argument("--force", action="store_true", help="re-run even targets already GREEN")
    p_run.add_argument("--restart", action="store_true", help="replace a live worker")
    p_run.add_argument("--foreground", action="store_true", help="run the queue in this process")
    p_run.set_defaults(func=cmd_run)

    p_worker = sub.add_parser("worker", help=argparse.SUPPRESS)
    p_worker.add_argument("--queue", required=True)
    p_worker.set_defaults(func=cmd_worker)

    p_shards = sub.add_parser(
        "shards",
        help="plan or inspect the shard cut of a lib target too big to run as one unit",
    )
    p_shards.add_argument("action", choices=["plan", "show"])
    p_shards.add_argument("--parent", default="clean-verify::lib",
                          help="the lib target to shard (default clean-verify::lib)")
    p_shards.add_argument("--max-tests", type=int, default=SHARD_MAX_TESTS_DEFAULT,
                          help=f"deepen a shard key while it exceeds this many tests "
                               f"(default {SHARD_MAX_TESTS_DEFAULT})")
    p_shards.add_argument("--no-pack", action="store_true",
                          help="one shard per module key, the pre-cache cut. Costs one "
                               "specification build per spec-holding shard; only useful for "
                               "isolating a single key.")
    p_shards.add_argument("--pack-max-tests", type=int, default=PACK_MAX_TESTS_DEFAULT,
                          help=f"cap on the tests packed into one bin (default {PACK_MAX_TESTS_DEFAULT})")
    p_shards.add_argument("--group-min-tests", type=int, default=PACK_GROUP_MIN_TESTS_DEFAULT,
                          help=f"a non-spec root smaller than this is swept into the `misc` "
                               f"group instead of getting its own bins (default "
                               f"{PACK_GROUP_MIN_TESTS_DEFAULT})")
    p_shards.add_argument("--top", type=int, default=20, help="show: how many shards to list")
    p_shards.add_argument("--json", action="store_true")
    p_shards.set_defaults(func=cmd_shards)

    p_policy = sub.add_parser("policy", help="print the timeout each target would get, and why")
    p_policy.add_argument("--json", action="store_true")
    p_policy.set_defaults(func=cmd_policy)

    p_seed = sub.add_parser("seed", help="import externally-reported results as UNKNOWN")
    p_seed.add_argument("--file", required=True)
    p_seed.set_defaults(func=cmd_seed)

    p_stop = sub.add_parser("stop", help="SIGTERM the running worker")
    p_stop.set_defaults(func=cmd_stop)

    args = parser.parse_args()

    def split_csv(values: list[str] | None, default: list[str]) -> list[str]:
        if not values:
            return default
        return [item for value in values for item in value.split(",") if item]

    args.packages = split_csv(args.packages, ["clean-verify"])
    args.only = split_csv(args.only, [])

    if shutil.which("cargo") is None:
        print("cargo not found on PATH", file=sys.stderr)
        return 2
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
