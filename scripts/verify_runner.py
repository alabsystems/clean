#!/usr/bin/env python3
"""Persistent, resumable, per-target test runner for the Clean workspace.

WHY THIS EXISTS
---------------
`targo --unverified test --locked -p clean-verify` is not completable inside one agent
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
     closure. The target package's OWN dev-dependencies are in that closure --
     they are linked into its test binaries. A DEPENDENCY's dev-dependencies
     are NOT: cargo resolves `[dev-dependencies]` when building a package's own
     tests and never when building it as a library on the way to something
     else, so they cannot change what this target compiles. Build-dependencies
     stay at every depth, because a dependency's build script really is run.
     A library's compile-time reads outside those directories -- its
     `include_str!`/`include_bytes!`, derived (`library_external_reads`), and
     its build script's, declared (`PACKAGE_EXTRA_PATHS`) -- follow the same
     closure; a dependency's test-only inputs do not. An integration-test
     row also takes its own target's derived reads (`row_target_reads`).
     See `path_dep_closure`, whose selftest falsifies both directions -- this
     is the one place where being too NARROW turns a stale green fresh;
  2. the workspace root `Cargo.toml`, `Cargo.lock`, `.cargo/config`,
     `.cargo/config.toml`, `rust-toolchain` and `rust-toolchain.toml` (including
     absence, so creating or deleting a configuration also changes the digest);
  3. the `trustc -vV` release/host/commit-hash string, re-read for each fresh
     run-boundary digest (ordinary status reads share a cached identity);
  4. the exact argv the target is run with, encoded as a JSON array so
     argument boundaries and empty arguments are preserved;
  5. the build profile, for a row that is not a debug build (the
     RELEASE_PROFILE_TARGETS rows; a debug row's digest is unchanged by this).

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
import shlex
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
from typing import Any, NamedTuple

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
# A gate that SKIPPED measured nothing, and nothing is not a pass. `derive`
# already sends any status outside {GREEN, RED, RUNNING} to UNKNOWN, which is
# exactly where a deferral belongs. See _SKIPPED_VERDICT_RE.
STATUS_SKIPPED = "SKIPPED"

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
# A KIND FLOOR IS A POPULATION'S FLOOR, AND `test` NOW HAS TWO POPULATIONS.
#
# `TIMEOUT_FLOOR_BY_KIND["test"] = 7200` is derived, in its own comment below,
# from clean-verify's SPEC-BUILDING integration targets. When clean-elab joined
# the runner's default board (2026-09-16) that floor landed on 138 targets that
# build no specification: measured, all 138 read `never completed here; test
# floor` at 7200 s, a 276 h serial ceiling for that block alone, and a wedged
# one would burn 2 h before anyone heard about it.
#
# The floor could not simply be lowered. `timeout_for` clamps a MEASURED budget
# UP to the floor as well (`max(scaled, floor)`), and 60 of clean-verify's 61
# integration rows sit at exactly 7200 that way against executions of 4-1145 s --
# so moving the KIND floor moves clean-verify's whole board. A per-(package,
# kind) row moves clean-elab alone.
#
# THAT CLEAN-ELAB CANNOT PAY THE 7200 COST IS ESTABLISHED WITH THE RUNNER'S OWN
# CLASSIFIER, not by reading: none of the five `SPEC_BUILDER_CALLS` strings
# occurs anywhere under `crates/clean-elab/` (0 hits in src and tests alike),
# against 124 hits for `build_spec_with_stack` under `crates/clean-verify/tests/`
# alone, and clean-elab's dev-dependencies do not include clean-verify.
#
# THE DERIVATION, and every constant is a dated measurement with its source, not
# a number somebody liked. Re-derive them before moving the floor; they have
# already moved twice under this very change.
#
#   fattest target  x  slowest rate ever seen in the crate  +  worst build leg
#
# _ELAB_MAX_TESTS_IN_TARGET -- 292, `crates/clean-elab/tests/integration.rs`,
#   from a `#[path]`-resolving `#[test]` scan over all 138 targets (median 6).
# _ELAB_WORST_PER_TEST_S -- 6.164 s/test, the worst COMPLETED shard record in
#   the JOURNAL (`lean4_corpus_tests`, 596 tests / 3673.59 s). Read from the
#   journal, NOT from `data/suite_state/`: the live record there is overwritten
#   by whatever ran last, and mid-change it read 1.996 (a fast shard) and then
#   5.178 before settling here. A constant sourced from the mutable copy would
#   be re-derived wrong by the next person.
# _WORST_INTEGRATION_BUILD_LEG_S -- 220.8 s, the worst build leg of ANY
#   integration target recorded here (n=60, median 4.4): clean-verify's
#   `axiom_ratchet`, exec 1140.6 s minus libtest's own "finished in 919.81s".
#   Conservative for clean-elab because clean-verify DEPENDS on clean-elab, so
#   that build is a strict superset.
#
# 292 x 6.164 + 220.8 = 2020.7 s, and 2100 is the only round candidate inside
# the no-slack window [derived, derived x 1.15) = [2020.7, 2323.8). A floor that
# is too tight self-heals -- a kill records ERROR (reads back UNKNOWN, never a
# pass) and the next budget doubles 2100 -> 4200 -> 7200 -- so the old budget
# stays reachable for a target that genuinely needs it; it just has to earn it.
_ELAB_MAX_TESTS_IN_TARGET = 292
_ELAB_WORST_PER_TEST_S = 6.164
_WORST_INTEGRATION_BUILD_LEG_S = 220.8
_ELAB_TEST_FLOOR_DERIVED_S = (
    _ELAB_MAX_TESTS_IN_TARGET * _ELAB_WORST_PER_TEST_S + _WORST_INTEGRATION_BUILD_LEG_S
)

TIMEOUT_FLOOR_BY_PACKAGE_KIND = {
    ("clean-elab", "test"): 2_100,
}

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
    # A MEASUREMENT gate: it does not compile the workspace, it re-elaborates
    # real Mathlib source through Clean's own frontend and compares the result
    # to a committed baseline. Only `gate::srcelab` is of this kind. Floor set
    # from the first end-to-end measurement of the whole pinned slice (see the
    # row's own comment) rather than from the 3600s `gate` floor, which would
    # kill it during its first file.
    "gate-measure": 43_200,
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
    # A per-(package, kind) floor wins over the kind's own, and the basis says
    # WHICH floor held a budget up -- a record that reads "floored at the test
    # floor" cannot tell you which population's floor that was.
    package = entry.get("package", "")
    floor_key = (package, kind)
    if floor_key in TIMEOUT_FLOOR_BY_PACKAGE_KIND:
        floor = TIMEOUT_FLOOR_BY_PACKAGE_KIND[floor_key]
        floor_name = f"{package} {kind}"
    else:
        floor = TIMEOUT_FLOOR_BY_KIND.get(kind, TIMEOUT_FLOOR_DEFAULT)
        floor_name = kind or "default"

    if record and record.get("source") == "measured":
        if _record_was_killed(record) and record.get("timeout_s"):
            prev = int(record["timeout_s"])
            budget = min(max(prev * 2, floor), TIMEOUT_HARD_CEILING)
            return budget, f"previous run was KILLED at {prev}s; doubled, floored at the {floor_name} floor {floor}s"
        # `exec_duration_s` when the record has it, `duration_s` otherwise. The
        # budget this returns bounds `proc.wait`, which starts AFTER the gate
        # admits -- so deriving it from `duration_s`, which starts BEFORE, pays
        # 4x headroom on time the target spent QUEUEING rather than running.
        # Measured 2026-08-28: axiom_ratchet's row reads 22444.2 s of which
        # 9,645 s was the block at heavy_gate. Records written before this field
        # existed keep the old basis, so no existing budget moves.
        duration = record.get("exec_duration_s")
        basis = "of execution (queue wait excluded)"
        if not isinstance(duration, (int, float)):
            duration = record.get("duration_s")
            basis = "this target last took here"
        if record.get("status") in (STATUS_GREEN, STATUS_RED) and isinstance(duration, (int, float)):
            scaled = int(duration * TIMEOUT_HEADROOM) + 1
            budget = min(max(scaled, floor), TIMEOUT_HARD_CEILING)
            return budget, (
                f"{TIMEOUT_HEADROOM:g}x the {duration:.1f}s {basis}, "
                f"floored at the {floor_name} floor {floor}s"
            )

    return min(floor, TIMEOUT_HARD_CEILING), f"never completed here; {floor_name} floor"


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
    """The workspace metadata, parsed from cargo's STDOUT alone.

    `run_capture` merges stderr into stdout, which is right for a log and wrong
    for a document. Measured 2026-09-24: `cargo` on this machine's PATH is
    aterm's reroute shim, which announces itself on stderr before handing over
    ("aterm: 'cargo' is the Rust name; ..."), and cargo also warns on stderr
    about a malformed manifest in a git checkout it scanned -- so the merged
    text began with prose, `json.loads` raised at char 0, and `status` died
    with a traceback on every call. stderr is kept for the failure message.
    """
    proc = subprocess.run(
        ["targo", "metadata", "--locked", "--format-version", "1", "--no-deps"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=600,
        check=False,
    )
    if proc.returncode != 0:
        raise SystemExit(f"targo metadata failed:\n{proc.stderr[-4000:]}{proc.stdout[-2000:]}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise SystemExit(
            f"targo metadata printed no JSON document on stdout ({exc}); stderr was:\n"
            f"{proc.stderr[-4000:]}"
        ) from exc


def _selftest_path_dep_closure() -> None:
    """Prove the closure keeps the root's dev-deps and drops a transitive one.

    Both directions, because only one of them can go wrong quietly. Dropping
    something cargo DOES build makes a stale green look fresh -- the failure the
    digest exists to prevent -- so the arm that asserts the root's own
    dev-dependency is still covered matters as much as the arm that asserts a
    dependency's dev-dependency is not.
    """
    def pkg(name, deps):
        return {
            "name": name,
            "manifest_path": f"/w/{name}/Cargo.toml",
            "dependencies": [{"name": n, "kind": k} for n, k in deps],
        }

    meta = {
        "packages": [
            pkg("root", [("normal_dep", None), ("root_dev", "dev")]),
            pkg("normal_dep", [("deep_dev", "dev"), ("deep_build", "build")]),
            pkg("root_dev", []),
            pkg("deep_dev", []),
            pkg("deep_build", []),
        ]
    }
    got = {p.name for p in path_dep_closure(meta, "root")}
    expected = {"root", "normal_dep", "root_dev", "deep_build"}
    if got != expected:
        raise SystemExit(
            "verify_runner SELFTEST FAILED: path_dep_closure returned "
            f"{sorted(got)}, expected {sorted(expected)}. A closure that is too "
            "WIDE re-runs a green an unrelated crate could not have changed; one "
            "that is too NARROW makes a stale green look fresh. Neither is safe."
        )


def path_dep_closure(meta: dict[str, Any], package: str) -> list[Path]:
    """Directories of `package` plus every workspace path-dependency it reaches.

    `package`'s OWN dev-dependencies are included -- they are linked into its
    test binaries, so a change in one genuinely invalidates a stored result.

    A DEPENDENCY's dev-dependencies are not, and this is the difference that
    matters: cargo builds `clean-mathverse` as a library on the way to
    `clean-elab`'s tests, and a library build never resolves that package's
    `[dev-dependencies]`. Walking dev edges at every depth therefore hashed
    almost the whole workspace into every target's digest -- measured at 25 of
    the workspace's crates for `clean-elab`, `clean-kernel` AND `clean-verify`
    alike, where the real closures are 13, 14 and 14. The one edge
    `clean-elab -> clean-mathverse -> (dev) clean-verify` is why an edit to
    `clean-verify`'s test harness demoted every clean-elab green, and it also
    pulled in `clean-lsp`, `clean-server`, `clean-tla`, `clean-cli` and `clean`.
    Nothing is lost by dropping them: `targo --unverified test -p clean-elab --no-run`
    compiles none of those crates, which is the whole argument and is checkable
    in one command.

    Build-dependencies stay at every depth -- a dependency's build script IS
    run on the way to the library, so its inputs are real inputs.

    Narrowing a freshness digest is the dangerous direction (a digest that stops
    covering an input makes a stale green look fresh), so
    `_selftest_path_dep_closure` falsifies BOTH directions on every call.
    """
    _selftest_path_dep_closure_once()
    by_name = {p["name"]: p for p in meta["packages"]}
    seen: set[str] = set()
    stack: list[tuple[str, int]] = [(package, 0)]
    dirs: list[Path] = []
    while stack:
        name, depth = stack.pop()
        if name in seen or name not in by_name:
            continue
        seen.add(name)
        pkg = by_name[name]
        dirs.append(Path(pkg["manifest_path"]).parent)
        for dep in pkg.get("dependencies", []):
            dep_name = dep.get("name")
            # Only workspace-local packages matter; registry deps are pinned by
            # Cargo.lock, which is hashed separately.
            if dep_name not in by_name:
                continue
            # `kind` is None for a normal dependency, "dev" or "build" otherwise.
            if depth > 0 and dep.get("kind") == "dev":
                continue
            stack.append((dep_name, depth + 1))
    return sorted(set(dirs))


_SELFTEST_CLOSURE_DONE = False


def _selftest_path_dep_closure_once() -> None:
    """Run the closure selftest once per process (it is called in a hot loop)."""
    global _SELFTEST_CLOSURE_DONE
    if not _SELFTEST_CLOSURE_DONE:
        _SELFTEST_CLOSURE_DONE = True
        _selftest_path_dep_closure()


def required_features_argv(target: dict[str, Any]) -> list[str]:
    """`--features <list>` for a target that declares `required-features`.

    Cargo REFUSES a `--test <name>` whose required features are off, before it
    builds anything: measured 2026-11-13, `targo --unverified test --locked -p
    clean-ck0 --test export_inductives` exits 101 with "target
    `export_inductives` in package `clean-ck0` requires the features:
    `export`". A row spelled without them would record that refusal as RED, a
    verdict about the argv rather than the tests. No test target of the four
    packages on the board before 2026-11-13 declared any; six of clean-kernel's
    and six of clean-ck0's do (self-proof unit E3). Sorted, so the argv -- and with it
    the input digest -- does not depend on the manifest's order.
    """
    features = sorted(set(target.get("required-features") or []))
    return ["--features", ",".join(features)] if features else []


# ---------------------------------------------------------------------------
# FEATURE-GATED LIB TESTS (2026-11-13, self-proof unit E3 fix-up)
# ---------------------------------------------------------------------------
#
# A package's lib row builds the library's tests with the features cargo
# resolves for `-p <pkg> --lib` (the defaults, and what dev-dependencies turn
# on: `resolved_features`), so a `#[test]` behind any other feature compiles
# into no row. Measured 2026-11-13: clean-ck0's 22 export-reader tests
# (`export::*`, `minimal_env::overlay::tests`, all behind `export`) and 83 of
# clean-kernel's (cli 6, test-utils 17, reduction-stats 1, inference-stats 6,
# geometry-tools 53) ran in no row. These rows run them: each builds the lib's
# tests with the feature that gates them and selects only the gated modules
# (the plain lib row and its shards run the rest). One row per feature, never
# one row with every feature: a test may depend on a feature being OFF.
#
# `lib_test_coverage_problems` re-derives, from the sources, every test the
# library may compile and refuses one that no lib row both compiles and
# selects: the rows below are typed, the check is not.
def _lib_row(package: str, features: str, filters: list[str]) -> dict[str, Any]:
    tag = features.replace(",", "+")
    return {
        "id": f"{package}::lib::features::{tag}",
        "package": package,
        # A filtered libtest process: the integration-target timeout floor, as
        # the release rows take.
        "kind": "test",
        "argv": ["targo", "--unverified", "test", "--locked", "-p", package, "--lib",
                 "--features", features] + (["--"] + filters if filters else []),
    }


FEATURE_LIB_ROWS: list[dict[str, Any]] = [
    # All 99 of clean-ck0's lib tests with `export` (77 run without it): the lib
    # builds in seconds, so the row needs no filter.
    _lib_row("clean-ck0", "export", []),
    # With `math-overlays`, which every clean-kernel test build has on (see
    # `resolved_features`); the one test behind its negation is in
    # LIB_TESTS_NO_ROW_RUNS.
    _lib_row("clean-kernel", "cli", ["cli::"]),
    _lib_row("clean-kernel", "test-utils", ["differential_baseline::"]),
    _lib_row("clean-kernel", "reduction-stats",
             ["tc::def_eq::proof_irrel::three_valued_tests::modes::"]),
    _lib_row("clean-kernel", "inference-stats",
             ["tc::infer_arc_memo::window_tests::", "tc::reduction_stats::inference::"]),
    _lib_row("clean-kernel", "geometry-tools", ["cert::"]),
]

# The packages whose lib tests `lib_test_coverage_problems` derives. Another
# package joins by adding its rows above and its name here; until then its
# feature-gated lib tests are unaccounted, as these two were.
FEATURE_SCAN_PACKAGES = ("clean-kernel", "clean-ck0")

# What `check_cargo_test_selectors.TEST_BODY_RE` matches (a test asserts the
# two stay equal): an attribute body whose last path segment is `test`.
TEST_ATTR_BODY_RE = re.compile(r"\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*test\s*(?:\(.*)?", re.S)


# The bare cfg names a compiler or tool sets itself and `--print cfg` names
# when, and only when, they hold: absent from the lane's answer, each is FALSE
# for a `targo --unverified test` unit (`kani`, `miri`, `doc`, `doctest` and
# `clippy` are set only under those tools). Any other bare name the answer
# lacks stays undecided: it could come from a `--cfg` this does not read.
TOOL_SET_CFG_NAMES = ("debug_assertions", "trust_verify", "kani", "miri", "doc", "doctest", "clippy")

_LANE_CFG_CACHE: dict[str, dict[str, Any]] = {}


def _config_rustflags() -> list[str]:
    """The rustflags .cargo/config.toml gives the host target: the host's
    `[target.<triple>]` table when it has rustflags (cargo then ignores
    `[build]`'s), else `[build]`'s."""
    import tomllib

    path = REPO_ROOT / ".cargo" / "config.toml"
    try:
        cfg = tomllib.loads(path.read_text())
    except (OSError, ValueError):
        return []
    host = next((line.split(":", 1)[1].strip() for line in toolchain_id().split("|")
                 if line.startswith("host:")), "")
    flags = (cfg.get("target", {}).get(host, {}).get("rustflags")
             or cfg.get("build", {}).get("rustflags") or [])
    return [str(f) for f in flags]


def lane_cfg_facts(profile: str) -> dict[str, Any] | None:
    """The cfgs `targo --unverified test` compiles a unit with in `profile`,
    from the compiler's own `--print cfg` under the lane's flags
    (`-Ztrust-verify=off`, the config rustflags, the profile's
    debug-assertions); None (nothing decided) when it cannot be asked, when
    RUSTFLAGS could add a `--cfg`, or for an unknown profile."""
    if _compiler_env_selectors():
        return None
    if profile in _LANE_CFG_CACHE:
        return _LANE_CFG_CACHE[profile]
    env_flags = " ".join(os.environ.get(k, "") for k in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"))
    if "--cfg" in env_flags or "cfg" in env_flags.split():
        return None
    if profile == PROFILE_DEV:
        extra = ["-C", "debug-assertions=on"]
    elif profile == PROFILE_RELEASE:
        extra = ["-C", "debug-assertions=off"]
    else:
        return None
    code, out = run_capture(["trustc", "-Ztrust-verify=off"] + _config_rustflags() + extra
                            + ["--print", "cfg"])
    if code != 0:
        return None
    facts: dict[str, Any] = {name: False for name in TOOL_SET_CFG_NAMES}
    values: dict[str, set[str]] = {}
    for name, eq, value in (line.partition("=") for line in out.split()):
        if eq:
            values.setdefault(name, set()).add(value.strip('"'))
        else:
            facts[name] = True
    facts.update({name: frozenset(vals) for name, vals in values.items()})
    _LANE_CFG_CACHE[profile] = facts
    return facts


class _CargoTreeFailed(Exception):
    pass


def resolved_features(meta: dict[str, Any], package: str,
                      entry: dict[str, Any]) -> frozenset[str] | None:
    """The features cargo turns on for `package` in this row's test build, from
    cargo's own resolver (`targo tree -p <pkg> --depth 0 -f {f}`, dev edges
    included, the row's `--features`/`--no-default-features`/`--all-features`).

    Not the row's flags expanded through the feature table: a test build
    unifies features across dev-dependencies, and measured 2026-11-13 every
    `cargo test -p clean-kernel` build has `math-overlays` on (clean-parser and
    clean-elab, dev-dependencies of clean-kernel, enable it), so a target behind
    `#![cfg(feature = "math-overlays")]` with no `required-features` runs its
    tests in the plain row. Stored under the target dir while every workspace
    manifest and the lockfile keep their size and mtime; None when cargo
    cannot answer (nothing decided)."""
    feats, defaults, every = argv_features(entry.get("argv") or [])
    argv = ["targo", "tree", "--locked", "-p", package, "--depth", "0",
            "-e", "normal,build,dev", "--prefix", "none", "-f", "{f}"]
    if feats:
        argv += ["--features", ",".join(sorted(set(feats)))]
    if not defaults:
        argv.append("--no-default-features")
    if every:
        argv.append("--all-features")
    manifests = {Path(p["manifest_path"]) for p in meta["packages"]}
    manifests |= {REPO_ROOT / "Cargo.toml", REPO_ROOT / "Cargo.lock"}

    def compute() -> tuple[list[str], set[Path]]:
        try:
            proc = subprocess.run(argv, cwd=str(REPO_ROOT), stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, text=True, timeout=600, check=False)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise _CargoTreeFailed(str(exc)) from exc
        lines = proc.stdout.splitlines()
        if proc.returncode != 0 or not lines:
            raise _CargoTreeFailed(proc.stderr[-2000:])
        return sorted(f for f in lines[0].strip().split(",") if f), manifests

    try:
        value = _cached("resolved-features", tuple(argv), [], compute)
    except _CargoTreeFailed:
        return None
    return frozenset(value)


def argv_features(argv: list[str]) -> tuple[list[str], bool, bool]:
    """(`--features` values, defaults on, `--all-features`) of a cargo argv."""
    cargo, _ = _split_libtest_args(argv)
    feats: list[str] = []
    defaults, every = True, False
    i = 0
    while i < len(cargo):
        tok = cargo[i]
        if tok in ("--features", "-F") and i + 1 < len(cargo):
            feats.extend(f for f in re.split(r"[ ,]+", cargo[i + 1]) if f)
            i += 1
        elif tok.startswith("--features="):
            feats.extend(f for f in re.split(r"[ ,]+", tok[len("--features="):]) if f)
        elif tok == "--no-default-features":
            defaults = False
        elif tok == "--all-features":
            every = True
        i += 1
    return feats, defaults, every


def row_cfg_facts(meta: dict[str, Any], pkg: dict[str, Any],
                  entry: dict[str, Any]) -> dict[str, Any] | None:
    """The cfg facts one row compiles its package with: the lane's, and the
    features cargo resolves for the row (`resolved_features`); None when either
    cannot be asked or the package has a build script (which may emit a cfg)."""
    lane = lane_cfg_facts(entry_profile(entry))
    if lane is None or any("custom-build" in t.get("kind", []) for t in pkg.get("targets", [])):
        return None
    enabled = resolved_features(meta, pkg["name"], entry)
    return None if enabled is None else dict(lane, feature=enabled)


def _crate_tests(root: Path, reach: Any, facts: dict[str, Any] | None) -> dict[str, str]:
    """{libtest path: file} of every `#[test]` fn the walk names for the crate
    rooted at `root` (scripts/rust_modules.py: CERTAIN, what surely compiles;
    MAYBE, what may)."""
    rm = _rust_modules()
    out: dict[str, str] = {}
    for path, modpath in rm.walk(root, reach, None, True, facts):
        if modpath is None:
            continue
        for test_path, attrs in rm.fn_items(path, modpath, reach, True, facts):
            if any(TEST_ATTR_BODY_RE.fullmatch(a) for a in attrs):
                out[test_path] = str(path)
    return out


def lib_test_coverage(meta: dict[str, Any], package: str,
                      rows: list[dict[str, Any]]) -> dict[str, Any]:
    """What the package's lib rows run of the tests its library may compile.

    `gated`: tests MAYBE-compiled under the dev lane with every feature
    undecided, but not CERTAIN-compiled by the plain lib row (the features
    cargo resolves for `-p <pkg> --lib`). `uncovered`: those no dev `--lib` row
    both CERTAIN-compiles (its resolved features) and selects (its libtest
    filters). `release_only`: tests the plain release lib build CERTAIN-compiles
    and the plain dev one does not; `release_uncovered`: those no release
    `--lib` row compiles and selects. `undecided`: the lane facts or cargo's
    resolved features could not be asked."""
    pkg = next(p for p in meta["packages"] if p["name"] == package)
    root = package_lib_root(meta, package)
    lib_rows = [r for r in rows if r["package"] == package and "--lib" in
                _split_libtest_args(r.get("argv") or [])[0] and r.get("kind") != KIND_ROLLUP
                and not r.get("_parent")]
    if root is None:
        return {"gated": [], "uncovered": [], "release_only": [], "release_uncovered": []}
    rm = _rust_modules()
    dev = lane_cfg_facts(PROFILE_DEV)
    plain = {"argv": ["targo", "test", "-p", package, "--lib"]}
    default_dev = row_cfg_facts(meta, pkg, plain)
    default_rel = row_cfg_facts(meta, pkg, dict(plain, profile=PROFILE_RELEASE))
    if dev is None or default_dev is None or default_rel is None:
        return {"undecided": True}
    may = _crate_tests(root, rm.Reach.MAYBE, dict(dev))  # no `feature`: all undecided
    surely_default = set(_crate_tests(root, rm.Reach.CERTAIN, default_dev))
    gated = sorted(set(may) - surely_default)

    def covered(entries: list[dict[str, Any]], wanted: list[str]) -> set[str]:
        got: set[str] = set()
        for entry in entries:
            facts = row_cfg_facts(meta, pkg, entry)
            if facts is None:
                continue
            compiled = set(_crate_tests(root, rm.Reach.CERTAIN, facts)) & set(wanted)
            filters, skips, exact = _libtest_filters(_split_libtest_args(entry["argv"])[1])
            got |= (libtest_select(sorted(compiled), filters, skips, exact) if filters
                    else {n for n in compiled if not any(sk in n for sk in skips)})
        return got

    dev_rows = [r for r in lib_rows if entry_profile(r) == PROFILE_DEV]
    rel_rows = [r for r in lib_rows if entry_profile(r) == PROFILE_RELEASE]
    release_only = sorted(set(_crate_tests(root, rm.Reach.CERTAIN, default_rel)) - surely_default)
    return {"gated": gated, "uncovered": sorted(set(gated) - covered(dev_rows, gated)),
            "release_only": release_only,
            "release_uncovered": sorted(set(release_only) - covered(rel_rows, release_only))}


# Lib tests no row can run, each with the reason: an account, not a skip list.
# `lib_test_coverage_problems` refuses when the derived set of unrun lib tests
# differs from this in either direction, so a new one, a renamed one, or one
# a row starts running all go red.
LIB_TESTS_NO_ROW_RUNS: dict[str, dict[str, str]] = {
    "clean-kernel": {
        "cli::constructive_claims::tests::run_without_math_overlays_returns_feature_gate_error":
            "behind `not(feature = \"math-overlays\")`, which every `cargo test -p "
            "clean-kernel` build turns on: clean-parser and clean-elab, dev-dependencies of "
            "clean-kernel, enable it, and cargo unifies a test build's features (measured "
            "2026-11-13 with `targo tree -p clean-kernel --depth 0 -f {f}`). No test build of "
            "the package compiles it",
    },
}


def lib_test_coverage_problems(meta: dict[str, Any], rows: list[dict[str, Any]]) -> list[str]:
    """One message per feature- or profile-gated lib test no row runs and
    LIB_TESTS_NO_ROW_RUNS does not account for (and per stale account), for
    every package in FEATURE_SCAN_PACKAGES the rows hold. Stored under the
    target dir while the package's sources, every workspace manifest, the
    lockfile, the rows' argv and the lane facts are unchanged."""
    problems: list[str] = []
    scanned = {r["package"] for r in rows}
    manifests = {Path(p["manifest_path"]) for p in meta["packages"]}
    manifests |= {REPO_ROOT / "Cargo.toml", REPO_ROOT / "Cargo.lock"}
    dev, rel = lane_cfg_facts(PROFILE_DEV), lane_cfg_facts(PROFILE_RELEASE)
    facts_key = json.dumps([sorted((k, sorted(v) if isinstance(v, frozenset) else v)
                                   for k, v in (f or {}).items()) for f in (dev, rel)])
    for package in FEATURE_SCAN_PACKAGES:
        pkg = next((p for p in meta["packages"] if p["name"] == package), None)
        if pkg is None or package not in scanned:
            continue
        row_argv = sorted(" ".join(r["argv"]) + "|" + entry_profile(r)
                          for r in rows if r["package"] == package)

        def compute(package: str = package) -> tuple[dict[str, Any], set[Path]]:
            return lib_test_coverage(meta, package, rows), manifests

        result = _cached("lib-test-coverage",
                         (package, hashlib.sha256("\n".join(row_argv).encode()).hexdigest(),
                          hashlib.sha256(facts_key.encode()).hexdigest()),
                         [Path(pkg["manifest_path"]).parent], compute)
        if result.get("undecided"):
            problems.append(f"{package}: the lane's cfg facts or cargo's resolved features could "
                            "not be asked, so which lib tests a row compiles cannot be decided")
            continue
        accounted = LIB_TESTS_NO_ROW_RUNS.get(package, {})
        unrun = set(result["uncovered"]) | set(result["release_uncovered"])
        for name in sorted(unrun - set(accounted)):
            why = ("is release-only and no release `--lib` row compiles and selects it"
                   if name in result["release_uncovered"] else
                   "compiles only with a feature no `--lib` row enables and selects")
            problems.append(f"{package}: lib test {name} {why} (FEATURE_LIB_ROWS, "
                            "RELEASE_PROFILE_TARGETS)")
        for name in sorted(set(accounted) - unrun):
            problems.append(f"{package}: LIB_TESTS_NO_ROW_RUNS names {name}, which is not an "
                            "unrun lib test (a row runs it, or it is gone): remove it")
    return problems


def root_compiles_nothing(root: Path, facts: dict[str, Any] | None) -> str | None:
    """The crate root's inner `#![cfg(..)]` that `facts` decide FALSE (so the
    crate compiles to nothing), or None."""
    if facts is None:
        return None
    rm = _rust_modules()
    try:
        lx = rm._lex(root.read_text(encoding="utf-8", errors="replace"))
    except OSError:
        return None
    if lx is None:
        return None
    for code, at in rm._attrs(lx, 0, None, True):
        head = re.match(r"\s*(\w+)\s*", code)
        if not head or head.group(1) != "cfg":
            continue
        pred = lx.kept[at + head.end():at + len(code)]
        if rm.rust_cfg().cfg(pred, facts) is False:
            return "#![cfg" + pred.strip() + "]"
    return None


def _test_target_name(argv: list[str]) -> str | None:
    """The `--test X` a cargo test argv names before `--`, or None."""
    cargo, _ = _split_libtest_args(argv)
    for i, tok in enumerate(cargo):
        if tok == "--test" and i + 1 < len(cargo):
            return cargo[i + 1]
        if tok.startswith("--test="):
            return tok[len("--test="):]
    return None


def compiled_out_rows(meta: dict[str, Any], inv: list[dict[str, Any]]) -> dict[str, str]:
    """{row id: the root's `#![cfg]`} for each integration-test row whose
    target root that row's own facts (lane, profile, features) decide compiles
    to nothing. Such a row can only ever record zero tests."""
    out: dict[str, str] = {}
    for entry in inv:
        name = _test_target_name(entry.get("argv") or [])
        if name is None or entry["package"] == "__workspace__":
            continue
        pkg = next((p for p in meta["packages"] if p["name"] == entry["package"]), None)
        tgt = pkg and next((t for t in pkg["targets"]
                            if t["name"] == name and "test" in t.get("kind", [])), None)
        if not tgt or not tgt.get("src_path"):
            continue
        facts = row_cfg_facts(meta, pkg, entry)
        why = root_compiles_nothing(Path(tgt["src_path"]),
                                    None if facts is None else dict(facts, test=True))
        if why:
            out[entry["id"]] = why
    return out


def debug_test_row(package: str, tgt: dict[str, Any]) -> dict[str, Any]:
    """The unsplit debug row `package_targets` derives for test target `tgt`."""
    return {
        "id": f"{package}::test::{tgt['name']}",
        "package": package,
        "kind": "test",
        "argv": ["targo", "--unverified", "test", "--locked", "-p", package,
                 "--test", tgt["name"]] + required_features_argv(tgt),
    }


def compiled_out_problems(meta: dict[str, Any], inv: list[dict[str, Any]]) -> list[str]:
    """A row that compiles its target to nothing is refused: such a target
    gets a release row that runs it whole and names it in
    `_replaces_debug_target` (`package_targets` then derives no debug row for
    it). A `_replaces_debug_target` naming a target that a debug build does
    compile (or whose root's cfg cannot be decided), or no test target at all,
    is refused too, so the pair cannot outlive the cfg that made it."""
    problems: list[str] = []
    for rid, why in sorted(compiled_out_rows(meta, inv).items()):
        problems.append(f"{rid}: its target root's `{why}` compiles it to nothing in this "
                        "row's profile and features, so the row records zero tests; give it a "
                        "release row that runs it whole and names it in `_replaces_debug_target`")
    for entry in inv:
        name = entry.get("_replaces_debug_target")
        pkg = name and next((p for p in meta["packages"] if p["name"] == entry["package"]), None)
        if not pkg:
            continue
        tgt = next((t for t in pkg["targets"]
                    if t["name"] == name and "test" in t.get("kind", [])), None)
        if tgt is None:
            problems.append(f"{entry['id']}: `_replaces_debug_target` names {name}, which is no "
                            f"test target of {entry['package']}")
        elif not compiled_out_rows(meta, [debug_test_row(entry["package"], tgt)]):
            problems.append(f"{entry['id']}: `_replaces_debug_target` names {name}, whose root "
                            "a debug build does not decide out: drop the field so its debug "
                            "row returns")
    return problems


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
            base = ["targo", "--unverified", "test", "--locked", "-p", package, "--lib"]
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
            # A wholly release-only target has one executable suite row, not
            # an additional debug row that can only report zero tests.
            if any(row["package"] == package and row.get("_replaces_debug_target") == tgt["name"]
                   for row in RELEASE_PROFILE_TARGETS):
                continue
            base_argv = debug_test_row(package, tgt)["argv"]
            split = TEST_SPLITS.get(tgt["name"])
            if split:
                for suffix, extra in split:
                    out.append(
                        {
                            "id": f"{package}::test::{tgt['name']}::{suffix}",
                            "package": package,
                            "kind": "test",
                            "argv": base_argv + ["--"] + extra,
                        }
                    )
            else:
                out.append(
                    {
                        "id": f"{package}::test::{tgt['name']}",
                        "package": package,
                        "kind": "test",
                        "argv": base_argv,
                    }
                )
    # The lib's feature-gated tests (FEATURE_LIB_ROWS): copies, because
    # build_inventory writes `_dirs` into each row it is handed.
    out.extend(dict(row) for row in FEATURE_LIB_ROWS if row["package"] == package)
    return sorted(out, key=lambda t: t["id"])


# Integration targets that cannot finish as ONE unit, split by libtest name
# filter. This is the integration-target analogue of the `clean-verify::lib`
# shard plan above, and it exists for the same reason: a target that never
# finishes records ERROR forever, and an ERROR is a measurement thrown away, not
# a verdict.
#
# `crystal_a3_semdiff` is the measured case (2026-09-09, re-stated in
# docs/CRYSTAL_BACKLOG.md). Its last three recorded states are budget kills at
# 7,200 / 14,400 / 28,800 s, and `b6e5ec2fd` read that as "the target has
# outgrown any single-process budget". Timed alone on an idle box with
# `--test-threads=1` the shape is narrower and far more actionable: the first
# TEN of its 23 tests finish in 12m51s, then
# `crystal_a3_semdiff_wide_measures_encoding_agreement` runs for 2h50m+ with
# twelve still queued behind it. Every recorded kill died in that ONE test with
# its predecessors green. So the target is nine-tenths cheap and one test
# unbounded, and cutting there makes 22 of 23 measurable in a quarter of an hour
# instead of never.
#
# SECOND CUT, 2026-09-20. Isolating that test into a `wide` row did not make it
# finish -- `wide` then recorded its own 7200 s timeout. Measured after sharding
# it per wide chain: NINE chains record GREEN in 72-218 s each, and
# `get_char_val_trunc` alone runs past 26 min, CPU-bound at a steady 0.6 GB
# (five inputs, one of them u64::MAX). One pathological chain was hiding nine
# healthy ones, and a timeout destroyed all ten verdicts together.
#
# The cut is by NAME, so it cannot silently drift: `--skip` and `--exact` are
# complementary over the same string, and `check_cargo_test_selectors.py`
# refuses a filter that provably selects nothing. Both halves run >0 tests, so
# neither can be demoted by the zero-test guard for the wrong reason.
TEST_SPLITS: dict[str, list[tuple[str, list[str]]]] = {
    # `crystal_a3_semdiff`'s W1 gate used to be ONE test over all ten wide
    # chains, and it never finished: the rows recorded `timed out after 28800s`
    # and `after 7200s`, exit -1. A target that times out records ERROR, and an
    # ERROR is a measurement thrown away — so the repo's only two-machine
    # semantic-agreement evidence was being discarded wholesale.
    #
    # Sharded 2026-09-20 into one test per chain
    # (`crystal_a3_semdiff_w1chain_*`), each its own row here so one slow or
    # failing chain cannot take the other nine down with it.
    #
    # The `w1chain_` prefix is load-bearing: `rest` skips exactly the shards,
    # and the two cheap guards (`crystal_a3_semdiff_w1_shards_cover_every_wide_chain`,
    # `crystal_a3_semdiff_w1_reports_irinst_coverage`) deliberately do NOT carry
    # it, so they keep running in `rest`. The first of those is what stops a
    # chain being added to `wide_chains()` and silently never measured.
    "crystal_a3_semdiff": [
        ("w1_bvar_in_range", ["--exact", "crystal_a3_semdiff_w1chain_bvar_in_range"]),
        ("w1_is_valid_char", ["--exact", "crystal_a3_semdiff_w1chain_is_valid_char"]),
        ("w1_flat_flags_contains", ["--exact", "crystal_a3_semdiff_w1chain_flat_flags_contains"]),
        ("w1_flat_flags_with", ["--exact", "crystal_a3_semdiff_w1chain_flat_flags_with"]),
        ("w1_node_id_index", ["--exact", "crystal_a3_semdiff_w1chain_node_id_index"]),
        ("w1_get_char_val_trunc", ["--exact", "crystal_a3_semdiff_w1chain_get_char_val_trunc"]),
        ("w1_has_loose_bvars", ["--exact", "crystal_a3_semdiff_w1chain_has_loose_bvars"]),
        ("w1_loose_bvar_range", ["--exact", "crystal_a3_semdiff_w1chain_loose_bvar_range"]),
        ("w1_strict_monads", ["--exact", "crystal_a3_semdiff_w1chain_strict_monads"]),
        ("w1_simp_priority_value", ["--exact", "crystal_a3_semdiff_w1chain_simp_priority_value"]),
        ("rest", ["--skip", "crystal_a3_semdiff_w1chain_"]),
    ],
}


# The workspace gates, spelled exactly as CLAUDE.md's "Before pushing --
# the real gate" spells them. `--workspace --all-targets` is load-bearing:
# `default-members` narrows a bare `cargo check`/`clippy` to 8 of 27 crates and
# 85 of 521 targets, so the bare forms are an inner loop, never a coverage claim.
WORKSPACE_GATES = [
    {
        "id": "gate::check",
        "package": "__workspace__",
        "kind": "gate",
        "argv": ["targo", "--unverified", "check", "--locked", "--workspace", "--all-targets"],
    },
    # `scripts/rust_frontend.sh` (which runs `targo tippy` / `targo fmt` and has
    # no stock fallback) keeps these rows' argv stable across driver renames.
    # The resolver changes the DRIVER, never the check: the flags below are the
    # same `--workspace --all-targets ... -D warnings` the pre-push gate has
    # always run. gate::check is spelled with targo's unverified lane directly.
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
        # `fmt --all --check` aborts on the Trust island form and exits 1 with
        # zero diffs reported (measured 2026-09-15) -- it cannot answer this
        # row's question. `--all` is the same predicate without that hole.
        "argv": ["python3", "scripts/check_fmt_changed.py", "--all"],
        "_extra_paths": ["scripts/check_fmt_changed.py"],
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
    # The Mathlib SOURCE-elaboration measurement (SRCELAB), added 2026-08-23 for
    # the same reason gate::paragon was: NOTHING RAN IT. `scripts/source_elab_gate.sh`
    # landed 2026-07 with a verdict-line contract, a ratchet artifact and its own
    # 26-case self-test, and for six weeks the only caller was a human typing it
    # by hand. Its ratchet sat UNARMED with all-zero baselines the whole time, and
    # three of its four pinned files had never been measured end to end -- so the
    # one number the repo has for "Clean elaborates real Mathlib source" could
    # regress to zero without anything going red.
    #
    # It is a `gate-measure`, not a `gate`: it compiles nothing and lints nothing.
    # It runs the RELEASE `clean` binary over FIVE pinned Mathlib .lean files
    # through Clean's own parser -> elaborator -> kernel and enforces that each
    # file's success count never drops below data/source_elab_ratchet.json.
    #
    # The slice grew from four to five on 2026-08-23 (Mathlib/Order/Basic.lean
    # added, and Mathlib/Logic/Unique.lean un-capped because the ~19.5 GB OOM
    # that forced its line-240 cap no longer reproduces -- 3.13 GiB measured for
    # the full file).
    #
    # `--jobs` deliberately STAYS AT 4. Five concurrent processes would be five
    # olean closures at ~6 GB each, i.e. ~30 GB against the ~15 GB this row's
    # gate weight was learned from -- and _gate_weight_gb only re-learns AFTER a
    # run, so the first five-wide pass would run under-reserved on a box whose
    # 2026-08-19 kernel panic was caused by exactly that: many medium processes
    # at once. At --jobs 4 the fifth file backfills the first freed slot, so the
    # peak is unchanged and the wall grows by the SHORTEST file rather than by a
    # whole wave -- a few hundred seconds on a row with a 43,200 s floor.
    #
    # COST, measured 2026-08-23 at a86c5ffd6 on this box with --jobs 4, against
    # real Mathlib v4.30.0-rc2 oleans, sharing the box with five other lanes:
    #   Mathlib/Logic/Basic.lean          12,905 s   151/256 success
    #   Mathlib/Logic/Function/Basic.lean 10,125 s    77/230
    #   Mathlib/Data/Subtype.lean          1,698 s    13/45
    #   Mathlib/Logic/Unique.lean:1-240      489 s     8/35
    # 25,217 s of CPU; 12,906 s (3 h 35 min) of WALL, i.e. max(file), which is
    # why `--jobs 4` is load-bearing: serially this row is the SUM, 7 CPU-hours,
    # and that is how the ratchet went un-armed for six weeks. Peak RSS was
    # ~6 GB per process, ~15 GB for the four. The 43,200 s `gate-measure` floor
    # is ~3.3x the measured wall, and the runner replaces it with 4x the row's
    # own last duration as soon as it has one.
    #
    # TWO HONESTY NOTES, both of which a reader of this row must apply:
    #
    #   1. It SKIP-GREENS (exit 0, verdict `SRCELAB_GATE=skipped:<reason>`) when
    #      target/release/clean or the Mathlib checkout is absent -- deliberate,
    #      so clones without a 4 GB olean corpus are not permanently red, and the
    #      same discipline scripts/kv_ratchet_gate.sh uses. This runner records
    #      the gate's verbatim final line, which IS the verdict line, so
    #      `verify_runner.sh status` shows `SRCELAB_GATE=measured` for a real
    #      measurement and `SRCELAB_GATE=skipped:no-binary` for a deferral. A
    #      GREEN on this row whose reason starts with `skipped:` measured NOTHING.
    #      The suite does not build the release binary; that is a prerequisite.
    #   2. The Mathlib checkout is OUTSIDE the repository and therefore outside
    #      the input digest -- the same documented exclusion this runner already
    #      carries for `.olean` corpora. A corpus that moves does not demote this
    #      row's green; the recorded per-file decl counts in
    #      reports/source-elab/ are how a reader notices.
    #
    # It never passes --update: arming a ratchet is a deliberate act with a report
    # behind it, never a side effect of the suite running.
    {
        "id": "gate::self-proof-elab",
        "package": "__workspace__",
        "kind": "gate-measure",
        "argv": ["python3", "scripts/self_proof_elab_probe.py"],
        "_extra_paths": [
            "scripts/self_proof_elab_probe.py",
            "reports/self-proof-elab/baseline.json",
            "theories/cic_l", "theories/cic_l_model", "theories/kcheck",
            "theories/kcheck_spec", "theories/kcheck_labelled",
        ],
    },
    {
        "id": "gate::srcelab",
        "package": "__workspace__",
        "kind": "gate-measure",
        "argv": ["scripts/source_elab_gate.sh", "--jobs", "4"],
        # The verdict is decided against the ratchet, computed by the classifier
        # and driven by the pinned slice inside the gate script -- none of which
        # is inside a crate directory, so without these an edit to any of them
        # would leave a recorded green reading fresh.
        "_extra_paths": [
            "scripts/source_elab_gate.sh",
            "scripts/srcelab_classify.py",
            # The per-declaration guard and the performance leg (2026-09-24)
            # decide part of the verdict too.
            "scripts/srcelab_decl_guard.py",
            "scripts/srcelab_perf.py",
            "data/source_elab_ratchet.json",
        ],
    },
    # The constructive-theorem SET ratchet, added 2026-08-25 for the third time
    # the same reason has come up: NOTHING RAN IT. `check_constructive_ratchet.py`
    # landed 2026-04 and was invoked by no runner in the tree -- it was the live
    # instance `scripts/check_gate_registry.py` cites in its own module docstring.
    # Its only fellow reader of `data/constructive_ratchet.json` was a pair of
    # unwired `scripts/audits/prover_*_audit.sh` ratchets, retired 2026-08-25, so
    # the property was enforced NOWHERE.
    #
    # And it is a property no other gate has: the NAMES of the clean-native
    # theorems with an empty transitive domain-axiom closure. `tcb_target_ratchet`
    # pins the axiom census (3 foundational / 0 domain) and does not move by one
    # when a constructive theorem silently DISAPPEARS. `axiom_audit.json`'s
    # `constructive_theorems` sums `theorems` over conjecture rows flagged
    # `constructive: true` -- a different population (265 there, 318 here).
    #
    # It lives here rather than in `local_gate.sh` for two reasons, both
    # measured. It shells out to a release `mathverse_shard build-native`, which
    # is minutes of cargo -- that cost is exactly why it fell out of every cheap
    # path and drifted for two months. And `do_check` accepts arbitrary drift
    # when `data/constructive_ratchet.json` is STAGED, an escape hatch that is
    # inert in a detached pinned worktree where nothing is ever staged, and would
    # be a live bypass in a pre-push leg. Falsifiability is
    # `scripts/test_constructive_ratchet.py` (10 arms on do_check + 4 on the
    # refresh path, in the `check_script_selftests.sh` suite); gutting `do_check`
    # turns all 10 red. Arms 8-10 (lane LOOSE, 2026-08-25) pin the
    # `Classical.choice` exception set as part of the baseline: `Constructive`
    # here means "no DOMAIN axiom", and Classical.choice IS foundational, so 2 of
    # the 396 are excluded middle counted "constructive". That set now moves only
    # through --update --notes -- the staged-file escape hatch does not cover it.
    {
        "id": "gate::constructive",
        "package": "__workspace__",
        "kind": "gate",
        "argv": ["python3", "scripts/check_constructive_ratchet.py"],
        # The gate MEASURES crates/clean-mathverse (covered by the workspace
        # dirs) but DECIDES against data/constructive_ratchet.json, using the
        # comparison in the script. Neither is inside a crate dir, so without
        # this a baseline edit or a comparison edit would leave a recorded green
        # reading fresh.
        "_extra_paths": [
            "data/constructive_ratchet.json",
            "scripts/check_constructive_ratchet.py",
        ],
    },
    # The ALWAYS-ON M1/M2/M4 MASQUERADE gate over the registered kernel corpus,
    # added 2026-08-25 (lane MASQ) for the fourth instance of the same story:
    # NOTHING RAN IT ON PURPOSE. It is a `#[test]` in
    # `crates/clean-kernel/src/env/tests_masquerade_gate.rs`, so it moves only
    # when somebody runs `cargo test -p clean-kernel --lib` or a whole-workspace
    # sweep -- neither of which is in local_gate.sh, the hook, or this suite. The
    # masquerade vector was therefore guarded by a test with no scheduled runner,
    # while the only other artifact aimed at it (`scripts/masquerade_gate/`, a
    # five-file Python fragment) could not even be imported: its `__main__.py`
    # imports a `cli` module that has never existed in this repo's history.
    # RETIRED 2026-08-25, superseded by this row -- see the registry's `retired`
    # list.
    #
    # It lives here rather than in local_gate.sh for one measured reason: it is a
    # BUILD. Measured 2026-08-25 at 0b3b94e5b on an 18-core box with two other
    # lanes loading the machine: ~25 min from an empty target dir, then 24.9 s of
    # test. Nothing that costs a cold clean-kernel test build belongs in a
    # pre-push leg. Warm, the run is seconds -- which is what makes it a suite
    # row rather than a battery nobody schedules.
    #
    # No `_extra_paths`: the gate MEASURES the registered corpus, which is
    # crates/clean-kernel/src/env/nn_verify_*.rs plus the prelude, and every one
    # of those is inside a crate directory already covered by the workspace
    # digest. An edit to any of them demotes this row's green to UNKNOWN, which
    # is exactly the wanted behaviour: a new registration is a new theorem to
    # scan.
    {
        "id": "gate::masquerade",
        "package": "__workspace__",
        "kind": "gate",
        "argv": [
            "targo", "--unverified", "test", "--locked", "-p", "clean-kernel", "--lib",
            "--", "masquerade",
        ],
    },
    # The FENCE: the acceptance tests of the Lean-reference entry
    # (`clean_kernel::reference`, the authority until `kcheck` holds it), added
    # 2026-11-12 by self-proof unit F2 for the reason every row above was added:
    # NOTHING SCHEDULED THEM. They are integration tests of `clean-kernel`, which
    # is not one of DEFAULT_PACKAGES, so no `<package>::test::*` row is derived
    # for them and they ran only when somebody ran the whole crate.
    #
    # Four binaries, one row: `reference_entry` (KR0: the refusals and their
    # controls), `reference_entry_folds` (unit F1: the entry over the prelude
    # with the kernel's Clean-only folds gated on the theory),
    # `reference_tripwires` and `reference_ax0` (KR1: the closure rules). The
    # halves that need the native-fold authority bypass or the pinned Lean
    # `Init` live in clean-olean and are ordinary rows already
    # (`clean-olean::test::reference_entry_fold_theory`, `_fold_controls`,
    # `_string_drop`, `_base_recheck`).
    #
    # A `targo --unverified test` row, so `_build_phase_argv` splits it and the
    # run phase does not hold the compile's reservation. No `_extra_paths`: the
    # subject is clean-kernel's source, inside the workspace digest.
    # Q4's standing result is fail-closed: a red/missing/stale record or an
    # unavailable member stays red. This reads evidence; it builds nothing.
    {
        "id": "gate::kstar-recheck",
        "package": "__workspace__",
        "kind": "gate",
        "argv": ["scripts/kstar_recheck.sh", "--check-record",
                 "reports/self-proof-q4-residuals-2026-11-15/replay/replay.json"],
        "_extra_paths": ["scripts/kstar_recheck.sh", "scripts/kstar_recheck.py",
                         "scripts/kstar_selftest.py", "scripts/kstar_subjects.py",
                         "scripts/kstar_subjects_selftest.py",
                         "scripts/lean4lean_recheck.py", "scripts/lean4lean_selftest.py",
                         "scripts/nanoda_recheck.py", "scripts/lean_export_replay",
                         "data/lean4lean_q4_pin.json", "data/lean4lean_q4_arena_reasons.json",
                         "theories/cic_l", "reports/self-proof-q4-residuals-2026-11-15/replay/replay.json"],
    },
    {
        "id": "gate::fence",
        "package": "__workspace__",
        "kind": "gate",
        "argv": [
            "targo", "--unverified", "test", "--locked", "-p", "clean-kernel",
            "--test", "reference_entry", "--test", "reference_entry_folds",
            "--test", "reference_tripwires", "--test", "reference_ax0",
        ],
    },
    # The FOREIGN-KERNEL cross-check, added 2026-08-28 for the fourth time the
    # same reason has come up: NOTHING RAN IT. `scripts/self_verify_crosscheck.sh`
    # is the referee-runnable form of SELF_VERIFICATION_CERTIFICATE.md section 4 --
    # it exports the whole live `Specification` environment as one self-contained
    # Lean 4 file and has an INDEPENDENT kernel with a disjoint implementation
    # re-check every emitted declaration. It is the strongest evidence in the
    # programme that Clean's kernel is not systematically wrong in its own favour,
    # and it is the one thing here that no amount of in-tree gating can substitute
    # for, because every other gate is Clean checking Clean.
    #
    # It had no runner and no registry row. The certificate says "keep re-running
    # at each release checkpoint" and the roadmap repeats it; in practice a human
    # had to remember. It was last run 2026-08-11 and re-run 2026-08-28 -- and it
    # was RED, on the zero-skip invariant, with 746 declarations no longer being
    # independently checked. Seventeen days of silent non-greenness is exactly the
    # window a registry row closes.
    #
    # `gate-measure`, like gate::srcelab: it lints nothing. It builds lean_export
    # in release, runs it (which builds the live spec, ~19 min), then runs the
    # PINNED Lean toolchain over the emitted file. The 43,200 s floor is what it
    # needs; the heavy_gate slot is taken by the caller, not here.
    #
    # It asserts INVARIANTS, not counts -- Lean accepts everything, exactly the 3
    # foundational axioms, zero skips, 100% coverage, flagship closures reach no
    # axiom -- so it stays meaningful as the spec grows instead of going stale the
    # way a pinned total would.
    {
        "id": "gate::leancross",
        "package": "__workspace__",
        "kind": "gate-measure",
        "argv": ["scripts/self_verify_crosscheck.sh"],
        # The spec content lives under crates/ and is covered by the workspace
        # dirs, but the DECIDING logic does not: the harness holds the invariant
        # thresholds and the pinned Lean toolchain, and the exporter decides what
        # is emittable at all -- the 4096 ctor-normal-form Nat cap in printer.rs is
        # what turned this row red. Without these an edit to the harness or the
        # printer would leave a recorded green reading fresh, which is the precise
        # failure `_dir_content_digest` exists to prevent.
        "_extra_paths": [
            "scripts/self_verify_crosscheck.sh",
            "crates/clean-verify/src/bin/lean_export/main.rs",
            "crates/clean-verify/src/bin/lean_export/audit_roots.rs",
            "crates/clean-verify/src/bin/lean_export/audit_roots/projection.rs",
            "crates/clean-verify/src/bin/lean_export/emit.rs",
            "crates/clean-verify/src/bin/lean_export/printer.rs",
            "crates/clean-verify/src/bin/lean_export/comparison_bridge.rs",
        ],
    },
]


# RELEASE-PROFILE ROWS (docs/DECISIONS.md R148, 2026-10-19).
#
# Some tests compile ONLY in a release build. The `replay_forged` lane tests for
# leanprover/lean4#14807 (`is_prop` requires a sort; a live Clean soundness hole
# until the guard landed, R84) sit behind `#[cfg(not(debug_assertions))]`: their
# fixture imports `Init.WF`, whose closure a debug build did not finish loading
# in 17 min where release takes ~24 s. A debug build therefore does not compile
# them, and every package row this runner enumerates is a debug build -- so
# `clean-olean::lib` and `clean-olean::test::replay_forged_lanes` go GREEN
# without running them, and clean-mathverse is not on the default board at all.
# Before these rows nothing routine reached the pins of that hole.
#
# A release row is a target in its own right, and three things keep a debug
# result from ever standing for it:
#
#   1. its id carries `::release::`, so it shares no record with a debug row;
#   2. its `profile` is written into every record it produces AND hashed into
#      its input digest, and `derive` refuses a record whose profile is not the
#      row's (a record with no `profile` field is a debug one);
#   3. its argv carries `--release` before any `--`, which `check_profiles`
#      refuses to let drift at inventory time, so the field cannot lie.
#
# And a release row names the tests it EXISTS for (`_must_pass`). It is GREEN
# only when the run printed `test <name> ... ok` for every one of them. A build
# that compiles them out -- a debug build, a cfg edit, a rename, a filter that
# stops selecting them -- exits 0 having run the rest, which the zero-test guard
# cannot see; that record reads UNKNOWN, naming what did not run.
#
# The rows are on the board whatever `--packages` says, like the workspace
# gates: they are the only routine path to these tests, so a person running
# `run` or `status` with no flags gets them. Each row runs the WHOLE target or
# module its filter names (all of `replay_forged_lanes`, all of the mathverse
# battery module), not only the release-only tests, so the release build is
# measured over the family the release-only tests belong to.
#
# A release row also carries the highest build peak measured for it, cold or
# warm (`_cold_build_peak_gb`), and its build phase reserves at least 1.5x
# that, whatever its own record learned. The rows share one target dir, so a
# row's learned build weight depends on which builds ran before it: measured
# 2026-10-19/20, the integration-test row's build ran after the lib row's had
# built its dependencies and peaked at 4.81 GB, which learns 8 GB, while three
# cold builds of it in fresh target dirs peaked at 8.84, 8.94 and 8.97 GB.
# `--only` one row, a fresh or pruned `release/` dir, or another order would
# have run that cold build under its own peak. heavy_gate's label-class floor
# does not catch it: an `acquire` ticket never reaches its peaks log.
# The field is named for the premise that a cold build costs the most. That
# premise is refuted: the lib row's cold build peaked at 5.97 GB and its later
# builds in the shared dir at 7.74 to 7.99 GB (2026-10-28, R190). The name
# stays; the figure is the highest peak measured, whichever build reached it.
# `check_profiles` refuses a release row without the field.
#
# kind `test`: each row is one filtered libtest process, so it takes the
# integration-target timeout floor and is dispatched with the integration rows.
PROFILE_DEV = "dev"
PROFILE_RELEASE = "release"
PROFILES = (PROFILE_DEV, PROFILE_RELEASE)

RELEASE_PROFILE_TARGETS: list[dict[str, Any]] = [
    {
        "id": "clean-kernel::release::test::release_infer_parity",
        "package": "clean-kernel",
        "kind": "test",
        "profile": PROFILE_RELEASE,
        "_replaces_debug_target": "release_infer_parity",
        "argv": ["targo", "--unverified", "test", "--locked", "--release",
                 "-p", "clean-kernel", "--test", "release_infer_parity"],
        "_must_pass": [
            "infer_parity_release_matches_certified_wave0_corpus",
            "infer_parity_release_matches_certified_local_context_paths",
            "infer_parity_release_matches_certified_error_paths",
            "infer_parity_release_matches_certified_error_locations",
            "infer_parity_release_matches_certified_cubical_mode_paths",
            "infer_parity_release_matches_certified_set_theoretic_paths",
            "infer_parity_release_matches_certified_impredicative_paths",
            "infer_parity_release_matches_certified_mode_error_paths",
            "infer_parity_release_type_cache_hits_on_repeated_closed_terms",
        ],
        # Highest build peak: 31.11 GB in the runner (cold run: 15.67 GB).
        # reports/self-proof-e3-release-infer-2026-11-13 retains both runs.
        # The E3 fix-up's: 15.33 GB in a fresh target dir (heavy_gate
        # `e3fix-kernel-release-test-build`, 2026-11-14T00:44:53Z), 7.82 GB in
        # the pinned runner at `7287e7f13` after the lib row below had built.
        # `package_cold_build_peak_gb` carries this figure to every release
        # build of the package.
        "_cold_build_peak_gb": 31.11,
    },
    {
        "id": "clean-olean::release::test::replay_forged_lanes",
        "package": "clean-olean",
        "kind": "test",
        "profile": PROFILE_RELEASE,
        "argv": ["targo", "--unverified", "test", "--locked", "--release",
                 "-p", "clean-olean", "--test", "replay_forged_lanes"],
        "_must_pass": [
            "test_verify_batch_full_lanes_projection_needs_a_sort_typed_type",
        ],
        # The highest of three cold build peaks (see above). No build of this
        # row journalled since has peaked higher: 8.94 GB over 193 samples,
        # 387.5 s, cold at c366ddfda, and 4.81 to 6.71 GB warm. The committed
        # record (1c37721b5, at fde616a28) says 6.71 GB.
        "_cold_build_peak_gb": 8.97,
    },
    {
        "id": "clean-olean::release::lib::replay_module",
        "package": "clean-olean",
        "kind": "test",
        "profile": PROFILE_RELEASE,
        "argv": ["targo", "--unverified", "test", "--locked", "--release",
                 "-p", "clean-olean", "--lib", "--", "replay_module::tests"],
        "_must_pass": [
            "replay_module::tests::is_prop_sort::"
            "test_replay_module_projection_needs_a_sort_typed_type",
            # Release-only since R150 (its module imports all of `Init`).
            "replay_module::tests::level_equiv::"
            "test_replay_module_admits_honest_wf_universe_levels",
        ],
        # The highest build peak measured for this row, raised 2026-10-28: 7.99 GB
        # over 136 samples, 273.0 s, the committed record (1c37721b5: a run at
        # fde616a28 finished 2026-10-27T10:51:57Z, built in the shared release
        # target dir after the mathverse row). The cold build in a fresh target
        # dir, 2026-10-20 at c366ddfda, peaked at 5.97 GB over 144 samples,
        # 289.3 s; every build of it journalled since 2026-10-22 peaked above
        # that (7.74, 7.87 and 7.99 GB), so the cold figure alone sat under the
        # measurement. A floor is never below a measured build peak.
        "_cold_build_peak_gb": 7.99,
    },
    {
        "id": "clean-mathverse::release::lib::replay_forged_lane_tests",
        "package": "clean-mathverse",
        "kind": "test",
        "profile": PROFILE_RELEASE,
        "argv": ["targo", "--unverified", "test", "--locked", "--release",
                 "-p", "clean-mathverse", "--lib", "--", "cli::replay_forged_lane_tests"],
        "_must_pass": [
            "cli::replay_forged_lane_tests::is_prop_sort::"
            "test_stamp_verified_all_modes_projection_needs_a_sort_typed_type",
            "cli::replay_forged_lane_tests::is_prop_sort::"
            "test_sharded_verify_module_projection_needs_a_sort_typed_type",
            "cli::replay_forged_lane_tests::is_prop_sort::"
            "test_per_constant_verify_projection_needs_a_sort_typed_type",
        ],
        # The highest build peak measured for this row, raised 2026-10-28:
        # 13.89 GB over 383 samples, 771.5 s, a GREEN run at fec2d64d6 finished
        # 2026-10-27T06:11:32Z, journalled for the clean-land-r5 projection
        # (suite-journal `suite-state-af837c3433d2.jsonl`). The committed record
        # (1c37721b5, at fde616a28) says 12.46 GB and the one before it
        # (adb301a3f, at caedb000d) 12.83 GB. The first cold builds peaked at
        # 11.77 GB and 11.97 GB (the 2026-10-20 guard demonstration's scratch
        # target dir). A floor is never below a measured build peak.
        "_cold_build_peak_gb": 13.89,
    },
    # The kernel's release-only lib tests (E3 fix-up, 2026-11-13). `infer_type`
    # takes the fast path in a release build and the certificate path in a
    # debug one, so 26 lib tests of the fast path are
    # `#[cfg(not(debug_assertions))]` and the debug lib rows compile them out
    # (`lib_test_coverage` derives them; the parity target above is the same
    # split at the scale of a whole target).
    {
        "id": "clean-kernel::release::lib::fast_path",
        "package": "clean-kernel",
        "kind": "test",
        "profile": PROFILE_RELEASE,
        # The six modules that hold the 26 (309 tests in a release build).
        "argv": ["targo", "--unverified", "test", "--locked", "--release",
                 "-p", "clean-kernel", "--lib", "--",
                 "env::tests::", "env::tests_constant_origin::",
                 "tc::cert::rebind::closed_memo::", "tc::infer_closed_data::tests::",
                 "tc::sharing_invariance::tests::", "tc::tests::infer_fast_arc_memo::"],
        "_must_pass": [
            "env::tests::test_add_decl_unchecked_overwrites_existing_in_release",
            "env::tests_constant_origin::test_g5_set_origins_refuses_unearned_kernel_checked_promotion",
            "tc::cert::rebind::closed_memo::release_tests::outer_fast_frame_clears_reentrant_certificate_support_on_success_and_error",
            "tc::infer_closed_data::tests::ambient_variable_hidden_in_environment_value_prevents_promotion",
            "tc::infer_closed_data::tests::binders_extensions_and_free_or_loose_variables_have_no_independent_key",
            "tc::infer_closed_data::tests::builtin_callback_custody_is_not_recreated_by_name_or_function_address",
            "tc::infer_closed_data::tests::fact_delta_reassembly_keeps_actual_callback_and_its_custody_together",
            "tc::infer_closed_data::tests::independent_data_survives_sibling_scopes_and_pins_actual_input",
            "tc::infer_closed_data::tests::independent_entries_share_total_capacity_and_never_leave_checker_in_tc_caches",
            "tc::infer_closed_data::tests::infer_only_app_cannot_supply_strict_argument_check",
            "tc::infer_closed_data::tests::mode_transparency_reducibility_and_level_callback_clear_retained_answers",
            "tc::infer_closed_data::tests::partial_universe_and_cumulative_policy_tightening_rechecks_actual_terms",
            "tc::infer_closed_data::tests::same_symbol_and_input_pointer_in_different_environment_do_not_share_answers",
            "tc::infer_closed_data::tests::unenumerated_lazy_provider_and_unknown_native_callback_keep_scoped_route",
            "tc::infer_closed_data::tests::unsafe_policy_transition_clears_independent_entries",
            "tc::sharing_invariance::tests::fast_arc_inference_does_not_reuse_an_earlier_choice",
            "tc::tests::infer_fast_arc_memo::certificate_check_mode_upgrades_type_only_entries",
            "tc::tests::infer_fast_arc_memo::fast_arc_memo_cleans_up_after_success_error_and_direct_calls",
            "tc::tests::infer_fast_arc_memo::fast_arc_memo_keys_the_active_binder_context",
            "tc::tests::infer_fast_arc_memo::fast_arc_memo_pins_owners_only_for_the_active_frame",
            "tc::tests::infer_fast_arc_memo::fast_arc_memo_preserves_dependent_binder_and_let_results",
            "tc::tests::infer_fast_arc_memo::fast_arc_memo_records_each_stable_child_kind",
            "tc::tests::infer_fast_arc_memo::fast_arc_memo_separates_inference_only_from_full_checking",
            "tc::tests::infer_fast_arc_memo::fast_arc_memo_zero_fallback_and_single_entry_turnover",
            "tc::tests::infer_fast_arc_memo::fast_arc_windows_admit_and_reuse_nodes_after_initial_capacity",
            "tc::tests::infer_fast_arc_memo::retained_projection_reentry_keeps_real_sort_certificate",
        ],
        # Its build right after the row above, in the same target dir (every
        # dependency warm), peaked at 13.73 GB over 4 min 40 s (heavy_gate
        # `e3fix-kernel-release-lib-build`, 2026-11-14T00:49:49Z); built cold
        # it compiles the same dependencies the row above did at 15.33 GB. Its
        # first pinned-runner build, at `7287e7f13` (2026-11-14T01:47Z, the
        # pinned target's release profile cold), peaked at 15.45 GB over
        # 13 min 23 s, reserving 23 GB: the highest measured, so the floor.
        "_cold_build_peak_gb": 15.45,
    },
]


def entry_profile(entry: dict[str, Any]) -> str:
    """The build profile a row (or a record) measures; absent means debug."""
    return entry.get("profile") or PROFILE_DEV


def _split_libtest_args(argv: list[str]) -> tuple[list[str], list[str]]:
    """(cargo args, libtest args): everything before and after the first `--`."""
    try:
        sep = argv.index("--")
    except ValueError:
        return list(argv), []
    return list(argv[:sep]), list(argv[sep + 1:])


def _libtest_filters(args: list[str]) -> tuple[list[str], list[str], bool]:
    """(positional filters, --skip filters, --exact) from a test binary's argv."""
    filters: list[str] = []
    skips: list[str] = []
    exact = False
    i = 0
    while i < len(args):
        tok = args[i]
        if tok == "--exact":
            exact = True
        elif tok == "--skip" and i + 1 < len(args):
            skips.append(args[i + 1])
            i += 1
        elif tok.startswith("--skip="):
            skips.append(tok[len("--skip="):])
        elif tok in ("--test-threads", "--format", "--color", "-Z") and i + 1 < len(args):
            i += 1
        elif not tok.startswith("-"):
            filters.append(tok)
        i += 1
    return filters, skips, exact


def _selects_a_profile(cargo: list[str]) -> bool:
    """Does a cargo argv (before `--`) build any profile but dev?"""
    return any(a in ("--release", "-r", "--profile") or a.startswith("--profile=")
               for a in cargo)


def _hides_ok_lines(cargo: list[str], libtest: list[str]) -> str | None:
    """The flag that keeps libtest from printing one `test <name> ... ok` line
    per test, or None. `passed_test_names` reads only those lines.

    cargo's `-q` passes `--quiet` (terse: one dot per test) to the harness;
    `--format` other than pretty drops the line; under `--nocapture` a test's
    own output can land on, or split, the line it passes on.
    """
    for tok in cargo:
        if tok in ("-q", "--quiet"):
            return f"cargo `{tok}`"
    for i, tok in enumerate(libtest):
        if tok in ("-q", "--quiet", "--nocapture", "--no-capture"):
            return f"libtest `{tok}`"
        if tok == "--format":
            fmt = libtest[i + 1] if i + 1 < len(libtest) else ""
        elif tok.startswith("--format="):
            fmt = tok[len("--format="):]
        else:
            continue
        if fmt != "pretty":
            return f"libtest `--format {fmt}`"
    return None


def check_profiles(entries: list[dict[str, Any]]) -> list[str]:
    """Problems that would let a row's `profile` disagree with what it builds.

    A row that declares a profile must be a cargo test invocation whose cargo
    half says so (`--release` for release, no `--release`/`--profile` for dev),
    and a release row must name, in `_must_pass`, tests its own filters select:
    a must-pass name its filters cannot select would make the row permanently
    UNKNOWN, and a release row with no must-pass list could go GREEN with its
    subject compiled out. A row with a must-pass list may not hide libtest's
    per-test `ok` lines (`_hides_ok_lines`), for the same reason. A release row
    must carry `_cold_build_peak_gb`, its highest measured build peak (see
    RELEASE_PROFILE_TARGETS). A cargo test
    row with no `profile` is recorded as dev, so it may not select a profile.
    """
    problems: list[str] = []
    for entry in entries:
        rid = entry.get("id", "?")
        argv = list(entry.get("argv") or [])
        if _build_phase_argv(argv) is not None:
            cargo_args, test_args = _split_libtest_args(argv)
            no_execution = (set(cargo_args) & {"--no-run", "--help", "-h"}) | (
                set(test_args) & {"--list", "--help", "-h"})
            if no_execution:
                problems.append(f"{rid}: command does not execute tests ({', '.join(sorted(no_execution))})")
        if "profile" not in entry:
            if entry.get("_replaces_debug_target") is not None:
                problems.append(f"{rid}: a debug-target replacement must declare a release profile")
            # Unlabelled: its records say `profile: dev`, so a cargo test row
            # with no `profile` may not build another profile either.
            if _build_phase_argv(argv) is not None and _selects_a_profile(
                    _split_libtest_args(argv)[0]):
                problems.append(
                    f"{rid}: has no `profile`, so its records read dev, but its argv "
                    "selects a profile")
            continue
        profile = entry["profile"]
        replacement = entry.get("_replaces_debug_target")
        if replacement is not None:
            cargo, libtest = _split_libtest_args(argv)
            filters, skips, _ = _libtest_filters(libtest)
            def option_value(flag):
                return cargo[cargo.index(flag) + 1] if flag in cargo and cargo.index(flag) + 1 < len(cargo) else None
            if (profile != PROFILE_RELEASE or not isinstance(replacement, str) or not replacement
                    or option_value("--test") != replacement
                    or option_value("-p") != entry.get("package") or filters or skips):
                problems.append(f"{rid}: a debug-target replacement must run the whole named package test in release")
        if profile not in PROFILES:
            problems.append(f"{rid}: profile {profile!r} is not one of {PROFILES}")
            continue
        if _build_phase_argv(argv) is None:
            problems.append(f"{rid}: declares profile {profile!r} but is not a cargo test argv")
            continue
        cargo, libtest = _split_libtest_args(argv)
        if profile == PROFILE_RELEASE and "--release" not in cargo:
            problems.append(f"{rid}: profile release but its argv has no --release before `--`")
        if profile == PROFILE_DEV and _selects_a_profile(cargo):
            problems.append(f"{rid}: profile dev but its argv selects a profile")
        if profile == PROFILE_RELEASE:
            cold = entry.get("_cold_build_peak_gb")
            if isinstance(cold, bool) or not isinstance(cold, (int, float)) or cold <= 0:
                problems.append(
                    f"{rid}: a release row must carry its highest measured build peak in "
                    "`_cold_build_peak_gb` (a positive number of GB)")
        must = entry.get("_must_pass")
        if profile == PROFILE_RELEASE and not must:
            problems.append(
                f"{rid}: a release row must name the tests it exists for in `_must_pass`")
            continue
        if must is None:
            continue
        if not isinstance(must, list) or not all(isinstance(n, str) and n for n in must):
            problems.append(f"{rid}: `_must_pass` must be a list of test names")
            continue
        hiding = _hides_ok_lines(cargo, libtest)
        if hiding:
            problems.append(
                f"{rid}: {hiding} stops libtest printing `test <name> ... ok`, so its "
                "must-pass tests could never be seen to pass")
        filters, skips, exact = _libtest_filters(libtest)
        selected = (libtest_select(must, filters, skips, exact) if filters
                    else {n for n in must if not any(s in n for s in skips)})
        unselected = sorted(set(must) - selected)
        if unselected:
            problems.append(f"{rid}: its own filters do not select must-pass {unselected}")
    return problems


_TEST_OK_RE = re.compile(r"^test (\S+) \.\.\. ok\b", re.M)


def passed_test_names(text: str) -> list[str]:
    """Every test libtest reported `... ok` in a run's output, sorted."""
    return sorted(set(_TEST_OK_RE.findall(text)))


def must_pass_missing(entry: dict[str, Any], record: dict[str, Any]) -> list[str]:
    """The row's must-pass tests the recorded run did not report `ok`."""
    must = entry.get("_must_pass") or []
    passed = set(record.get("passed_tests") or [])
    return sorted(name for name in must if name not in passed)


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
    "clean::test::prelude_source_cli": ["theories/cic_l/CICL/Level.lean"],
    "clean::test::function_field_recursion_cli": ["theories/cic_l_model/CICLModel/RawSets.lean"],
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
    #
    # AND IT HAPPENED A THIRD TIME -- measured 2026-08-27 by lane REV, the same
    # way lane V measured the second: enumerate what the test sources actually
    # OPEN, then diff against this list. Chain 18 landed on 2026-08-21 and
    # brought four `lane18` records with it; `freshness.rs:99` promoted
    # `data/crystal_chain_revalidation_2026-08-21_lane18.json` to CURRENT_RECORD
    # -- the newest live-dump comparison in the tree, the one every "the chains
    # were revalidated" claim rests on -- and NONE of the four entered this list.
    # `data/crystal_frontier_census_2026-08-21.json` and
    # `data/crystal_mint_blind_slots.json` were outside it too. So the row that
    # exists to notice chain drift could go green while the record it reads to
    # decide that was edited underneath it.
    #
    # Twice is an instance; three times is a class, and a hand-maintained list
    # is the class. `_crystal_extra_paths_owed()` below now RE-DERIVES the owed
    # set from the test sources on every invocation and refuses rather than
    # letting the fourth one land silently.
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
        # Chain 18's cohort, 2026-08-21 -- missing until lane REV, 2026-08-27.
        "data/crystal_chain_revalidation_2026-08-21_lane18.json",
        "data/crystal_fixture_freshness_2026-08-21_lane18.json",
        "data/crystal_fixture_rebaseline_2026-08-21_lane18.json",
        "data/crystal_fixture_rebaseline_bindings_2026-08-21_lane18.json",
        # The 2026-09-20 AT-HEAD record the freshness scope binds (read by
        # `freshness_scope.rs` through the scope file's `record` field, so the
        # source scan cannot see it -- listed by hand, which is what the
        # scan-owed check cannot refuse and this comment exists to make visible),
        # and the freshness report it was minted from.
        "data/crystal_chain_revalidation_2026-09-20_athead_c46d6594b.json",
        "data/crystal_fixture_freshness_2026-09-20_lane20.json",
        # Read by `has_loose_bvars_evidence.rs` and `operand_audit.rs`
        # respectively; missing for the same reason.
        "data/crystal_frontier_census_2026-08-21.json",
        "data/crystal_mint_blind_slots.json",
        # Named in a live assertion MESSAGE (`bvar_in_range.rs`,
        # `flat_flags_contains.rs`): the record those lanes promise to disagree
        # with in writing rather than reconcile away. Part of the evidence
        # statement, so part of the digest.
        "data/crystal_flip_census_2026-08-13.json",
        "data/crystal_freshness_scope.json",
        "data/crystal_chain_revalidation_2026-10-07_047ebd051.json",
        "data/crystal_fixture_rebaseline_2026-10-07_047ebd051.json",
        "data/crystal_fixture_rebaseline_bindings_2026-10-07_047ebd051.json",
        "data/crystal_fixture_freshness_2026-10-07_047ebd051_strict.json",
        # The 2026-10-28 AT-HEAD record the scope binds (read through the scope
        # file's `record` field, so listed by hand like the 2026-09-20 one), the
        # freshness report it was minted from, and the byte-for-byte control it
        # names (the 2026-10-18 one).
        "data/crystal_chain_revalidation_2026-10-28_athead_1633a8e20.json",
        "data/crystal_fixture_freshness_2026-10-28_athead.json",
        "data/crystal_revalidation_at_head_2026-10-18_r4sweep.json",
        "scripts/crystal_chain_revalidation.py",
        "scripts/crystal_fixture_freshness.py",
        "scripts/crystal_fixture_rebaseline.py",
        "scripts/crystal_freshness_scope.py",
        "scripts/trust_ir_build.sh",
    ],
    # ---- clean-elab, added 2026-09-16 when the package joined the runner's
    # default set. Every path below was DERIVED by `_crystal_extra_paths_owed`
    # from the targets' own sources and then committed -- not typed from
    # reading. `_EXTRA_PATH_SOURCES` re-derives them on every call and refuses
    # any that is read but unlisted, so this block cannot silently fall behind.
    # The Lean4 compat corpus, its manifests/scorecard/schemas, the recorded frontend
    # run artifacts, the olean fixtures, and the classification generator this suite
    # shells out to.
    "clean-elab::test::integration": [
        "scripts/lean4_compat/generate_frontend_classification.py",
        "tests/fixtures/olean/v4.13.0/custom/Inductive.olean",
        "tests/fixtures/olean/v4.13.0/custom/Minimal.olean",
        "tests/fixtures/olean/v4.13.0/custom/Structure.olean",
        "tests/lean4_compat/MANIFEST.json",
        "tests/lean4_compat/frontend_corpus_classification.json",
        "tests/lean4_compat/frontend_diagnostic_artifact_schema.json",
        "tests/lean4_compat/frontend_exit_status_artifact_schema.json",
        "tests/lean4_compat/frontend_replacement_scorecard.json",
        "tests/lean4_compat/frontend_run_artifacts",
        "tests/lean4_compat/frontend_run_artifacts/lean4",
        "tests/lean4_compat/frontend_run_artifacts/lean4/diagnostic",
        "tests/lean4_compat/frontend_run_artifacts/lean4/diagnostic/220.lean.json",
        "tests/lean4_compat/frontend_run_artifacts/lean4/exit_status",
        "tests/lean4_compat/frontend_run_artifacts/lean4/exit_status/220.lean.json",
        "tests/lean4_compat/frontend_slice_manifest.txt",
        "tests/lean4_compat/lean4_tests",
        "tests/lean4_compat/lean4_tests/248.lean",
        "tests/lean4_compat/lean4_tests/309.lean",
        "tests/lean4_compat/lean4_tests/348.lean",
        "tests/lean4_compat/phase1_expected_outcomes.json",
        "tests/lean4_compat/phase1_gate_manifest.txt",
    ],
    # The ratchets the aggregated spec suite decides its verdict from. DERIVED by
    # `_crystal_extra_paths_owed` from the 78 sources `tests/spec_suite.rs`
    # actually compiles, then committed -- not typed from reading. Every one of
    # these was read by a target whose digest did NOT cover it before the merge,
    # so a green survived an edit to the ratchet it checks.
    "clean-verify::test::spec_suite": [
        "data/clean_verify_axiom_ratchet.json",
        "data/clean_verify_derivedproved_debt.json",
        "data/crystal_enum_tag_pin.json",
        "data/crystal_mint_blind_slots.json",
        "data/premise_witness_ratchet.json",
    ],
    # The phase-1 gate manifest and the corpus it names.
    "clean-elab::test::phase1_full_corpus": [
        "tests/lean4_compat/lean4_tests",
        "tests/lean4_compat/phase1_gate_manifest.txt",
    ],
    # A RATCHET whose verdict is decided by these three committed JSON files; none
    # is inside any crate, so without them an edit to the ratchet leaves the row's
    # GREEN reading fresh.
    "clean-elab::test::silent_tactic_census": [
        "data/silent_tactic_census.json",
        "data/silent_tactic_probes.json",
        "data/silent_tactic_ratchet.json",
    ],
    # A GATE over a growing machine-checked proof directory; the whole tree is the
    # input, so the directory is listed rather than each file.
    "clean-elab::test::trust_soundness_ouroboros_gate": [
        "proofs/trust-soundness",
    ],
    # The CIC_L qualification tests (self-proof plan unit E1, 2026-11-12). Their
    # subject is not Rust: both compile the Lean theory under `theories/cic_l`
    # with the Lean the workspace `lean-toolchain` pins and re-check the result,
    # and none of that is inside a crate directory -- so before this entry a
    # recorded GREEN survived any edit to the theory it had qualified. The
    # module tree `theories/cic_l/CICL` and the `ORDER` that says which of it
    # is compiled are the input, and they are listed by hand: the tests reach
    # them through the fixture family's `ORDER` line `theory cic_l`
    # (crates/clean-olean/tests/fixtures/lean/<pin>/cic_l_level/ORDER), which a
    # scan of the `.rs` sources cannot see. The other files are the ones the
    # sources `include_str!`, re-derived by `_EXTRA_PATH_SOURCES`. The
    # declarative theory's README is deliberately outside: it is prose, several
    # lanes edit it, and a verdict that went stale on a paragraph would be
    # re-run for nothing. The model package (`theories/cic_l_model`, its own
    # directory since the model lane separated it) is listed whole, because the
    # model test walks that directory for its source inventory; the model test
    # compiles the declarative theory first, so that is its input too. The
    # Lean install itself is outside the repository and outside every digest.
    "clean-olean::test::cic_l_level": [
        "data/cic_l_rule_inventory.json",
        "data/lean_axiom_census.json",
        "lean-toolchain",
        "theories/cic_l/CICL",
        "theories/cic_l/ORDER",
        "theories/cic_l/lakefile.toml",
        "theories/cic_l/lean-toolchain",
    ],
    "clean-olean::test::cic_l_model": [
        "data/cic_l_rule_inventory.json",
        "lean-toolchain",
        "theories/cic_l/CICL",
        "theories/cic_l/ORDER",
        "theories/cic_l_model",
        "theories/cic_l_model/ORDER",
        "theories/cic_l_model/declaration_inventory.json",
        "theories/cic_l_model/model_statement_pins.json",
        "theories/cic_l_model/named_choice_exceptions.json",
    ],
    # Checker qualification compiles these packages through the fixture ORDER;
    # kcheck_spec additionally copies its package for the cold lake-build control.
    # Keep complete package inputs, plus the directly embedded pin files which
    # the source-read census checks individually.
    "clean-olean::test::kcheck_core": [
        "lean-toolchain",
        "theories/cic_l",
        "theories/kcheck",
        "theories/kcheck/ORDER",
        "theories/kcheck/axiom_closures.json",
        "theories/kcheck/expected_output.txt",
        "theories/kcheck/statement_pins.json",
    ],
    "clean-olean::test::kcheck_spec": [
        "lean-toolchain",
        "theories/cic_l",
        "theories/cic_l_model",
        "theories/kcheck_spec",
        "theories/kcheck_spec/ORDER",
        "theories/kcheck_spec/axiom_closures.json",
        "theories/kcheck_spec/statement_pins.json",
    ],
    # Independent reference proofs and canonical R5 callers compile the entire
    # specification dependency chain; directly embedded pins remain explicit.
    "clean-olean::test::kcheck_sort_bounds": [
        "lean-toolchain",
        "theories/cic_l",
        "theories/cic_l_model",
        "theories/kcheck_spec",
        "theories/kcheck_sort_bounds",
        "theories/kcheck_sort_bounds/ORDER",
        "theories/kcheck_sort_bounds/axiom_closures.json",
        "theories/kcheck_sort_bounds/statement_pins.json",
    ],
    # The design's checker (unit C2) compiles cic_l, cic_l_model, kcheck_spec and
    # itself through its fixture ORDER, and embeds its ORDER, pins, closures and
    # the executable's expected output.
    "clean-olean::test::kcheck_labelled": [
        "lean-toolchain",
        "theories/cic_l",
        "theories/cic_l_model",
        "theories/kcheck_spec",
        "theories/kcheck_labelled",
        "theories/kcheck_labelled/ORDER",
        "theories/kcheck_labelled/axiom_closures.json",
        "theories/kcheck_labelled/expected_output.txt",
        "theories/kcheck_labelled/statement_pins.json",
        "theories/kcheck_soundness",
    ],
    "clean-olean::test::cic_l_base_bridge": [
        "lean-toolchain",
        "theories/cic_l",
        "theories/cic_l_model",
        "theories/kcheck_spec",
        "theories/cic_l_base_bridge",
    ],
    "clean-olean::test::cic_l_nat_model": [
        "lean-toolchain",
        "theories/cic_l",
        "theories/cic_l_model",
        "theories/kcheck_spec",
        "theories/cic_l_nat_model",
    ],
    # Bounded compiled-byte qualification of `theories/binding_not_review` across
    # pinned Lean, fenced Clean, and the hash-qualified stock ck0 binary.
    "clean-olean::test::binding_not_review": [
        "crates/clean-ck0",
        "lean-toolchain",
        "reports/2026-11-14-extension-binding-not-review",
        "reports/2026-11-14-extension-binding-not-review/artifact",
        "reports/2026-11-14-extension-binding-not-review/generated/BindingNotReviewCensus.lean",
        "reports/self-proof-ck0-shared-2026-11-14/stock-build-inputs.json",
        "theories/binding_not_review",
    ],
    # `structure_projection_tests.rs` (`clean-olean::lib`) and `ndjson_export_writer` (Q1)
    # compile `theories/cic_l` through `cic_l_level/ORDER`; VF4/VF5 compile `theories/chk_lia`.
    "clean-olean::lib": ["lean-toolchain", "theories/cic_l/CICL", "theories/cic_l/ORDER"],
    "clean-olean::test::ndjson_export_writer": [
        "lean-toolchain", "scripts/lean_export_mint.sh", "scripts/lean_export_replay",
        "scripts/lean_export_replay.sh", "theories/cic_l/CICL", "theories/cic_l/ORDER",
    ],
    "clean-olean::test::vf4_chk_lia": ["lean-toolchain", "theories/chk_lia"],
    "clean-olean::test::vf4_chk_lia_f1": [
        "lean-toolchain", "reports/2026-10-26-vf4-f1-corpus", "theories/chk_lia",
    ],
    "clean-olean::test::vf4_chk_lia_quorum": ["lean-toolchain", "theories/chk_lia"],
    "clean-olean::test::vf5_f1_reference": ["lean-toolchain", "theories/chk_lia"],
    # Parser-only test inputs outside the crate. These are not library inputs:
    # parse_world.rs reads the pin/table under cfg(test), and the grammar tests
    # read the source/corpora. Keep them on the test rows, not PACKAGE_EXTRA_PATHS.
    "clean-parser::lib": [
        "crates/clean-olean/lean_worlds.tsv",
        "lean-toolchain",
        "reports/local-function-headers-2026-11-06/sources/let_rec_equation_class.lean",
        "tests/lean4_compat/lean4_tests",
        "tests/matp_bench",
    ],
    "clean-parser::test::module_system_b_e2e": [
        "lean-toolchain",
        "tests/fixtures/module_spellings/modifier_matrix.tsv",
        "tests/fixtures/module_spellings/verdicts.tsv",
    ],
    "clean-parser::test::parse_parity": [
        "tests/fixtures/parser_parity/README.md",
        "tests/fixtures/parser_parity/ground_truth.tsv",
    ],
    # ---- clean-kernel and clean-ck0, added 2026-11-13 when both packages
    # joined the default set (self-proof unit E3). The relative literals were
    # RESOLVED by `_crystal_extra_paths_owed` (the `RESOLVE_RELATIVE` rows
    # below, generated for every target of the two packages) and then
    # committed; the rest are reads the resolver cannot see because the path is
    # assembled by `join`, and each says so. A lib shard inherits its parent's
    # list (`build_inventory`), so the shards of `clean-kernel::lib` are
    # digested over the same reads as the roll-up that stands for them.
    "clean-kernel::lib": [
        # `env/tests_prelude_axiom_ratchet.rs`: the census `clean check` loads.
        "data/prelude_axiom_ratchet.json",
        # (`model_islands.rs`'s five `include_str!` of clean-verify's spec
        # sources are derived since 2026-11-13: `library_external_reads`.)
        # `env/carrier_differential_tests.rs`: the Lean v4.30 ground truth.
        "tests/fixtures/carrier_v4_30/op_table.tsv",
        # `differential_baseline.rs`: the cached Lean baseline and its inputs.
        "tests/differential/expressions.txt",
        "tests/differential/lean4_baseline.json",
        # `cert/benchmark.rs` assembles this with `join`: the suite its
        # certificate-verification test runs.
        "benchmarks/geometry/alphageometry",
    ],
    # Assembled with `join`, not a literal: the audit it pins and the golden it
    # compares the audit's mirror against.
    "clean-kernel::test::verify_axiom_audit_integration": [
        "data/axiom_audit.json",
        "data/soundness_tcb.json",
    ],
    # The lint walks every `.rs` file under `crates/`, so the whole directory is
    # its input: an edit to any crate can turn it red.
    "clean-kernel::test::lint_sorry_bypass": [
        "crates",
    ],
    # (clean-ck0's `export_inductives` and `level_as_written` embed their reads
    # with `include_str!`, derived since 2026-11-13: `row_target_reads`.)
}

# A LIBRARY'S COMPILE-TIME READS OUTSIDE ITS CRATE, DERIVED (2026-11-13).
#
# A package's library can embed files that lie outside every crate directory:
# `clean-kernel`'s `env/soundness_certificate.rs` embeds
# `data/soundness_tcb.json` with `include_str!` in non-test code (the C2 golden
# its certificate compares the live axiom set against), so an edit to it
# rebuilds the kernel and every row that compiles the kernel runs a different
# program. Until this date that one read sat in a hand table
# (`PACKAGE_EXTRA_PATHS`) applied to the package's own rows only: deleting the
# entry left the runner's whole self-test green, every dependent package's rows
# never digested it, and the same class in `clean-elab` (213 out-of-crate
# `include_str!`/`include_bytes!`), `clean-olean` (30) and `clean-parser` (5)
# had no entry at all.
#
# Now the reads are derived on every inventory, by `library_external_reads`:
# the library's module tree is walked by scripts/rust_modules.py in MAYBE mode
# (every file rustc may compile for it under the host's platform cfgs, with
# `kani` and `miri` off and every feature open), comments and literals are
# blanked by its lexer, each `include_str!` / `include_bytes!` found in CODE
# has its argument read from the comment-blanked text (a literal is
# file-relative; `concat!(env!("CARGO_MANIFEST_DIR"), "...")` is
# crate-relative; a `concat!` that continues past its literals reads somewhere
# under the directory its literal prefix names), and a module file the walk
# loads from outside the crate counts as read too. A result outside the crate
# that git can see is owed; an argument it cannot read refuses the inventory,
# naming the site, rather than narrowing a digest.
#
# Every row takes the non-test reads of every package in its closure (a
# dependent compiles the same library), a package's lib row and shards take
# its `#[cfg(test)]` reads too, a workspace row takes both for every package,
# and an integration-test row takes its own target's, by the same walk from the
# target's root (`row_target_reads`). Measured 2026-11-13 (distinct files
# outside the crate): `clean-kernel`'s library 6, `clean-olean`'s 29,
# `clean-elab`'s `cfg(test)` code 46 and ten of its integration targets 199,
# `clean-parser`'s `cfg(test)` code 3 and one target 3, fifteen `clean-olean`
# targets 17, two `clean-ck0` targets 2. A build script's reads are not
# derived; they are declared in PACKAGE_EXTRA_PATHS (below).
_INCLUDE_MACRO_RE = re.compile(r"\binclude_(?:str|bytes)\s*!\s*\(")
_STR_LITERAL_RE = re.compile(
    r'\s*(?:r(?P<h>#*)"(?P<raw>.*?)"(?P=h)|"(?P<s>[^"\\]*)")\s*', re.S)
_MANIFEST_DIR_RE = re.compile(r'\s*env\s*!\s*\(\s*"CARGO_MANIFEST_DIR"\s*,?\s*\)\s*')


def _split_top_level(text: str) -> list[str]:
    """`text` split on commas outside brackets (a `concat!` argument list)."""
    parts, depth, cur = [], 0, []
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
            continue
        cur.append(ch)
    if "".join(cur).strip():
        parts.append("".join(cur))
    return parts


def _literal(piece: str) -> str | None:
    m = _STR_LITERAL_RE.fullmatch(piece)
    if not m:
        return None
    return m.group("raw") if m.group("raw") is not None else m.group("s")


def _include_argument_path(arg: str, file_dir: Path, crate_dir: Path) -> Path | None:
    """The file an include macro's argument names, or the directory it reads
    under when the argument continues past its literals (a `concat!` with a
    macro variable); None when it cannot be read."""
    lit = _literal(arg)
    if lit is not None:
        return Path(lit) if os.path.isabs(lit) else file_dir / lit
    m = re.fullmatch(r"\s*concat\s*!\s*\((?P<inner>.*)\)\s*", arg, re.S)
    if not m:
        return None
    pieces = _split_top_level(m.group("inner"))
    anchor = file_dir
    if pieces and _MANIFEST_DIR_RE.fullmatch(pieces[0]):
        anchor, pieces = crate_dir, pieces[1:]
    prefix, partial = "", False
    for piece in pieces:
        value = _literal(piece)
        if value is None:
            partial = True
            break
        prefix += value
    if anchor is crate_dir:
        prefix = prefix.lstrip("/")
    if not prefix and not partial:
        return None
    if not partial:
        return anchor / prefix
    # `"dir/" + $name` reads under dir/; `"dir/stem_" + $name` under dir/ too.
    return anchor / prefix if prefix.endswith("/") or not prefix else (anchor / prefix).parent


def _file_include_reads(path: Path) -> tuple[set[Path], list[str]]:
    """(paths an include macro in this file's CODE may read, sites it cannot read)."""
    try:
        raw = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        return set(), [f"{path}: unreadable ({exc})"]
    if "include_str" not in raw and "include_bytes" not in raw:
        return set(), []
    rm = _rust_modules()
    lx = rm._lex(raw)
    if lx is None:
        return set(), [f"{path}: not lexable as rustc reads it, so its include macros cannot be placed"]
    crate_dir = _crate_dir_of(path)
    reads: set[Path] = set()
    unreadable: list[str] = []
    kept = lx.kept
    for m in _INCLUDE_MACRO_RE.finditer(lx.code):
        close = lx.pairs.get(m.end() - 1)
        if close is None:
            unreadable.append(f"{path}:{lx.code.count(chr(10), 0, m.start()) + 1}: unbalanced include")
            continue
        found = _include_argument_path(kept[m.end():close], path.parent, crate_dir)
        if found is None:
            line = lx.code.count("\n", 0, m.start()) + 1
            unreadable.append(f"{path}:{line}: include argument {kept[m.end():close].strip()!r} "
                              f"is not a literal or a literal-led concat!")
            continue
        reads.add(Path(os.path.normpath(found)))
    return reads, unreadable


def _crate_dir_of(path: Path) -> Path:
    """The directory of the nearest Cargo.toml above `path`."""
    for parent in path.parents:
        if (parent / "Cargo.toml").is_file():
            return parent
    return path.parent


_LIBRARY_READS_CACHE: dict[tuple[str, bool], tuple[str, ...]] = {}
# Bump when the derivation's rule changes, so a stored answer is not reused.
_LIBRARY_READS_RULE = "library-reads-v1"


def _rs_stats(dirs: list[Path], files: list[Path]) -> str:
    """A fingerprint of every `.rs` file and Cargo.toml under `dirs` (outside
    `target/`) and of `files`: path, size and mtime, as cargo's own freshness
    reads them. It keys a stored derivation; it is never a digest a verdict
    stands on -- the digest hashes content."""
    hasher = hashlib.sha256()
    entries: list[str] = []
    for d in dirs:
        for dirpath, dirnames, filenames in os.walk(d):
            dirnames[:] = sorted(n for n in dirnames if n != "target" and not n.startswith("."))
            for name in sorted(filenames):
                if name.endswith(".rs") or name == "Cargo.toml":
                    entries.append(os.path.join(dirpath, name))
    entries.extend(str(f) for f in files)
    for path in sorted(set(entries)):
        try:
            st = os.stat(path)
            hasher.update(f"{path}\0{st.st_size}\0{st.st_mtime_ns}\n".encode())
        except OSError:
            hasher.update(f"{path}\0absent\n".encode())
    return hasher.hexdigest()


def _derivation_cache_path() -> Path:
    return target_dir() / "suite-runner" / "derivation_cache.json"


def _tool_fingerprint() -> str:
    """The rule and the code that derives: this script and the module walk's."""
    here = Path(__file__).resolve().parent
    hasher = hashlib.sha256(_LIBRARY_READS_RULE.encode())
    for name in ("verify_runner.py", "rust_modules.py", "rust_cfg.py", "check_add_decl_ratchet.py"):
        path = here / name
        hasher.update(path.read_bytes() if path.is_file() else b"absent")
    return hasher.hexdigest()


def _cached(kind: str, key_parts: tuple[str, ...], dirs: list[Path],
            compute: Any) -> Any:
    """`compute()` -> (value, files outside `dirs` it read), stored under the
    target dir and reused while every `.rs`/Cargo.toml under `dirs` and every
    file it read keep their size and mtime and this tool is unchanged."""
    cache_path = _derivation_cache_path()
    try:
        store = json.loads(cache_path.read_text())
        if not isinstance(store, dict) or store.get("tool") != _tool_fingerprint():
            store = {"tool": _tool_fingerprint(), "entries": {}}
    except (OSError, json.JSONDecodeError):
        store = {"tool": _tool_fingerprint(), "entries": {}}
    name = kind + "\0" + "\0".join(key_parts)
    hit = store["entries"].get(name)
    if isinstance(hit, dict):
        files = [Path(f) for f in hit.get("files", [])]
        if hit.get("stats") == _rs_stats(dirs, files):
            return hit.get("value")
    value, files = compute()
    store["entries"][name] = {"stats": _rs_stats(dirs, list(files)),
                              "files": sorted(str(f) for f in files), "value": value}
    try:
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        tmp = cache_path.with_suffix(f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps(store))
        tmp.replace(cache_path)
    except OSError:
        pass
    return value


def _library_read_facts() -> dict[str, Any]:
    """What MAYBE decides `cfg` from here: the host's platform cfgs, `kani` and
    `miri` off (neither is set by a cargo build), every feature undecided."""
    return dict(_rust_modules().rust_cfg().host_facts(), kani=False, miri=False)


def library_external_reads(lib_root: Path, test_cfg: bool, base: Path | None = None) -> tuple[str, ...]:
    """Repository-relative files (or directories) the library rooted at
    `lib_root` may read at compile time outside its crate, that git can see.
    SystemExit names any include it cannot read: an unread argument is never
    taken as "reads nothing"."""
    root_base = (base or REPO_ROOT).resolve()
    key = (str(lib_root), test_cfg)
    if base is None and key in _LIBRARY_READS_CACHE:
        return _LIBRARY_READS_CACHE[key]
    crate_dir = _crate_dir_of(lib_root.resolve())

    def compute() -> tuple[list[Any], set[Path]]:
        rm = _rust_modules()
        owed: set[str] = set()
        visited_outside: set[Path] = set()
        unreadable: list[str] = []
        for path, _modpath in rm.walk(lib_root, rm.Reach.MAYBE, None, test_cfg,
                                      _library_read_facts()):
            path = Path(path).resolve()
            candidates: set[Path] = set()
            if crate_dir not in path.parents:
                candidates.add(path)
                visited_outside.add(path)
            reads, bad = _file_include_reads(path)
            unreadable.extend(bad)
            candidates |= reads
            for cand in candidates:
                cand = cand.resolve() if cand.exists() else cand
                if cand == crate_dir or crate_dir in cand.parents:
                    continue
                try:
                    rel = cand.relative_to(root_base)
                except ValueError:
                    continue
                if cand.exists():
                    owed.add(rel.as_posix())
        if unreadable:
            return [["unreadable", sorted(unreadable)]], visited_outside
        return [["owed", sorted(_git_visible(root_base, owed))]], visited_outside

    if base is None:
        value = _cached("library-reads", (str(lib_root), str(test_cfg)), [crate_dir], compute)
    else:
        value = compute()[0]
    tag, items = value[0]
    if tag == "unreadable":
        raise SystemExit(
            "verify_runner: a compile-time read cannot be placed, so no digest can be said to "
            "cover it:\n  " + "\n  ".join(items))
    result = tuple(items)
    if base is None:
        _LIBRARY_READS_CACHE[key] = result
    return result


def test_target_root(meta: dict[str, Any], package: str, name: str) -> Path | None:
    """The root source of a workspace package's integration-test target `name`."""
    pkg = next((p for p in meta["packages"] if p["name"] == package), None)
    for tgt in (pkg or {}).get("targets", []):
        if tgt.get("name") == name and "test" in tgt.get("kind", []):
            return Path(tgt["src_path"]) if tgt.get("src_path") else None
    return None


def row_target_reads(meta: dict[str, Any], entry: dict[str, Any]) -> tuple[str, ...]:
    """An integration-test row's own compile-time reads outside its crate: the
    same derivation as a library's (`library_external_reads`), over the test
    target's module tree, `cfg(test)` on. () for any other row."""
    if entry["package"] == "__workspace__":
        return ()
    name = _test_target_name(entry.get("argv") or [])
    root = test_target_root(meta, entry["package"], name) if name else None
    return library_external_reads(root, True) if root is not None else ()


def package_lib_root(meta: dict[str, Any], package: str) -> Path | None:
    """The lib target's root source of a workspace package, from cargo metadata."""
    pkg = next((p for p in meta["packages"] if p["name"] == package), None)
    if pkg is None:
        return None
    for tgt in pkg.get("targets", []):
        if set(tgt.get("kind", [])) & {"lib", "rlib", "proc-macro"}:
            return Path(tgt["src_path"]) if tgt.get("src_path") else None
    return None


def closure_library_reads(meta: dict[str, Any], dirs: list[Path], own: str | None,
                          own_test_cfg: bool) -> tuple[str, ...]:
    """The non-test library reads of every workspace package whose directory is
    in `dirs`, plus the `#[cfg(test)]` reads of `own` when `own_test_cfg`."""
    by_dir = {Path(p["manifest_path"]).parent: p["name"] for p in meta["packages"]}
    out: set[str] = set()
    for d in dirs:
        name = by_dir.get(Path(d))
        root = package_lib_root(meta, name) if name else None
        if root is None:
            continue
        out.update(library_external_reads(root, False))
        if own_test_cfg and name == own:
            out.update(library_external_reads(root, True))
    return tuple(sorted(out))


# A BUILD SCRIPT'S READS outside its crate are not derived (a `build.rs` reads
# with `fs::read`, a path the module walk cannot see), so they stay declared by
# hand, per package, and follow the same closure as the library's derived
# reads: every row that compiles the package digests them (`build_inventory`).
# `_check_olean_world_inputs` re-derives clean-olean's from the table its
# build script reads. clean-kernel's `data/soundness_tcb.json`, the table's
# first entry until 2026-11-13, is an `include_str!` and is derived now.
PACKAGE_EXTRA_PATHS: dict[str, list[str]] = {
    # build.rs reads the workspace pin to generate the library's world table
    # and pinned-toolchain identity, so this is not just a test fixture input.
    "clean-olean": [
        "lean-toolchain",
        # build.rs also derives each world identity from these table fixtures.
        "tests/fixtures/olean/v4.13.0/custom/Minimal.olean",
        "tests/fixtures/olean/v4.13.0/stdlib/Init.olean",
        "tests/fixtures/olean/v4.26.0/custom/StringCompat.olean",
        "tests/fixtures/olean/v4.30.0/closure_cache/Init.olean",
        "tests/fixtures/olean/v4.30.0/closure_cache/Target.olean",
        "tests/fixtures/olean/v4.30.0/module-system/Sigma.olean",
        "tests/fixtures/olean/v4.35.0/matcher-metadata/MatcherParity.olean",
        "tests/fixtures/olean/v4.36.0-rc2/matcher-metadata/MatcherParity.olean",
        "tests/fixtures/olean/v4.8.0/witness/FactLib.olean",
    ],
}

# The packages whose EVERY target is scanned with `RESOLVE_RELATIVE`: one
# generated row per `crates/<pkg>/tests/*.rs` target (its reachable sources)
# and one for the lib (`src/**/*.rs`). A new target that reads outside its
# crate through a relative literal is then refused at inventory time until its
# list above names the read, instead of joining the board with a digest that
# misses it. Added with the two packages (E3).
RESOLVED_SCAN_PACKAGES = ("clean-kernel", "clean-ck0", "clean-parser")

# The test sources whose `data/crystal_*.json` references the list above owes an
# entry for.  Kept beside the list so a new crystal test directory is a one-line
# addition here rather than a silent gap.
CRYSTAL_DIGEST_SOURCE_GLOBS = (
    "crates/clean-verify/tests/crystal_a1_lineage.rs",
    "crates/clean-verify/tests/crystal_a1_lineage/*.rs",
)


def _blank_rust_comments(src: str) -> str:
    """Replace every Rust comment with spaces, leaving string literals intact.

    The discrimination matters in both directions here.  A `data/crystal_*.json`
    named in a `//!` module doc is PROSE -- narrative about how a chain was
    chosen -- and putting it in the digest would demote a green whenever someone
    improved a paragraph.  The same name inside a live `assert!` message is
    CODE: it is the record the lane promises, in the failing output, to disagree
    with in writing rather than reconcile away, and editing it changes what the
    row means.  Blanking comments and keeping string literals is exactly that
    line.  (Naive `split("//")` gets it backwards on both counts -- it drops the
    tail of any literal containing `//`, and keeps doc text that merely mentions
    a path.)
    """
    out: list[str] = []
    i, n = 0, len(src)
    while i < n:
        ch = src[i]
        if ch == '"':
            out.append(ch)
            i += 1
            while i < n:
                out.append(src[i])
                if src[i] == "\\":
                    if i + 1 < n:
                        out.append(src[i + 1])
                        i += 2
                        continue
                elif src[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        if ch == "'" and i + 2 < n and (src[i + 1] != "\\" and src[i + 2] == "'"):
            out.append(src[i : i + 3])  # char literal, never a lifetime
            i += 3
            continue
        if src.startswith("//", i):
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if src.startswith("/*", i):
            depth, i = 1, i + 2
            out.append("  ")
            while i < n and depth:
                if src.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                    out.append("  ")
                elif src.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                    out.append("  ")
                else:
                    out.append(" " if src[i] != "\n" else "\n")
                    i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


# WHICH TARGETS READ OUTSIDE THEIR CRATE, AND THE PATTERN THAT FINDS WHAT THEY READ.
#
# Each row is (target, source globs, regex over the BLANKED source). The regex is
# applied to code with comments blanked, so a path named only in prose is not
# demanded -- `//! see data/crystal_x.json` must not force a digest entry, while
# a path inside a string literal that itself contains `//` must still be found.
#
# WHY A TABLE AND NOT A LIST OF PATHS. The paths are re-derived from the SOURCES
# on every call and compared against `TARGET_EXTRA_PATHS`; the list is the thing
# being checked, so a checker that read it back would prove nothing. Adding a
# target here is what makes forgetting to widen its digest impossible -- which is
# the failure three separate lanes already shipped for `crystal_a1_lineage`.
#
# The clean-elab rows were added 2026-09-16, when that package was wired into the
# runner's default set. Measured then: 10 of its 138 integration targets decide
# against files outside every crate directory, and this guard was structurally
# unable to see any of them -- it iterated a literal one-tuple whose regex only
# matched `data/crystal_*.json`. Four source families cover those ten targets.
RESOLVE_RELATIVE = "@resolve-relative"

_EXTRA_PATH_SOURCES: tuple[tuple[str, tuple[str, ...], str], ...] = (
    (
        "clean-verify::test::crystal_a1_lineage",
        CRYSTAL_DIGEST_SOURCE_GLOBS,
        r"data/crystal_[A-Za-z0-9_.-]+\.json",
    ),
    # A RATCHET: its verdict is decided by committed census/probe/ratchet JSON
    # named in `const *_REL` bindings, none of which is inside any crate.
    (
        "clean-elab::test::silent_tactic_census",
        ("crates/clean-elab/tests/silent_tactic_census.rs",),
        r"data/silent_tactic_[A-Za-z0-9_.-]+\.json",
    ),
    # A GATE over a growing machine-checked proof directory reached with
    # `CARGO_MANIFEST_DIR`/../../.
    (
        "clean-elab::test::trust_soundness_ouroboros_gate",
        ("crates/clean-elab/tests/trust_soundness_ouroboros_gate.rs",),
        r"\.\./\.\./(proofs/[A-Za-z0-9_./-]+)",
    ),
    # The Lean4 compat corpus, its manifests/scorecard/schemas, and the
    # classification generator the suite shells out to.
    (
        "clean-elab::test::integration",
        ("crates/clean-elab/tests/integration/*.rs",),
        r"\.\./\.\./((?:tests|scripts)/[A-Za-z0-9_./-]+)",
    ),
    (
        "clean-elab::test::phase1_full_corpus",
        ("crates/clean-elab/tests/phase1_full_corpus.rs",),
        r"\.\./\.\./((?:tests|scripts)/[A-Za-z0-9_./-]+)",
    ),
    # RATCHETS the aggregated spec suite decides its verdict from, none of which
    # is inside any crate directory. Found 2026-09-20 while merging the suite
    # into one binary and measured, not assumed: four records
    # (clean_verify_axiom_ratchet, clean_verify_derivedproved_debt,
    # crystal_mint_blind_slots, premise_witness_ratchet) were read by tests whose
    # digest had never covered them, so a green survived an edit to the very
    # ratchet it checks. That is the fourth instance of the class the comment
    # above `TARGET_EXTRA_PATHS` names, and it is re-derived rather than typed.
    # `@reach:` rather than a glob because this target is an aggregator: a
    # `tests/*.rs` glob would attribute the six DELIBERATELY separate targets'
    # records to it as well.
    (
        "clean-verify::test::spec_suite",
        ("@reach:crates/clean-verify/tests/spec_suite.rs",),
        r"data/[A-Za-z0-9_.-]+\.json",
    ),
    # The CIC_L qualification tests `include_str!` theory files (and the
    # workspace Lean pin) from outside every crate directory. `@reach:` because
    # `cic_l_level.rs` keeps its evidence checks in a `#[path]` module. The
    # declarative test also reads E7's census (`data/lean_axiom_census.json`),
    # which it requires to agree with what the reference replay admitted, and
    # E6's rule inventory (`data/cic_l_rule_inventory.json`, read at run time),
    # which names each judgment constructor's negative control.
    (
        "clean-olean::test::cic_l_level",
        ("@reach:crates/clean-olean/tests/cic_l_level.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain|data/[A-Za-z0-9_.-]+\.json)",
    ),
    (
        "clean-olean::test::cic_l_model",
        ("@reach:crates/clean-olean/tests/cic_l_model.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain|data/[A-Za-z0-9_.-]+\.json)",
    ),
    # The kcheck qualification tests `include_str!` their package's ORDER, pins,
    # closures and (for the checkers) expected output.
    (
        "clean-olean::test::kcheck_core",
        ("@reach:crates/clean-olean/tests/kcheck_core.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain)",
    ),
    (
        "clean-olean::test::kcheck_spec",
        ("@reach:crates/clean-olean/tests/kcheck_spec.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain)",
    ),
    (
        "clean-olean::test::kcheck_sort_bounds",
        ("@reach:crates/clean-olean/tests/kcheck_sort_bounds.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain)",
    ),
    (
        "clean-olean::test::kcheck_labelled",
        ("@reach:crates/clean-olean/tests/kcheck_labelled.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain)",
    ),
    (
        "clean-olean::test::cic_l_base_bridge",
        ("@reach:crates/clean-olean/tests/cic_l_base_bridge.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain)",
    ),
    (
        "clean-olean::test::cic_l_nat_model",
        ("@reach:crates/clean-olean/tests/cic_l_nat_model.rs",),
        r"(?:\.\./)+(theories/[A-Za-z0-9_./-]+|lean-toolchain)",
    ),
    (
        "clean-olean::test::binding_not_review",
        ("@reach:crates/clean-olean/tests/binding_not_review.rs",),
        r'repo\.join\(\s*"([A-Za-z0-9_./-]+)"',
    ),
    ("clean-olean::test::ndjson_export_writer", ("@reach:crates/clean-olean/tests/ndjson_export_writer.rs",), r'repo_root\(\)\.join\(\s*"([A-Za-z0-9_./-]+)"'),
    ("clean-olean::test::vf4_chk_lia", ("@reach:crates/clean-olean/tests/vf4_chk_lia.rs",), RESOLVE_RELATIVE),
    ("clean-olean::test::vf4_chk_lia_f1", ("@reach:crates/clean-olean/tests/vf4_chk_lia_f1.rs",), RESOLVE_RELATIVE),
    ("clean-olean::test::vf4_chk_lia_quorum", ("@reach:crates/clean-olean/tests/vf4_chk_lia_quorum.rs",), RESOLVE_RELATIVE),
    ("clean-olean::test::vf5_f1_reference", ("@reach:crates/clean-olean/tests/vf5_f1_reference.rs",), RESOLVE_RELATIVE),
)


def _reachable_test_sources(crate_root: Path) -> set[Path]:
    """Every source file cargo compiles into the test target rooted at `crate_root`.

    A `@reach:` glob means "whatever this target actually builds", which is the
    only honest scope for an aggregating target: `tests/spec_suite.rs` is 56
    `#[path]` modules and a glob over `tests/*.rs` would sweep in the six files
    it deliberately does NOT include, widening its digest with records only a
    different target reads.

    The module walk is IMPORTED from `rust_modules.py`, the one walk this runner,
    `check_test_target_coverage.py` and `check_cargo_test_selectors.py` share, not
    copied. A byte-copied mirror drifts -- that is why the crystal discharge table
    stopped keeping one -- and these readers must agree about what a target
    compiles or one of them is deciding freshness for a file set the other does
    not have. It is asked for the POSSIBLE side: where rustc's answer depends on
    more than the walk reads, a file left out here would keep a stale digest
    fresh, so this scope ignores `cfg`, takes every candidate the walk can read
    (`include!`d files included) and, where it cannot place a file (a macro's
    `mod`, an unlexable file, an unreadable `include!` or `path`), every `.rs`
    under every directory in force; `rust_modules.walk` names the gaps that
    remain. The coverage gate takes only what surely builds. The root is passed
    as given: rustc resolves beside it, not beside a symlink's target.
    """
    rm = _rust_modules()
    return rm.reachable_from(crate_root, rm.Reach.POSSIBLE)


_REACH_MOD: Any = None


def _rust_modules() -> Any:
    """scripts/rust_modules.py, the module walk this runner shares with
    check_test_target_coverage.py and check_cargo_test_selectors.py: imported
    once, never copied."""
    import importlib.util

    global _REACH_MOD
    if _REACH_MOD is None:
        src = Path(__file__).resolve().parent / "rust_modules.py"
        spec = importlib.util.spec_from_file_location("clean_rust_modules", src)
        if not src.is_file() or spec is None or spec.loader is None:
            raise SystemExit(
                f"cannot load the module walk from {src}; a digest scope or test "
                f"coverage derived from it cannot be computed, and guessing one would "
                f"decide freshness for the wrong file set"
            )
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _REACH_MOD = mod
    return _REACH_MOD


# The pattern slot of a row whose reads are RESOLVED, not matched. A regex
# that captures `tests/x` out of `"../../tests/x"` assumes the literal is
# relative to the crate directory (`CARGO_MANIFEST_DIR`); an `include_str!`
# literal is relative to the FILE, so the same spelling names a crate-internal
# fixture in one place and a repository file in another (both shapes are in
# clean-kernel's source: `src/env/dag_serialization/tests.rs` reaches its own
# `tests/fixtures/` with `../../../tests/`, `src/env/carrier_differential_tests.rs`
# the repository's with `../../tests/` from the crate directory). So every
# `"../..."` literal in the comment-blanked source is resolved against both
# anchors, and a result is owed when it lies outside the crate directory and
# git can see it (tracked, or untracked and not ignored) -- exactly the files
# the digest itself hashes, so an output directory such as `metrics/` is never
# demanded on the box that happens to hold one.
_RELATIVE_LITERAL_RE = re.compile(r'"((?:\.\./)+[A-Za-z0-9_][A-Za-z0-9_./-]*)')


def _resolve_relative_reads(path: Path, crate_dir: Path, base: Path, code: str) -> set[str]:
    """Repository-relative candidates of every `"../..."` literal in `code`
    that exist and lie outside `crate_dir`. Visibility to git is decided by the
    caller, once for all rows."""
    found: set[str] = set()
    for literal in _RELATIVE_LITERAL_RE.findall(code):
        for anchor in (path.parent, crate_dir):
            candidate = Path(os.path.normpath(anchor / literal))
            if candidate == crate_dir or crate_dir in candidate.parents:
                continue
            try:
                rel = candidate.relative_to(base)
            except ValueError:
                continue
            if candidate.exists():
                found.add(rel.as_posix())
    return found


def _git_visible(base: Path, candidates: set[str]) -> set[str]:
    """The candidates git can see under `base`: a file listed by `ls-files -c -o
    --exclude-standard`, or a directory holding one. Fails closed: when git
    cannot be asked, every candidate is kept (an over-wide owed set refuses,
    never passes)."""
    if not candidates:
        return set()
    proc = subprocess.run(
        ["git", "-C", str(base), "ls-files", "-c", "-o", "--exclude-standard", "-z", "--"]
        + sorted(candidates),
        capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        return set(candidates)
    files = [f for f in proc.stdout.split("\0") if f]
    return {
        c for c in candidates
        if any(f == c or f.startswith(c.rstrip("/") + "/") for f in files)
    }


def _resolved_scan_rows(base: Path) -> list[tuple[str, tuple[str, ...], str]]:
    """One `RESOLVE_RELATIVE` row per lib and integration target of every
    package in `RESOLVED_SCAN_PACKAGES`, derived from the tree on each call so
    a target added later is scanned without anyone remembering to add it."""
    rows: list[tuple[str, tuple[str, ...], str]] = []
    for package in RESOLVED_SCAN_PACKAGES:
        crate = base / "crates" / package
        if (crate / "src").is_dir():
            rows.append((f"{package}::lib", (f"@tree:crates/{package}/src",), RESOLVE_RELATIVE))
        for test_root in sorted((crate / "tests").glob("*.rs")):
            rows.append((
                f"{package}::test::{test_root.stem}",
                (f"@reach:crates/{package}/tests/{test_root.name}",),
                RESOLVE_RELATIVE,
            ))
    return rows


def _crystal_extra_paths_owed(root: Path | None = None) -> dict[str, set[str]]:
    """Re-derive, per crystal target, the `data/crystal_*.json` files it reads.

    Read back from the SOURCES, never from `TARGET_EXTRA_PATHS` -- the list is
    the thing being checked, and a checker that consults its subject proves
    nothing.  Three separate lanes have now added a record that the row reads
    and forgotten to widen the digest; this makes the fourth impossible.

    Rows whose pattern is `RESOLVE_RELATIVE` (every target of the
    `RESOLVED_SCAN_PACKAGES`) resolve their relative literals instead of
    matching them; see that constant. A file is read only when its raw text
    contains `"../`: blanking a comment never creates a literal, so a file
    without one has nothing to resolve, and the 43 MB of clean-kernel's source
    is not blanked on every call.
    """
    # Resolved, so a path the module walk returns (it resolves symlinks) and a
    # path built from `base` compare equal: `relative_to` would otherwise drop
    # every read of a tree reached through a link (macOS's /var -> /private/var).
    base = (root or REPO_ROOT).resolve()
    owed: dict[str, set[str]] = {}
    resolved: dict[str, set[str]] = {}
    for target, globs, pattern in tuple(_EXTRA_PATH_SOURCES) + tuple(_resolved_scan_rows(base)):
        found: set[str] = set()
        crate_dir = base / "crates" / target.split("::")[0]
        for glob_pattern in globs:
            if glob_pattern.startswith("@reach:"):
                paths = sorted(_reachable_test_sources(base / glob_pattern[7:]))
            elif glob_pattern.startswith("@tree:"):
                paths = sorted((base / glob_pattern[6:]).rglob("*.rs"))
            else:
                parent, _, tail = glob_pattern.rpartition("/")
                paths = sorted((base / parent).glob(tail))
            for path in paths:
                text = path.read_text(encoding="utf-8", errors="replace")
                if pattern == RESOLVE_RELATIVE:
                    if '"../' in text:
                        found |= _resolve_relative_reads(
                            path, crate_dir, base, _blank_rust_comments(text))
                    continue
                code = _blank_rust_comments(text)
                for hit in re.findall(pattern, code):
                    # A pattern may capture (`../../tests/x` -> `tests/x`) or not
                    # (`data/crystal_*.json` is already repo-relative). findall
                    # returns the GROUP when there is one, the whole match when
                    # there is not, so both spellings normalise here rather than
                    # forcing every pattern to carry a group it does not need.
                    found.add(hit if isinstance(hit, str) else hit[0])
        if pattern == RESOLVE_RELATIVE:
            resolved[target] = resolved.get(target, set()) | found
        else:
            owed[target] = owed.get(target, set()) | found
    visible = _git_visible(base, set().union(*resolved.values()) if resolved else set())
    for target, found in resolved.items():
        owed[target] = owed.get(target, set()) | (found & visible)
    return owed


def _selftest_crystal_digest_coverage() -> None:
    """Prove the checker can say no, on every invocation, before it says yes.

    Four arms on a synthetic tree, ~1 ms, no repo I/O: a read record that is
    listed must be silent; the same record unlisted must be reported; a record
    named only in a `//!` doc must NOT be demanded; and a record named inside a
    string literal that itself contains `//` must still be found (the exact case
    a `split("//")` scanner truncates).  A checker whose refusal is only
    exercised when somebody remembers is the thing this check exists to stop.
    """
    import tempfile

    src = (
        '//! prose naming data/crystal_doc_only.json\n'
        'fn a() { let _ = read_json("data/crystal_listed.json"); }\n'
        'fn b() { let _ = read_json("data/crystal_unlisted.json"); }\n'
        'fn c() { panic!("see https://x/y data/crystal_after_slashes.json"); }\n'
    )
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        (base / "crates/clean-verify/tests/crystal_a1_lineage").mkdir(parents=True)
        (base / "crates/clean-verify/tests/crystal_a1_lineage/x.rs").write_text(src)
        (base / "crates/clean-verify/tests/crystal_a1_lineage.rs").write_text("")
        found = _crystal_extra_paths_owed(base)["clean-verify::test::crystal_a1_lineage"]
    expected = {
        "data/crystal_listed.json",
        "data/crystal_unlisted.json",
        "data/crystal_after_slashes.json",
    }
    if found != expected:
        raise SystemExit(
            "verify_runner SELFTEST FAILED: crystal digest re-derivation returned "
            f"{sorted(found)}, expected {sorted(expected)} -- the scanner can no "
            "longer tell a read record from a documented one, so its green is void"
        )


def _check_olean_world_inputs(root: Path | None = None) -> list[str]:
    """Every repository fixture read by the world-table build is a library input.

    The table is itself under the crate's source digest. This check keeps a new
    fixture in that table from being compiled while omitted from the digest.
    External installed toolchain bytes remain outside this repository check.
    """
    base = (root or REPO_ROOT).resolve()
    table = base / "crates/clean-olean/lean_worlds.tsv"
    try:
        lines = table.read_text().splitlines()
    except OSError as exc:
        return [f"cannot read olean world input table {table}: {exc}"]
    declared = set(PACKAGE_EXTRA_PATHS.get("clean-olean", ()))
    problems: list[str] = []
    fixtures: set[str] = set()
    for number, line in enumerate(lines, 1):
        if not line.strip() or line.startswith("#"):
            continue
        columns = line.split("\t")
        if len(columns) != 4 or not columns[3].strip():
            problems.append(f"lean_worlds.tsv:{number}: expected four columns and fixtures")
            continue
        for fixture in columns[3].split():
            path = Path(fixture)
            if path.is_absolute() or ".." in path.parts or "\\" in fixture:
                problems.append(f"lean_worlds.tsv:{number}: non-repository fixture {fixture}")
                continue
            candidate = base / path
            if not candidate.resolve().is_relative_to(base):
                problems.append(f"lean_worlds.tsv:{number}: external fixture {fixture}")
                continue
            if fixture not in declared:
                problems.append(f"clean-olean world fixture {fixture} is missing from PACKAGE_EXTRA_PATHS")
            if not candidate.is_file():
                problems.append(f"clean-olean world fixture is missing: {fixture}")
            else:
                fixtures.add(fixture)
    for fixture in sorted(fixtures - _git_visible(base, fixtures)):
        problems.append(f"clean-olean world fixture is not git-visible to the digest: {fixture}")
    return problems


def check_crystal_extra_paths(root: Path | None = None) -> list[str]:
    """Return one message per crystal record read but absent from the digest.

    One-directional by design: an entry LISTED but not re-derived here is fine
    and several are correct (the lane-13 freshness record is cited as
    provenance by `tests/fixtures/*.lineage.json`, not by any `.rs`).  Only the
    other direction can turn a stale green fresh, and only that is refused.
    """
    _selftest_crystal_digest_coverage()
    problems = _check_olean_world_inputs(root)
    base = (root or REPO_ROOT).resolve()
    library_of: dict[tuple[str, bool], set[str]] = {}

    def library(package: str, test_cfg: bool) -> set[str]:
        if (package, test_cfg) not in library_of:
            lib_root = base / "crates" / package / "src" / "lib.rs"
            library_of[(package, test_cfg)] = set(
                library_external_reads(lib_root, test_cfg, None if root is None else base)
                if lib_root.is_file() else ())
        return library_of[(package, test_cfg)]

    for target, owed in _crystal_extra_paths_owed(root).items():
        # A row also digests its package library's derived compile-time reads
        # (`library_external_reads`), the `#[cfg(test)]` ones too for the lib,
        # and an integration-test row its own target's (`row_target_reads`).
        package = target.split("::")[0]
        listed = (set(TARGET_EXTRA_PATHS.get(target, ())) | library(package, False)
                  | set(PACKAGE_EXTRA_PATHS.get(package, ())))
        if target == f"{package}::lib":
            listed |= library(package, True)
        parts = target.split("::")
        if len(parts) == 3 and parts[1] == "test":
            test_root = base / "crates" / package / "tests" / f"{parts[2]}.rs"
            if test_root.is_file():
                listed |= set(library_external_reads(
                    test_root, True, None if root is None else base))
        for missing in sorted(owed - listed):
            problems.append(
                f"{target} reads {missing} but it is not in TARGET_EXTRA_PATHS, so a "
                f"recorded GREEN for that target survives an edit to it"
            )
    return problems


def workspace_library_reads(meta: dict[str, Any]) -> tuple[str, ...]:
    """Every workspace library's compile-time reads outside its crate, with
    and without `cfg(test)`: what a workspace row compiles."""
    out: set[str] = set()
    for pkg in meta["packages"]:
        root = package_lib_root(meta, pkg["name"])
        if root is not None:
            out.update(library_external_reads(root, False))
            out.update(library_external_reads(root, True))
    return tuple(sorted(out))


def _builds_own_lib_tests(entry: dict[str, Any]) -> bool:
    """Does this row compile its package's library with `cfg(test)`? Its lib
    row, the lib's shards and roll-up, and any cargo test row with `--lib`."""
    if entry.get("kind") in ("lib", KIND_ROLLUP) or entry.get("_parent"):
        return True
    argv = entry.get("argv") or []
    return _build_phase_argv(argv) is not None and "--lib" in _split_libtest_args(argv)[0]


def target_file_name_problems(entries: list[dict[str, Any]]) -> list[str]:
    """Reject aliases of the shared record/log filename, also on case-folding filesystems."""
    names: dict[str, str] = {}
    problems: list[str] = []
    for entry in entries:
        target = entry["id"]
        key = safe_name(target).casefold()
        previous = names.get(key)
        if previous is not None and previous != target:
            problems.append(f"filename collision: {previous!r} and {target!r} map to {key!r}")
        else:
            names[key] = target
    return problems


def build_inventory(packages: list[str], with_gates: bool = True) -> list[dict[str, Any]]:
    # Fail closed BEFORE any verdict is derived or reported. An under-covering
    # digest does not make a run wrong; it makes an already-recorded GREEN read
    # fresh after the evidence beneath it moved -- so the wrong moment to notice
    # is while printing that GREEN.
    problems = check_crystal_extra_paths()
    if problems:
        raise SystemExit(
            "verify_runner: crystal digest coverage is incomplete -- add the path(s) to "
            "TARGET_EXTRA_PATHS:\n  " + "\n  ".join(problems)
        )
    meta = cargo_metadata()
    inv: list[dict[str, Any]] = []
    if with_gates:
        inv.extend(WORKSPACE_GATES)
        # On the board whatever --packages says: see RELEASE_PROFILE_TARGETS.
        inv.extend(RELEASE_PROFILE_TARGETS)
    for package in packages:
        inv.extend(package_targets(meta, package))
    # Records and logs share a namespace across invocations. A --packages
    # selection must not hide its alias in another package or a standing gate.
    known = list(inv) + list(WORKSPACE_GATES) + list(RELEASE_PROFILE_TARGETS)
    for package in meta["packages"]:
        if package["name"] not in packages and package.get("targets"):
            known.extend(package_targets(meta, package["name"]))
    name_problems = target_file_name_problems(known)
    if name_problems:
        raise SystemExit("verify_runner: target filenames are ambiguous:\n  "
                         + "\n  ".join(name_problems))
    profile_problems = check_profiles(inv)
    if profile_problems:
        raise SystemExit(
            "verify_runner: a row's build profile and its argv disagree:\n  "
            + "\n  ".join(profile_problems)
        )
    # Every test the scanned packages' libraries may compile runs in some row
    # (FEATURE_LIB_ROWS), and no debug row stands for a target its own root
    # compiles out (`compiled_out_problems`). Both judge the packages this
    # inventory holds, against the release rows whether or not it lists them
    # (`with_gates=False`, as `shards plan` builds it, leaves them out; they
    # are on the board all the same).
    board = inv + [r for r in RELEASE_PROFILE_TARGETS if r not in inv]
    coverage_problems = lib_test_coverage_problems(
        meta, [e for e in board if e["package"] in packages]) + compiled_out_problems(meta, board)
    if coverage_problems:
        raise SystemExit(
            "verify_runner: a test compiles in no row, or a row compiles nothing:\n  "
            + "\n  ".join(coverage_problems)
        )
    # attach the digest scope directories
    ws_dirs = sorted({Path(p["manifest_path"]).parent for p in meta["packages"]})
    for entry in inv:
        if entry["package"] == "__workspace__":
            entry["_dirs"] = ws_dirs
            # A workspace row compiles every library, test cfg included.
            library = workspace_library_reads(meta)
        else:
            entry["_dirs"] = path_dep_closure(meta, entry["package"])
            library = closure_library_reads(
                meta, entry["_dirs"], entry["package"], _builds_own_lib_tests(entry))
        # What the build leg compiles, for its warm key (build_warm_key): the
        # closure of each package it builds by name, and their libraries'
        # compile-time reads. A row that builds nothing by name uses `_dirs`.
        built = built_packages(entry.get("argv") or [])
        if built:
            bdirs: set[Path] = set()
            for name in built:
                bdirs.update(path_dep_closure(meta, name))
            build_reads = closure_library_reads(
                meta, sorted(bdirs), built[0] if len(built) == 1 else None,
                _builds_own_lib_tests(entry)) + tuple(
                path for package in meta["packages"]
                if Path(package["manifest_path"]).parent in bdirs
                for path in PACKAGE_EXTRA_PATHS.get(package["name"], ()))
            entry["_build_dirs"] = sorted(bdirs) + [
                REPO_ROOT / r for r in dict.fromkeys(build_reads)]
        # A gate whose verdict depends on files outside every crate dir declares
        # them here; `_dir_content_digest` accepts file pathspecs as readily as
        # directories, so they widen the scope rather than replacing it. Read
        # non-destructively: `_dirs` is rebuilt on every call, but the entry
        # dicts are the module-level ones, so popping the key would silently
        # narrow the digest on the second call.
        #
        # A lib SHARD takes its parent's list: the shards run the parent's
        # binary over a partition of its tests, so they read what it reads, and
        # `rollup` derives a missing shard's row from the parent's `_dirs`.
        # Every row takes its closure's derived library reads (see
        # `library_external_reads`), and its closure's declared build-script
        # reads (PACKAGE_EXTRA_PATHS): library inputs follow the exact source
        # closure (including the root's dev-dependencies, excluding a
        # dependency's dev-dependencies). Workspace gates already include all
        # workspace directories, so inherit them all.
        source_dirs = set(entry["_dirs"])
        inherited = tuple(
            path for package in meta["packages"]
            if Path(package["manifest_path"]).parent in source_dirs
            for path in PACKAGE_EXTRA_PATHS.get(package["name"], ())
        )
        extra = (
            tuple(entry.get("_extra_paths") or ())
            + tuple(TARGET_EXTRA_PATHS.get(entry["id"], ()))
            + tuple(TARGET_EXTRA_PATHS.get(entry.get("_parent") or "", ()))
            + (tuple(TARGET_EXTRA_PATHS.get(
                f"{entry['package']}::test::{entry['_replaces_debug_target']}", ()))
               if entry.get("_replaces_debug_target") else ())
            + tuple(PACKAGE_EXTRA_PATHS.get(entry["package"], ()))
            + inherited
            + library
            + row_target_reads(meta, entry)
        )
        extra = tuple(dict.fromkeys(extra))
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
        ["targo", "--unverified", "test", "--locked", "-p", package, "--lib", "--no-run", "--message-format=json"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        check=False,
    )
    if proc.returncode != 0:
        raise SystemExit(f"targo --unverified test --no-run failed for {package}:\n{proc.stderr[-4000:]}")
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
COMPILER_ENV_SELECTORS = (
    "RUSTC", "RUSTDOC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTDOC", "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
)


def _compiler_env_selectors() -> list[str]:
    return [key for key in COMPILER_ENV_SELECTORS if os.environ.get(key)]


def _compiler_identity_problem() -> str:
    selectors = _compiler_env_selectors()
    return ("compiler identity unavailable: explicit " + ", ".join(selectors) + " override"
            if selectors else "compiler identity unavailable")


def toolchain_id(fresh: bool = False) -> str:
    global _TOOLCHAIN_CACHE
    # A PATH trustc query cannot identify an environment-selected compiler or
    # wrapper. Refuse before the cache, without executing that alternate route.
    if _compiler_env_selectors():
        return "rustc-unavailable"
    if not fresh and _TOOLCHAIN_CACHE is not None:
        return _TOOLCHAIN_CACHE
    code, out = run_capture(["trustc", "-vV"])
    keep = [
        line
        for line in out.splitlines()
        if line.startswith(("rustc ", "commit-hash:", "host:", "release:"))
    ]
    identity = "|".join(keep) if code == 0 else "rustc-unavailable"
    if not fresh:
        # A status table shares one identity. Run-boundary reads must query the
        # live compiler without replacing that snapshot for other readers.
        _TOOLCHAIN_CACHE = identity
    return identity


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
    # --stdin-paths reads Git C-quoted lines, not literal newline-delimited
    # names. Quote every path byte: otherwise a file named '"x"' hashes x,
    # and embedded newlines split one filename into unrelated requests.
    quoted = ['"' + "".join(f"\\{byte:03o}" for byte in os.fsencode(path)) + '"'
              for path in files]
    stdout, stderr = proc.communicate("\n".join(quoted) + "\n" if quoted else "")
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


# These root inputs affect every target, even when crate sources and the
# currently resolved compiler identity stay unchanged. Hash absent files too:
# creating a legacy config or toolchain override must invalidate old results.
ROOT_BUILD_INPUTS = (
    "Cargo.toml", "Cargo.lock", ".cargo/config", ".cargo/config.toml",
    "rust-toolchain", "rust-toolchain.toml",
)
BUILD_ENV_KEYS = (
    "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS",
    "CARGO_BUILD_RUSTFLAGS", "CARGO_BUILD_RUSTDOCFLAGS",
    "CARGO_INCREMENTAL", "CARGO_BUILD_INCREMENTAL",
    "CARGO_BUILD_TARGET",
)


def _build_environment_bytes() -> bytes:
    """Declared compile/execution settings; values enter hashes, not records."""
    values = {key: value for key, value in os.environ.items()
              if key in BUILD_ENV_KEYS or key.startswith("CARGO_PROFILE_")
              or (key.startswith("CARGO_TARGET_")
                  and key.endswith(("_RUSTFLAGS", "_RUSTDOCFLAGS", "_LINKER", "_RUNNER")))}
    # Preserve old keys with no overrides; an explicitly empty value still
    # matters (e.g. encoded flags override ordinary flags even when empty).
    if not values:
        return b""
    return b"build-env=" + json.dumps(values, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=True).encode() + b"\n"


DIGEST_SCOPE = (
    "path-dep-closure(working tree) + root inputs("
    + ", ".join(ROOT_BUILD_INPUTS) + ") + trustc -vV + argv(JSON array) + compile/execution env"
)


def input_digest(entry: dict[str, Any], fresh: bool = False) -> str | None:
    """Current evidence key, or None when the compiler cannot be identified."""
    identity = toolchain_id(fresh=fresh)
    if identity in ("", "rustc-unavailable"):
        return None
    hasher = hashlib.sha256()
    hasher.update(b"schema=" + SCHEMA.encode() + b"\n")
    hasher.update(b"sources=" + _dir_content_digest(entry["_dirs"], fresh).encode() + b"\n")
    for extra in ROOT_BUILD_INPUTS:
        path = REPO_ROOT / extra
        blob = hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else "absent"
        hasher.update(f"{extra}={blob}\n".encode())
    hasher.update(_build_environment_bytes())
    hasher.update(b"toolchain=" + identity.encode() + b"\n")
    # Space-joining aliases ["tool", "a b"] and ["tool", "a", "b"].
    # Hash the vector, including empty arguments, rather than its display text.
    argv_json = json.dumps(entry["argv"], separators=(",", ":"), ensure_ascii=True)
    hasher.update(b"argv=" + argv_json.encode() + b"\n")
    # Only a non-debug profile is hashed, so every debug row keeps the digest
    # its records already carry (RELEASE_PROFILE_TARGETS).
    profile = entry_profile(entry)
    if profile != PROFILE_DEV:
        hasher.update(b"profile=" + profile.encode() + b"\n")
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


def _phys_ram_gb() -> float:
    """Physical RAM, or 0.0 when it cannot be read (then nothing is clamped)."""
    try:
        return os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") / 1073741824.0
    except (ValueError, OSError, AttributeError):
        return 0.0


class RssProfile(NamedTuple):
    """What a run cost in memory, and how sure we are of it.

    `peak_gb` is the number the gate weight is derived from. The other three
    exist because ONE number could not distinguish the two ways this
    measurement misleads, and both were live:

    * `raw_peak_gb` -- summing `ps rss` across a process group DOUBLE-COUNTS
      pages shared between its processes, so the sum can exceed physical RAM.
      That is not a hypothesis: `clean-verify::test::kernel_core_red_env_fidelity`
      has a recorded 57.26 GB peak on a 36 GB box (1.59x physical). A resident
      set larger than the machine is an artifact of the instrument, so
      `peak_gb` is clamped at physical RAM and the unclamped sum is kept here
      rather than quietly discarded.
    * `p50_gb` -- the MEDIAN sample, i.e. what the job cost for most of its
      life. `targo --unverified test -p clean-verify --test X` is a build followed by a much
      longer run, one process group, one peak: a three-minute rustc spike sets
      the weight that is then held for six hours of 1 GB test execution. Peak
      and median together say which shape a target is; peak alone cannot.
      Measured 2026-08-28: `axiom_ratchet` recorded 28.87 GB on a cold sweep
      and 9.11 GB warm, with nothing in either record to tell them apart.
    * `samples` -- a peak from two samples is not a peak. A row with a handful
      of samples is a lower bound, and a reader must be able to see that.
    """

    peak_gb: float
    raw_peak_gb: float
    p50_gb: float
    samples: int


def _rss_profile(pgid: int, stop: threading.Event) -> RssProfile:
    """Poll the child's whole process group; return its memory profile.

    Polling rather than getrusage: cargo spawns rustc and the test binary into
    the group, and the peak we care about is the SUM across the group at one
    instant, which getrusage(RUSAGE_CHILDREN) cannot give.
    """
    phys = _phys_ram_gb()
    samples: list[float] = []
    while not stop.is_set():
        try:
            out = subprocess.run(["ps", "-o", "rss=", "-g", str(pgid)],
                                 capture_output=True, text=True, timeout=5).stdout
            total_kb = sum(int(x) for x in out.split() if x.isdigit())
            samples.append(total_kb / 1048576.0)
        except Exception:
            pass
        stop.wait(2.0)
    if not samples:
        return RssProfile(0.0, 0.0, 0.0, 0)
    raw_peak = max(samples)
    peak = min(raw_peak, phys) if phys > 0 else raw_peak
    ordered = sorted(samples)
    p50 = ordered[len(ordered) // 2]
    return RssProfile(peak, raw_peak, min(p50, phys) if phys > 0 else p50, len(samples))


def _prior_peak_rss_gb(target_id: str, prior_record: dict[str, Any] | None = None) -> float | None:
    """The last peak this target ACTUALLY cost here, carried across interruptions.

    A killed run -- by its timeout, by `stop`, by a lane clearing a gate wedge --
    leaves a RUNNING record whose `peak_rss_gb` is blank, because no measurement
    was taken. Reading only that key therefore DOWNGRADES an interrupted target
    to the unmeasured default on its retry, which is the one direction a memory
    gate must never move by accident.

    Measured 2026-08-23: eight targets were stopped mid-queue while waiting at
    the gate, and `clean-verify::test::kernel_core_red_env_fidelity` -- whose
    measured peak is 56.3 GB -- would have re-admitted at the 12 GB default. A
    44 GB under-reservation is exactly the unaccounted concurrency that panicked
    this machine on 2026-08-19. So the RUNNING template carries the last known
    peak forward under `prior_peak_rss_gb`, and this reader falls back to it.

    A KILLED RUN'S PEAK IS A LOWER BOUND, NEVER A REPLACEMENT
    --------------------------------------------------------
    The 2026-08-23 fix above covered a run that recorded NO peak. It did not
    cover the commoner case: a run that was killed mid-flight and therefore
    recorded a peak *of the part that ran*. That number is smaller than the
    job by however much of the job never happened, and taking it as the new
    measurement silently CUTS the weight.

    Measured 2026-08-30 -- both rows live in `data/suite_state/` at the time,
    both with `timed_out: true`:

        axiom_ratchet     killed at 12799 s, peak 9.11 GB over a 28.87 GB
                          carried peak  ->  weight 44 GB cut to 14 GB
        vacuity_firewall  killed at 13890 s, peak 1.13 GB (its cargo leg was a
                          3.39 s no-op build) over a 28.68 GB carried peak
                          ->  weight 44 GB cut to 2 GB

    A 26 GB cut to a target previously measured at 28.68 GB is exactly the
    unaccounted concurrency that panicked this box on 2026-08-19 and
    2026-08-24, and the artifact would have called it "learning". So when the
    last run did not succeed, the two numbers are combined with `max` instead of
    the fresher one winning: a partial observation may RAISE a weight (it is
    real memory that was really used) and may never lower one. A successful run
    with stable inputs still replaces the carried peak outright -- that is
    the learning loop. A changed-input run uses the same conservative maximum
    as an interrupted run.
    """
    prior = prior_record if prior_record is not None else (load_record(target_id) or {})
    values = []
    for key in ("peak_rss_gb", "prior_peak_rss_gb"):
        value = _positive_gb(prior.get(key))
        if value is not None:
            values.append(value)
    if not values:
        return None
    if _run_was_cut_short(prior):
        return max(values)
    return values[0]


def _run_was_cut_short(record: dict[str, Any]) -> bool:
    """Did this record fail to measure one complete job at stable inputs?

    Deliberately generous: a timeout, a failed, skipped or ERROR verdict, changed inputs,
    or a record still marked RUNNING mean the measurement cannot replace history. Reading
    this wrong in the permissive direction only ever holds a weight HIGHER than
    strictly necessary, which is the safe side of a memory gate.
    """
    if record.get("inputs_moved_during_run") or (
        record.get("input_digest_at_finish") is not None
        and record["input_digest_at_finish"] != record.get("input_digest")
    ):
        return True
    if record.get("timed_out") is True:
        return True
    # Required-name evidence was captured with this measurement. Missing or
    # malformed observations cannot size a smaller complete workload.
    required = record.get("must_pass")
    if required is not None:
        observed = record.get("passed_tests")
        for names in (required, observed):
            if names is not None and (
                not isinstance(names, list) or any(not isinstance(name, str) for name in names)
            ):
                return True
        if must_pass_missing({"_must_pass": required}, record):
            return True
    # A failed or skipped invocation may only have reached a cheaper prefix.
    # It is evidence for raising a reservation, not for sizing a successful
    # retry below prior history or the unmeasured default.
    if record.get("status") in (STATUS_RED, STATUS_ERROR, STATUS_RUNNING, STATUS_SKIPPED):
        return True
    # A RUN THAT EXECUTED NO TEST MEASURED NO TEST.
    #
    # `status` alone does not catch this. Measured 2026-09-18 on
    # `clean-elab::lib::shard::lean4_corpus_tests`: an external dependency's
    # manifest stopped cargo before a single test ran, and the row recorded
    # RED with `counts.result_lines: 0`, `passed: 0`, a 51 s duration and a
    # 1.53 GB peak over ONE sample -- the cost of a cargo invocation dying.
    # That is not a partial observation of the job, it is an observation of
    # something else entirely, and taking it as the fresher measurement CUT the
    # weight from 23 GB to 3 GB against a carried 14.83 GB peak.
    #
    # This is the dual of the killed-run rule directly above, and it fails the
    # same safe way: such a peak may still RAISE a weight (the memory was
    # really used) and may never lower one. The runner already refuses to call
    # a zero-test run GREEN; this refuses to let it size a reservation.
    counts = record.get("counts")
    if isinstance(counts, dict):
        if not counts.get("result_lines"):
            # A completed shell gate need not run libtest. Unknown commands
            # and cargo-test gates still fail closed when no test ran.
            if record.get("kind") == "gate" and record.get("status") == STATUS_GREEN:
                command = record.get("command")
                if isinstance(command, str) and command:
                    try:
                        argv = shlex.split(command)
                    except ValueError:
                        return True
                    if argv and _build_phase_argv(argv) is None:
                        return False
            return True
        executed = (counts.get("passed") or 0) + (counts.get("failed") or 0)
        if executed == 0:
            return True
    return False


def _gate_budget_gb() -> int:
    """The machine-wide budget, mirroring `heavy_gate.sh`'s own arithmetic.

    A DUPLICATE, and knowingly so: this is used only to say whether a weight
    would be admitted exclusively, and importing it would mean shelling out to
    the gate for a read-only view. `heavy_gate.sh status` remains authoritative,
    and a test compares the two so the copy cannot drift in silence.
    """
    phys = _phys_ram_gb()
    if phys <= 0:
        return 0
    budget = int(phys - max(phys / 4, 8))
    if budget < 4:                      # heavy_gate's small-box floor
        budget = max(1, int(phys / 2))
    return budget


# A reservation below this is not worth a sentence however wrong it is.
RESERVATION_MIN_REPORT_GB = 4
# Below this fraction of its reservation, a job is called over-reserved.
RESERVATION_LOW_FRACTION = 0.4


def _reservation_verdict(weight_gb: int, profile: RssProfile) -> str | None:
    """Did the weight this row reserved match what the row actually used?

    A REPORT, deliberately: it changes no admission and resizes no request. It
    exists because the artifact already held both numbers and said nothing,
    and a reservation nobody can see is wrong is the same shape as a gate
    nobody has seen fail.

    `None` when there is nothing to say -- no samples, or a reservation small
    enough that being wrong about it costs the machine nothing.
    """
    if profile.samples <= 0 or profile.peak_gb <= 0:
        return None
    if profile.peak_gb > weight_gb:
        return (
            f"UNDER-RESERVED: reserved {weight_gb} GB, peaked at "
            f"{profile.peak_gb:.2f} GB. This is the direction that panicked "
            f"this machine on 2026-08-19 and 2026-08-24."
        )
    if weight_gb < RESERVATION_MIN_REPORT_GB:
        return None
    if profile.peak_gb >= weight_gb * RESERVATION_LOW_FRACTION:
        return None
    return (
        f"OVER-RESERVED: reserved {weight_gb} GB, peaked at "
        f"{profile.peak_gb:.2f} GB ({profile.peak_gb / weight_gb * 100:.0f}%), "
        f"median {profile.p50_gb:.2f} GB over {profile.samples} samples. A "
        f"weight above the machine budget is admitted EXCLUSIVELY, so an "
        f"over-sized one makes this a single-lane box for the whole run; "
        f"peak x1.5 = {max(MIN_TARGET_GB, math.ceil(profile.peak_gb * 1.5))} GB."
    )


def _gate_weight_gb(target_id: str) -> int:
    prior = load_record(target_id) or {}
    measured = _prior_peak_rss_gb(target_id, prior_record=prior)
    if measured is not None:
        # +50% headroom: peak RSS is sampled, so the true peak can fall between
        # samples, and a target's cost grows as the spec does.
        weight = max(MIN_TARGET_GB, math.ceil(measured * 1.5))
        # A partial observation can raise the default, never establish that a
        # not-yet-completed job fits below it. Keep that floor across retries.
        return max(DEFAULT_TARGET_GB, weight) if _run_was_cut_short(prior) else weight
    return DEFAULT_TARGET_GB


# ---------------------------------------------------------------------------
# THE BUILD/RUN RESERVATION SPLIT (2026-09-16)
# ---------------------------------------------------------------------------
#
# A `cargo test` invocation is two jobs wearing one weight. The compile is wide
# and short; the test run is usually narrow and long. The gate saw one process
# and reserved for its PEAK, so every target held a compile-shaped reservation
# for the whole of its run.
#
# Measured on this 24 GB / 16 GB-budget host, mid-sweep:
# `clean-elab::lib::shard::lean4_corpus_tests` held the ENTIRE budget
# exclusively (weight 19, clamped to 16) at an observed peak of 3.86 GB -- 24%
# of its reservation -- with a 1 GB shard queued behind it unable to backfill,
# because an oversize weight is admitted exclusively. Its stored record showed
# peak 12.13 GB against p50 0.85 GB over 1524 samples -- a 14x peak/median gap.
#
# CORRECTION, measured once this split existed to measure it: for THAT row the
# peak is the RUN, not the build. Separated, it reads build 0.0 GB over 1 sample
# (warm, no-op, correctly refused as thin) and run 14.83 GB over 1820 samples at
# a 0.66 GB median, with rss_group_sum_peak_gb equal to the peak, so it is not a
# clamping artifact. The split therefore does NOT lower that row's weight. The
# pre-split record could not have told the two readings apart -- a peak and a
# median that far apart are consistent with a build spike OR a run spike -- and
# distinguishing them is exactly what this code added, so the original claim
# should have been stated as the hypothesis it was. The 22.5x gap INSIDE its run
# is a real and separate defect: a brief spike in one test forcing a 61-minute
# exclusive hold, whose remedy is finding that test, not re-weighting below the
# spike, which would under-reserve during it.
#
# The split is still right, and it is demonstrated where a build DOES dominate:
# `macro_integration` reads build 3.36 GB over 17 samples against a run of 0.0.
#
# CLAUDE.md has named this brick for weeks -- "reserve big, build, release,
# reserve small, run ... nothing in this repo does it yet". This is it.
#
# What makes it safe rather than merely smaller: the two phases are reserved
# SEPARATELY and each is measured separately, so neither weight is ever inferred
# from the other. The run weight is derived from `run_peak_rss_gb` only; until a
# target has a split-phase record it falls back to the combined
# `peak_rss_gb`, which is the pre-split behaviour exactly. A partial observation
# can still only raise a weight, never lower one -- `_prior_peak_rss_gb` owns
# that rule and is untouched here.
def _build_phase_argv(argv: list[str]) -> list[str] | None:
    """`targo --unverified test ... --no-run`, or None when the split does not apply.

    Only a cargo TEST invocation splits, and the test is the ARGV SHAPE, never
    the row's `kind`. Most gate rows drive a script, which has no separable
    compile phase this runner can see, so they keep one reservation -- guessing
    at one would be inventing a phase boundary. But `gate::masquerade` is a
    `targo --unverified test` row and DOES split, which is the point of keying on argv: the
    rows that need the split are not the ones the `kind` field names. Measured
    2026-09-17 (then a `cargo test` row), that row reserved 18 GB -- above this
    box's 16 GB budget, so it held the machine EXCLUSIVELY -- while ITS OWN last
    run here peaked at 10.91 GB with a 3.5 GB median over 138 samples. A test row
    whose median is a third of its peak is paying for a compile.

    CITE THE RIGHT BOX. The 18 GB weight above is derived from a record measured
    on `m8Macbo128GB8TB`, not here: `data/suite_state/` holds 69 records from
    that 128 GB machine and 1 from this 24 GB one, and nothing in the weight
    path reads `runner_host`. Comparing the 64 targets measured on both, the
    median other/this peak ratio is 0.90x -- so importing a TEST target's peak
    is roughly neutral -- but every compile-bearing `gate::*` row reads HIGHER
    there (gate::check 6.00 -> 10.06, gate::clippy 8.32 -> 11.14, masquerade
    9.34 -> 11.46), because more cores run more rustc at once. An earlier draft
    of this comment quoted that foreign record's 0.14 GB median as an "82x
    spike" measured here. It was not measured here.

    `--no-run` must land BEFORE any `--` separator: everything after `--` is the
    test binary's own argv (the shard filters live there), and cargo would pass
    the flag through to libtest, which does not know it.
    """
    if len(argv) < 2:
        return None
    prog = os.path.basename(argv[0])
    # `targo --unverified test` / `targo trust test` (owner directive
    # 2026-09-28); a stock `cargo test` row keeps the same split.
    is_targo_test = (prog == "targo" and len(argv) >= 3
                     and argv[1] in ("--unverified", "trust") and argv[2] == "test")
    if not (is_targo_test or (prog == "cargo" and argv[1] == "test")):
        return None
    try:
        sep = argv.index("--")
    except ValueError:
        return list(argv) + ["--no-run"]
    return list(argv[:sep]) + ["--no-run"] + list(argv[sep:])


# How many RSS samples a phase needs before its peak may size a reservation, and
# which field carries that count. Three is the smallest number that cannot be a
# single unlucky read at process start or exit; a phase thinner than that is
# reported honestly as "not measured" rather than as a small number.
_PHASE_MIN_SAMPLES = 3
_PHASE_SAMPLE_FIELD = {
    "build_peak_rss_gb": "build_rss_samples",
    "run_peak_rss_gb": "rss_samples",
}


def _phase_peak_gb(target_id: str, field: str) -> float | None:
    """The recorded peak for ONE phase, or None if this target has never split.

    Deliberately NOT routed through `_prior_peak_rss_gb`: that reader carries a
    fallback chain for the combined figure, and a run-phase weight must never
    silently inherit a build-shaped number -- which is the whole defect being
    fixed.
    """
    rec = load_record(target_id)
    if not isinstance(rec, dict):
        return None
    # A THIN SAMPLE IS NOT A MEASUREMENT, and must never LOWER a weight.
    #
    # Measured 2026-09-16 on `clean-elab::lib::shard::macro_integration`: the run
    # phase finished in 0.01 s and the sampler got ONE sample reading 0.0 GB.
    # That is the sampler missing the process, not a run that needed no memory,
    # and a weight derived from it would be a partial observation lowering a
    # weight -- precisely what CLAUDE.md forbids after the 2026-08-30 incident
    # where two killed runs cut their own weights 44 -> 14 and 44 -> 2.
    #
    # So a phase peak counts only with a real sample floor behind it and a
    # positive value; anything thinner falls back to the combined weight, which
    # is the pre-split behaviour. The failure direction is deliberate: falling
    # back over-reserves, and over-reserving is slow, while under-reserving is
    # how this box panicked twice.
    # A RUN WHOSE INPUTS MOVED HAS NO PHASE ATTRIBUTION.
    #
    # The split reserves big, builds, releases, reserves small, runs. That holds
    # only while the build leg's work is still valid when the run leg starts. If
    # the tree moves in between -- another lane commits, or this one edits --
    # the run leg's `cargo test` RECOMPILES, and the compile lands inside the
    # figure that is supposed to describe the tests.
    #
    # RETRACTION 2026-09-17, same day, by the measurement that was supposed to
    # confirm it. This guard first landed citing
    # `clean-elab::lib::shard::lean4_corpus_tests` as a measured instance: its
    # build leg found nothing to do (0.0 GB, ONE sample), its run leg recorded
    # 14.83 GB over 1820 samples, and its record carries
    # `inputs_moved_during_run: true`, so the run leg's `cargo test` had plainly
    # recompiled. The first three quarters of that shard, run straight from the
    # prebuilt binary, peak at 0.46 / 0.40 / 0.54 GB, which seemed to settle it.
    #
    # The FOURTH quarter peaks at 15.10 GB -- from the prebuilt binary, no
    # cargo, nothing compiling -- and reproduces the recorded 14.83 GB almost
    # exactly. So that shard's peak is REAL TEST MEMORY, its 23 GB weight is
    # honest, and it was never an instance of this defect. (That run was KILLED
    # at its 1500 s budget without finishing, so 15.10 GB is a LOWER bound and
    # its count is unverified; the spike lives somewhere in tests 448-596.)
    #
    # The MECHANISM below is still real and the guard stays: a run leg that
    # recompiles does put build memory into the run phase's figure, and the
    # runner cannot tell that apart after the fact. What is withdrawn is the
    # claim to have measured it happening. Nothing here has yet been SEEN to
    # fail this way, which by this repo's own standard makes it a guard on a
    # mechanism rather than on an observation -- kept because it is free and
    # fails safe, not because a number vindicated it. The cost of being wrong in
    # this direction is one target falling back to its combined weight, and the
    # measurement above shows that fallback landing on the right answer anyway.
    #
    # The runner already knows: it records the digest at start and at finish and
    # correctly demotes the row's GREEN when they differ. It just never told the
    # WEIGHT. This is the same rule the killed-run guard states in the other
    # direction -- a number that did not measure what it claims to measure is
    # not a measurement -- and it fails the same safe way, back to `combined`.
    # Share the combined-weight rule: incomplete or unstable measurements
    # cannot supply lower replacement estimates for either phase.
    if _run_was_cut_short(rec):
        return None
    samples = rec.get(_PHASE_SAMPLE_FIELD.get(field, ""))
    if not isinstance(samples, int) or samples < _PHASE_MIN_SAMPLES:
        return None
    return _positive_gb(rec.get(field))


def cold_build_floor_gb(entry: dict[str, Any]) -> int:
    """The least a row's build phase may reserve: 1.5x its highest measured
    build peak (`_cold_build_peak_gb`, RELEASE_PROFILE_TARGETS), or 0 for a row
    that declares none. The same headroom a learned weight gets."""
    peak = _positive_gb(entry.get("_cold_build_peak_gb"))
    if peak is None:
        return 0
    return max(MIN_TARGET_GB, math.ceil(peak * 1.5))


def _split_weights_gb(target_id: str, build_floor_gb: int = 0) -> tuple[int, int]:
    """(build_gb, run_gb) for a split target.

    Each phase reads its OWN history and falls back to the combined weight, so
    the first split run of a target reserves exactly what the unsplit run did
    and the change cannot make a first admission larger.

    `build_floor_gb` (`cold_build_floor_gb`) only ever RAISES the build weight:
    a build's record depends on which builds ran before it in the shared target
    dir, so one record can learn less than another build of the same row cost.
    """
    combined = _gate_weight_gb(target_id)
    build_measured = _phase_peak_gb(target_id, "build_peak_rss_gb")
    run_measured = _phase_peak_gb(target_id, "run_peak_rss_gb")
    build_gb = (
        max(MIN_TARGET_GB, math.ceil(build_measured * 1.5))
        if build_measured is not None
        else combined
    )
    run_gb = (
        max(MIN_TARGET_GB, math.ceil(run_measured * 1.5))
        if run_measured is not None
        else combined
    )
    return max(build_gb, build_floor_gb), run_gb


# ---------------------------------------------------------------------------
# THE PACKAGE COLD-BUILD FLOOR (2026-11-13, self-proof unit E3 fix-up)
# ---------------------------------------------------------------------------
#
# A row learns its build weight from its own last build, and a build's cost
# depends on what the shared target dir already holds. Measured 2026-11-13 on
# m34: the 101 clean-kernel rows were first run after a hand prebuild, so every
# build leg was warm (0.0 GB over one sample) and each row learned 1 GB, while
# a cold rebuild of the same targets peaks at 12.57 GB (gate::fence's record:
# the four reference_* targets, 89 samples, at 220cabe1a), 10.48 GB (the lib
# test binary, heavy_gate `e3-kernel-plan`) and 6.86 to 7.72 GB (one feature
# set each, `e3-kernel-feat-build`). clean-kernel's dev-dependencies include
# clean-elab and clean-parser, so an edit to either rebuilds every kernel test
# target. The first kernel row to run after such an edit would have built cold
# under a 1 GB reservation: eleven GB unaccounted, the class that panicked this
# machine (reports/kernel-panic-rca-2026-08-19.md). clean-elab's rows were
# exposed the same way (6.75 GB recorded for one cold shard build, 1 GB
# learned), and no floor protected them.
#
# So the FIRST build of each build shape in a runner process reserves at least
# 1.5x the highest build peak recorded for the package it builds: a build of a
# shape the process has not yet seen succeed at the current sources may be
# cold, whatever the row's own record learned. A shape is the build argv less
# its `--test <name>` pairs (every integration target of one feature set links
# the same library and dev-dependencies); its key also carries the content
# digest of the built packages' closure, Cargo.toml, Cargo.lock and the
# toolchain, so an edit between two rows makes the second cold again. Later
# builds of a shape the same process built at the same key reserve what they
# learned: what they still compile is their own test binary.
#
# The peak is DERIVED FROM RECORDS: the highest `build_peak_rss_gb` or
# `max_build_peak_rss_gb` of any record whose command builds the package in
# the same profile (gate rows included: gate::fence carries clean-kernel's
# 12.57 GB). `max_build_peak_rss_gb` is carried forward by every run and only
# rises, so a cold peak survives the warm runs that follow it. A package with
# no recorded build peak reserves DEFAULT_TARGET_GB, the unmeasured default.
# PACKAGE_COLD_BUILD_SEED_GB holds the peaks measured OUTSIDE the runner,
# which no record carries; a seed never lowers what the records say.
#
# What this does not see: a cargo rebuild the source digest cannot predict --
# a file touched with identical content between two builds of one process,
# RUSTFLAGS changed underneath it, the target dir pruned mid-run. Such a build
# reserves what its row learned; its peak is then recorded and raises the
# package's floor for the next process.
PACKAGE_COLD_BUILD_SEED_GB: dict[tuple[str, str], tuple[float, str]] = {
    # The lib test binary's cold build, measured by heavy_gate (label
    # `e3-kernel-plan`, 2026-11-13T22:38:05Z, 4 min 11 s): no runner record
    # carries it, because `shards plan` builds outside the runner's gate.
    ("clean-kernel", PROFILE_DEV): (
        10.48, "heavy_gate e3-kernel-plan 2026-11-13T22:38:05Z (lib test build, cold)"),
    # clean-ck0's two cold builds, heavy_gate `e3-ck0-build` (0.56 and 0.76 GB,
    # 2026-11-13T22:43Z); its runner records saw only warm builds (0.0 GB).
    ("clean-ck0", PROFILE_DEV): (
        0.76, "heavy_gate e3-ck0-build 2026-11-13T22:43:44Z (cold)"),
    # The release build of `--test release_infer_parity` in a fresh target dir,
    # heavy_gate `e3fix-kernel-release-test-build` (2026-11-14T00:44:53Z, 11 min
    # 2 s): every release dependency of a kernel test build, cold.
    ("clean-kernel", PROFILE_RELEASE): (
        15.33, "heavy_gate e3fix-kernel-release-test-build 2026-11-14T00:44:53Z (cold)"),
}

_PACKAGE_FLAGS = ("-p", "--package")


def built_packages(argv: list[str]) -> tuple[str, ...]:
    """The packages a cargo test argv builds by name (`-p X`, `--package X`,
    `-pX`, `--package=X`), before any `--`; () for anything else."""
    if _build_phase_argv(argv) is None:
        return ()
    cargo, _ = _split_libtest_args(argv)
    out: list[str] = []
    i = 0
    while i < len(cargo):
        tok = cargo[i]
        if tok in _PACKAGE_FLAGS and i + 1 < len(cargo):
            out.append(cargo[i + 1])
            i += 1
        elif tok.startswith("--package="):
            out.append(tok[len("--package="):])
        elif tok.startswith("-p") and len(tok) > 2 and not tok.startswith("--"):
            out.append(tok[2:])
        i += 1
    return tuple(dict.fromkeys(out))


def build_shape(argv: list[str]) -> tuple[str, ...] | None:
    """The build-relevant part of a cargo test argv: its cargo half, less every
    `--test <name>` pair (`--test=<name>` too) and `--no-run`. None for a row
    with no build phase."""
    if _build_phase_argv(argv) is None:
        return None
    cargo, _ = _split_libtest_args(argv)
    shape: list[str] = []
    i = 0
    while i < len(cargo):
        tok = cargo[i]
        if tok == "--test" and i + 1 < len(cargo):
            i += 2
            continue
        if tok.startswith("--test=") or tok == "--no-run":
            i += 1
            continue
        shape.append(os.path.basename(tok) if i == 0 else tok)
        i += 1
    return tuple(shape)


def _positive_gb(value: Any) -> float | None:
    """A usable memory observation, including when read from permissive JSON."""
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        peak = float(value)
    except OverflowError:
        return None
    # Admission applies 50% headroom. Reject a value whose headroom would
    # overflow too, rather than passing infinity to ceil downstream.
    return peak if peak > 0 and math.isfinite(peak * 1.5) else None


def recorded_build_peak_gb(record: dict[str, Any] | None) -> float | None:
    """The highest build peak a record states: this run's build leg, or the
    peak carried forward from earlier ones (`max_build_peak_rss_gb`). Any
    sample count: a thin reading can raise a floor, never lower one."""
    if not isinstance(record, dict):
        return None
    values = [v for v in (_positive_gb(record.get("build_peak_rss_gb")),
                          _positive_gb(record.get("max_build_peak_rss_gb"))) if v is not None]
    return max(values) if values else None


_RECORDS_CACHE: list[dict[str, Any]] | None = None


def _all_records(fresh: bool = True) -> list[dict[str, Any]]:
    """Every record under STATE_DIR (top level and shards), parsed; unreadable
    ones skipped. `fresh=False` reuses one read per process, for read-only
    tables (`weights`); a run about to reserve memory reads them again."""
    global _RECORDS_CACHE
    if not fresh and _RECORDS_CACHE is not None:
        return _RECORDS_CACHE
    out: list[dict[str, Any]] = []
    if not STATE_DIR.is_dir():
        return out
    for path in sorted(STATE_DIR.glob("*.json")) + sorted(STATE_DIR.glob("shards/*/*.json")):
        try:
            rec = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(rec, dict):
            out.append(rec)
    _RECORDS_CACHE = out
    return out


def package_cold_build_peak_gb(package: str, profile: str,
                               fresh: bool = True) -> tuple[float | None, str]:
    """(highest build peak recorded for `package` in `profile`, where it came from).

    Read from every record whose command builds the package by name in that
    profile, from the `_cold_build_peak_gb` of each such release row (a peak
    measured outside the records, which a record need not carry), and from
    PACKAGE_COLD_BUILD_SEED_GB; (None, ...) when none has one.
    """
    best: float | None = None
    basis = "unmeasured"
    seed = PACKAGE_COLD_BUILD_SEED_GB.get((package, profile))
    if seed is not None:
        best, basis = seed[0], f"seed: {seed[1]}"
    for row in RELEASE_PROFILE_TARGETS:
        peak = _positive_gb(row.get("_cold_build_peak_gb"))
        if (peak is not None and package in built_packages(row.get("argv") or [])
                and entry_profile(row) == profile and (best is None or peak > best)):
            best, basis = peak, f"row {row['id']} `_cold_build_peak_gb`"
    for rec in _all_records(fresh):
        argv = str(rec.get("command") or "").split()
        if package not in built_packages(argv) or entry_profile(rec) != profile:
            continue
        peak = recorded_build_peak_gb(rec)
        if peak is not None and (best is None or peak > best):
            best, basis = peak, f"record {rec.get('target')} ({rec.get('finished_at') or 'unfinished'})"
    return best, basis


def package_cold_build_floor_gb(entry: dict[str, Any], fresh: bool = True) -> tuple[int, str]:
    """(GB, basis): the least a possibly-cold build of this row reserves -- 1.5x
    the highest recorded build peak of any package it builds, DEFAULT_TARGET_GB
    for a package with none. (0, "") for a row with no build phase."""
    packages = built_packages(entry.get("argv") or [])
    if not packages:
        return 0, ""
    floor, basis = 0, ""
    for package in packages:
        peak, why = package_cold_build_peak_gb(package, entry_profile(entry), fresh)
        gb = DEFAULT_TARGET_GB if peak is None else max(MIN_TARGET_GB, math.ceil(peak * 1.5))
        if gb > floor:
            floor = gb
            where = f"{package} ({entry_profile(entry)})"
            basis = (f"{where}: unmeasured, the {DEFAULT_TARGET_GB} GB default" if peak is None
                     else f"{where}: 1.5x {peak} GB, {why}")
    return floor, basis


# The build keys this process has seen a build leg finish with exit 0 at. A
# runner process is one `run` invocation; nothing is persisted, so a new
# process, a fresh target dir or a moved tree starts cold again.
_WARM_BUILDS: set[str] = set()
_WARM_LOCK = threading.Lock()


def build_warm_key(entry: dict[str, Any]) -> str | None:
    """The key a successful build leg marks warm: the build shape, the content
    digest of the built packages' sources (`_build_dirs`, or the row's `_dirs`),
    all ROOT_BUILD_INPUTS and the live compiler. None without a build or identity."""
    shape = build_shape(entry.get("argv") or [])
    if shape is None:
        return None
    dirs = entry.get("_build_dirs") or entry.get("_dirs") or []
    hasher = hashlib.sha256()
    hasher.update(("shape=" + "\0".join(shape) + "\n").encode())
    hasher.update(("profile=" + entry_profile(entry) + "\n").encode())
    hasher.update(("sources=" + (_dir_content_digest(list(dirs), fresh=True) if dirs else "none")
                   + "\n").encode())
    for extra in ROOT_BUILD_INPUTS:
        path = REPO_ROOT / extra
        blob = hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else "absent"
        hasher.update(f"{extra}={blob}\n".encode())
    hasher.update(_build_environment_bytes())
    identity = toolchain_id(fresh=True)
    if identity in ("", "rustc-unavailable"):
        return None
    hasher.update(("toolchain=" + identity + "\n").encode())
    return "sha256:" + hasher.hexdigest()


def build_is_warm(key: str | None) -> bool:
    if key is None:
        return False
    with _WARM_LOCK:
        return key in _WARM_BUILDS


def mark_build_warm(key: str | None) -> None:
    if key is not None:
        with _WARM_LOCK:
            _WARM_BUILDS.add(key)


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
# Exit codes from `heavy_gate.sh acquire` that mean REFUSED -- the request was
# understood and denied, so the target must NOT run.
#
# 75 is the one this box actually produces: in SMALL_BOX mode an over-budget
# request is refused with `exit 75` (heavy_gate.sh:541), and the gate's own
# selftest asserts it (:686). 2 was the only code accepted here until
# 2026-09-17 and `heavy_gate.sh` NEVER EMITS IT -- grep its exits: 0, 1, 3, 7,
# 64, 75. So the refusal branch below was dead, every refusal fell through the
# retry loop to `(None, False, False)`, and run_one took that as "gate absent"
# and ran the target UNGATED. On this 8 GB box that is 155 of 231 rows, and it
# is exactly the fail-open the 2026-08-24 kernel-panic postmortem forbids --
# the call site three hundred lines below already says "A refusal is never a
# licence to run ungated", it just never got the chance to act on one.
GATE_REFUSAL_CODES = (2, 75)


def _gate_acquire(weight_gb: int, label: str) -> tuple[str | None, bool, bool]:
    """Reserve `weight_gb` from the machine-wide gate.

    Returns `(token, admitted, refused)`.

    A gate MALFUNCTION -- missing script, lock starvation, an exception -- keeps
    the old fail-open contract: `admitted=False`, and the caller proceeds
    loudly, because a broken ledger must not stop the suite.

    A gate REFUSAL (exit 2: "this cannot run") is a DIFFERENT ANSWER and is NOT
    fail-open. Measured 2026-08-24: 31 clean-verify targets weighed more than
    this 24 GB box's whole budget, the gate refused every one, this function
    reported `admitted=False`, the caller ran them anyway -- TWO AT A TIME,
    since the worker runs `--jobs 2` -- and the kernel watchdog panicked the
    machine with two 23 GB spec binaries alive. Fail-open on a refusal converts
    "does not fit" into "unbounded", so a refusal now ERRORs the row instead.
    (After the same-day heavy_gate fix an oversize job is admitted exclusively
    rather than refused, so this path should no longer fire at all -- which is
    exactly why it must be closed rather than left as the silent fallback.)
    """
    if not HEAVY_GATE.exists():
        return None, False, False
    for attempt in range(GATE_ACQUIRE_ATTEMPTS):
        try:
            env = dict(os.environ, HEAVY_GATE_OWNER_PID=str(os.getpid()))
            proc = subprocess.run([str(HEAVY_GATE), "acquire", str(weight_gb), label],
                                  capture_output=True, text=True, env=env)
            token = proc.stdout.strip()
            if proc.returncode == 0 and token:
                return token, True, False
            if proc.returncode in GATE_REFUSAL_CODES:
                return None, False, True    # refusal: do not retry, do not run
        except Exception:
            pass         # never let the gate stop the suite from running
        if attempt + 1 < GATE_ACQUIRE_ATTEMPTS:
            time.sleep(GATE_ACQUIRE_BACKOFF_S * (attempt + 1))
    return None, False, False


def _gate_release(token: str | None) -> None:
    if token and HEAVY_GATE.exists():
        try:
            subprocess.run([str(HEAVY_GATE), "release", token],
                           capture_output=True, timeout=10)
        except Exception:
            pass


# --------------------------------------------------------------------------
# the write-through journal
# --------------------------------------------------------------------------
#
# WHY THIS EXISTS -- A CHECKOUT ATE A 14.33-HOUR SWEEP
# ----------------------------------------------------
# `data/suite_state/` is git-TRACKED, and it is also RUNNER OUTPUT that changes
# without a commit. Those two roles are incompatible in exactly one place: any
# `git checkout` / `git restore` / branch switch touching the directory silently
# reverts every record written since the last commit, with no error, no warning
# and no exit code. A routine crash-recovery checkout destroyed a complete
# 14.33-hour sweep that way; the results survived only because the
# worker's out-of-tree `worker.log` happened to still hold them, and recovering
# from a log is heroics, not a design.
#
# So the tracked directory stops being the truth and becomes a PROJECTION. The
# truth is an append-only journal outside the working tree, which git has no
# handle on at all:
#
#     write_record()  ->  journal_append()   [truth, append-only, out of tree]
#                     ->  _project_record()  [projection, tracked, reviewable]
#
# A checkout can still revert the projection. It can no longer lose anything:
# the next `status` re-projects the journal and says so out loud.
#
# WHY THE JOURNAL IS KEYED ON STATE_DIR, NOT ON REPO_ROOT
# -------------------------------------------------------
# `verify_runner_pinned.sh` runs THIS FILE from a throwaway worktree while
# exporting VERIFY_RUNNER_STATE_DIR back at the main checkout, precisely so both
# modes feed one artifact. REPO_ROOT differs between the two; STATE_DIR does
# not. Keying the journal on the resolved STATE_DIR therefore gives the
# invariant that matters -- ONE JOURNAL PER PROJECTION -- and gives the module's
# own tests a sandboxed journal for free, since they already redirect STATE_DIR.
#
# WHY NOT A LOCK OR A CHECKOUT HOOK
# ---------------------------------
# A pidfile-held guard only covers the in-flight case, and this runner has
# already shipped a pidfile that was never written on one of its two launch
# paths (`run --foreground`, fixed in edf6ec0f5) -- a guard keyed on that would
# have been disarmed and silent, which is the failure mode being fixed here. The
# journal has no armed/disarmed state: if the record was written, it is in the
# journal.
JOURNAL_SCHEMA = "clean.suite_journal/v1"

# Records under a `superseded-*` directory are the retired output of a retired
# scheme. They are kept as evidence and are MECHANICALLY INERT: `record_path`
# only ever addresses `shards/<parent>/<id>.json`, and every walk below globs
# one level, so nothing here reads them, rolls them up, or journals them.
SUPERSEDED_DIR_PREFIX = "superseded-"


def _journal_dir() -> Path:
    override = os.environ.get("VERIFY_RUNNER_JOURNAL_DIR")
    if override:
        return Path(override)
    xdg = os.environ.get("XDG_STATE_HOME")
    base = Path(xdg) if xdg else Path.home() / ".local" / "state"
    return base / "clean" / "suite-journal"


def journal_path() -> Path:
    """The journal for THIS projection directory.

    Outside the repository on purpose: a path inside it survives `git checkout`
    only while it stays ignored, and one `git clean -xdf` -- or one lane tidying
    its worktree, which this machine does routinely -- would put us back where
    we started. The name carries a readable stem plus a digest of the resolved
    state directory, so two clones never share a journal and neither can be
    mistaken for the other.
    """
    real = os.path.realpath(STATE_DIR)
    key = hashlib.sha256(real.encode("utf-8")).hexdigest()[:12]
    stem = re.sub(r"[^A-Za-z0-9]+", "-", Path(real).name).strip("-") or "state"
    return _journal_dir() / f"{stem}-{key}.jsonl"


def journal_append(record: dict[str, Any], origin: str = "measured") -> None:
    """Append one entry. Never rewrites, never truncates, never deletes.

    One `os.write` on an O_APPEND descriptor, so two runners (the main-tree one
    and the pinned one, which share a projection) interleave whole LINES and
    never each other's bytes. fsync'd, because the accident class this file
    exists for includes losing the machine.
    """
    path = journal_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    entry = {
        "schema": JOURNAL_SCHEMA,
        "appended_at": now_iso(),
        "origin": origin,
        "state_dir": str(STATE_DIR),
        "target": record.get("target"),
        "record": record,
    }
    payload = (json.dumps(entry, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
    try:
        os.write(fd, payload)
        os.fsync(fd)
    finally:
        os.close(fd)


def record_field_problem(record: dict[str, Any]) -> str | None:
    """Structural checks for fields consumed by status and recovery, not a full schema."""
    for key in ("commit", "started_at", "finished_at"):
        value = record.get(key)
        if value is not None and not isinstance(value, str):
            return f"record {key} must be a string or null"
    pid = record.get("pid")
    if pid is not None and (type(pid) is not int or pid < 0):
        return "record pid must be a nonnegative integer or null"
    counts = record.get("counts")
    if counts is not None:
        if not isinstance(counts, dict):
            return "record counts must be an object or null"
        for key in ("passed", "failed", "ignored", "result_lines"):
            if key in counts and (type(counts[key]) is not int or counts[key] < 0):
                return f"record counts.{key} must be a nonnegative integer"
    return None


def journal_read() -> tuple[dict[str, dict[str, Any]], list[str]]:
    """(latest entry per target, complaints).

    A malformed line is REPORTED, never skipped quietly: a torn write is exactly
    the situation where silence would hand back a partial history as if it were
    the whole one.
    """
    latest: dict[str, dict[str, Any]] = {}
    problems: list[str] = []
    path = journal_path()
    if not path.exists():
        return latest, problems
    with path.open("r", encoding="utf-8", errors="replace") as handle:
        for lineno, line in enumerate(handle, 1):
            line = line.strip()
            if not line:
                continue
            try:
                entry = json.loads(line)
            except json.JSONDecodeError as exc:
                problems.append(f"{path}:{lineno}: not valid JSON ({exc.msg})")
                continue
            if not isinstance(entry, dict) or entry.get("schema") != JOURNAL_SCHEMA:
                problems.append(f"{path}:{lineno}: not a {JOURNAL_SCHEMA} entry")
                continue
            record = entry.get("record")
            target = entry.get("target")
            if not isinstance(record, dict) or not isinstance(target, str):
                problems.append(f"{path}:{lineno}: entry carries no target/record pair")
                continue
            if record.get("target") != target:
                problems.append(f"{path}:{lineno}: record target does not match journal target {target!r}")
                continue
            problem = record_field_problem(record)
            if problem:
                problems.append(f"{path}:{lineno}: {problem}")
                continue
            latest[target] = entry
    return latest, problems


def projection_records() -> list[tuple[Path, dict[str, Any]]]:
    """Every record file the runner can ADDRESS, with its parsed content.

    Deliberately one level deep under `shards/<parent>/`, which is the whole
    disposition of the retired fine-cut records: they sit in a
    `superseded-*/` subdirectory that no walk here descends into.
    """
    out: list[tuple[Path, dict[str, Any]]] = []
    if not STATE_DIR.exists():
        return out
    paths = sorted(STATE_DIR.glob("*.json"))
    shard_root = STATE_DIR / "shards"
    if shard_root.is_dir():
        for parent in sorted(p for p in shard_root.iterdir() if p.is_dir()):
            if parent.name.startswith(SUPERSEDED_DIR_PREFIX):
                continue
            paths.extend(sorted(parent.glob("*.json")))
    for path in paths:
        try:
            doc = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(doc, dict) and isinstance(doc.get("target"), str):
            out.append((path, doc))
    return out


def _record_stamp(record: dict[str, Any]) -> str:
    return str(record.get("finished_at") or record.get("started_at") or "")


def _unordered_rollup_metadata(left: dict[str, Any], right: dict[str, Any]) -> bool:
    """Only timestamp-less derived plan metadata differs, not run evidence.

    A sharded parent's bucket is recomputed from its plan and measured children;
    its SUPERSEDED record is not a run. Host-local plan paths and declared counts
    have no temporal order. Retain an existing projection when those alone differ,
    but protect the entire historical superseded_run and every other field.
    """
    for record in (left, right):
        if (record.get("schema") != SCHEMA
                or record.get("source") != "derived"
                or record.get("kind") != KIND_ROLLUP
                or record.get("status") != "SUPERSEDED"
                or _record_stamp(record)):
            return False
    plan_metadata = {"declared_tests", "shard_count", "shard_plan"}
    return ({k: v for k, v in left.items() if k not in plan_metadata}
            == {k: v for k, v in right.items() if k not in plan_metadata})


def reconcile_projection(apply: bool = False) -> dict[str, Any]:
    """Compare the tracked projection against the journal; optionally re-project.

    Comparison verdicts, including two reasons not to blindly overwrite:

      ok           the projection matches the journal's latest entry.
      restore      the projection lost it, or disagrees with a journal entry
                   that is at least as new -- i.e. the accident. Re-projected.
      held         the journal's entry is `adopted` -- a snapshot this journal
                   never witnessed being measured -- and the projection differs.
                   An adoption is not evidence, so it never overwrites content.
                   It still restores a record the tree has LOST, which is the
                   whole reason to adopt.
                   Also: both records are timestamp-less derived SUPERSEDED
                   lib-rollups differing only in unordered plan metadata, with
                   identical historical run evidence. Neither host's path or
                   count establishes recency. Missing records still restore.
      foreign      the projection carries a record STRICTLY NEWER than anything
                   in this journal. That is a record from another machine,
                   arrived by git, and this journal has no standing to overwrite
                   it. Reported, never touched.
      unjournalled a record in the projection that this journal has never seen.
                   Also from elsewhere (or from before the journal existed);
                   `journal --adopt` takes local ownership of those.

    `held` is not hypothetical caution. On 2026-08-25 the lane that LOST the
    14.33-hour sweep recovered it from `worker.log` and pushed the reconstructed
    records; any journal that had adopted the reverted, stale versions first
    would have been holding an older snapshot of the same targets. A rule that
    said only "newer wins" would have depended on the reconstructed timestamps
    happening to compare the right way. This one does not depend on that.
    """
    latest, problems = journal_read()
    projected = {doc["target"]: doc for _path, doc in projection_records()}
    actions: list[dict[str, Any]] = []
    for target in sorted(latest):
        entry = latest[target]
        jrec = entry["record"]
        prec = projected.get(target)
        if prec is None:
            verdict = "restore"
            why = "record file is absent from the projection"
        elif prec == jrec:
            verdict = "ok"
            why = ""
        elif entry.get("origin") == "adopted":
            verdict = "held"
            why = ("journal entry is `adopted`, not measured here, and the projection "
                   "differs; an adoption never overwrites content")
        elif _unordered_rollup_metadata(jrec, prec):
            verdict = "held"
            why = ("timestamp-less derived rollups differ only in unordered plan metadata; "
                   "historical run evidence matches, so the existing projection is retained")
        elif _record_stamp(prec) > _record_stamp(jrec):
            verdict = "foreign"
            why = f"projection is newer ({_record_stamp(prec)} > {_record_stamp(jrec)}); left alone"
        else:
            verdict = "restore"
            why = "projection disagrees with the journal and is not newer"
        if verdict == "restore" and apply:
            _project_record(jrec)
        actions.append(
            {
                "target": target,
                "verdict": verdict,
                "reason": why,
                "journal_status": jrec.get("status"),
                "journal_stamp": _record_stamp(jrec),
                "origin": entry.get("origin"),
            }
        )
    unjournalled = sorted(set(projected) - set(latest))
    counts = {v: sum(1 for a in actions if a["verdict"] == v)
              for v in ("ok", "restore", "held", "foreign")}
    return {
        "schema": JOURNAL_SCHEMA,
        "journal": str(journal_path()),
        "journal_exists": journal_path().exists(),
        "state_dir": str(STATE_DIR),
        "applied": apply,
        "counts": counts,
        "unjournalled": unjournalled,
        "problems": problems,
        "actions": actions,
    }


def journal_adopt() -> dict[str, Any]:
    """Take local ownership of projection records the journal has never seen.

    Labelled `adopted`, NOT `measured`: an adoption entry says only "this file
    content was in the projection when the journal was created here". It makes
    no claim that this machine ran the target -- the record's own
    `runner_host` / `source` fields already say who did.
    """
    latest, _ = journal_read()
    adopted = []
    for _path, doc in projection_records():
        if doc["target"] in latest:
            continue
        journal_append(doc, origin="adopted")
        adopted.append(doc["target"])
    return {"adopted": sorted(adopted), "journal": str(journal_path())}


def heal_projection(quiet: bool = False) -> dict[str, Any]:
    """Re-project anything the projection lost, and SAY SO.

    Called at the top of `status`, because the projection is derived data and a
    silently stale derived file is the entire defect. Loud on stderr so
    `status --json` stays machine-readable.
    """
    report = reconcile_projection(apply=True)
    # Take ownership of anything that arrived some other way -- a record pulled
    # from another machine, or written before this journal existed. Only when a
    # journal ALREADY exists: a throwaway worktree that nobody has run the
    # runner in should not mint a journal for a projection it will never write.
    # Safe by construction now that an `adopted` entry can never overwrite
    # differing content; without that rule this would be a way to launder a
    # stale snapshot into the durable record.
    if journal_path().exists():
        newly = journal_adopt()["adopted"]
        if newly and not quiet:
            print(f"[journal] adopted {len(newly)} record(s) the journal had not seen "
                  f"(labelled `adopted`, never `measured`)", file=sys.stderr)
    restored = [a["target"] for a in report["actions"] if a["verdict"] == "restore"]
    if restored and not quiet:
        print(
            f"[journal] RESTORED {len(restored)} record(s) that {STATE_DIR} had lost or "
            f"reverted, from {report['journal']}: "
            + ", ".join(restored[:8])
            + (f" (+{len(restored) - 8} more)" if len(restored) > 8 else "")
            + "\n[journal] a checkout, restore or branch switch dropped or rewound them; the "
              "journal is the truth and has re-projected them. Commit the restored files.",
            file=sys.stderr,
        )
    if report["problems"] and not quiet:
        for problem in report["problems"]:
            print(f"[journal] MALFORMED: {problem}", file=sys.stderr)
    return report


def cmd_journal(args: argparse.Namespace) -> int:
    if args.path:
        print(journal_path())
        return 0
    if args.adopt:
        result = journal_adopt()
        print(f"journal: {result['journal']}")
        print(f"adopted {len(result['adopted'])} record(s) not previously journalled")
        for target in result["adopted"]:
            print(f"  + {target}")
        return 0
    report = reconcile_projection(apply=args.apply)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"journal:   {report['journal']}"
              f"{'' if report['journal_exists'] else '  (DOES NOT EXIST)'}")
        print(f"projection {report['state_dir']}")
        counts = report["counts"]
        print(f"ok {counts['ok']}   restore {counts['restore']}   held {counts['held']}   "
              f"foreign {counts['foreign']}   unjournalled {len(report['unjournalled'])}")
        for action in report["actions"]:
            if action["verdict"] != "ok":
                print(f"  {action['verdict']:<8} {action['target']}: {action['reason']}")
        for target in report["unjournalled"]:
            print(f"  unjournalled {target}")
        for problem in report["problems"]:
            print(f"  MALFORMED {problem}")
        if args.apply:
            print("(re-projected every `restore` row above)")
    if report["problems"]:
        return 1
    if not args.apply and report["counts"]["restore"]:
        return 1
    return 0


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
        record = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeError):
        problem = "record file is not valid UTF-8 JSON"
    else:
        if not isinstance(record, dict):
            problem = "record file must contain a JSON object"
        elif record.get("target") != target_id:
            problem = f"record target does not match requested target {target_id!r}"
        else:
            problem = record_field_problem(record)
            if problem is None:
                return record
    # Keep bad evidence on disk for inspection, but never let it supply a
    # verdict or masquerade as an absent record. derive reports this reason.
    return {"target": target_id, "status": STATUS_ERROR,
            "notes": problem, "_record_error": problem}


def _project_record(record: dict[str, Any]) -> None:
    """Write the tracked, reviewable copy. Atomic, so no reader sees a half file."""
    path = record_path(record["target"])
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def write_record(record: dict[str, Any]) -> None:
    """JOURNAL FIRST, then project. The order is the protection.

    Journalling after projecting would leave a window in which the tracked file
    exists and the durable one does not -- and that window is precisely when a
    checkout is fatal. Journal-first can at worst leave an entry whose
    projection has not landed yet, which the next `status` repairs.
    """
    try:
        journal_append(record)
    except OSError as exc:
        # A runner that cannot journal is a runner whose results are again
        # checkout-fragile -- but throwing away a measurement that cost hours
        # because $HOME is unwritable would be strictly worse than the problem.
        # So: project it anyway, say so loudly, and let the record be caught at
        # push time. `check_suite_journal.py` clause J5 refuses a record that is
        # uncommitted AND unjournalled, which is exactly what this leaves behind.
        print(
            f"[journal] WRITE FAILED for {record.get('target')}: {exc}\n"
            f"[journal] the record is being projected to {STATE_DIR} anyway, but NOTHING "
            f"durable holds it -- one `git checkout` ends it. Fix {journal_path().parent} "
            f"or set VERIFY_RUNNER_JOURNAL_DIR, then re-run `journal --adopt`.",
            file=sys.stderr,
        )
    _project_record(record)


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


def zero_exit_test_conflict(counts: dict[str, Any] | None) -> str | None:
    """A successful command cannot establish a pass while reporting failed tests."""
    failed = (counts or {}).get("failed", 0)
    if failed > 0:
        return (f"command exited 0 but reported failed tests ({failed}); "
                "exit/result evidence conflicts, so this is not a measured pass")
    return None


def zero_test_run(record: dict[str, Any]) -> str | None:
    """Did a GREEN row exit 0 having run NO tests at all?

    THE SAME PROPERTY AS ABOVE, UNBOUNDED FROM SHARDS (2026-08-26).

    `shard_count_mismatch` states the principle correctly and then returns early
    unless `entry["_shard"]` is set, so every NON-shard row was exempt from it --
    `gate::masquerade` (`targo --unverified test ... --lib -- masquerade`) among them. A
    filter that stops selecting is not a sharding-specific hazard; it is what
    `cargo test --locked -p clean-kernel axiom_refutation_gate` did when measured
    (2026-08-26), exiting 0 with "0 passed; 0 failed; 0 ignored; 0 measured; 10412
    filtered out" because that gate lives in clean-verify.

    The signal is exact and needs no argv parsing: libtest printed at least one
    `test result:` line -- so a test binary really did run -- and the passed +
    failed total is zero. Ignored tests did not execute and cannot supply a
    measurement. A shell gate produces no such line
    (`result_lines == 0`) and is untouched; a target that genuinely declares
    zero tests is not a pass either, and reads UNKNOWN, which is the honest
    bucket for a measurement of nothing.

    Measured over the 196 records in `data/suite_state/` carrying counts on the
    day this landed: ZERO would flip. It fires on the new class only.
    """
    counts = record.get("counts") or {}
    if int(counts.get("result_lines", 0)) < 1:
        return None
    ran = (
        int(counts.get("passed", 0))
        + int(counts.get("failed", 0))
    )
    if ran == 0:
        return (
            "exited 0 having run ZERO tests -- ignored tests did not execute, "
            "and an empty selection is also reported as `ok` by libtest"
        )
    return None


def derive(
    entry: dict[str, Any],
    record: dict[str, Any] | None,
    digest: str | None,
    shard_rows: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Map (inventory entry, stored record, current digest) -> reported bucket.

    This is the only place a bucket is decided, and it defaults to UNKNOWN.
    """
    target = entry["id"]
    base = {"target": target, "kind": entry["kind"], "package": entry["package"]}

    if digest is None:
        return {**base, "bucket": BUCKET_UNKNOWN,
                "reason": _compiler_identity_problem() + "; no current input digest", "last_known": None}
    if entry["kind"] == KIND_ROLLUP:
        return rollup(entry, digest, shard_rows or [])

    if record is None:
        return {**base, "bucket": BUCKET_UNKNOWN, "reason": "never run by this runner", "last_known": None}

    problem = record.get("_record_error") or record_field_problem(record)
    if problem:
        return {**base, "bucket": BUCKET_UNKNOWN,
                "reason": f"invalid record: {problem}", "last_known": None}

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

    # Before the digest, so the reason names the profile: the digest of a
    # non-debug row hashes its profile too, so a mismatch is stale there anyway.
    if entry_profile(record) != entry_profile(entry):
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": (
                f"recorded under the {entry_profile(record)} profile; this row measures "
                f"the {entry_profile(entry)} profile, and one build never stands for the other"
            ),
            "last_known": last_known,
        }

    # A run spanning different inputs never measured one coherent snapshot.
    # Returning the tree to its start digest cannot rehabilitate that run.
    # Check both fields: a false flag must not override unequal recorded hashes.
    finish_digest = record.get("input_digest_at_finish")
    if record.get("inputs_moved_during_run") or (
        finish_digest is not None and finish_digest != record.get("input_digest")
    ):
        return {
            **base,
            "bucket": BUCKET_UNKNOWN,
            "reason": "inputs changed during the recorded run; remeasure a stable snapshot",
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
        conflict = zero_exit_test_conflict(record.get("counts"))
        if conflict:
            return {**base, "bucket": BUCKET_UNKNOWN, "reason": conflict,
                    "last_known": last_known}
        # Shard first: for a shard it knows the PLANNED count, so it says "ran 0
        # tests, the shard plan declares 5" where the general rule can only say
        # "ran zero". Same verdict either way; the more specific diagnostic wins.
        mismatch = shard_count_mismatch(entry, record)
        if mismatch:
            return {
                **base,
                "bucket": BUCKET_UNKNOWN,
                "reason": f"shard exited 0 but {mismatch}; its filter no longer selects its planned tests",
                "last_known": last_known,
            }
        vacuous = zero_test_run(record)
        if vacuous:
            return {
                **base,
                "bucket": BUCKET_UNKNOWN,
                "reason": f"{vacuous}; re-point the filter or the package",
                "last_known": last_known,
            }
        missing = must_pass_missing(entry, record)
        if missing:
            return {
                **base,
                "bucket": BUCKET_UNKNOWN,
                "reason": (
                    f"exited 0 but never reported `ok` for must-pass {missing}: the tests "
                    "this row exists for did not run (compiled out, renamed or unselected)"
                ),
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

# EXIT 0 IS NOT ALWAYS A MEASUREMENT.
#
# Several gates under scripts/ deliberately exit 0 when a prerequisite is
# missing -- source_elab_gate.sh and kv_ratchet_gate.sh both do -- and both say
# so in a machine-readable verdict line rather than only in prose:
#
#     SRCELAB_GATE=skipped:no-binary
#     KV_RATCHET_GATE=skipped:no-corpus
#
# Exiting 0 is right for the pre-push hook, which must not refuse a pusher over
# an unbuilt release binary. It is WRONG for this artifact, whose entire claim
# is that a row never says more than was measured: recorded GREEN,
# `gate::srcelab` asserts the source-elab ratchet held when nothing ran at all.
#
# Measured 2026-08-23 at 3a2aaaa2e, which is what prompted this:
#
#     [worker] DONE (1/11) gate::srcelab -> GREEN (527.7s) SRCELAB_GATE=skipped:no-binary
#
# That row is UNKNOWN -- the absence of information, which CLAUDE.md says is
# never rounded up in either direction. The verdict grammar is the gates' own,
# so this reads their contract rather than inventing one.
_SKIPPED_VERDICT_RE = re.compile(r"^[A-Z][A-Z0-9_]*_GATE=skipped:(\S+)", re.M)

# A NON-ZERO EXIT IS NOT ALWAYS A MEASUREMENT EITHER.
#
# _SKIPPED_VERDICT_RE above closes the exit-0 half of this: a gate that exits 0
# without measuring anything is UNKNOWN, not a pass. The non-zero half was still
# open, and it fails the other way -- toward a red the code did not earn.
#
# `rust-toolchain.toml` pins `channel = "trust"`, and the Trust frontends
# AUTHENTICATE themselves before doing any work: they hash the resolved stage2
# binary and every ancestor directory of it, and refuse to run if any of that
# moves while they are running. On a single-lane box that is a sound tamper
# check. On this one it is a hair trigger, because one of those ancestors is
# `$HOME` -- the HOME DIRECTORY -- and a dozen lanes create and delete
# worktrees and scratch files directly inside it.
#
# Measured 2026-08-25 at d67054a45, `gate::clippy`:
#
#     error: branded Tippy driver identity changed: directory-chain identity
#     changed while embedded Tippy compiler was running: selected Trust
#     toolchain directory ancestor `$HOME` changed identity or contents
#
# and the row was recorded RED after 23.6s. The toolchain was not tampered with:
# `targo-tippy` had not been written since Aug 8, while `$HOME` carried
# an mtime from that same minute. Clippy never linted a line, so the run says
# NOTHING about whether the workspace is clean -- and "RED" says it is dirty.
#
# That is the same defect as a stale GREEN, pointed the other way, and this
# repo's rule is that UNKNOWN is never rounded up in EITHER direction. So a
# refusal is recorded ERROR, which `derive` sends to UNKNOWN.
#
# This does not weaken the gate. UNKNOWN is not a pass: `cmd_gate` returns 2 on
# any UNKNOWN row, so an unrunnable lint gate still fails the board -- it just
# fails as "could not be measured" instead of as "your code is broken", which is
# the actionable difference. A run that emitted real lint errors AND then hit a
# refusal is also incomplete, and reporting it UNKNOWN is the honest reading:
# nothing can claim those were all the errors.
#
# Matched on the frontends' own refusal vocabulary. None of these strings can
# appear in a clippy diagnostic.
_TOOLCHAIN_REFUSAL_RE = re.compile(
    r"^.*(?:"
    r"changed identity or contents"
    r"|unauthenticated toolchain process"
    r"|protected Trust toolchain directory"
    r"|protected Targo frontends cannot be"
    r").*$",
    re.M,
)

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
    text = shlex.join(argv)
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
    build_log_path = LOG_DIR / "build" / f"{safe_name(entry['id'])}.log"
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = str(target_dir())
    env.setdefault("CARGO_TERM_COLOR", "never")

    # Weight from what this target ACTUALLY cost here last time. Read BEFORE the
    # RUNNING template below overwrites the record -- otherwise it reads its own
    # blank `peak_rss_gb` and every target admits at the default forever. That
    # bug was live for one commit; the test below pins it.
    gate_weight = _gate_weight_gb(entry["id"])
    prior_peak = _prior_peak_rss_gb(entry["id"])
    # The highest build peak this row has recorded, carried forward so a warm
    # build cannot erase the cold one the package floor is derived from.
    prior_max_build = recorded_build_peak_gb(load_record(entry["id"]))
    build_argv = _build_phase_argv(entry["argv"])
    # Snapshot both phases before RUNNING replaces the previous measurement.
    # The cold-build floor is applied below, after its current basis is known.
    prior_build_gb, prior_run_gb = (
        _split_weights_gb(entry["id"]) if build_argv is not None
        else (gate_weight, gate_weight)
    )

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
        "digest_scope": DIGEST_SCOPE
        + ("" if entry_profile(entry) == PROFILE_DEV else " + profile"),
        # The build profile this record measured. `derive` refuses a record
        # whose profile is not its row's; absent (older records) means debug.
        "profile": entry_profile(entry),
        "started_at": now_iso(),
        "finished_at": None,
        "duration_s": None,
        "exit_code": None,
        "final_line": None,
        "counts": None,
        "log": repo_relative(log_path),
        "build_log": None,  # populated only after the build transcript is opened
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
        # The same measurement's provenance -- see RssProfile. `peak_rss_gb` is
        # clamped at physical RAM; the unclamped group sum, the median sample
        # and the sample count are kept so a reader can tell a real 28 GB
        # target from a three-minute build spike held for six hours, and can
        # tell either from a peak taken over four samples.
        "rss_group_sum_peak_gb": None,
        "rss_p50_gb": None,
        "rss_samples": None,
        # The last peak this target cost here, carried forward so a run that is
        # killed cannot downgrade its own retry to the unmeasured default. It is
        # provenance for the weight, never a claim that THIS run measured
        # anything -- that is what `peak_rss_gb` above is for, and it stays blank
        # until the sampler returns.
        "prior_peak_rss_gb": prior_peak,
        # The highest build-leg peak any run of this row recorded: raised by a
        # build that peaks above it, never lowered. The package cold-build
        # floor reads it (package_cold_build_peak_gb).
        "max_build_peak_rss_gb": prior_max_build,
        "gate_weight_gb": gate_weight,
        # Whether the machine-wide gate actually reserved that weight. False
        # means the row ran with NO reservation -- see _gate_acquire.
        "gate_admitted": None,
        # How that reservation compared to what the job actually used, in
        # WORDS, so a stale weight is a thing the artifact SAYS and not a thing
        # a reader has to derive from two other fields. See _reservation_verdict.
        "reservation_verdict": None,
        # `duration_s` is wall time from the moment the worker picked this row
        # up, so it INCLUDES the block at heavy_gate. These two split it.
        # Measured 2026-08-28: axiom_ratchet's ERROR row reads duration 22444.2s
        # against a 12799s timeout -- 9,645 s of it, 2h41m, was queueing. Every
        # cross-sweep "this got slower" comparison drawn from `duration_s`, and
        # the next run's timeout budget, were reading that queue.
        "gate_wait_s": None,
        "exec_duration_s": None,
        "notes": "",
    }
    if digest is None:
        problem = _compiler_identity_problem()
        record.update(status=STATUS_ERROR, finished_at=now_iso(), log=None,
                      duration_s=round(time.time() - started, 1),
                      final_line=f"<{problem}; target NOT run>",
                      notes=f"No input digest: {problem}; target NOT run")
        write_record(record)
        return record
    write_record(record)

    # ---- PHASE 1 of the split: compile under a build-shaped reservation, and
    # RELEASE it before the run phase asks for its own. Only a successful build
    # may advance: a failed, killed or refused build could compile again under
    # the smaller run reservation. Retain that build's own result instead.
    if build_argv is not None:
        build_floor = cold_build_floor_gb(entry)
        # A shape this process has not built at the current sources may be
        # cold: it reserves the package floor (see PACKAGE_COLD_BUILD_SEED_GB).
        warm_key = build_warm_key(entry)
        if build_is_warm(warm_key):
            record["build_floor_basis"] = (
                "warm: this runner process built the same shape at the same sources")
        else:
            package_floor, package_basis = package_cold_build_floor_gb(entry)
            if package_floor > build_floor:
                build_floor = package_floor
            record["build_floor_basis"] = (
                f"possibly cold (first build of its shape in this process): {package_basis}")
        # Use the pre-RUNNING phase estimates; a package floor can only raise
        # the build reservation and never changes the run estimate.
        build_gb, run_gb = max(prior_build_gb, build_floor), prior_run_gb
        record["gate_weight_build_gb"] = build_gb
        record["gate_weight_run_gb"] = run_gb
        if build_floor:
            record["gate_weight_build_floor_gb"] = build_floor
        b_wait_started = time.time()
        b_token, b_admitted, b_refused = _gate_acquire(build_gb, entry["id"] + " [build]")
        # Keep the build's clocks and transcript even when tests cannot start.
        record["build_gate_wait_s"] = round(time.time() - b_wait_started, 1)
        b_launch_error = None
        b_timed_out = False
        build_rc = None
        record["build_gate_admitted"] = b_admitted
        if not b_refused:
            b_stop = threading.Event()
            b_prof: list[RssProfile] = []
            b_exec_started = time.time()
            bproc: subprocess.Popen[str] | None = None
            try:
                build_log_path.parent.mkdir(parents=True, exist_ok=True)
                with open(build_log_path, "w", encoding="utf-8") as bh:
                    record["build_log"] = repo_relative(build_log_path)
                    bproc = subprocess.Popen(
                        build_argv, cwd=str(REPO_ROOT), stdout=bh,
                        stderr=subprocess.STDOUT, env=env, text=True,
                        start_new_session=True,
                    )
                    with _LIVE_LOCK:
                        _LIVE_CHILDREN.add(bproc.pid)
                    bsampler = threading.Thread(
                        target=lambda: b_prof.append(_rss_profile(bproc.pid, b_stop)),
                        daemon=True,
                    )
                    bsampler.start()
                    try:
                        bproc.wait(timeout=timeout)
                    except subprocess.TimeoutExpired:
                        b_timed_out = True
                        try:
                            os.killpg(bproc.pid, signal.SIGKILL)
                        except (ProcessLookupError, PermissionError):
                            bproc.kill()
                        bproc.wait()
                    finally:
                        b_stop.set()
                        bsampler.join(timeout=5)
                        with _LIVE_LOCK:
                            _LIVE_CHILDREN.discard(bproc.pid)
            except OSError as exc:
                b_launch_error = str(exc)
                b_stop.set()
            record["build_exec_duration_s"] = round(time.time() - b_exec_started, 1)
            if b_prof:
                record["build_peak_rss_gb"] = round(b_prof[0].peak_gb, 2)
                record["build_rss_p50_gb"] = round(b_prof[0].p50_gb, 2)
                record["build_rss_samples"] = b_prof[0].samples
            peaks = [p for p in (prior_max_build, _positive_gb(record.get("build_peak_rss_gb")))
                     if p is not None]
            record["max_build_peak_rss_gb"] = max(peaks) if peaks else None
            # Only a build that finished, exit 0, inside its budget, makes its
            # shape warm for the rest of this process.
            build_rc = bproc.returncode if bproc is not None else None
            record["build_exit_code"] = build_rc
            if build_rc == 0 and not b_timed_out:
                mark_build_warm(warm_key)
        _gate_release(b_token)
        record["build_timed_out"] = b_timed_out
        if b_refused or b_launch_error is not None:
            reason = (f"heavy_gate REFUSED build reservation {build_gb} GB"
                      if b_refused else f"build launch failed: {b_launch_error}")
            record.update(status=STATUS_ERROR, log=record["build_log"], finished_at=now_iso(),
                          duration_s=round(time.time() - started, 1),
                          final_line=f"<{reason}>", notes=reason + "; tests NOT run")
            write_record(record)
            return record
        if build_rc != 0 or b_timed_out:
            # The build transcript is the measured failure; there is no test
            # transcript and no second admission or implicit compilation retry.
            record["log"] = record["build_log"]
            record["peak_rss_gb"] = record.get("build_peak_rss_gb")
            record["gate_weight_gb"] = build_gb
            record["gate_admitted"] = b_admitted
            record["gate_wait_s"] = record["build_gate_wait_s"]
            record["exec_duration_s"] = record["build_exec_duration_s"]
            return _finish_measurement(entry, record, build_log_path.read_text(errors="replace"),
                                       build_rc, b_timed_out, started)
        # The run phase uses its saved run estimate, never the new build peak.
        gate_weight = run_gb
        record["gate_weight_gb"] = gate_weight

    gate_wait_started = time.time()
    gate_token, gate_admitted, gate_refused = _gate_acquire(gate_weight, entry["id"])
    record["gate_wait_s"] = round(time.time() - gate_wait_started, 1)
    record["gate_admitted"] = gate_admitted
    if gate_refused:
        # A refusal is never a licence to run ungated -- see _gate_acquire and
        # the 2026-08-24 panic. ERROR is the established encoding for "did not
        # run here" (docs/SUITE_STATE.md): never GREEN, never RED, and it reads
        # back as UNKNOWN, which is the truth.
        record.update(
            status=STATUS_ERROR,
            finished_at=now_iso(),
            duration_s=round(time.time() - started, 1),
            exit_code=None,
            final_line=f"<heavy_gate refused {gate_weight} GB>",
            notes=(
                (record["notes"] + " | ") if record["notes"] else ""
            ) + f"heavy_gate REFUSED {gate_weight} GB; target NOT run. A refusal "
                "is not a licence to run ungated (2026-08-24 panic).",
        )
        write_record(record)
        _gate_release(gate_token)
        return record
    if not gate_admitted:
        record["notes"] = (
            (record["notes"] + " | ") if record["notes"] else ""
        ) + f"ran UNGATED: heavy_gate did not reserve {gate_weight} GB "\
            f"(script absent, or acquire failed {GATE_ACQUIRE_ATTEMPTS} times)"
        write_record(record)
    rss_stop = threading.Event()
    rss_future: list[RssProfile] = []
    exec_started = time.time()

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
                target=lambda: rss_future.append(_rss_profile(proc.pid, rss_stop)),
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
    record["exec_duration_s"] = round(time.time() - exec_started, 1)
    profile = rss_future[0] if rss_future else None
    if profile is not None:
        # `run_peak_rss_gb` is the RUN phase alone and is what the next run's run
        # weight derives from. `peak_rss_gb` stays the combined figure so every
        # existing reader -- weights, policy, _prior_peak_rss_gb, the committed
        # history -- keeps meaning what it meant before the split.
        record["run_peak_rss_gb"] = round(profile.peak_gb, 2)
        build_peak = record.get("build_peak_rss_gb")
        combined = profile.peak_gb
        if isinstance(build_peak, (int, float)):
            combined = max(combined, float(build_peak))
        record["peak_rss_gb"] = round(combined, 2)
        record["rss_group_sum_peak_gb"] = round(profile.raw_peak_gb, 2)
        record["rss_p50_gb"] = round(profile.p50_gb, 2)
        record["rss_samples"] = profile.samples

    return _finish_measurement(entry, record, log_path.read_text(errors="replace"),
                               exit_code, timed_out, started, reservation_profile=profile)


def _finish_measurement(entry: dict[str, Any], record: dict[str, Any], text: str,
                        exit_code: int, timed_out: bool, started: float, *,
                        reservation_profile: RssProfile | None = None) -> dict[str, Any]:
    """Classify one completed invocation, whether compilation or tests failed."""
    timeout, timeout_basis = record["timeout_s"], record["timeout_basis"]
    final_line, counts = summarize_output(text, exit_code)
    if entry.get("_must_pass"):
        # Every `... ok` the run printed, so `derive` can judge the row's
        # must-pass list -- the one it holds THEN -- against this record.
        record["must_pass"] = list(entry["_must_pass"])
        record["passed_tests"] = passed_test_names(text)

    # Did another lane edit the source closure while this target was running?
    # If so the derived status is UNKNOWN even if the tree later returns to
    # the start digest: the run did not measure a stable input snapshot.
    # Recording both hashes keeps that evidence after any later edit.
    # Known residual race: the tree can move in the seconds between the
    # start digest and cargo actually reading the sources; nothing here closes
    # that window.
    digest_at_finish = input_digest(entry, fresh=True)
    record["input_digest_at_finish"] = digest_at_finish
    record["inputs_moved_during_run"] = digest_at_finish != record["input_digest"]

    record["timed_out"] = timed_out

    if timed_out:
        status = STATUS_ERROR
        notes = (
            f"KILLED after the runner timeout of {timeout}s ({timeout_basis}) -- this is NOT a pass "
            f"and NOT a failure. The next run of this target gets {min(timeout * 2, TIMEOUT_HARD_CEILING)}s "
            f"by policy; if it is still killed there, investigate the target, do not raise the budget by hand."
        )
        final_line = f"<timed out after {timeout}s; last line: {final_line}>"
    elif digest_at_finish is None:
        status = STATUS_ERROR
        problem = _compiler_identity_problem()
        notes = f"{problem} at finish; result cannot be qualified"
        final_line = f"<{problem}; last line: {final_line}>"
    elif exit_code == 0:
        skipped = _SKIPPED_VERDICT_RE.search(text)
        if skipped:
            status = STATUS_SKIPPED
            notes = (
                f"the gate exited 0 without measuring anything ({skipped.group(0)}). "
                "Recorded SKIPPED, which derives to UNKNOWN: a deferral is not a pass. "
                "Supply the missing prerequisite and re-run this row."
            )
            final_line = skipped.group(0)
        else:
            conflict = zero_exit_test_conflict(counts)
            status = STATUS_ERROR if conflict else STATUS_GREEN
            notes = conflict or ""
            missing = must_pass_missing(entry, record)
            if missing and not conflict:
                # Stored as measured (exit 0); `derive` reads it UNKNOWN. Said
                # here too, so the record explains itself without the inventory.
                notes = (
                    f"exited 0 but never reported `ok` for must-pass {missing}: the tests "
                    "this row exists for did not run (compiled out, renamed or unselected), "
                    "so it reads UNKNOWN, not GREEN"
                )
    else:
        refusal = _TOOLCHAIN_REFUSAL_RE.search(text)
        if refusal:
            status = STATUS_ERROR
            notes = (
                f"the toolchain REFUSED to run: {refusal.group(0).strip()}. Nothing was "
                "compiled or linted, so this run says nothing about the code under test. "
                "Recorded ERROR, which derives to UNKNOWN -- not a pass and not a failure. "
                "Re-run when the Trust stage2 and its ancestor directories are quiet."
            )
            final_line = f"<toolchain refused; nothing measured: {final_line}>"
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
    if reservation_profile is not None:
        record["reservation_verdict"] = _reservation_verdict(record["gate_weight_gb"], reservation_profile)
        record["reservation_verdict"] = _recorded_reservation_verdict(entry, record)
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
    # Repair the projection BEFORE deriving anything from it. A record that a
    # checkout reverted is indistinguishable, to `derive`, from a target that
    # never ran -- it reports UNKNOWN, which is correct about the file and wrong
    # about the world. Healing first means the table is derived from everything
    # this machine has actually measured. `--no-heal` inspects the projection
    # exactly as it sits on disk.
    if not args.no_heal:
        heal_projection()
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


# A WORKER MUST ANNOUNCE ITSELF, HOWEVER IT WAS STARTED.
#
# `run` without `--foreground` daemonizes, and `scripts/daemonize.py --pidfile`
# writes WORKER_PIDFILE for it. `run --foreground` called `cmd_worker` in-process
# and wrote NOTHING, so a foreground worker was invisible to every reader of that
# file. Two guards were silently disarmed by that:
#
#   * `cmd_run`'s "a worker is already running" check -- two foreground runs
#     would both proceed and thrash one CARGO_TARGET_DIR;
#   * `scripts/verify_runner_pinned.sh`'s refuse-to-re-pin check, whose whole
#     job is to stop a checkout moving the input digest's own sources underneath
#     an in-flight measurement.
#
# Measured here on 2026-08-25: a `--foreground` pinned run of gate::clippy was
# in flight at dba565b24 when a plain `status` call in another shell re-pinned
# the same worktree to d67054a45 and the guard said nothing, because worker.pid
# still held a long-dead pid from a previous lane. That is exactly the
# hours-of-work-discarded scenario the guard's own comment describes.
#
# So the WORKER owns the pidfile, not the launcher. The daemonized path writes
# the same pid daemonize.py already recorded, so this is idempotent there.
def _claim_worker_pidfile() -> bool:
    """Record this process as the live worker. Returns True if we wrote it."""
    try:
        WORKER_PIDFILE.parent.mkdir(parents=True, exist_ok=True)
        WORKER_PIDFILE.write_text(f"{os.getpid()}\n", encoding="utf-8")
        return True
    except OSError:
        # A worker that cannot announce itself must still run: the pidfile is a
        # concurrency courtesy, never a precondition for measuring.
        return False


def _release_worker_pidfile() -> None:
    """Drop our claim -- but only if it is still OURS.

    A worker started with `--restart` SIGTERMs the incumbent and writes its own
    pid. If the dying incumbent then unlinked the file on its way out, the live
    worker would be invisible again and the guards would re-open. So compare
    before unlinking.
    """
    try:
        if WORKER_PIDFILE.read_text().strip() == str(os.getpid()):
            WORKER_PIDFILE.unlink()
    except (OSError, ValueError):
        pass


def cmd_worker(args: argparse.Namespace) -> int:
    """In-process queue walker. Launched detached by `run`; not for direct use.

    Runs up to `jobs` targets concurrently. Safe on a shared CARGO_TARGET_DIR,
    but concurrency only pays once the target dir is warm: cargo holds the
    build-directory lock for the build phase and releases it before executing
    the test binary, so concurrent invocations serialize while building and
    overlap only while running. Both halves measured on this workspace -- a
    second `targo --unverified test --test X` started immediately beside a target past its
    build, and a second cold `targo tippy` blocked on the build-directory lock.
    """
    install_signal_handlers()
    _claim_worker_pidfile()
    try:
        return _worker_loop(args)
    finally:
        _release_worker_pidfile()


def _worker_loop(args: argparse.Namespace) -> int:
    queue = json.loads(Path(args.queue).read_text())
    inventory = {e["id"]: e for e in build_inventory(queue["packages"])}
    jobs = max(1, int(queue.get("jobs", 1)))
    print(
        f"[worker] pid={os.getpid()} targets={len(queue['targets'])} jobs={jobs} "
        f"start={now_iso()} commit={git_head()[:9]}",
        flush=True,
    )

    pending: list[tuple[dict[str, Any], str | None]] = []
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

    def execute(item: tuple[dict[str, Any], str | None]) -> dict[str, Any]:
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
            # That line is the RECORDED status; `status` prints what `derive`
            # reads (an exit 0 that never reported a must-pass test is UNKNOWN).
            read = derive(inventory[target_id], result, result.get("input_digest", ""))
            if read["bucket"] != result["status"]:
                print(f"[worker]      {target_id}: reads {read['bucket']}, not {result['status']}: "
                      f"{read['reason']}", flush=True)
            # Say it where a human is already looking. The record has carried
            # both numbers for weeks; nothing ever put them side by side, and a
            # 31x over-reservation held this machine single-lane for 6h12m
            # without one line of output that could have been doubted.
            if result.get("reservation_verdict"):
                print(f"[worker]      {target_id}: {result['reservation_verdict']}", flush=True)
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
    kind_rank = {"test": 0, "gate": 1, "lib": 2, KIND_SHARD_SPEC: 2, KIND_SHARD: 3,
                 # hours long and it forks its own children: start it early so it
                 # is not the last thing still running when everything else is done.
                 "gate-measure": 0}
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
    print(f"  journal:{journal_path()}")
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
    base_argv = ["targo", "--unverified", "test", "--locked", "-p", package, "--lib"]
    # The plan's freshness is the freshness of the UNSHARDED target: that is the
    # command whose inputs the shards collectively stand in for.
    parent_entry = dict(entry, argv=base_argv, kind="lib")
    digest = input_digest(parent_entry, fresh=True)
    if digest is None:
        print(f"{_compiler_identity_problem()}; shard plan NOT built", file=sys.stderr)
        return 2

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
        "digest_scope": DIGEST_SCOPE,
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


def _weight_basis(record: dict[str, Any]) -> str | None:
    """Why this weight is not simply `peak x 1.5`, when it is not.

    `None` -- the common case -- means the weight IS the last completed peak
    times the headroom, and the PEAK column already says everything.
    """
    peak = record.get("peak_rss_gb")
    carried = record.get("prior_peak_rss_gb")
    if not _run_was_cut_short(record):
        return None
    if not isinstance(carried, (int, float)) or isinstance(carried, bool):
        return None
    if carried <= (peak if isinstance(peak, (int, float)) else 0):
        return None
    return (f"last run was CUT SHORT ({record.get('status')}"
            f"{', timed out' if record.get('timed_out') else ''}); its "
            f"{peak} GB is a LOWER BOUND, so the weight holds the {carried} GB "
            f"carried peak instead")


def _this_host() -> str:
    """The hostname records made here are stamped with (see `runner_host`)."""
    return socket.gethostname()


def _host_key(name: str | None) -> str:
    """Compare hosts by identity, not by spelling.

    macOS reports this machine as BOTH `m1AirM224GB1TB2.localdomain` and
    `m1-Air-M2-24GB-1TB-2.local` depending on whether mDNS answered, and both
    spellings are already committed in `data/suite_state/`. Comparing the raw
    strings marks a third of this box's OWN records as foreign, and a marker
    that cries wolf is one people learn to skip -- which is how the thing it
    marks gets missed. So fold case and drop the separators and the domain.
    """
    if not name:
        return ""
    head = str(name).split(".")[0]
    return "".join(ch for ch in head.lower() if ch.isalnum())


def _is_foreign_record(host: str | None) -> bool:
    """True when a record was measured on a DIFFERENT machine than this one.

    Unknown provenance is NOT foreign: an older record predating the
    `runner_host` field says nothing either way, and guessing would put a mark
    on rows nobody can check.
    """
    return bool(host) and _host_key(host) != _host_key(_this_host())


def _recorded_reservation_verdict(entry: dict[str, Any], record: dict[str, Any]) -> str | None:
    """Keep supported finalized advice; preserve raw metrics and stored history."""
    verdict = record.get("reservation_verdict")
    if isinstance(verdict, str) and verdict.startswith("OVER-RESERVED"):
        # This describes the recorded snapshot, not a fresh run of today's tree.
        # Older producers reported before final classification and could leave
        # advice on RED/UNKNOWN records. Raw observations remain untouched.
        if record.get("status") != STATUS_GREEN or derive(
            entry, record, record.get("input_digest")
        )["bucket"] != BUCKET_GREEN:
            return None
    return verdict


def cmd_weights(args: argparse.Namespace) -> int:
    """Show the memory weight each target would reserve, and what it used.

    The mirror of `policy` for the OTHER resource. A weight nobody can inspect
    is a magic number with extra steps -- and unlike a timeout, an over-sized
    one is invisible while it does damage: above the machine budget the gate
    admits EXCLUSIVELY, so one stale weight turns a shared box into a
    single-lane one and every part of the gate still looks like it is working.

    Read the `EXCL` column first. It is not a warning about this target; it is
    the number of other lanes that can run while it does, and that number is
    zero.
    """
    phys = _phys_ram_gb()
    budget = _gate_budget_gb()
    inventory = [e for e in select(build_inventory(args.packages), args.only)
                 if e["kind"] != KIND_ROLLUP]
    rows = []
    for entry in inventory:
        record = load_record(entry["id"]) or {}
        weight = _gate_weight_gb(entry["id"])
        rows.append(
            {
                "target": entry["id"],
                "weight_gb": weight,
                "exclusive": bool(budget and weight > budget),
                "peak_rss_gb": record.get("peak_rss_gb"),
                "rss_p50_gb": record.get("rss_p50_gb"),
                "rss_group_sum_peak_gb": record.get("rss_group_sum_peak_gb"),
                "rss_samples": record.get("rss_samples"),
                "measured_at": record.get("finished_at"),
                # WHICH BOX measured it. `data/suite_state/` is git-tracked and
                # shared, so most records here were made on another machine, and
                # nothing in the weight path reads this field. The table must at
                # least SAY so -- see the footer.
                "measured_host": record.get("runner_host"),
                "verdict": _recorded_reservation_verdict(entry, record),
                # Where the weight actually came from. Without this the table
                # can print `WEIGHT 44` beside `PEAK 9.11` and leave a reader
                # to guess -- and the guess ("the weight is stale, cut it") is
                # the one that under-reserves. See _prior_peak_rss_gb.
                "weight_basis": _weight_basis(record),
                # The least the build phase reserves whatever `weight_gb` says:
                # 1.5x the row's highest measured build peak (RELEASE_PROFILE_TARGETS).
                "build_floor_gb": cold_build_floor_gb(entry) or None,
                # The least the FIRST build of its shape in a runner process
                # reserves (PACKAGE_COLD_BUILD_SEED_GB), and where it came from.
                "package_build_floor_gb": package_cold_build_floor_gb(entry, fresh=False)[0] or None,
                "package_build_floor_basis": package_cold_build_floor_gb(entry, fresh=False)[1] or None,
            }
        )
    if args.json:
        print(json.dumps({"schema": SCHEMA, "generated_at": now_iso(),
                          "physical_ram_gb": round(phys, 1), "gate_budget_gb": budget,
                          "targets": rows}, indent=2))
        return 0
    width = max((len(r["target"]) for r in rows), default=10)
    print(f"physical RAM {phys:.0f} GB, gate budget ~{budget} GB "
          f"(a weight above it runs ALONE)")
    print(f"{'TARGET':<{width}}  WEIGHT  EXCL   PEAK    P50  SAMPLES  MEASURED")
    for row in sorted(rows, key=lambda r: (-r["weight_gb"], r["target"])):
        peak = f"{row['peak_rss_gb']:.2f}" if isinstance(row["peak_rss_gb"], (int, float)) else "-"
        p50 = f"{row['rss_p50_gb']:.2f}" if isinstance(row["rss_p50_gb"], (int, float)) else "-"
        samples = row["rss_samples"] if row["rss_samples"] is not None else "-"
        foreign = _is_foreign_record(row["measured_host"])
        print(f"{row['target']:<{width}}  {row['weight_gb']:>5} GB  {'YES' if row['exclusive'] else '   '}"
              f"  {peak:>6} {p50:>6}  {str(samples):>7}  {row['measured_at'] or 'never'}"
              f"{' *' if foreign else ''}")
    excl = sum(1 for r in rows if r["exclusive"])
    print()
    print(f"{excl} of {len(rows)} targets reserve more than the budget and therefore run ALONE.")
    unmeasured = sum(1 for r in rows if r["rss_p50_gb"] is None)
    print(f"{unmeasured} of {len(rows)} have no median/sample provenance yet: their weight comes from "
          f"a PEAK alone, which for a `targo --unverified test` row is usually its rustc build and not the row.")
    # A weight that does NOT follow from the PEAK column beside it must say so
    # in the same breath, or the table invites the reader to "fix" it downwards.
    for row in sorted(rows, key=lambda r: r["target"]):
        if row["weight_basis"]:
            print(f"  {row['target']}: {row['weight_basis']}.")
    # A row with a build floor can reserve more for its build than its
    # record's PEAK column suggests; say so beside it.
    for entry in sorted(inventory, key=lambda e: e["id"]):
        floor = cold_build_floor_gb(entry)
        if floor:
            print(f"  {entry['id']}: its build reserves at least {floor} GB, 1.5x its "
                  f"{entry['_cold_build_peak_gb']} GB highest measured build peak, whatever a "
                  f"build's record learns.")
    # The package floor: what a possibly-cold build reserves, per package and
    # profile, once per table rather than once per row.
    floors = sorted({(r["package_build_floor_gb"], r["package_build_floor_basis"])
                     for r in rows if r["package_build_floor_gb"]}, key=lambda f: f[1])
    if floors:
        print()
        print("The first build of each build shape in a runner process may be cold and reserves "
              "at least its package floor:")
        for gb, basis in floors:
            print(f"  {gb} GB  ({basis})")
    # PROVENANCE. `data/suite_state/` is git-tracked and shared between machines,
    # and no part of the weight derivation reads `runner_host` -- so a row marked
    # `*` reserves memory on THIS box on the strength of a measurement taken on
    # another one. Measured 2026-09-17 across the 64 targets recorded on both
    # this 24 GB box and the 128 GB one: the median other/this peak ratio is
    # 0.90x, so importing a TEST row is roughly neutral, but every
    # compile-bearing `gate::*` row reads higher there (gate::check 6.00 -> 10.06,
    # gate::clippy 8.32 -> 11.14, gate::masquerade 9.34 -> 11.46) because more
    # cores run more rustc at once. Marking beats filtering: dropping foreign
    # rows would leave a target with NO weight, and the unmeasured default is a
    # worse number than a neighbour's measurement.
    foreign_rows = [r for r in rows if _is_foreign_record(r["measured_host"])]
    if foreign_rows:
        print()
        print(f"* {len(foreign_rows)} of {len(rows)} rows were measured on another machine "
              f"(this box is {_this_host()}); their weight is that machine's peak x1.5.")
        hosts = sorted({r["measured_host"] for r in foreign_rows})
        print(f"  foreign hosts: {', '.join(hosts)}")
    return 0


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
            # ADMISSION ONLY, NEVER A VERDICT. A seeded record may carry a
            # measured peak so the gate can ADMIT the target; the status above
            # stays UNKNOWN regardless, so this can never turn into a claim that
            # the target passed.
            #
            # It exists because a NEW row is otherwise unmeasurable on a small
            # box: `_gate_weight_gb` falls back to DEFAULT_TARGET_GB (12), and
            # `heavy_gate` REFUSES anything over the budget (4 GB here), so the
            # first admission can never happen and only a COMPLETED run lowers a
            # weight. Measured 2026-09-20: all ten
            # `crystal_a3_semdiff::w1_*` rows returned
            # `ERROR (0.2s) <heavy_gate refused 12 GB>` while the same test run
            # directly under heavy_gate completed at a 0.27 GB peak.
            #
            # The seeded peak is a LOWER-CONFIDENCE input than a run here, and
            # it is treated as one: the first completed run replaces it
            # outright (`_prior_peak_rss_gb`'s learning loop is untouched), and
            # the +50% headroom in `_gate_weight_gb` still applies on top.
            # Seeding a peak you did not measure is falsifying the gate's input;
            # cite the heavy_gate line it came from in `seed_note`.
            "peak_rss_gb": item.get("peak_rss_gb"),
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


# The board `status` / `run` enumerate when no --packages is given. Read the
# rationale at its use in main(); the wrapper script and the tests read it here.
DEFAULT_PACKAGES = (
    "clean-verify", "clean-elab", "clean-parser", "clean-olean", "clean-kernel", "clean-ck0",
)


def _canonical_targo_first_on_path() -> None:
    """Put the canonical Trust targo FIRST on this process's PATH.

    Every command here spells `targo` (the recorded argv stay as they are), and
    a bare `targo` resolves through PATH. On this machine `~/.cargo/bin` sits
    ahead of the Trust sysroot and `~/.cargo/bin/targo` is a rustup symlink
    that targo refuses to run as ("not a plain regular file"), so a suite run
    -- or `weights`, which starts with `targo metadata` -- failed for one
    operator and worked for another (2026-09-29). The canonical one comes from
    `scripts/rust_frontend.sh --targo`, the single place the rule lives; a
    private directory holding only a `targo` wrapper that execs it goes first
    on PATH, and every child (the detached worker included) inherits it. A
    wrapper, never a symlink, for the reason above. When the frontend refuses,
    PATH is left alone and each command reports its own failure."""
    try:
        r = subprocess.run(["bash", str(REPO_ROOT / "scripts" / "rust_frontend.sh"), "--targo"],
                           capture_output=True, check=False)
    except OSError:
        return
    targo = os.fsdecode(r.stdout).removesuffix("\n")
    if r.returncode != 0 or not targo.strip():
        return
    import tempfile
    shim = Path(tempfile.gettempdir()) / (
        "clean-verify-runner-targo-" + hashlib.sha256(targo.encode()).hexdigest()[:16])
    wrapper = shim / "targo"
    text = "#!/bin/sh\nexec " + shlex.quote(targo) + ' "$@"\n'
    try:
        if not wrapper.is_file() or wrapper.read_text() != text:
            shim.mkdir(parents=True, exist_ok=True)
            tmp = shim / f".targo.{os.getpid()}"
            tmp.write_text(text)
            tmp.chmod(0o755)
            os.replace(tmp, wrapper)
    except OSError:
        return
    os.environ["PATH"] = f"{shim}{os.pathsep}{os.environ.get('PATH', '')}"


def main() -> int:
    _canonical_targo_first_on_path()
    parser = argparse.ArgumentParser(prog="verify_runner", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    # Single-valued and repeatable rather than nargs="*": a greedy list argument
    # sitting in front of a subcommand swallows the subcommand's own flags.
    parser.add_argument("--packages", action="append", default=None,
                        help="workspace package to enumerate; repeatable, or comma-separated "
                             f"(default: {','.join(DEFAULT_PACKAGES)})")
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
    p_status.add_argument("--no-heal", action="store_true",
                          help="do NOT re-project journal records the working tree has lost; "
                               "read data/suite_state/ exactly as it sits on disk")
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

    p_weights = sub.add_parser(
        "weights", help="print the memory weight each target would reserve, and what it used")
    p_weights.add_argument("--json", action="store_true")
    p_weights.set_defaults(func=cmd_weights)

    p_seed = sub.add_parser("seed", help="import externally-reported results as UNKNOWN")
    p_seed.add_argument("--file", required=True)
    p_seed.set_defaults(func=cmd_seed)

    p_stop = sub.add_parser("stop", help="SIGTERM the running worker")
    p_stop.set_defaults(func=cmd_stop)

    p_journal = sub.add_parser(
        "journal",
        help="the append-only durable record behind data/suite_state/ (checkout-proof)",
    )
    p_journal.add_argument("--path", action="store_true", help="print the journal file and exit")
    p_journal.add_argument("--apply", action="store_true",
                           help="re-project every record the working tree has lost")
    p_journal.add_argument("--adopt", action="store_true",
                           help="one-time: journal projection records this journal has never "
                                "seen, labelled `adopted` (never `measured`)")
    p_journal.add_argument("--json", action="store_true")
    p_journal.set_defaults(func=cmd_journal)

    args = parser.parse_args()

    def split_csv(values: list[str] | None, default: list[str]) -> list[str]:
        if not values:
            return default
        return [item for value in values for item in value.split(",") if item]

    # DEFAULT BOARD: clean-verify AND clean-elab (2026-09-16).
    #
    # clean-elab was absent for the runner's whole life, so 11,410 lib tests and
    # 138 integration targets -- the crate where every elaborator and tactic
    # change lands -- had NO recorded verdict on any box. The lib target does not
    # finish as one unit (> 90 min at --test-threads=4, and > 50 min even with
    # --skip codata), which is why it is SHARDED by
    # data/suite_plans/clean-elab__lib.json exactly as clean-verify::lib is.
    #
    # This grows the board 78 -> 229 rows, and those rows start UNKNOWN, which is
    # the honest reading: they were never measured. UNKNOWN is never rounded up,
    # so `status --gate` already exits non-zero on the 78-row board today and
    # keeps doing so -- the change adds visibility, not a new refusal.
    #
    # AND clean-parser AND clean-olean (2026-09-24). The first all-targets run
    # after the wave-3 merges found RED integration targets in THREE crates --
    # clean-elab structural_recursion_prefix_params, clean-parser
    # no_silent_trees, clean-olean prelude_instance_priority_census -- and this
    # board could see only the first: the other two crates had no row at all
    # (reports/lean4-replacement-audit-2026-09-24/process.json). The per-merge
    # net for all four frontend crates is scripts/frontend_merge_suite.sh; this
    # board is where their targets keep a durable, digest-bound verdict, and
    # where the merge suite's pinned slow-list says its slow targets run.
    #
    # AND clean-kernel AND clean-ck0 (2026-11-13, self-proof unit E3). The
    # trusted kernel and the quorum's re-checker seed had no row: a kernel
    # change was qualified by the four rows that happen to run its tests
    # (gate::masquerade, gate::fence, and the kernel tests the other packages
    # reach), never by its own ~10,900 lib tests or 88 integration targets.
    # Their test targets are the first on the board with `required-features`
    # (`required_features_argv`), and they read outside their crates in ways a
    # pattern cannot see (`RESOLVE_RELATIVE`); clean-kernel's lib is sharded by
    # data/suite_plans/clean-kernel__lib.json.
    args.packages = split_csv(args.packages, list(DEFAULT_PACKAGES))
    args.only = split_csv(args.only, [])

    if shutil.which("targo") is None:
        print("targo not found on PATH (the driver is targo; there is no stock fallback)", file=sys.stderr)
        return 2
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
