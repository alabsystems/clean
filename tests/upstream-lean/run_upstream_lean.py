#!/usr/bin/env python3
"""Upstream-Lean drop-in gate: FAILS on any outcome not covered by an active row.

Mirrors trust/tests/upstream-rust/. Three clauses, all of them enforced here:

  1. BASELINE PIN — baseline.toml pins the upstream Lean revision, and this
     runner re-reads tests/lean4_compat/MANIFEST.json on every run and FAILS if
     the two disagree. Two pins that can drift apart are not a pin.
  2. EXPIRING LEDGER — exceptions.toml rows carry owner / issue / reviewed_on /
     expires_on, checked by the sibling check_ledger_expirations.py.
  3. A GATE THAT FAILS — every probe's observed outcome must equal its pinned
     `expected`, or an ACTIVE exception row must cover exactly that observation.
     Anything else exits non-zero.

This is the inversion of what the tree had. Measured 2026-09-01 at clean HEAD
c89b44931, the two pre-existing instruments over the same corpus were:

  * crates/clean-parser/src/lean4_compat.rs::lean4_parser_compatibility_suite —
    an 85% floor. A floor says how MANY may fail, never WHICH, so a fixed file
    and a newly broken one net to zero.
  * crates/clean-elab/tests/phase1_full_corpus.rs — print-only, and self-skipping
    unless CLEAN_PHASE1_FULL_CORPUS=1. It asserts nothing about any outcome.

Neither is in scripts/local_gate.sh, and neither routes a single corpus file
through `emit_trust_ir` — so the drop-in claim was unmeasured at exactly the
level TrustIr is the contract.

Refusals that are NOT waivable, whatever the ledger says:
  * `crashed` — a panic or fatal signal on valid upstream input is a defect that
    needs an owner, not a row.
  * a stale waiver — an active row whose probe produced its EXPECTED outcome.
    The Rust-side ledger's own closing note records that nothing there reports a
    row covering no failure, which is how 71 rows came to waive a defect fixed
    thirteen days before they were written.
  * an unbuildable subject with a seeded corpus — if `clean` cannot be found,
    nothing was measured, so nothing may pass.
  * an inferred subject — the binary is built from this tree (`--build`) or
    named (`--clean-bin` / `$CLEAN_BIN`), never taken from PATH or a leftover
    target/; and a probe whose import was served by Clean's hand-written
    stand-in instead of the pinned Lean library (`unsupported`).

Usage:
    tests/upstream-lean/run_upstream_lean.py --build          # the measurement
    tests/upstream-lean/run_upstream_lean.py --clean-bin PATH
    tests/upstream-lean/run_upstream_lean.py --ledger-only    # no probe runs
    tests/upstream-lean/run_upstream_lean.py --build --json
    tests/upstream-lean/run_upstream_lean.py --build --seed-from-corpus-dir
    tests/upstream-lean/run_upstream_lean.py --self-test

Exit codes:
    0   every probe matched its pin, or was covered by an active row
    1   any uncovered outcome, ledger defect, pin drift, or missing subject

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
from dataclasses import dataclass
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
BASELINE = HERE / "baseline.toml"
EXCEPTIONS = HERE / "exceptions.toml"
CORPUS = HERE / "corpus.toml"
EXPIRY_GATE = HERE / "check_ledger_expirations.py"

OUTCOMES = ("lowers", "rejected", "empty", "timeout", "crashed")
WAIVABLE_OUTCOMES = ("rejected", "empty", "timeout")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
# A probe's budget is CPU time, not wall-clock time. The 60 s WALL timeout that
# stood here was never measured, and on 2026-10-07 it was shown to measure the
# box instead of the probe: all six probes over an `import Lean` file read
# `timeout`, and each spends 87-91 s of user CPU loading the pinned
# v4.30.0-rc2 `Lean` package (260,817 constants) before its first declaration
# elaborates -- 97-191 s of wall time at load averages 34-42 on an 18-core
# M5 Max, every one of them ending `rejected` once allowed to finish. CPU time
# is what the subject spends whatever else the box runs, so the verdict stops
# depending on who else is building. 240 s is 2.6x the largest import measured;
# a probe that exhausts it is killed by SIGXCPU and reads `timeout`. The wall
# clock stays as a backstop for a subject that blocks without computing.
DEFAULT_CPU_BUDGET_SECONDS = 240
DEFAULT_TIMEOUT_SECONDS = 900
# The one command every "no `clean` binary" finding tells a maintainer to run,
# and the build `--build` runs (with `--locked --bin clean` and JSON messages
# added), so the hint cannot drift from what the gate builds.
# The package is `clean`, whose [[bin]] is the `clean` this runner executes;
# `-p clean-cli` builds the deprecated shim, a binary named `clean-cli` whose
# `--emit` has no `trustir`. self_test() holds this to the manifests.
BUILD_HINT = "targo --unverified build --release -p clean --features trust-ir-backend"
BUILD_CMD = shlex.split(BUILD_HINT) + [
    "--locked",
    "--bin",
    "clean",
    "--message-format=json-render-diagnostics",
]
# What clean-elab logs when an `import` was answered by its hand-written
# stand-in instead of a real `.olean` (crates/clean-elab/src/imports.rs,
# serve_from_prelude). A probe that hits it measured a FABRICATED module, not
# the pinned Lean library, so its outcome says nothing about vanilla Lean.
FABRICATED_IMPORT_MARKERS = (
    "import served by Clean's hand-written prelude",
    "FABRICATING a prelude",
)
# Every search-path variable clean-olean reads ahead of the pinned library.
# They are removed from a probe's environment, and LEAN_PATH is set to the
# pinned library alone, so a maintainer's Mathlib checkout or Lake packages
# cannot change what `import Lean` resolves to.
IMPORT_PATH_VARS = ("MATHLIB_PATH", "LEAN_PATH", "LEAN_PACKAGES_PATH")


def _reexec_under_a_toml_capable_python() -> None:
    import importlib.util

    if importlib.util.find_spec("tomllib") or importlib.util.find_spec("tomli"):
        return
    if os.environ.get("CLEAN_UPSTREAM_LEAN_PY_REEXEC"):
        return
    for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(candidate)
        if not found:
            continue
        os.environ["CLEAN_UPSTREAM_LEAN_PY_REEXEC"] = "1"
        os.execv(found, [found, os.path.abspath(__file__), *sys.argv[1:]])


_reexec_under_a_toml_capable_python()

TOML_PARSER_ERROR = (
    "error: no TOML parser available; use Python 3.11+ for stdlib tomllib, or "
    "install tomli for this Python environment"
)


def load_toml_text(text: str) -> dict[str, Any]:
    try:
        import tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib  # type: ignore[no-redef]
        except ModuleNotFoundError as exc:
            raise RuntimeError(TOML_PARSER_ERROR) from exc
    return tomllib.loads(text)


@dataclass
class ProbeResult:
    probe_id: str
    file: str
    decl: str
    expected: str
    observed: str
    detail: str = ""


@dataclass
class ProbeLimits:
    """How one probe is run: its deadlines and the environment it sees.

    `cpu_budget` is enforced with RLIMIT_CPU in the child, so it measures what
    the subject computes, not how loaded the box is; `timeout` is the wall-clock
    backstop. `env`, when set, is the child's WHOLE environment -- the runner
    builds it with the pinned Lean library as the only import search path.
    """

    timeout: int = DEFAULT_TIMEOUT_SECONDS
    cpu_budget: int | None = DEFAULT_CPU_BUDGET_SECONDS
    env: dict[str, str] | None = None


def classify_run(
    returncode: int, stdout: str, stderr: str = "", cpu_budget: int | None = None
) -> tuple[str, str]:
    """Map one `clean compile --emit trustir` invocation onto an outcome.

    A negative returncode is a fatal signal on POSIX. It is kept DISTINCT from a
    non-zero exit because the two mean opposite things: a non-zero exit is the
    compiler refusing, which is an accountable answer; a signal is the compiler
    dying, which is never an acceptable response to valid upstream input and is
    therefore not waivable.

    A binary built WITHOUT the `trust-ir-backend` feature has no `trustir` value
    for `--emit`, so the argument parser refuses before the compiler sees the
    file. That is the SUBJECT being unable to answer, not the lowering
    rejecting a declaration, and reporting it as `rejected` made every probe a
    pin mismatch and the whole ledger meaningless — measured 2026-09-21 at
    origin/main `18409a6b8`, where 11 probes read `rejected  exit 2: error:
    invalid value 'trustir' for '--emit <EMIT>'`. It is its own outcome so the
    message names the missing feature instead.

    SIGXCPU is `timeout`, not `crashed`, ONLY when this runner set the CPU
    budget (`cpu_budget`): then the signal is the budget expiring, which is the
    runner's own deadline. Without a budget it is an unexplained signal and
    stays a crash.

    An import answered by Clean's hand-written stand-in is `unsupported` too:
    the probe then ran against a fabricated module, so whatever it did after
    that is not a measurement of vanilla Lean. It is checked AFTER the crash
    arms, so a crash is never relabelled.
    """
    if cpu_budget is not None and returncode == -signal.SIGXCPU:
        return ("timeout", f"CPU budget of {cpu_budget}s exhausted (SIGXCPU)")
    if returncode < 0:
        return ("crashed", f"terminated by signal {-returncode}")
    if any(marker in (stderr or "") for marker in FABRICATED_IMPORT_MARKERS):
        return (
            "unsupported",
            "an import was served by Clean's hand-written stand-in, not by the pinned "
            "Lean library, so the probe measured a fabricated module (nothing about "
            "vanilla Lean was measured)",
        )
    if returncode == 2 and "invalid value 'trustir'" in (stderr or ""):
        return (
            "unsupported",
            "this `clean` binary has no `--emit trustir`: rebuild it with "
            "`--features trust-ir-backend` (nothing about the lowering was measured)",
        )
    if returncode != 0:
        return ("rejected", f"exit {returncode}")
    if "module" not in stdout:
        return (
            "empty",
            "exit 0 but stdout carries no textual TrustIr module",
        )
    return ("lowers", "")


# Top-level COMPUTATIONAL declarations, which are what `--emit trustir` lowers.
# Deliberately not `theorem`/`example`: a proof has no computational content to
# lower, so a row over one would pin the lowering's refusal of a thing it is not
# for. Modifiers are skipped, attributes are skipped, and the name is taken
# verbatim — Lean names may carry `.`, `'`, `!`, `?`.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|partial|unsafe|noncomputable|nonrec)\s+)*"
    r"(?:def|abbrev)\s+"
    r"([A-Za-z_\u03b1-\u03c9][A-Za-z0-9_'!?\u03b1-\u03c9]*(?:\.[A-Za-z0-9_'!?]+)*)",
    re.MULTILINE,
)


def propose_probe_rows(
    clean_bin: Path, corpus_dir: Path, limits: ProbeLimits, per_file: int
) -> list["ProbeResult"]:
    """Run the lowering over the corpus DIRECTORY and return one result per probe.

    This is what `--seed-from-corpus-dir` needs and did not have: the seed path
    used to print rows only for probes ALREADY in corpus.toml, so on an empty
    corpus it proposed nothing and the documented seeding command could never
    seed. Every `expected` a caller commits from this output is an outcome a real
    run produced — the file's own rule — because it is read off `observed`.
    """
    proposals: list[ProbeResult] = []
    for path in sorted(corpus_dir.rglob("*.lean")):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        names: list[str] = []
        for match in DECL_RE.finditer(text):
            name = match.group(1)
            if name not in names:
                names.append(name)
            if len(names) >= per_file:
                break
        rel = path.relative_to(corpus_dir).as_posix()
        for decl in names:
            probe = {
                "id": f"upstream-lean.{path.stem}.{decl}",
                "file": rel,
                "decl": decl,
                # No pin yet: the row being proposed IS the pin. `run_probe`
                # copies this into `expected`, and the printer below writes
                # `observed` into the proposed row, never this placeholder.
                "expected": "",
            }
            proposals.append(run_probe(clean_bin, corpus_dir, probe, limits))
    return proposals


def _cpu_limiter(budget: int | None):
    """A preexec_fn that caps the child's CPU time at `budget` seconds."""
    if budget is None:
        return None

    def limit() -> None:
        import resource

        resource.setrlimit(resource.RLIMIT_CPU, (budget, budget + 10))

    return limit


def run_probe(
    clean_bin: Path, corpus_dir: Path, probe: dict[str, Any], limits: ProbeLimits
) -> ProbeResult:
    timeout = limits.timeout
    source = corpus_dir / str(probe["file"])
    cmd = [
        str(clean_bin),
        "compile",
        str(source),
        "--decl",
        str(probe["decl"]),
        "--emit",
        "trustir",
    ]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(REPO_ROOT),
            env=limits.env,
            preexec_fn=_cpu_limiter(limits.cpu_budget),
        )
    except subprocess.TimeoutExpired:
        return ProbeResult(
            probe_id=str(probe["id"]),
            file=str(probe["file"]),
            decl=str(probe["decl"]),
            expected=str(probe["expected"]),
            observed="timeout",
            detail=f"no result within {timeout}s of wall time",
        )
    observed, detail = classify_run(
        completed.returncode, completed.stdout, completed.stderr or "", limits.cpu_budget
    )
    if observed in ("rejected", "crashed"):
        first_line = (completed.stderr or "").strip().splitlines()
        if first_line:
            detail = f"{detail}: {first_line[0][:200]}"
    return ProbeResult(
        probe_id=str(probe["id"]),
        file=str(probe["file"]),
        decl=str(probe["decl"]),
        expected=str(probe["expected"]),
        observed=observed,
        detail=detail,
    )


def validate_ledgers(
    baseline: dict[str, Any],
    corpus: dict[str, Any],
    exceptions: dict[str, Any],
    manifest: dict[str, Any] | None,
    today: date,
) -> list[str]:
    """Schema + pin-coherence checks that need no subject to run."""
    findings: list[str] = []

    # --- pin coherence: baseline.toml vs the corpus manifest ------------------
    upstream = baseline.get("upstream") or {}
    declared = str(upstream.get("revision", ""))
    if manifest is None:
        findings.append(
            "tests/lean4_compat/MANIFEST.json is missing; the baseline pin cannot "
            "be corroborated. Refusing to assume it."
        )
    else:
        commit = str(manifest.get("lean4_commit", ""))
        version = str(manifest.get("lean4_version", ""))
        want = f"leanprover/lean4:{commit}"
        if declared != want:
            findings.append(
                f"baseline.toml [upstream] revision {declared!r} disagrees with "
                f"tests/lean4_compat/MANIFEST.json {want!r}. Two pins that can "
                f"drift apart are not a pin."
            )
        if str(upstream.get("version", "")) != version:
            findings.append(
                f"baseline.toml [upstream] version {upstream.get('version')!r} "
                f"disagrees with MANIFEST.json {version!r}"
            )
        declared_count = upstream.get("file_count")
        actual_count = manifest.get("file_count")
        if declared_count != actual_count:
            findings.append(
                f"baseline.toml [upstream] file_count {declared_count!r} disagrees "
                f"with MANIFEST.json {actual_count!r}"
            )

    # --- corpus schema --------------------------------------------------------
    probes = corpus.get("probes") or []
    probe_ids: set[str] = set()
    for index, probe in enumerate(probes):
        if not isinstance(probe, dict):
            findings.append(f"corpus.toml: probes[{index}] is not a table")
            continue
        missing = [k for k in ("id", "file", "decl", "expected") if not probe.get(k)]
        if missing:
            findings.append(
                f"corpus.toml: probes[{index}] is missing {', '.join(missing)}"
            )
            continue
        probe_id = str(probe["id"])
        if probe_id in probe_ids:
            findings.append(f"corpus.toml: duplicate probe id {probe_id!r}")
            continue
        probe_ids.add(probe_id)
        if str(probe["expected"]) not in OUTCOMES:
            findings.append(
                f"{probe_id}: expected {probe['expected']!r} is not one of {OUTCOMES}"
            )
        if str(probe["expected"]) == "crashed":
            findings.append(
                f"{probe_id}: `crashed` may never be an EXPECTED outcome. Pinning a "
                f"crash records it as normal; it is a defect that needs an owner."
            )

    # --- exception schema -----------------------------------------------------
    required = (
        "id",
        "probe_id",
        "observed",
        "kind",
        "status",
        "owner",
        "reason",
        "issue",
        "reviewed_on",
        "expires_on",
    )
    seen_ids: set[str] = set()
    for index, row in enumerate(exceptions.get("exceptions") or []):
        if not isinstance(row, dict):
            findings.append(f"exceptions.toml: exceptions[{index}] is not a table")
            continue
        missing = [k for k in required if not str(row.get(k, "")).strip()]
        if missing:
            findings.append(
                f"exceptions.toml: exceptions[{index}] "
                f"({row.get('id', '<no id>')}) is missing {', '.join(missing)}"
            )
            continue
        row_id = str(row["id"])
        if row_id in seen_ids:
            findings.append(f"exceptions.toml: duplicate exception id {row_id!r}")
            continue
        seen_ids.add(row_id)
        if str(row.get("status", "")).lower() != "active":
            continue
        if str(row["probe_id"]) not in probe_ids:
            findings.append(
                f"{row_id}: probe_id {row['probe_id']!r} names no probe in "
                f"corpus.toml. A retired probe must not leave a live waiver behind."
            )
        if str(row["observed"]) not in WAIVABLE_OUTCOMES:
            findings.append(
                f"{row_id}: observed {row['observed']!r} is not waivable "
                f"({WAIVABLE_OUTCOMES}). A crash is never waived by a row."
            )
        for field_name in ("reviewed_on", "expires_on"):
            if not DATE_RE.match(str(row[field_name])):
                findings.append(
                    f"{row_id}: {field_name} {row[field_name]!r} is not YYYY-MM-DD"
                )
        if DATE_RE.match(str(row["reviewed_on"])) and DATE_RE.match(str(row["expires_on"])):
            if str(row["expires_on"]) <= str(row["reviewed_on"]):
                findings.append(
                    f"{row_id}: expires_on {row['expires_on']} <= reviewed_on "
                    f"{row['reviewed_on']}"
                )
            elif str(row["expires_on"]) <= today.isoformat():
                findings.append(
                    f"{row_id}: active but expires_on {row['expires_on']} has lapsed "
                    f"(today {today.isoformat()}). Re-review, then renew or retire."
                )
    return findings


def adjudicate(
    results: list[ProbeResult], exceptions: dict[str, Any]
) -> tuple[list[str], set[str]]:
    """Compare observations against pins and active waivers. Fail-closed."""
    findings: list[str] = []
    active: dict[str, dict[str, Any]] = {}
    for row in exceptions.get("exceptions") or []:
        if not isinstance(row, dict):
            continue
        if str(row.get("status", "active")).lower() != "active":
            continue
        if row.get("probe_id"):
            active.setdefault(str(row["probe_id"]), row)

    used: set[str] = set()
    for result in results:
        if result.observed == result.expected:
            continue
        if result.observed == "crashed":
            findings.append(
                f"{result.probe_id}: CRASHED ({result.detail}). A panic or fatal "
                f"signal on valid upstream Lean is a defect that needs an owner, "
                f"not a waiver — no exception row can cover it."
            )
            continue
        row = active.get(result.probe_id)
        if row is None:
            findings.append(
                f"{result.probe_id}: observed {result.observed!r}, pinned "
                f"{result.expected!r} — no active exception row covers it. "
                f"{result.detail}"
            )
            continue
        if str(row.get("observed")) != result.observed:
            findings.append(
                f"{result.probe_id}: observed {result.observed!r} but active row "
                f"{row.get('id')!r} waives {row.get('observed')!r}. A row waives one "
                f"observation, not a probe."
            )
            continue
        used.add(str(row["id"]))

    for probe_id, row in active.items():
        row_id = str(row["id"])
        if row_id in used:
            continue
        matching = [r for r in results if r.probe_id == probe_id]
        if matching and all(r.observed == r.expected for r in matching):
            findings.append(
                f"{row_id}: STALE WAIVER — probe {probe_id} produced its expected "
                f"outcome {matching[0].expected!r}, so this row waives nothing. "
                f"Delete it; a row that covers no failure hides the day it stops "
                f"being true."
            )
    return findings, used


def find_clean_bin(explicit: str | None) -> Path | None:
    """The subject a caller NAMED (`--clean-bin`, then `$CLEAN_BIN`), or None.

    There is no implicit fallback, and that is the fix, not an omission. This
    used to fall through to `target/{release,debug}/clean` and then to whatever
    `clean` PATH named. Measured 2026-10-07 in the pre-push hook's pristine
    checkout: no `target/` exists there (the hook's CARGO_TARGET_DIR is
    elsewhere), so every run executed aterm's INSTALLED `clean` -- a binary
    with no `--emit trustir`, built from no tree under test -- and all 56 probes
    read `unsupported`. A PATH binary is never the tree being gated, and a
    leftover `target/` binary is whatever was last built. `--build` builds the
    subject from this tree; anything else must be named explicitly.
    """
    if explicit:
        candidate = Path(explicit)
        return candidate if candidate.is_file() else None
    env = os.environ.get("CLEAN_BIN")
    if env and Path(env).is_file():
        return Path(env)
    return None


def build_clean_bin() -> tuple[Path | None, str]:
    """Build the subject FROM THIS TREE and return the executable cargo reports.

    Runs BUILD_CMD (the BUILD_HINT build, `--locked`, the `clean` bin only)
    from the repository root, so the binary is fresh for exactly the checked-out
    sources by cargo's own reckoning, in whatever CARGO_TARGET_DIR the caller
    set. The path is read from cargo's `compiler-artifact` message rather than
    guessed from a target directory.
    """
    try:
        done = subprocess.run(
            BUILD_CMD, cwd=str(REPO_ROOT), capture_output=True, text=True
        )
    except OSError as exc:
        return (None, f"`{' '.join(BUILD_CMD)}` could not start: {exc}")
    if done.returncode != 0:
        tail = "\n".join((done.stderr or "").strip().splitlines()[-25:])
        return (None, f"`{' '.join(BUILD_CMD)}` exited {done.returncode}:\n{tail}")
    executable = None
    for line in (done.stdout or "").splitlines():
        try:
            message = json.loads(line)
        except ValueError:
            continue
        target = message.get("target") or {}
        if (
            message.get("reason") == "compiler-artifact"
            and target.get("name") == "clean"
            and "bin" in (target.get("kind") or [])
            and message.get("executable")
        ):
            executable = Path(message["executable"])
    if executable is None or not executable.is_file():
        return (None, f"`{' '.join(BUILD_CMD)}` succeeded but reported no `clean` executable")
    return (executable, "")


def pinned_lean_library(
    baseline: dict[str, Any], environ: dict[str, str] | None = None
) -> tuple[Path | None, str]:
    """The installed library of the Lean the baseline pins, or why there is none.

    A corpus file's `import Lean` must resolve to the PINNED library and to
    nothing else, or the probe measures whatever this box happens to have: a
    different toolchain's `.olean`s, or -- with none -- Clean's hand-written
    stand-in, which classify_run refuses. The 2026-09-20 seeding run finished
    all 56 probes inside a 60 s budget, which a run that loads the real `Lean`
    package cannot do (97-191 s each, measured 2026-10-07), so its six
    `import Lean` pins were taken against something other than the library
    this baseline names. Resolved through elan (`$ELAN_HOME`, else
    `~/.elan`), the same toolchain directory `lean-toolchain` selects.
    """
    environ = dict(os.environ) if environ is None else environ
    version = str((baseline.get("upstream") or {}).get("version", ""))
    if not version:
        return (None, "baseline.toml [upstream] carries no `version`")
    elan_home = Path(environ.get("ELAN_HOME") or Path(environ.get("HOME", "~")) / ".elan")
    lib = elan_home / "toolchains" / f"leanprover--lean4---{version}" / "lib" / "lean"
    missing = [n for n in ("Init/Prelude.olean", "Lean.olean") if not (lib / n).is_file()]
    if missing:
        return (
            None,
            f"the pinned Lean library is not installed: {lib} lacks {', '.join(missing)}. "
            f"Install it with `elan toolchain install leanprover/lean4:{version}`.",
        )
    return (lib, "")


def probe_environment(lib: Path, environ: dict[str, str] | None = None) -> dict[str, str]:
    """This process's environment with the pinned library as the ONLY import path."""
    env = dict(os.environ) if environ is None else dict(environ)
    for name in IMPORT_PATH_VARS:
        env.pop(name, None)
    env["LEAN_PATH"] = str(lib)
    return env


def run_expiry_gate() -> tuple[int, str]:
    if not EXPIRY_GATE.exists():
        return (1, f"{EXPIRY_GATE} is missing")
    completed = subprocess.run(
        [sys.executable, str(EXPIRY_GATE)], capture_output=True, text=True
    )
    return (completed.returncode, completed.stdout + completed.stderr)


# --------------------------------------------------------------------------- #
# self-test                                                                     #
# --------------------------------------------------------------------------- #

SELF_TEST_MANIFEST = {
    "lean4_version": "v4.27.0",
    "lean4_commit": "db93fe1608548721853390a10cd40580fe7d22ae",
    "file_count": 100,
}
SELF_TEST_BASELINE = """
schema_version = "0.1.0"
id = "t"
[upstream]
channel = "lean4"
revision = "leanprover/lean4:db93fe1608548721853390a10cd40580fe7d22ae"
version = "v4.27.0"
snapshot_date = "2026-01-28"
file_count = 100
[seeding]
unseeded_until = "2026-12-01"
"""
SELF_TEST_CORPUS = """
schema_version = "0.1.0"
[[probes]]
id = "p.ok"
file = "1.lean"
decl = "a"
expected = "lowers"
[[probes]]
id = "p.bad"
file = "2.lean"
decl = "b"
expected = "lowers"
"""


def _exc(**kw: Any) -> str:
    base = {
        "id": "x.1",
        "probe_id": "p.bad",
        "observed": "rejected",
        "kind": "expected_fail",
        "status": "active",
        "owner": "@clean",
        "reason": "r",
        "issue": "local:i",
        "reviewed_on": "2026-08-01",
        "expires_on": "2027-08-01",
    }
    base.update(kw)
    rows = "\n".join(f'{k} = "{v}"' for k, v in base.items())
    return f'schema_version = "0.1.0"\n[[exceptions]]\n{rows}\n'


def check_build_hint(hint: str, crates_dir: Path) -> list[str]:
    """The package `hint` builds must ship the `clean` binary find_clean_bin
    looks for, and must declare the `trust-ir-backend` feature it enables."""
    match = re.search(r"(?:^|\s)-p\s+(\S+)", hint)
    if match is None:
        return [f"build hint {hint!r} names no `-p <package>`"]
    package = match.group(1)
    for manifest_path in sorted(crates_dir.glob("*/Cargo.toml")):
        manifest = load_toml_text(manifest_path.read_text(encoding="utf-8"))
        if manifest.get("package", {}).get("name") != package:
            continue
        bins = [b.get("name") for b in manifest.get("bin", []) if isinstance(b, dict)]
        problems = []
        if "clean" not in bins:
            problems.append(
                f"build hint builds package {package!r}, whose binaries are {bins}: "
                "none is the `clean` that find_clean_bin looks for"
            )
        if "trust-ir-backend" not in manifest.get("features", {}):
            problems.append(f"build hint's package {package!r} has no `trust-ir-backend` feature")
        return problems
    return [f"build hint names package {package!r}, which no crates/*/Cargo.toml declares"]


def self_test() -> int:
    failures: list[str] = []

    # --- the build hint every "no binary" finding prints ----------------------
    # It named `-p clean-cli` (a binary called `clean-cli`) in one of its two
    # copies, so a maintainer who followed it built something the next run
    # still could not find.
    for problem in check_build_hint(BUILD_HINT, REPO_ROOT / "crates"):
        failures.append(f"BUILD_HINT: {problem}")
    if not check_build_hint(BUILD_HINT.replace("-p clean ", "-p clean-cli "), REPO_ROOT / "crates"):
        failures.append("check_build_hint accepted `-p clean-cli`, whose binary is not `clean`")
    today = date(2026, 9, 1)
    baseline = load_toml_text(SELF_TEST_BASELINE)
    corpus = load_toml_text(SELF_TEST_CORPUS)
    empty_exc = load_toml_text('schema_version = "0.1.0"\nexceptions = []\n')

    def expect(name: str, findings: list[str], want_pass: bool, fragment: str = "") -> None:
        passed = not findings
        if passed != want_pass:
            failures.append(
                f"{name}: expected {'pass' if want_pass else 'fail'}, got "
                f"{'pass' if passed else 'fail'} ({findings})"
            )
        elif fragment and not any(fragment in f for f in findings):
            failures.append(f"{name}: no finding mentioned {fragment!r}: {findings}")

    # --- classify_run ---------------------------------------------------------
    xcpu = -signal.SIGXCPU
    fabricated = "WARN import served by Clean's hand-written prelude for this module"
    for rc, out, err, budget, want in (
        (0, 'module "clean_module" { }', "", None, "lowers"),
        (0, "", "", None, "empty"),
        (1, "", "", None, "rejected"),
        (101, "", "", None, "rejected"),
        (-11, "", "", None, "crashed"),
        (2, "", "error: invalid value 'trustir' for '--emit <EMIT>'", None, "unsupported"),
        # the runner's own CPU deadline is a timeout; the same signal with no
        # budget set is unexplained and stays a crash
        (xcpu, "", "", 240, "timeout"),
        (xcpu, "", "", None, "crashed"),
        (-11, "", "", 240, "crashed"),
        # a probe answered by the hand-written stand-in measured nothing real,
        # whatever its exit -- and a crash is never relabelled by it
        (1, "", fabricated, None, "unsupported"),
        (0, 'module "clean_module" { }', fabricated, None, "unsupported"),
        (-11, "", fabricated, None, "crashed"),
    ):
        got, _ = classify_run(rc, out, err, budget)
        if got != want:
            failures.append(
                f"classify_run({rc}, {out!r}, {err[:30]!r}, cpu_budget={budget}) -> {got}, want {want}"
            )

    # --- the subject is never inferred ----------------------------------------
    # A `clean` on PATH or in target/ is not the tree under test: the hook ran
    # aterm's installed binary this way and measured nothing. Both directions:
    # an inferred subject is refused, a named one is taken.
    import tempfile

    held_env = {k: os.environ.get(k) for k in ("PATH", "CLEAN_BIN")}
    with tempfile.TemporaryDirectory() as tmp:
        decoy = Path(tmp) / "clean"
        decoy.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        decoy.chmod(0o755)
        try:
            os.environ["PATH"] = f"{tmp}{os.pathsep}{held_env['PATH'] or ''}"
            os.environ.pop("CLEAN_BIN", None)
            if find_clean_bin(None) is not None:
                failures.append("find_clean_bin inferred a subject from PATH/target/")
            if find_clean_bin(str(decoy)) != decoy:
                failures.append("find_clean_bin refused an explicitly named subject")
            os.environ["CLEAN_BIN"] = str(decoy)
            if find_clean_bin(None) != decoy:
                failures.append("find_clean_bin ignored $CLEAN_BIN")
        finally:
            for key, value in held_env.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value

    # --- the import environment is the pinned library, or nothing -------------
    with tempfile.TemporaryDirectory() as tmp:
        lib = Path(tmp) / "toolchains" / "leanprover--lean4---v4.27.0" / "lib" / "lean"
        (lib / "Init").mkdir(parents=True)
        (lib / "Init" / "Prelude.olean").write_bytes(b"")
        fake = {"ELAN_HOME": tmp, "HOME": "/nonexistent"}
        got_lib, why = pinned_lean_library(baseline, fake)
        if got_lib is not None or "Lean.olean" not in why:
            failures.append(f"a library without Lean.olean was accepted: {got_lib} {why}")
        (lib / "Lean.olean").write_bytes(b"")
        got_lib, why = pinned_lean_library(baseline, fake)
        if got_lib != lib:
            failures.append(f"the pinned library was not found: {why}")
        other = {**fake, "ELAN_HOME": str(Path(tmp) / "elsewhere")}
        if pinned_lean_library(baseline, other)[0] is not None:
            failures.append("pinned_lean_library accepted a toolchain the baseline does not name")
        env = probe_environment(lib, {"MATHLIB_PATH": "/m", "LEAN_PACKAGES_PATH": "/p",
                                      "LEAN_PATH": "/other", "HOME": "/h"})
        if env.get("LEAN_PATH") != str(lib) or "MATHLIB_PATH" in env or "LEAN_PACKAGES_PATH" in env:
            failures.append(f"probe_environment leaked a search path: {env}")

    # --- ledger validation ----------------------------------------------------
    expect("clean ledgers", validate_ledgers(baseline, corpus, empty_exc, SELF_TEST_MANIFEST, today), True)
    drifted = dict(SELF_TEST_MANIFEST)
    drifted["lean4_commit"] = "0" * 40
    expect(
        "pin drift",
        validate_ledgers(baseline, corpus, empty_exc, drifted, today),
        False,
        "not a pin",
    )
    expect(
        "missing manifest",
        validate_ledgers(baseline, corpus, empty_exc, None, today),
        False,
        "Refusing to assume",
    )
    expect(
        "waiver for an unknown probe",
        validate_ledgers(baseline, corpus, load_toml_text(_exc(probe_id="ghost")), SELF_TEST_MANIFEST, today),
        False,
        "names no probe",
    )
    expect(
        "expired waiver",
        validate_ledgers(baseline, corpus, load_toml_text(_exc(expires_on="2026-08-31")), SELF_TEST_MANIFEST, today),
        False,
        "has lapsed",
    )
    expect(
        "waiver with no owner",
        validate_ledgers(baseline, corpus, load_toml_text(_exc(owner="")), SELF_TEST_MANIFEST, today),
        False,
        "is missing owner",
    )
    expect(
        "waiver for a crash",
        validate_ledgers(baseline, corpus, load_toml_text(_exc(observed="crashed")), SELF_TEST_MANIFEST, today),
        False,
        "is not waivable",
    )
    expect(
        "probe pinning a crash",
        validate_ledgers(
            baseline,
            load_toml_text(SELF_TEST_CORPUS.replace('expected = "lowers"', 'expected = "crashed"', 1)),
            empty_exc,
            SELF_TEST_MANIFEST,
            today,
        ),
        False,
        "may never be an EXPECTED outcome",
    )

    # --- adjudication ---------------------------------------------------------
    ok = ProbeResult("p.ok", "1.lean", "a", "lowers", "lowers")
    bad = ProbeResult("p.bad", "2.lean", "b", "lowers", "rejected", "exit 1")
    crash = ProbeResult("p.bad", "2.lean", "b", "lowers", "crashed", "signal 11")
    good_bad = ProbeResult("p.bad", "2.lean", "b", "lowers", "lowers")

    expect("all pins met", adjudicate([ok, good_bad], empty_exc)[0], True)
    expect(
        "uncovered failure fails the gate",
        adjudicate([ok, bad], empty_exc)[0],
        False,
        "no active exception row covers it",
    )
    expect(
        "an active row covers its observation",
        adjudicate([ok, bad], load_toml_text(_exc()))[0],
        True,
    )
    expect(
        "a row waiving a different observation does not cover",
        adjudicate([ok, bad], load_toml_text(_exc(observed="timeout")))[0],
        False,
        "waives one observation",
    )
    expect(
        "a resolved row covers nothing",
        adjudicate([ok, bad], load_toml_text(_exc(status="resolved")))[0],
        False,
        "no active exception row covers it",
    )
    expect(
        "a crash is never waivable",
        adjudicate([ok, crash], load_toml_text(_exc(observed="rejected")))[0],
        False,
        "needs an owner",
    )
    expect(
        "a stale waiver fails",
        adjudicate([ok, good_bad], load_toml_text(_exc()))[0],
        False,
        "STALE WAIVER",
    )

    # --- end-to-end against a stub compiler, so the subprocess path is real ----
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "1.lean").write_text("def a : Nat := 0\n", encoding="utf-8")
        stub = tmp_path / "clean"
        # argv is `clean compile <src> --decl <name> --emit trustir`, so the
        # source path is $2 ($0 is the script itself, $1 is `compile`).
        stub.write_text(
            "#!/bin/sh\n"
            'case "$2" in\n'
            '  *2.lean) echo "boom" >&2; exit 1 ;;\n'
            "esac\n"
            "echo 'module \"clean_module\" { }'\n",
            encoding="utf-8",
        )
        stub.chmod(0o755)
        probe_ok = {"id": "p.ok", "file": "1.lean", "decl": "a", "expected": "lowers"}
        probe_bad = {"id": "p.bad", "file": "2.lean", "decl": "b", "expected": "lowers"}
        limits = ProbeLimits(timeout=30, cpu_budget=30)
        got_ok = run_probe(stub, tmp_path, probe_ok, limits)
        got_bad = run_probe(stub, tmp_path, probe_bad, limits)
        if got_ok.observed != "lowers":
            failures.append(f"stub run: expected lowers, got {got_ok.observed} ({got_ok.detail})")
        if got_bad.observed != "rejected":
            failures.append(f"stub run: expected rejected, got {got_bad.observed}")
        expect("stub end-to-end, uncovered", adjudicate([got_ok, got_bad], empty_exc)[0], False, "no active exception")
        expect("stub end-to-end, covered", adjudicate([got_ok, got_bad], load_toml_text(_exc()))[0], True)
        # The CPU budget reaches the CHILD, not just the record: the stub
        # lowers only if its own `ulimit -t` reads the budget, so a limiter
        # that is never installed (or installed in this process) fails here.
        # The kernel enforces a set RLIMIT_CPU; classify_run's SIGXCPU arms
        # above pin what its expiry reads as.
        limited = tmp_path / "limited"
        limited.write_text(
            "#!/bin/sh\n"
            '[ "$(ulimit -t)" = "7" ] || exit 3\n'
            "echo 'module \"clean_module\" { }'\n",
            encoding="utf-8",
        )
        limited.chmod(0o755)
        got_lim = run_probe(limited, tmp_path, probe_ok, ProbeLimits(timeout=30, cpu_budget=7))
        if got_lim.observed != "lowers":
            failures.append(
                f"the CPU budget did not reach the probe's process ({got_lim.observed}: "
                f"{got_lim.detail})"
            )

    if failures:
        print("upstream-lean runner self-test FAILED:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(
        "upstream-lean runner self-test passed (2 build hint + 12 classify + 3 subject + "
        "4 import environment + 8 ledger + 7 adjudicate + 5 end-to-end)."
    )
    return 0


# --------------------------------------------------------------------------- #


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    subject = p.add_mutually_exclusive_group()
    subject.add_argument(
        "--clean-bin",
        default=None,
        help="Path to the `clean` binary to measure (else $CLEAN_BIN). Never inferred.",
    )
    subject.add_argument(
        "--build",
        action="store_true",
        help=f"Build the subject from THIS tree (`{' '.join(BUILD_CMD)}`, into the "
        "caller's CARGO_TARGET_DIR) and measure exactly that binary.",
    )
    subject.add_argument(
        "--ledger-only",
        action="store_true",
        help="Check the ledgers, the baseline pin and the ramp; execute NO probe. "
        "Never a measurement of the lowering: the full gate's `upstream-lean-probes` "
        "leg is.",
    )
    p.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT_SECONDS,
        help="Wall-clock backstop per probe, seconds.",
    )
    p.add_argument(
        "--cpu-budget",
        type=int,
        default=DEFAULT_CPU_BUDGET_SECONDS,
        help="CPU-time budget per probe, seconds (RLIMIT_CPU; exhausting it reads `timeout`).",
    )
    p.add_argument("--json", action="store_true")
    p.add_argument("--as-of", default=None, help="Override today's date (ISO YYYY-MM-DD).")
    p.add_argument("--self-test", action="store_true")
    p.add_argument(
        "--seed-from-corpus-dir",
        action="store_true",
        help="Print proposed corpus.toml rows from a real run over the corpus. "
        "Prints only — a human reviews and commits them.",
    )
    p.add_argument(
        "--seed-per-file",
        type=int,
        default=1,
        help="How many top-level computational declarations to propose per corpus "
        "file when seeding (default 1). The selection is documented in "
        "baseline.toml [corpus]; it is a slice, not a sample.",
    )
    return p.parse_args()


NO_SUBJECT = (
    "no `clean` subject was named (looked at --clean-bin and $CLEAN_BIN only; a "
    "binary on PATH or left in target/ is not the tree under test, so neither is "
    "ever inferred). Pass --build to build it from this tree with "
    f"`{BUILD_HINT}`, or name one with --clean-bin."
)


def resolve_subject(args: argparse.Namespace) -> tuple[Path | None, str]:
    if args.build:
        print(f"building the subject from this tree: {' '.join(BUILD_CMD)}", file=sys.stderr)
        return build_clean_bin()
    found = find_clean_bin(args.clean_bin)
    if found is None:
        named = args.clean_bin or os.environ.get("CLEAN_BIN")
        if named:
            return (None, f"the named subject {named!r} is not a file. {NO_SUBJECT}")
        return (None, NO_SUBJECT)
    return (found, "")


def main() -> int:
    args = parse_args()
    if args.self_test:
        return self_test()

    today = (
        date.fromisoformat(args.as_of) if args.as_of else datetime.now(timezone.utc).date()
    )

    try:
        baseline = load_toml_text(BASELINE.read_text(encoding="utf-8"))
        corpus = load_toml_text(CORPUS.read_text(encoding="utf-8"))
        exceptions = load_toml_text(EXCEPTIONS.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    except RuntimeError as exc:
        print(exc, file=sys.stderr)
        return 1

    manifest_path = REPO_ROOT / str(
        (baseline.get("upstream") or {}).get("manifest_path", "tests/lean4_compat/MANIFEST.json")
    )
    manifest = (
        json.loads(manifest_path.read_text(encoding="utf-8"))
        if manifest_path.exists()
        else None
    )

    findings = validate_ledgers(baseline, corpus, exceptions, manifest, today)

    expiry_rc, expiry_out = run_expiry_gate()
    if expiry_rc != 0:
        findings.append(f"ledger expiry gate FAILED (rc={expiry_rc}):\n{expiry_out.strip()}")

    probes = corpus.get("probes") or []
    corpus_dir = REPO_ROOT / str(
        (baseline.get("upstream") or {}).get("corpus_path", "tests/lean4_compat/lean4_tests")
    )
    results: list[ProbeResult] = []
    unseeded = not probes
    measure = not args.ledger_only and (not unseeded or args.seed_from_corpus_dir)
    if args.ledger_only and args.seed_from_corpus_dir:
        findings.append("--ledger-only executes no probe, so it cannot seed; drop one flag")
        measure = False

    if unseeded:
        deadline = str((baseline.get("seeding") or {}).get("unseeded_until", ""))
        print("=" * 72)
        print("UPSTREAM-LEAN CORPUS IS UNSEEDED — nothing was executed.")
        print("")
        print("  corpus.toml carries no probes, so this run measures NOTHING about")
        print("  whether vanilla Lean lowers to TrustIr. It is not a pass.")
        print("")
        print(f"  Seed it:  {(baseline.get('seeding') or {}).get('seed_command', '')}")
        print(f"  This ramp starts FAILING on {deadline or '<unset>'}.")
        print("=" * 72)
        if not deadline or not DATE_RE.match(deadline):
            findings.append(
                "baseline.toml [seeding] unseeded_until is missing or not YYYY-MM-DD. "
                "An unseeded corpus with no deadline is a gate that never has to run."
            )
        elif today.isoformat() >= deadline:
            findings.append(
                f"corpus.toml is still unseeded and the ramp expired on {deadline}. "
                f"Seed it or move the deadline with a stated reason; do not delete it."
            )

    if measure:
        # THE SUBJECT AND ITS ENVIRONMENT. Both are pinned before a single probe
        # runs: the binary is the tree under test (built here, or named), and
        # `import` resolves to the baseline's Lean library and nothing else.
        clean_bin, why = resolve_subject(args)
        lib, lib_why = pinned_lean_library(baseline)
        if clean_bin is None:
            findings.append(f"{why} Nothing was measured, so nothing may pass.")
        elif lib is None:
            findings.append(f"{lib_why} Nothing was measured, so nothing may pass.")
        elif not corpus_dir.exists():
            findings.append(f"corpus directory {corpus_dir} is missing")
        else:
            print(f"subject:      {clean_bin}", file=sys.stderr)
            print(f"Lean library: {lib} (the only import search path)", file=sys.stderr)
            limits = ProbeLimits(
                timeout=args.timeout,
                cpu_budget=args.cpu_budget,
                env=probe_environment(lib),
            )
            if unseeded:
                # THE SEED PATH. Without this the documented seeding command is
                # inert on the corpus it exists to seed: the printer below
                # iterates `results`, and `results` was only ever filled from
                # probes that already existed.
                results = propose_probe_rows(clean_bin, corpus_dir, limits, args.seed_per_file)
            else:
                for probe in probes:
                    if not isinstance(probe, dict) or not probe.get("id"):
                        continue
                    results.append(run_probe(clean_bin, corpus_dir, probe, limits))
                unsupported = [r for r in results if r.observed == "unsupported"]
                if unsupported and len(unsupported) == len(results):
                    findings.append(
                        f"every one of the {len(results)} probes reports `unsupported` "
                        f"({unsupported[0].detail}): NOTHING about the lowering was "
                        "measured; a gate that cannot measure never passes."
                    )
                else:
                    adjudication, _ = adjudicate(results, exceptions)
                    findings.extend(adjudication)

    matched = sum(1 for r in results if r.observed == r.expected)
    summary = {
        "probes": len(probes),
        "executed": len(results),
        "matched_pin": matched,
        "unseeded": unseeded,
        "ledger_only": bool(args.ledger_only),
        "findings": len(findings),
    }

    if args.json:
        json.dump(
            {
                "summary": summary,
                "results": [vars(r) for r in results],
                "findings": findings,
            },
            sys.stdout,
            indent=2,
        )
        sys.stdout.write("\n")
    else:
        print("")
        print("upstream-lean drop-in gate" + (" — LEDGER ONLY" if args.ledger_only else ""))
        print(f"  probes pinned:   {summary['probes']}")
        print(f"  probes executed: {summary['executed']}")
        print(f"  matched pin:     {summary['matched_pin']}")
        if args.ledger_only:
            print("  This mode checks the ledgers, the baseline<->MANIFEST pin and the ramp,")
            print("  and EXECUTES NO PROBE: it says nothing about whether vanilla Lean lowers.")
            print("  That is measured by `run_upstream_lean.py --build` (local_gate.sh full")
            print("  mode, leg `upstream-lean-probes`).")
        for result in results:
            if result.observed != result.expected:
                print(
                    f"    {result.probe_id}: expected {result.expected}, "
                    f"observed {result.observed}  {result.detail}"
                )
        if findings:
            print("")
            print("FINDINGS — gate FAIL:")
            for finding in findings:
                print(f"  • {finding}")

    if args.seed_from_corpus_dir:
        print("")
        print("# proposed corpus.toml rows — REVIEW EVERY ONE BEFORE COMMITTING")
        for result in results:
            print("[[probes]]")
            print(f'id = "{result.probe_id}"')
            print(f'file = "{result.file}"')
            print(f'decl = "{result.decl}"')
            print(f'expected = "{result.observed}"')
            print("")

    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
