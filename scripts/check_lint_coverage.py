#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Fail closed when a tracked crate or target escapes the documented lint gate.

`Cargo.toml` narrows `default-members` to the publish smoke surface on purpose
(see the rationale at `Cargo.toml:33-37`), so the bare `targo --unverified check --locked` /
`targo tippy --locked --all-targets` inner loop compiles only a fraction of the
workspace. That is a deliberate speed trade, not a coverage claim — the coverage
claim belongs to the pre-push gate, which must select **every** member and
**every** target kind.

This script checks the two ways that guarantee silently rots:

  1. Orphan crates — a git-tracked package manifest (`[package]`, anywhere in
     the tree) that is not a workspace member is compiled, linted, and tested
     by *no* workspace command, not even `--workspace`. Such a crate is either
     STANDALONE_GATED -- THIS CHECK RUNS ITS TESTS AND LINTS IT (see
     STANDALONE CRATES ARE RUN below) -- or recorded in `KNOWN_ORPHANS` with
     the disposition that keeps it out; both maps are checked from the other
     side (a stale entry fails too).
  2. Gate narrowing — the documented full gate must appear verbatim in the
     places that are supposed to run it (`CLAUDE.md`, `Justfile`,
     `scripts/local_gate.sh`), so dropping `--workspace` or `--all-targets` from
     any one of them breaks the gate instead of quietly shrinking it.

It also prints the live coverage delta (crates and targets selected by the fast
inner loop vs. the full gate) so the numbers quoted in CLAUDE.md can be
re-derived on demand rather than trusted.

STANDALONE CRATES ARE RUN
-------------------------
A standalone crate (its own [workspace]) is compiled by no workspace command, so
this check runs each STANDALONE_GATED crate itself, on every invocation -- the
pre-push hook's `lint-coverage` leg and `scripts/local_gate.sh` alike -- with the
command lines fixed here in Python:

  * `cargo test --locked -v` must exit 0, print `test result:` lines that are
    all `ok` and pass at least one test between them, and show cargo EXECUTING
    a test binary it built;
  * `scripts/rust_frontend.sh clippy --all-targets -v -- -D warnings -F
    <FORBIDDEN_LINTS>` must exit 0 and show, in THIS run (a per-run
    `clean_lint_run` cfg re-lints the crate's own units), the clippy driver
    linting the crate's TEST target over a command line holding nothing but
    what cargo writes for it (an ALLOWLIST), under the debug-assertions and
    overflow-checks the tests ran with. The wildcard lints are FORBIDDEN, so no
    `#[allow]` in the source can lower them (error E0453);
  * `cargo check --all-targets -v` with scripts/lint_types -- rustc itself
    (`rustc_driver`) plus two rules, built from this tree -- as the crate's
    RUSTC_WORKSPACE_WRAPPER (THE TYPED SCAN, lane r11) must exit 0 and show, in
    THIS run (a per-run CLEAN_LINT_TYPES_RUN the driver records in the unit's
    dep-info re-checks the crate's own units), the driver checking every unit of
    the crate, its TEST target included, over the same allowlisted command line,
    and printing its scan of each. The rules, read off the THIR the compiler
    lowers every body to: no catch-all may stand for variants of a trust-ir enum
    (or of the crate's own) that another alternative of the same pattern names
    -- in any `match` (a macro's included), `if let`, `while let`, `let` chain or
    `let .. else` -- and no comparison (`t == Ty::A`, `ts.contains(&Ty::A)`,
    `same(t, Ty::A)`) or cast (`t as u32`) may tell one apart by value, the named
    variant followed through the whole crate, its own functions included
    (scripts/lint_types/src/main.rs states both). Every type, name, constant and
    field is what the compiler resolved, so nothing a wildcard lint reads is
    decided by hand (verifier r10b: a whole-arm `_` beside a named constant
    passed the syn walk this replaced);
  * every file rustc compiled for any run -- read off its dep-info, which is
    what sees a module behind a directory symlink, `src/extra.RS` opened as
    `src/extra.rs` on APFS, a target path outside the crate -- must be a
    git-tracked regular file of the crate; every file the tests compiled must
    also have been linted, and every file the tests or the lint compiled read
    by the typed scan; and scripts/lint_scan (syn) must find in those files none
    of the source that keeps code out of those runs while the tests still run
    it: a cfg naming anything but `test`, a macro that writes a match, a `use`
    renaming one onto an admitted name, ... (its src/main.rs states them). The
    scanner and the typed driver are themselves STANDALONE_GATED, so this check
    runs their tests and lints and scans them, each with both scans.

THE RUNS ARE HERMETIC (lane r10, 2026-09-26). A cargo configuration file above
the checkout or in CARGO_HOME -- files nothing in this repository can pin --
capped every lint until verifier r9 (`rustflags = ["@lint.args"]`), and reading
the flags back off the command line was a list of symptoms. Now the runs see an
allowlisted environment (ENV_ALLOW); a private CARGO_HOME holding nothing but
links to the real one's caches, so its configuration is never read;
CARGO_ENCODED_RUSTFLAGS / _RUSTDOCFLAGS set to GATE_RUSTFLAGS, which REPLACES the
rustflags of every configuration file, the repository's and the ones above it
alike; and RUSTC_WRAPPER='' / RUSTC_WORKSPACE_WRAPPER='', which reset any
configured wrapper (the clippy frontend sets the driver as its own). What cargo
configuration can still say, cargo itself reports (`targo config get --merged
no`), and a key outside MODELED_CONFIG is refused wherever its file lives -- a
profile's rustflags, a `runner`, a `[patch]`, `[unstable]` -- before anything is
built or run under it. A profile's `debug`
(at a level that keeps debuginfo on), `split-debuginfo` and `codegen-units` are
modeled: they lower to codegen flags the line allowlist already admits
(_CONFIG_PROFILE says how that was measured). The line allowlist stays as the
check that this worked.

What decides the verdict is pinned, derived rather than listed: `--pinned-inputs`
prints every file whose change can change how this check decides (THE PINNED
INPUTS), and check_gate_registry.py R7 refuses the row until its arms are
replayed over any change to one.

The threat model is docs/GATE_REGISTRY.md's: this defends against ACCIDENTAL
shapes -- a forgotten file, an unpinned input, a configuration that caps a lint
-- not against source written to evade it; the spellings recorded there as out
of model are not special-cased here. What it does not do: decide anything about
`scripts/local_gate.sh` (which reaches this check as leg 4b), or stop a
crate-level `#![allow(dead_code)]` from quieting `-D warnings` for that one
lint.

The self-test (`LINT_COVERAGE_SELFTEST arms=N failed=0`) runs the same runner
against stub `targo`, clippy and scanner tools on a stub crate, and requires each
failure shape above to fail it and the clean crate to pass it; the scan rules
themselves are the scanner crate's own tests, which this check runs.

Usage:  python3 scripts/check_lint_coverage.py [--quiet] [--selftest]
        python3 scripts/check_lint_coverage.py --pinned-inputs

The self-test runs first on every invocation; `--selftest` stops after it.
`--pinned-inputs` prints the derived pin set and runs nothing.
"""

from __future__ import annotations

import json
import os
import re
import secrets
import shlex
import shutil
import subprocess
import sys
import types
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Execute the pinned helper bytes; a matching .pyc is not a declared input.
RESOURCE_TRANSPORT = "scripts/resource_transport.py"
_transport = types.ModuleType("lint_coverage_resource_transport")
_transport.__file__ = str(ROOT / RESOURCE_TRANSPORT)
exec(compile((ROOT / RESOURCE_TRANSPORT).read_bytes(), _transport.__file__, "exec",
             dont_inherit=True), _transport.__dict__)

# Tracked crates that are deliberately (or, historically, accidentally) outside
# `[workspace] members`. SHRINK-ONLY: a stale entry — one that has become a
# member, or whose manifest is gone — fails this check, so the list cannot
# outlive the deviation it records.
KNOWN_ORPHANS: dict[str, str] = {
    "crates/clean-mathverse-server": (
        "tracked but not a workspace member and not in Cargo.lock; no cargo "
        "command in this repo builds or lints it. Keep-or-kill decision is "
        "open — docs/AUDIT_2026-07_DISPOSITIONS.md rows 19, 31, 132."
    ),
    # Recorded 2026-09-24, when the scan widened past crates/: each is its
    # own workspace (or excluded from this one) and no leg builds it. The
    # test-file counts are `#[test]`-bearing .rs files, measured that day.
    "bench-runner": (
        "standalone paragon-benchmark driver (own [workspace]); 4 test files "
        "that no leg runs"
    ),
    "cli-runner": "standalone driver for the real `clean` CLI (own [workspace]); no tests",
    "crown-proofs/kani": "Kani proof-harness crate (own [workspace]); no tests, no leg builds it",
    "fuzz": (
        "cargo-fuzz targets, excluded from [workspace]; 1 test file that no "
        "leg runs"
    ),
    "realtelem-harness": "standalone telemetry generator (own [workspace]); no tests",
    # Recorded 2026-09-28 (Trust migration): both landed 2026-09-25 with the
    # module-trust report and were invisible here until this check stopped
    # dying at `cargo metadata` (rc 127 on the aterm reroute).
    "reports/2026-09-24-module-trust/mtprobe": (
        "measurement probe of the 2026-09-24 module-trust report (own [workspace]); "
        "no tests, no leg builds it"
    ),
    "reports/2026-09-24-module-trust/round27/battery/vt": (
        "battery driver of the 2026-09-24 module-trust report (own [workspace]); "
        "no tests, no leg builds it"
    ),
    "scripts/isa_harness": "ISA/FP harness binaries, excluded from [workspace]; no tests",
    "telemetry-harness": "standalone telemetry generator (own [workspace]); no tests",
    "third-party/carcara/carcara": (
        "vendored Carcara, excluded from [workspace]; compiled only as "
        "clean-auto's optional `carcara` dependency under `carcara-verify`, "
        "and its 37 test files run under no leg"
    ),
    "third-party/carcara/carcara-macros": "vendored Carcara's proc-macro crate; no tests",
    "third-party/carcara/test-generator": (
        "vendored Carcara's test generator; 1 test file that no leg runs"
    ),
    # Recorded 2026-09-25 (lane r9): added to the nested carcara workspace by
    # f35ec454e (2026-09-24) with no disposition here, which left this check
    # RED on origin/main from 329b1c9f7. Measured that day: 4 `#[test]`-bearing
    # files (src/eval.rs, src/literals.rs, src/regex.rs, tests/battery.rs).
    "third-party/carcara/soundness": (
        "Trust-authored rule-soundness battery for the vendored Carcara, a member "
        "of the nested carcara workspace; 4 test files that no leg runs"
    ),
    # Recorded 2026-11-13 (PKG-U14 landing): added by 44b5bc2ab with no
    # disposition here, which left this check RED on origin/main. Tried as
    # STANDALONE_GATED first and refused by this check's hermetic model: its
    # clippy and typed-scan lines carry `-L native=` paths from the psm and
    # zstd-sys build scripts (clean-olean's graph), and `test -v` shows a
    # trustdoc doctest compile it reads as a wrapper. Gating it needs that model
    # widened, which is this check's owner's call, not an expedient edit.
    "scripts/kcheck_trace_probe": (
        "C4 labelled-carrier controls (own [workspace]); src/lib.rs #[path]-includes "
        "crates/clean-kernel/tests/kcheck_trace.rs, whose own [[test]] target needs the "
        "default-off kcheck-trace + reduction-stats features, and tests/pinned_literal.rs "
        "(1 test, pinned-import feature); no leg runs either"
    ),
}

# Tracked crates outside `[workspace]` whose tests and lint THIS CHECK RUNS (see
# STANDALONE CRATES ARE RUN in the module doc).
STANDALONE_GATED: dict[str, str] = {
    "scripts/crystal_a2_project": (
        "the crystal-A2 projector (own [workspace]: it depends on trust-ir, "
        "which nothing Clean ships does)"
    ),
    "scripts/lint_scan": (
        "the syn source scanner this check runs over every STANDALONE_GATED crate, "
        "itself included (own [workspace])"
    ),
    "scripts/lint_types": (
        "the typed scan (rustc_driver) this check runs as the workspace wrapper of every "
        "STANDALONE_GATED crate, itself included (own [workspace])"
    ),
}
SCANNER = "scripts/lint_scan"
# THE TYPED SCAN (see the module doc): the driver's crate, its binary, the
# variable whose per-run value it records in each unit's dep-info, and the line
# it prints for every unit it scanned.
TYPES = "scripts/lint_types"
TYPES_RUN_VAR = "CLEAN_LINT_TYPES_RUN"
TYPES_SUMMARY = re.compile(
    r"^lint-types: scanned crate `(\S+)` test=(true|false) bodies=(\d+) .*refused=(\d+)$", re.M)
# Denied at the projector's crate root because a catch-all over a trust-ir enum
# would refuse -- or image -- a shape nobody classified; FORBIDDEN on the
# command line so the source cannot allow them back.
FORBIDDEN_LINTS = (
    "clippy::wildcard_enum_match_arm",
    "clippy::match_wildcard_for_single_variants",
    "clippy::wildcard_in_or_patterns",
)
FRONTEND = "scripts/rust_frontend.sh"
PACKAGE_TABLE = re.compile(r"^\[package\]\s*$", re.MULTILINE)

# The pre-push gate. Every site listed below must contain this string verbatim.
#
# The DRIVER is deliberately not part of the string. What this check defends is
# the SELECTION -- `--workspace` and `--all-targets`, the two flags whose loss
# re-opens the blind spot. The gate sites invoke clippy through
# `scripts/rust_frontend.sh` (the pinned `trust` toolchain ships clippy as
# `targo-tippy`), so matching on the subcommand and its flags keeps this check
# blind to the driver and sharp on the selection.
FULL_GATE = "clippy --locked --workspace --all-targets"
GATE_SITES = ("CLAUDE.md", "Justfile", "scripts/local_gate.sh")


class CoverageFailure(RuntimeError):
    """A tracked crate or a gate site no longer matches the documented gate."""


def custody_fds(env: dict[str, str]) -> tuple[int, ...]:
    """Keep advertised transport alive; only the native owner authenticates it."""
    try:
        return _transport.resource_fds(env)
    except RuntimeError as exc:
        raise CoverageFailure(f"lint resource transport refused: {exc}") from exc


def resolve_targo(env: dict[str, str] | None = None) -> str:
    """The targo every run of this check uses, from `scripts/rust_frontend.sh --targo`.

    Never `targo` from PATH. On this machine `~/.cargo/bin/targo` is a rustup
    symlink ahead of the Trust sysroot on PATH, targo refuses to run as a
    symlink, and until 2026-09-29 this leg was RED on every tree for a pusher
    whose PATH had that order and GREEN for one whose PATH did not. The rule
    (an explicit `$TARGO`, else `$(rustc +trust --print=sysroot)/bin/targo`)
    lives in the frontend, once; this asks it, with the caller's environment,
    and fails closed on its refusal."""
    child_env = dict(os.environ if env is None else env)
    try:
        proc = subprocess.run(["bash", str(ROOT / FRONTEND), "--targo"], cwd=ROOT,
                              env=child_env, pass_fds=custody_fds(child_env),
                              capture_output=True, check=False)
    except OSError as exc:
        raise CoverageFailure(f"{FRONTEND} --targo could not run: {exc}") from exc
    targo = os.fsdecode(proc.stdout).removesuffix("\n")
    if proc.returncode != 0 or not targo.strip():
        raise CoverageFailure(f"no targo to run: {FRONTEND} --targo exited {proc.returncode}: "
                              f"{' '.join(os.fsdecode(proc.stderr).split())}")
    return targo


def cargo_metadata() -> dict:
    """Workspace shape from cargo itself (authoritative, ~0.04s, no build)."""
    child_env = dict(os.environ)
    proc = subprocess.run(
        [resolve_targo(child_env), "metadata", "--locked", "--no-deps", "--format-version", "1"],
        cwd=ROOT,
        env=child_env, pass_fds=custody_fds(child_env),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise CoverageFailure(f"targo metadata failed: {proc.stderr.strip()}")
    return json.loads(proc.stdout)


def tracked_crate_manifests() -> list[str]:
    """Every tracked `Cargo.toml` that declares a `[package]`, anywhere.

    The root manifest and virtual workspaces (no `[package]`) are not crates.
    Manifests nested under a workspace member (e.g.
    `crates/clean-rust-sem/tests/source_macro_ingestion/`) are compile-env
    fixtures whose sources are `#[path]`-included into a real test target, so
    the full gate already lints them through their owning crate;
    `check_orphans` drops them.
    """
    proc = subprocess.run(
        ["git", "ls-files", "--", "Cargo.toml", "*/Cargo.toml"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise CoverageFailure(f"git ls-files failed: {proc.stderr.strip()}")
    return sorted(
        line
        for line in proc.stdout.splitlines()
        if line != "Cargo.toml"
        and PACKAGE_TABLE.search((ROOT / line).read_text(encoding="utf-8"))
    )


_GIT_LOCATION_VARS = ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                      "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_PREFIX")


def tracked_files(root: Path, crate: str) -> list[str]:
    """`git ls-files` of one crate, repo-relative (git's own spelling and case)."""
    env = {k: v for k, v in os.environ.items() if k not in _GIT_LOCATION_VARS}
    proc = subprocess.run(["git", "ls-files", "-z", "--", crate], cwd=root, env=env,
                          capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        raise CoverageFailure(f"git ls-files {crate} failed: {proc.stderr.strip()}")
    return [p for p in proc.stdout.split("\0") if p]


# ── STANDALONE CRATES ARE RUN (see the module doc) ─────────────────────────

RESULT_LINE = re.compile(
    r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored", re.M
)
# `cargo -v` prints every command it starts, compile and execution alike.
RUNNING_LINE = re.compile(r"^\s*Running `(.*)`\s*$", re.M)
# The programs cargo may start for a lint of the crate's own units: the clippy
# driver, Trust's `tippy-driver` (the frontend is `targo tippy`, owner directive
# 2026-09-28; a stock `clippy-driver` is a different lint set and is refused).
CLIPPY_DRIVERS = ("tippy-driver",)
# ...and for the test build, the compiler itself.
RUSTC_NAMES = ("rustc", "trustc")
# The per-run clippy argument. clippy-driver tracks CLIPPY_ARGS in the crate's
# dep-info, so a value no earlier run carried makes cargo re-lint the crate's
# OWN units (dependencies stay Fresh), print the command it ran and write fresh
# dep-info.
NONCE_CFG = "clean_lint_run"


def standalone_commands(root: Path, crate: str, nonce: str,
                        targo: str) -> dict[str, list[str]]:
    """The three command lines, fixed here -- never read from a gate script.
    `targo` is `resolve_targo()`'s answer; the clippy half reaches the same
    one through the frontend, which the run's environment hands it as TARGO."""
    manifest = f"{crate}/Cargo.toml"
    forbid = [flag for lint in FORBIDDEN_LINTS for flag in ("-F", lint)]
    return {
        "tests": [targo, "--unverified", "test", "--locked", "--manifest-path", manifest, "-v",
                  "--message-format=json-render-diagnostics"],
        "clippy": [
            str(root / FRONTEND), "clippy", "--locked", "--manifest-path", manifest,
            "--all-targets", "--message-format=json", "-v", "--", "-D", "warnings", *forbid,
            "--cfg", f'{NONCE_CFG}="{nonce}"',
            "--check-cfg", f"cfg({NONCE_CFG}, values(any()))",
        ],
        # Run with the typed driver as RUSTC_WORKSPACE_WRAPPER and TYPES_RUN_VAR
        # set to the nonce (`run_standalone`).
        "types": [targo, "--unverified", "check", "--locked", "--manifest-path", manifest, "--all-targets",
                  "-v", "--message-format=json"],
    }


def running_commands(out: str) -> list[list[str]]:
    """Every command `cargo -v` reports starting, as argv (leading `VAR=value`
    assignments dropped). A line shlex cannot split is kept as one word, which
    no rule below accepts."""
    commands = []
    for line in RUNNING_LINE.findall(out):
        try:
            argv = shlex.split(line)
        except ValueError:
            argv = [line]
        while argv and re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", argv[0]):
            argv.pop(0)
        # Cargo prints the PROGRAM unquoted (measured: `.../Application
        # Support/.../tippy-driver '.../rustc' --crate-name ...`), so a path
        # with a space splits; rejoin the shortest prefix that names a file.
        prog, j = argv[0] if argv else "", 1
        while prog and not os.path.isfile(prog) and j < len(argv):
            prog, j = f"{prog} {argv[j]}", j + 1
        if prog and os.path.isfile(prog):
            argv = [prog, *argv[j:]]
        if argv:
            commands.append(argv)
    return commands


def _messages(out: str) -> list[dict]:
    """The JSON messages cargo printed, one per line."""
    messages = []
    for line in out.splitlines():
        if line.startswith("{"):
            try:
                messages.append(json.loads(line))
            except ValueError:
                continue
    return messages


def _artifacts(out: str, manifest: Path) -> list[dict]:
    """The `compiler-artifact` messages of the crate at `manifest`."""
    return [m for m in _messages(out)
            if m.get("reason") == "compiler-artifact"
            and Path(m.get("manifest_path", "")).resolve() == manifest.resolve()]


# THE LINT'S COMMAND LINE IS AN ALLOWLIST: every argument after the driver and
# the rustc it wraps must be one cargo writes for this crate, or GATE_RUSTFLAGS.
# With the runs hermetic, nothing else should reach it -- a profile's rustflags
# or a manifest `[lints]` table still would, which is what this is FOR.
_LINT_ARGS_BARE = frozenset({"--test", "--verbose"})
_LINT_ARGS_VALUED = frozenset({
    "--crate-name", "--edition", "--error-format", "--json", "--crate-type", "--emit",
    "--check-cfg", "--out-dir", "-L", "--extern", "-C", "--codegen", "-Z",
    "--force-warn",
})
# `-C` keys cargo writes from a profile or for the unit's own identity; none
# of them reaches a lint level, and no cfg they set is one the source may name.
_LINT_CODEGEN_KEYS = frozenset({
    "codegen-units", "debug-assertions", "debuginfo", "embed-bitcode", "extra-filename",
    "incremental", "lto", "metadata", "opt-level", "overflow-checks", "panic",
    "split-debuginfo", "strip",
})
# The flags the runs pass through CARGO_ENCODED_RUSTFLAGS: the pinned `trust`
# toolchain verifies every unit by default, and the third-party graph is not
# what this check is about (.cargo/config.toml's header says why).
GATE_RUSTFLAGS = ("-Ztrust-verify=off",)
# ...and what cargo itself adds for CARGO_UNSTABLE_CHECKSUM_FRESHNESS (see
# `hermetic_env`): the hash rustc records in dep-info.
_LINT_UNSTABLE_OPTS = frozenset({"trust-verify=off", "checksum-hash-algorithm=blake3"})


def _split_flag(arg: str) -> tuple[str, str | None]:
    """`--flag=value` / `-Cvalue` / `-Zvalue` / `-Lvalue` -> (flag, value);
    anything else -> (arg, None)."""
    if arg.startswith("--") and "=" in arg:
        flag, value = arg.split("=", 1)
        return flag, value
    if arg[:2] in ("-C", "-Z", "-L") and len(arg) > 2:
        return arg[:2], arg[2:]
    return arg, None


def lint_args(argv: list[str]) -> tuple[list[tuple[str, str | None]], list[str]]:
    """A compile command line past its program, as ([(flag, value)], [positional]).
    A valued flag with no value left is kept as (flag, None)."""
    pairs, positional, k = [], [], 0
    while k < len(argv):
        flag, value = _split_flag(argv[k])
        if flag in _LINT_ARGS_VALUED and value is None and k + 1 < len(argv):
            k += 1
            value = argv[k]
        if flag.startswith("-"):
            pairs.append((flag, value))
        else:
            positional.append(flag)
        k += 1
    return pairs, positional


def unmodeled_lint_args(argv: list[str], dirs: list[Path] | None = None) -> list[str]:
    """The arguments of one lint command line -- past the clippy driver and the
    rustc it wraps -- that this check does not model. `dirs` are where this run
    builds: `--out-dir`, `-L dependency=` and `--extern` must point into them."""
    found = [a for a in argv if a.startswith("@")]  # rustc expands `@file` anywhere
    pairs, positional = lint_args(argv)

    def inside(path: str) -> bool:
        return dirs is None or any(_is_under(path, d) for d in dirs)

    for flag, value in pairs:
        if flag in _LINT_ARGS_BARE and value is None:
            continue
        if flag not in _LINT_ARGS_VALUED or value is None:
            found.append(flag if value is None else f"{flag}={value}")
        elif flag in ("-C", "--codegen") and value.split("=", 1)[0] not in _LINT_CODEGEN_KEYS:
            found.append(f"-C {value}")
        elif flag == "-Z" and value not in _LINT_UNSTABLE_OPTS:
            found.append(f"-Z {value}")
        elif flag == "--force-warn" and value != "unused_crate_dependencies":
            found.append(f"--force-warn={value}")
        elif flag == "-L" and not (value.startswith("dependency=")
                                   and inside(value[len("dependency="):])):
            found.append(f"-L {value}")
        elif flag == "--extern" and not ("=" in value and inside(value.split("=", 1)[1])):
            found.append(f"--extern {value}")
        elif flag == "--out-dir" and not inside(value):
            found.append(f"--out-dir {value}")
    # Cargo adds this exact flag for its unused-dependency tracking. It must
    # not become an allowance for other lint-level changes. Its warnings are
    # explicitly refused below, since force-warn takes precedence over -D.
    if sum(flag == "--force-warn" for flag, _ in pairs) > 1:
        found.append("repeated --force-warn")
    sources = [p for p in positional if not p.startswith("@")]
    if len(sources) != 1:
        found.append(f"{len(sources)} positional arguments ({' '.join(sources)}) where cargo "
                     f"passes one crate root")
    return found


def _flag_value(argv: list[str], want: str, key: str | None = None) -> str | None:
    """The value of the LAST `want` flag (for `-C`, the one whose key is `key`)."""
    pairs, _ = lint_args(argv)
    found = None
    for flag, value in pairs:
        if value is None:
            continue
        if key is None and flag == want:
            found = value
        elif key is not None and flag in ("-C", "--codegen") and value.startswith(key + "="):
            found = value[len(key) + 1:]
    return found


def read_dep_info(d: Path, crate_dir: Path) -> tuple[set[str] | None, str]:
    """(every file a rustc dep-info names, as the absolute normalized path rustc
    was given -- NOT resolved, so a symlink stays visible --, "") or (None, why)."""
    try:
        text = d.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return None, f"its dep-info {d} cannot be read ({exc})"
    paths: set[str] = set()
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        toks = [re.sub(r"\\(.)", r"\1", t) for t in re.findall(r"(?:\\.|\S)+", line)]
        if not toks[0].endswith(":"):
            return None, f"its dep-info {d} has a line this check does not read: {line!r}"
        paths.update(os.path.normpath(os.path.join(crate_dir, t)) for t in toks[1:])
    if not paths:
        return None, f"its dep-info {d} names no source file"
    return paths, ""


def lint_dep_info(argv: list[str]) -> Path | None:
    """`<out-dir>/<crate-name><extra-filename>.d` of one lint command line."""
    out_dir = _flag_value(argv, "--out-dir")
    name = _flag_value(argv, "--crate-name")
    extra = _flag_value(argv, "-C", "extra-filename") or ""
    return Path(out_dir) / f"{name}{extra}.d" if out_dir and name else None


def _crate_name(argv: list[str]) -> str | None:
    """The `--crate-name` a compile command carries, or None."""
    if "--crate-name" in argv[:-1]:
        return argv[argv.index("--crate-name") + 1]
    return None


def _is_under(path: str, directory: Path) -> bool:
    try:
        Path(path).resolve().relative_to(directory.resolve())
        return True
    except (ValueError, OSError):
        return False


def tests_verdict(rc: int, out: str, dirs: list[Path] | None = None) -> str | None:
    """Why a `targo --unverified test -v` run does not show the crate's tests passing, or None.

    `dirs` are the target and build dirs the run built into; when given, every
    binary the run EXECUTED must be one cargo built there, and every compile
    must start the compiler itself (RUSTC_WRAPPER='' resets a configured one;
    this is the check that it did)."""
    results = RESULT_LINE.findall(out)
    failed = [line for line in out.splitlines() if line.startswith("test ") and
              line.endswith("FAILED")]
    if rc != 0:
        return (f"`targo --unverified test` exited {rc}"
                + (f"; failing: {'; '.join(failed[:5])}" if failed else "")
                + f" -- {' | '.join(out.strip().splitlines()[-3:])}")
    if any(verdict != "ok" for verdict, *_ in results):
        return "`targo --unverified test` exited 0 but a test binary reported FAILED"
    if sum(int(passed) for _, passed, *_ in results) == 0:
        return ("`targo --unverified test` exited 0 and no `test result:` line reports a test passed -- "
                "a run that selects nothing cannot fail")
    if dirs:
        commands = running_commands(out)
        for argv in commands:
            if _crate_name(argv) is not None and Path(argv[0]).name not in RUSTC_NAMES:
                return (f"`targo --unverified test -v` compiled through `{argv[0]}`, not the compiler -- a "
                        f"rustc wrapper stands between cargo and the code the tests run")
        executed = [argv for argv in commands if _crate_name(argv) is None]
        messages = _messages(out)
        artifacts = {
            os.path.realpath(m["executable"])
            for m in messages
            if m.get("reason") == "compiler-artifact"
            and (m.get("profile") or {}).get("test") is True
            and isinstance(m.get("executable"), str)
            and any(_is_under(m["executable"], d) for d in dirs)
        }
        # Dependency build scripts also appear as `Running` commands. Their
        # artifact kind and exact output distinguish them from test runners;
        # their execution cannot count as having executed a test binary.
        build_scripts = {
            os.path.realpath(path)
            for m in messages
            if m.get("reason") == "compiler-artifact"
            and (m.get("target") or {}).get("kind") == ["custom-build"]
            and (m.get("profile") or {}).get("test") is False
            for path in m.get("filenames", [])
            if isinstance(path, str) and any(_is_under(path, d) for d in dirs)
        }
        for argv in executed:
            if os.path.realpath(argv[0]) not in artifacts | build_scripts:
                return (f"`targo --unverified test -v` ran `{' '.join(argv[:3])}`, which is not a binary it "
                        f"built -- a test runner stands between cargo and the tests, and its "
                        f"output is not their verdict")
        if not any(os.path.realpath(argv[0]) in artifacts for argv in executed):
            return (f"`targo --unverified test -v` reported executing no test binary it built (under "
                    f"{' or '.join(map(str, dirs))}) -- the `test result:` lines above were "
                    f"printed by something else")
    return None


def lint_units(out: str, manifest: Path) -> list[list[str]]:
    """The command lines this clippy run linted the crate's own units with."""
    names = {str((m.get("target") or {}).get("name", "")).replace("-", "_")
             for m in _artifacts(out, manifest)}
    return [argv for argv in running_commands(out) if _crate_name(argv) in names]


def clippy_verdict(rc: int, out: str, manifest: Path,
                   dirs: list[Path] | None = None) -> str | None:
    """Why a `clippy --message-format=json -v` run does not show the crate's test
    target linted clean IN THIS RUN, over a command line this check models
    (`dirs`: where the run builds), or None."""
    messages = _messages(out)
    errors = _errors(messages)
    if rc != 0:
        return (f"clippy exited {rc}"
                + (f": {' || '.join(e.splitlines()[0] for e in errors[:3] if e)}" if errors
                   else f" -- {' | '.join(out.strip().splitlines()[-3:])}"))
    if _unused_dependency_warning(messages):
        return "clippy reported unused_crate_dependencies despite exiting 0"
    if not any((m.get("profile") or {}).get("test") is True for m in _artifacts(out, manifest)):
        return ("clippy exited 0 and left no record of having checked the crate's TEST "
                "target (no `compiler-artifact` with profile.test for "
                f"{manifest}) -- nothing shows the lint ran")
    lines = lint_units(out, manifest)
    if not any("--test" in argv for argv in lines):
        return ("clippy exited 0 but reported no command linting the crate's TEST target in "
                "THIS run (`cargo -v` prints one for every unit it re-checks, and this run's "
                f"`{NONCE_CFG}` argument makes the crate's units re-check) -- a Fresh unit "
                "replays an earlier run's verdict, or the frontend dropped the arguments")
    for argv in lines:
        if Path(argv[0]).name not in CLIPPY_DRIVERS:
            return (f"the crate is linted through `{argv[0]}`, not a clippy driver "
                    f"({' / '.join(CLIPPY_DRIVERS)}) -- a rustc wrapper stands between "
                    f"cargo and the lint")
        if len(argv) < 2 or Path(argv[1]).name not in RUSTC_NAMES:
            return (f"the clippy driver's command line does not name the rustc it wraps "
                    f"next: {' '.join(argv[:3])}")
        unmodeled = unmodeled_lint_args(argv[2:], dirs)
        if unmodeled:
            return (f"the crate's lint ran with {' '.join(unmodeled)} on its command line, "
                    f"which this check does not model -- the line is an ALLOWLIST, and the "
                    f"hermetic run replaces every configuration file's rustflags, so a "
                    f"profile's rustflags or a `[lints]` table put it there")
    return None


def _errors(messages: list[dict]) -> list[str]:
    """The rendered text of every error the compiler reported."""
    return [
        (m.get("message") or {}).get("rendered", "").strip()
        for m in messages
        if m.get("reason") == "compiler-message"
        and (m.get("message") or {}).get("level") in ("error", "error: internal compiler error")
    ]


def _unused_dependency_warning(messages: list[dict]) -> bool:
    """Cargo's force-warn must not let this warning bypass the strict gate."""
    return any(
        m.get("reason") == "compiler-message"
        and (m.get("message") or {}).get("level") == "warning"
        and ((m.get("message") or {}).get("code") or {}).get("code")
        == "unused_crate_dependencies"
        for m in messages
    )


def types_verdict(rc: int, out: str, manifest: Path, driver: Path,
                  dirs: list[Path] | None = None) -> str | None:
    """Why a `targo --unverified check --all-targets -v --message-format=json` run under the
    typed driver does not show every unit of the crate scanned clean IN THIS
    RUN, through that driver, over a command line this check models, or None."""
    messages = _messages(out)
    errors = [e for e in _errors(messages) if e]
    if rc != 0:
        shown = " || ".join(" ".join(e.split()) for e in errors[:4])
        return (f"the typed scan exited {rc}: "
                + (shown or " | ".join(out.strip().splitlines()[-3:])))
    if _unused_dependency_warning(messages):
        return "the typed scan reported unused_crate_dependencies despite exiting 0"
    artifacts = _artifacts(out, manifest)
    if not any((m.get("profile") or {}).get("test") is True for m in artifacts):
        return ("the typed scan exited 0 and left no record of having checked the crate's "
                f"TEST target (no `compiler-artifact` with profile.test for {manifest})")
    units = lint_units(out, manifest)
    if len(units) < len(artifacts):
        return (f"the typed scan built {len(artifacts)} unit(s) of the crate and reported "
                f"starting {len(units)} in THIS run (`{TYPES_RUN_VAR}` is recorded in each "
                f"unit's dep-info, so the crate's units re-check) -- a Fresh unit replays an "
                f"earlier run's verdict")
    scanned = {(name, test == "true") for name, test, _, _ in TYPES_SUMMARY.findall(out)}
    for argv in units:
        if len(argv) < 2 or os.path.realpath(argv[0]) != os.path.realpath(driver):
            return (f"the crate is checked through `{argv[0]}`, not the typed driver {driver} -- "
                    f"its units were compiled by something that does not scan them")
        if Path(argv[1]).name not in RUSTC_NAMES:
            return (f"the typed driver's command line does not name the rustc it replaces "
                    f"next: {' '.join(argv[:3])}")
        unmodeled = unmodeled_lint_args(argv[2:], dirs)
        if unmodeled:
            return (f"the typed scan ran with {' '.join(unmodeled)} on its command line, which "
                    f"this check does not model -- the line is an ALLOWLIST")
        if (_crate_name(argv), "--test" in argv) not in scanned:
            return (f"the typed driver checked `{_crate_name(argv)}`"
                    f"{' (test)' if '--test' in argv else ''} and printed no scan of it -- a "
                    f"driver that compiles without scanning passes everything")
    return None


# ── THE RUNS ARE HERMETIC (see the module doc) ─────────────────────────────
#
# The environment is an allowlist: what stays selects WHERE things are (paths,
# caches, network, the SDK) or how hard to try -- none of it reaches a lint
# level or a test verdict. (`RUSTFLAGS=--cap-lints=allow` inherited from a shell
# passed a planted catch-all until verifier r8b; a scrub list misses the next
# spelling.)
ENV_ALLOW = frozenset({
    "PATH", "HOME", "USER", "LOGNAME", "SHELL", "TMPDIR", "TERM", "LANG", "TZ",
    "CARGO_HOME", "RUSTUP_HOME", "CARGO_TARGET_DIR", "CARGO_BUILD_BUILD_DIR",
    "CARGO_INCREMENTAL", "CARGO_BUILD_JOBS", "CARGO_NET_OFFLINE",
    "CARGO_NET_GIT_FETCH_WITH_CLI", "SSL_CERT_FILE", "SSL_CERT_DIR",
    "HTTP_PROXY", "HTTPS_PROXY", "NO_PROXY", "http_proxy", "https_proxy", "no_proxy",
    "DEVELOPER_DIR", "SDKROOT",
    "CLEAN_FRONTEND_ATTEMPTS", "CLEAN_FRONTEND_BACKOFF",
    # Preserve routing and backed limits exactly, never infer authority from them.
    "CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "CARGO_JOBSERVER_HANDOFF",
    "TRUST_CPU_HANDOFF", "TRUST_FIXED_CLAIM_HANDOFF_V1", "TRUST_CPU_IMPLICIT_FD",
    "ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1", "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
    "BUILD_SLOT_HELD", "BUILD_SLOT_CPU_PROTOCOL", "BUILD_SLOT_CPU_MODE",
    "BUILD_SLOT_CPU_SOURCE", "BUILD_SLOT_CPU_BUDGET", "BUILD_SLOT_POOL_SLOTS",
    "BUILD_SLOT_DIR", "BUILD_SLOT_EXCLUSIVE", "BUILD_SLOT_LEGACY_DIR",
    "BUILD_SLOT_V2_DIR", "BUILD_SLOT_V2_SLOTS", "BUILD_SLOT_FENCE_FDS",
    "TARGO_PLANNED_JOBS", "TARGO_CALLER_JOBS", "HEAVY_GATE_HELD",
})


def sanitized_env(env: dict[str, str]) -> dict[str, str]:
    return {k: v for k, v in env.items() if k in ENV_ALLOW or k.startswith("LC_")}


# The CARGO_HOME entries a run may share with the caller's: the download
# caches. Its `config.toml`, credentials and binaries stay out.
_HOME_CACHES = ("registry", "git")


def _private_cargo_home(home: Path, real: Path) -> None:
    """`home` holds links to `real`'s caches and whatever cargo writes itself
    (its lock and cache tracker) -- nothing anybody put there, such as a
    `config.toml`, survives. Idempotent, so concurrent runs can share it."""
    home.mkdir(parents=True, exist_ok=True)
    for entry in home.iterdir():
        if entry.name in _HOME_CACHES and entry.is_symlink() \
                and os.readlink(entry) == str(real / entry.name):
            continue
        if entry.name.startswith((".package-cache", ".global-cache")):
            continue
        if entry.is_dir() and not entry.is_symlink():
            shutil.rmtree(entry, ignore_errors=True)
        else:
            entry.unlink(missing_ok=True)
    for cache in _HOME_CACHES:
        if (real / cache).is_dir() and not (home / cache).is_symlink():
            try:
                (home / cache).symlink_to(real / cache, target_is_directory=True)
            except FileExistsError:
                pass


def _private_home_path(base: dict[str, str], root: Path) -> Path:
    """ONE private CARGO_HOME per target root: cargo fingerprints a registry
    dependency by the path its source is read from, so a home per crate
    rebuilt the scanner's dependencies on every run (measured 2026-09-26:
    `Dirty proc-macro2: the path to the source changed`, 3.9s a run)."""
    return Path(base.get("CARGO_TARGET_DIR") or root / "target") / "lint-coverage-cargo-home"


def hermetic_env(env: dict[str, str], home: Path) -> dict[str, str]:
    """The environment both runs (and the scanner's build) see."""
    run = sanitized_env(env)
    real = Path(run.get("CARGO_HOME") or Path(run.get("HOME") or "~").expanduser() / ".cargo")
    _private_cargo_home(home, real)
    run["CARGO_HOME"] = str(home)
    flags = "\x1f".join(GATE_RUSTFLAGS)
    run["CARGO_ENCODED_RUSTFLAGS"] = flags
    run["CARGO_ENCODED_RUSTDOCFLAGS"] = flags
    # An EMPTY value overrides any `build.rustc-wrapper` / `-workspace-wrapper`
    # and runs none (cargo's documented reset) -- for the scanner's build too
    # (verifier r10: a configured workspace wrapper built the scanner). The
    # clippy frontend sets its own workspace wrapper, the driver.
    run["RUSTC_WRAPPER"] = ""
    run["RUSTC_WORKSPACE_WRAPPER"] = ""
    # A unit is Fresh when its sources' CONTENT is what it was built from, not
    # their mtimes. Measured 2026-09-26: a failing test planted, built, and the
    # file's bytes restored with an older mtime (`cp -p`, the replay sandbox's
    # clone) -- `cargo test` reran the planted binary, a verdict about bytes the
    # tree does not have; under checksum freshness it rebuilt and passed. The
    # other direction is the fail-open one: a passing artifact over a tree whose
    # test now fails.
    run["CARGO_UNSTABLE_CHECKSUM_FRESHNESS"] = "true"
    return run


# The cargo configuration keys a run may be under. Each selects where things are
# or how hard to try, or is neutralized by `hermetic_env` (rustflags by
# CARGO_ENCODED_*, a wrapper by RUSTC_WRAPPER='' / RUSTC_WORKSPACE_WRAPPER='',
# the target dir by CARGO_TARGET_DIR), or lowers only to codegen flags the line
# allowlist already admits (a profile's debuginfo and codegen-unit keys,
# _CONFIG_PROFILE below). Anything else -- the rest of `profile.*` (its
# rustflags, a debug-assertions split, its opt-level, a build-override or package
# table), `target.*.runner`, `build.rustc`, `build.target`, `[patch]`,
# `[source]`, `[unstable]`, `[host]`, another `[env]` key -- is refused wherever
# its file lives.
_CONFIG_WHERE = frozenset({
    "net", "http", "term", "registries", "registry", "cargo-new", "future-incompat-report",
    "install", "cache", "credential-alias", "doc",
})
_CONFIG_BUILD = frozenset({
    "jobs", "incremental", "target-dir", "rustflags", "rustdocflags", "rustc-wrapper",
    "rustc-workspace-wrapper",
})
_CONFIG_TARGET = frozenset({"rustflags", "rustdocflags", "linker"})
# A PROFILE'S DEBUGINFO AND CODEGEN-UNIT KEYS -- `profile.<name>.<key>` exactly,
# never under `build-override` or `package.<spec>`. The owner's global
# ~/.cargo/config.toml, a kernel-panic guard every checkout under the home
# directory inherits through cargo's ancestor search (no private CARGO_HOME hides
# it), sets `[profile.dev] debug = "line-tables-only"`, `split-debuginfo =
# "unpacked"`, `codegen-units = 16`; refusing them left this check red on that box
# for a file it must never edit. Why they cannot move a verdict:
#   * cargo lowers them to `-C debuginfo=`, `-C split-debuginfo=` and `-C
#     codegen-units=` on each unit's line (targo's `build_base_args`, the same as
#     upstream cargo), keys of _LINT_CODEGEN_KEYS: they reach no lint level, and
#     `trustc --print cfg` prints the same cfg set with and without all three
#     (measured 2026-09-29), so no cfg the source may name moves;
#   * cargo hashes the profile into the unit's identity (`-C metadata`, `-C
#     extra-filename`, compute_metadata), which names artifacts and nothing else;
#   * the one other reader of a debug level is whether debuginfo is ON -- a build
#     script's `DEBUG` variable (custom_build.rs) and the default `strip` -- so
#     `debug` is admitted only at a value that keeps it on, as the dev default
#     (`true`) does; `debug = false` reaches every dependency's build script.
# Measured 2026-09-30: `run_standalone` over two copies of the three gated crates
# outside the home directory, one under a configuration file holding only these
# three keys (verbatim from the owner's file) above it, the other under none. Of
# the 69 compile lines each side printed, 53 (the target units) differed, and
# only in `-C debuginfo=2` -> `-C debuginfo=line-tables-only`, an added `-C
# codegen-units=16` and the identity hashes (`split-debuginfo=unpacked` is
# cargo's macOS default, so it was on both sides); the 16 host units (build
# scripts, a build-dependency) were identical. Every exit code, `test result:`
# line, per-test line, compiler message and typed-scan line was the same, and
# both sides passed.
# NOT admitted: `opt-level` (`trustc --print cfg -C opt-level=3` drops
# `ub_checks`, a cfg cargo does not restore, and optimisation moves what a test
# can observe, stack depth first), and every key that can carry a flag or a cfg
# (`rustflags`, `debug-assertions`, `overflow-checks`, `panic`, `lto`,
# `inherits`, `build-override.*`, `package.*`).
_CONFIG_PROFILE = frozenset({"debug", "split-debuginfo", "codegen-units"})
# cargo's `debug` spellings whose debuginfo is ON (`TomlDebugInfo` other than None).
_DEBUGINFO_ON = frozenset({"limited", "full", "line-tables-only", "line-directives-only"})
CONFIG_ARGS = ("-Zunstable-options", "config", "get", "--merged", "no", "--format", "toml")


def _profile_value_inert(field: str, value: object) -> bool:
    """Whether `profile.<name>.<field> = value` lowers only to codegen flags."""
    if field == "debug":
        return value is True or (type(value) is int and value in (1, 2)) \
            or (type(value) is str and value in _DEBUGINFO_ON)
    if field == "codegen-units":
        return type(value) is int and value > 0
    return field == "split-debuginfo" and value in ("off", "packed", "unpacked")


def modeled_config_key(key: tuple[str, ...], value: object = None) -> bool:
    head, rest = key[0], key[1:]
    if head in _CONFIG_WHERE:
        return True
    if head == "profile":
        return len(rest) == 2 and rest[1] in _CONFIG_PROFILE \
            and _profile_value_inert(rest[1], value)
    if head == "build":
        return len(rest) == 1 and rest[0] in _CONFIG_BUILD
    if head == "target":
        return len(rest) == 2 and rest[1] in _CONFIG_TARGET
    if head == "alias":
        # the frontend runs `clippy` / `tippy`, external subcommands an alias shadows
        return len(rest) == 1 and rest[0] not in ("clippy", "tippy")
    if head == "env":
        return rest[:1] == ("RUST_MIN_STACK",)
    return False


def _leaf_items(doc: dict, prefix: tuple[str, ...] = ()) -> list[tuple[tuple[str, ...], object]]:
    items: list[tuple[tuple[str, ...], object]] = []
    for k, v in doc.items():
        if isinstance(v, dict) and v:
            items += _leaf_items(v, prefix + (k,))
        else:
            items.append((prefix + (k,), v))
    return items


def _config_problem(origin: str, key: tuple[str, ...], value: object) -> str:
    name = ".".join(key)
    if key[0] == "profile" and len(key) == 3 and key[2] in _CONFIG_PROFILE:
        why = (" (`debug` must keep debuginfo on: every build script reads whether it is)"
               if key[2] == "debug" else "")
        return (f"{origin} sets `{name}` to {value!r}, a value this check does not model -- "
                f"it admits that key only where it lowers to nothing but a codegen "
                f"flag{why}, and a file outside the repository cannot be pinned")
    return (f"{origin} sets `{name}`, a cargo configuration key this check does not model -- "
            f"it can change what the tests run or the lint sees, and a file outside the "
            f"repository cannot be pinned")


def config_problems(root: Path, env: dict[str, str], targo: str) -> list[str]:
    """Every cargo configuration key the runs would be under that this check does
    not model, by the file that sets it -- as cargo itself reports them."""
    import tomllib
    config_argv = (targo, *CONFIG_ARGS)
    try:
        proc = subprocess.run(list(config_argv), cwd=root, env=env, capture_output=True,
                              text=True, check=False, pass_fds=custody_fds(env))
    except (OSError, CoverageFailure) as exc:
        return [f"cargo cannot say which configuration it reads: {exc}"]
    if proc.returncode != 0:
        tail = " | ".join((proc.stderr or proc.stdout).strip().splitlines()[-2:])
        return [f"`{' '.join(config_argv)}` exited {proc.returncode} ({tail}) -- which cargo "
                f"configuration the runs read is unknown, so they are not judged"]
    problems = []
    for block in re.split(r"\n\s*\n", proc.stdout.strip()):
        lines = block.splitlines()
        if not lines:
            continue
        if not lines[0].startswith("# "):
            return [f"`{' '.join(config_argv)}` printed a section with no origin line "
                    f"({lines[0]!r}) -- output this check does not read"]
        origin = lines[0][2:].strip()
        if origin == "Environment variables":
            continue  # the environment is ENV_ALLOW's
        try:
            doc = tomllib.loads("\n".join(lines[1:]))
        except ValueError as exc:
            return [f"cargo's report of {origin} does not parse ({exc})"]
        problems += [_config_problem(origin, key, value)
                     for key, value in _leaf_items(doc) if not modeled_config_key(key, value)]
    return problems


def _run(argv: list[str], root: Path, env: dict[str, str]) -> tuple[int, str]:
    try:
        proc = subprocess.run(argv, cwd=root, env=env, capture_output=True, text=True,
                              check=False, pass_fds=custody_fds(env))
        return proc.returncode, proc.stdout + proc.stderr
    except (OSError, CoverageFailure) as exc:
        return 127, f"could not run {argv[0]}: {exc}"


def _dirs(base: dict[str, str], root: Path, crate: str, sub: str) -> dict[str, str]:
    """CARGO_TARGET_DIR (and CARGO_BUILD_BUILD_DIR, when one is inherited -- the
    gate-demonstration sandbox sets it) for one kind of build this check runs,
    in a directory only this check builds into."""
    target = Path(base.get("CARGO_TARGET_DIR") or root / crate / "target")
    dirs = {"CARGO_TARGET_DIR": str(target / sub)}
    if base.get("CARGO_BUILD_BUILD_DIR"):
        dirs["CARGO_BUILD_BUILD_DIR"] = str(Path(base["CARGO_BUILD_BUILD_DIR"]) / sub)
    return dirs


def build_scanner(root: Path, env: dict[str, str], targo: str) -> tuple[Path | None, str]:
    """(the scanner binary, "") or (None, why) -- built from this tree."""
    run_env = {**env, **_dirs(sanitized_env(env), root, SCANNER, "check-tests")}
    rc, out = _run([targo, "--unverified", "build", "--locked", "--manifest-path", f"{SCANNER}/Cargo.toml",
                    "--message-format=json-render-diagnostics"], root, run_env)
    exes = [m["executable"] for m in _artifacts(out, root / SCANNER / "Cargo.toml")
            if m.get("executable")]
    if rc != 0 or len(exes) != 1:
        return None, (f"the scanner {SCANNER} did not build (exit {rc}, {len(exes)} "
                      f"executables) -- {' | '.join(out.strip().splitlines()[-3:])}")
    return Path(exes[0]), ""


def build_types(root: Path, env: dict[str, str], targo: str) -> tuple[Path | None, str]:
    """(the typed driver, "") or (None, why) -- built from this tree.

    It links the compiler's own library, and cargo starts a workspace wrapper
    directly, with no library search path of its own; so the driver is linked
    with an rpath to the sysroot of the compiler that builds it. A driver linked
    against another toolchain's library does not load, and the typed run fails.

    That compiler is targo's own sibling `trustc` (targo's default executable;
    `RUSTC` is not in ENV_ALLOW and a `build.rustc` key is refused), never the
    `trustc` PATH names. Measured 2026-10-15: PATH named aterm's package-store
    trustc (321aaeda7) while targo's sibling was trust-7d5533b2, so the driver
    linked trust-7d5533b2's librustc_driver with an rpath to the other lib/,
    and the typed run died in dyld for anybody whose PATH was not the hook's."""
    compiler = Path(targo).parent / "trustc"
    if not compiler.is_file() or not os.access(compiler, os.X_OK):
        return None, (f"the targo this check runs ({targo}) has no sibling `trustc`, the "
                      f"compiler that builds the typed driver")
    try:
        proc = subprocess.run([str(compiler), "--print=sysroot"], cwd=root, env=env,
                              capture_output=True, check=False,
                              pass_fds=custody_fds(env))
    except (OSError, CoverageFailure) as exc:
        return None, f"`{compiler} --print=sysroot` could not run: {exc}"
    output = os.fsdecode(proc.stdout).removesuffix("\n")
    sysroot = (Path(output) if proc.returncode == 0 and output
               and not any(c in output for c in "\n\r\x00")
               and Path(output).is_absolute() else None)
    if sysroot is None or not (sysroot / "lib").is_dir():
        return None, (f"`{compiler} --print=sysroot` named no sysroot (exit {proc.returncode}: "
                      f"{os.fsdecode(proc.stdout + proc.stderr).strip()[-200:]})")
    run_env = {**env, **_dirs(sanitized_env(env), root, TYPES, "check-tests")}
    rc, out = _run([targo, "--unverified", "rustc", "--locked", "--manifest-path", f"{TYPES}/Cargo.toml",
                    "--bin", "lint-types", "--message-format=json-render-diagnostics", "--",
                    "-C", f"link-arg=-Wl,-rpath,{sysroot / 'lib'}"], root, run_env)
    exes = [m["executable"] for m in _artifacts(out, root / TYPES / "Cargo.toml")
            if m.get("executable")]
    if rc != 0 or len(exes) != 1:
        return None, (f"the typed driver {TYPES} did not build (exit {rc}, {len(exes)} "
                      f"executables) -- {' | '.join(out.strip().splitlines()[-3:])}")
    return Path(exes[0]), ""


def scan_sources(root: Path, scanner: Path, files: list[str]) -> list[str]:
    """The scanner's refusals over `files` (repo-relative)."""
    forbid = [flag for lint in FORBIDDEN_LINTS for flag in ("--forbidden", lint)]
    rc, out = _run([str(scanner), *forbid, *files], root, {"PATH": os.environ.get("PATH", "")})
    lines = out.strip().splitlines()
    if rc == 0 and not lines:
        return []
    if rc == 1 and lines:
        return lines
    return [f"the scanner exited {rc} -- {' | '.join(lines[-3:])}"]


def source_problems(root: Path, crate: str, outs: dict[str, str],
                    scanner: Path, typed: str | None) -> list[str]:
    """What the runs compiled, tied to the source (see the module doc). `typed`
    is the typed scan's output when it passed (its failure is already one)."""
    crate_dir = root / crate
    manifest = crate_dir / "Cargo.toml"
    compiled: dict[str, set[str]] = {"clippy": set(), "tests": set(), "types": set()}
    for half, out in (("clippy", outs["clippy"]), ("types", typed or "")):
        for argv in lint_units(out, manifest):
            d = lint_dep_info(argv[2:])
            paths, why = read_dep_info(d, crate_dir) if d else (
                None, "its command line names no --out-dir or --crate-name")
            if paths is None:
                return [f"the {'lint' if half == 'clippy' else 'typed scan'} of "
                        f"`{_crate_name(argv)}` cannot be tied to its source: {why}"]
            # The driver's OWN executable is not source: a clippy driver built
            # with debug assertions records `current_exe()` in the dep-info so
            # an edited driver re-lints (clippy_driver `track_files`; Trust's
            # stage2 tippy-driver, measured 2026-09-26 in 4b5d85505). Exactly
            # that path.
            own_driver = os.path.realpath(argv[0])
            compiled[half] |= {p for p in paths if os.path.realpath(p) != own_driver}
    tested = [m for m in _artifacts(outs["tests"], manifest)
              if (m.get("profile") or {}).get("test") and m.get("executable")]
    if not tested:
        return ["`targo --unverified test` reported no test executable for the crate -- nothing ties the "
                "tests to their source"]
    for m in tested:
        paths, why = read_dep_info(Path(m["executable"] + ".d"), crate_dir)
        if paths is None:
            return [f"the test build cannot be tied to its source: {why}"]
        compiled["tests"] |= paths
    problems = []
    # A profile can set the two runs apart (`[profile.test] debug-assertions =
    # false` in the crate's manifest, verifier r9): cargo reports what each unit
    # was built under, Fresh or not.
    for key in ("debug_assertions", "overflow_checks"):
        ran = {str((m.get("profile") or {}).get(key)) for m in tested}
        for half, what in (("clippy", "the lint"), ("types", "the typed scan")):
            if half == "types" and typed is None:
                continue
            checked = {str((m.get("profile") or {}).get(key))
                       for m in _artifacts(typed if half == "types" else outs["clippy"], manifest)
                       if (m.get("profile") or {}).get("test")}
            if checked != ran:
                problems.append(f"{what} checked the test target with {key}={sorted(checked)} "
                                f"and the tests ran it with {key}={sorted(ran)} -- code under a "
                                f"cfg that setting decides is tested and never "
                                f"{'linted' if half == 'clippy' else 'scanned'}")
    tracked = set(tracked_files(root, crate))
    real_root = os.path.realpath(root)

    def rel(path: str) -> str:
        return os.path.relpath(path, root)

    everything = compiled["clippy"] | compiled["tests"] | compiled["types"]
    untracked = {rel(p) for p in everything
                 if rel(p) not in tracked
                 or os.path.realpath(p) != os.path.join(real_root, rel(p))}
    if untracked:
        problems.append(f"rustc compiled {', '.join(sorted(untracked))}, which is not a "
                        f"git-tracked regular file of {crate} -- a module behind a directory "
                        f"symlink, a name git does not track (`src/extra.RS` opened as "
                        f"`src/extra.rs`), a path outside the crate: source nobody pinned or "
                        f"scanned")
    only_tested = sorted(rel(p) for p in compiled["tests"] - compiled["clippy"])
    if only_tested:
        problems.append(f"the tests compiled {', '.join(only_tested)}, which the lint run never "
                        f"compiled -- tested and never linted")
    # The manifest is in the lint's dep-info (clippy tracks it) and is no source.
    unscanned = sorted(rel(p) for p in (compiled["tests"] | compiled["clippy"])
                       - compiled["types"] - {os.path.normpath(manifest)})
    if typed is not None and unscanned:
        problems.append(f"the tests or the lint compiled {', '.join(unscanned)}, which the typed "
                        f"scan never read -- a catch-all there is judged by nobody")
    files = sorted(rel(p) for p in everything
                   if p != os.path.normpath(manifest) and rel(p) not in untracked)
    return problems + [f"its source keeps code out of the lint run: {line}"
                       for line in (scan_sources(root, scanner, files) if files else [])]


def run_standalone(root: Path, crate: str, env: dict[str, str] | None = None) -> list[str]:
    """Run the crate's tests, its lint and its typed scan, and scan what they
    compiled; one message per thing that fails.

    Each run builds into a directory only this check builds into (`check-tests`,
    `clippy`, `types` beneath the crate's target dir or CARGO_TARGET_DIR), so a
    Fresh unit was compiled under these same settings, never by someone's own
    `targo --unverified test` beside it."""
    source_env = dict(os.environ if env is None else env)
    base = sanitized_env(source_env)
    head = (f"{crate} is STANDALONE_GATED -- no workspace command compiles it, and this "
            f"check is what runs it --")
    try:
        import tomllib
        package = tomllib.loads((root / crate / "Cargo.toml").read_text(encoding="utf-8")).get(
            "package", {})
    except (ImportError, OSError, ValueError) as exc:
        return [f"{head} and its Cargo.toml cannot be read for a build-script key: {exc}"]
    failures = []
    if (root / crate / "build.rs").exists() or "build" in package:
        failures.append(f"{head} and it has a build script -- it runs under clippy and under "
                        f"`targo --unverified test` alike and can set a cfg only in one of them")
    try:
        targo = resolve_targo(source_env)
    except CoverageFailure as exc:
        return failures + [f"{head} and {exc}"]
    hermetic = hermetic_env(source_env, _private_home_path(base, root))
    # The frontend's clippy run resolves through the same rule; hand it THIS
    # answer, so the three runs cannot use two different targos.
    hermetic["TARGO"] = targo
    # A configuration this check does not model is refused BEFORE anything is
    # built or run under it. Measured 2026-10-15: the refusal used to be one
    # failure among the runs', so a `runner = "/usr/bin/env"` (the demonstration
    # arm) still ran `targo test` through the SIP-protected /usr/bin/env, which
    # drops DYLD_*; lint_types' test binary died in dyld (SIGABRT, a crash
    # report) on every replay while the arm passed on this message.
    unmodeled = config_problems(root, hermetic, targo)
    if unmodeled:
        return failures + [f"{head} and {p} -- refused before anything was built or run"
                           for p in unmodeled]
    # Resolve downloads before collecting execution evidence. In a cold cache,
    # verbose Targo reports its Git fetch as a `Running` command too. Keep
    # tests_verdict's strict executable check: fetching is a separate phase,
    # and the test phase must work offline over those locked dependencies.
    fetch = [targo, "fetch", "--locked", "--manifest-path", f"{crate}/Cargo.toml"]
    fetch_rc, fetch_out = _run(fetch, root, hermetic)
    if fetch_rc != 0:
        return failures + [f"{head} and dependency fetch exited {fetch_rc}: "
                           f"{' | '.join(fetch_out.strip().splitlines()[-3:])}"]
    scanner, why = build_scanner(root, hermetic, targo)
    if scanner is None:
        failures.append(f"{head} and its source cannot be scanned: {why}")
    driver, why = build_types(root, hermetic, targo)
    if driver is None:
        failures.append(f"{head} and its source cannot be type-scanned: {why}")
    blocked = bool(failures)
    manifest = root / crate / "Cargo.toml"
    nonce = secrets.token_hex(8)
    outs: dict[str, str] = {}
    verdicts: dict[str, str | None] = {}
    for half, argv in standalone_commands(root, crate, nonce, targo).items():
        if half == "types" and driver is None:
            continue
        dirs = _dirs(base, root, crate, {"tests": "check-tests"}.get(half, half))
        run_env = {**hermetic, **dirs}
        if half == "tests":
            run_env["CARGO_NET_OFFLINE"] = "true"
        if half == "types" and driver is not None:
            run_env.update({"RUSTC_WORKSPACE_WRAPPER": str(driver), TYPES_RUN_VAR: nonce})
        rc, outs[half] = _run(argv, root, run_env)
        built_in = [Path(v) for v in dirs.values()]
        if half == "tests":
            verdicts[half] = tests_verdict(rc, outs[half], built_in)
        elif half == "clippy":
            verdicts[half] = clippy_verdict(rc, outs[half], manifest, built_in)
        elif driver is not None:
            verdicts[half] = types_verdict(rc, outs[half], manifest, driver, built_in)
        if verdicts.get(half):
            failures.append(f"{head} and its {half} FAILED: {verdicts[half]}. "
                            f"Command: {' '.join(argv)}")
    # The source scan needs what the tests and the lint compiled; a failed typed
    # scan does not hold it back (each says what it found).
    if not blocked and scanner is not None and not verdicts.get("tests") \
            and not verdicts.get("clippy"):
        typed = outs.get("types") if "types" in verdicts and not verdicts["types"] else None
        failures += [f"{head} and {p}"
                     for p in source_problems(root, crate, outs, scanner, typed)]
    return failures


# ── THE PINNED INPUTS ──────────────────────────────────────────────────────
#
# `--pinned-inputs` prints every file whose change can change how this check
# decides -- the frontend it runs clippy through, every git-tracked file of
# every STANDALONE_GATED crate (sources, manifests, lockfiles; the scanner's
# included), and the cargo configuration and toolchain files cargo reads from
# the directory it runs in. check_gate_registry.py R7 hashes that list into the
# row's `inputs` and refuses any change to it -- an edited file, an added one, a
# removed one -- until the row's arms are replayed over it (`--repin`).
#
# What it deliberately leaves out: the files the crate's tests READ as the thing
# under test (`eval_ir_machine.rs`: a change there turns this check red, it
# cannot make it blind), the gate sites and manifests this check inspects, and
# anything outside the repository (the toolchain binaries; configuration there
# is refused or neutralized by the hermetic runs).
# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): this check answers
# `--pinned-inputs`, so its registry row must pin what that prints.
ANSWERS_PINNED_INPUTS = True
CARGO_CONFIG_FILES = (".cargo/config.toml", ".cargo/config", "rust-toolchain.toml",
                      "rust-toolchain")


def pinned_inputs(root: Path) -> list[str]:
    """The derived pin set (see above), repo-relative, sorted; excludes this
    script, which the registry row pins as its `script_sha256`."""
    files = {FRONTEND, RESOURCE_TRANSPORT}
    for crate in sorted(STANDALONE_GATED):
        tracked = tracked_files(root, crate)
        if not tracked:
            raise CoverageFailure(f"{crate} has no tracked files to pin")
        files.update(tracked)
    files.update(name for name in CARGO_CONFIG_FILES if (root / name).is_file())
    files.discard(Path(__file__).resolve().relative_to(ROOT).as_posix())
    return sorted(files)


def member_dirs(metadata: dict, key: str) -> set[str]:
    ids = set(metadata[key])
    dirs: set[str] = set()
    for package in metadata["packages"]:
        if package["id"] in ids:
            manifest = Path(package["manifest_path"]).resolve().parent
            dirs.add(manifest.relative_to(ROOT).as_posix())
    return dirs


def check_orphans(
    metadata: dict,
    tracked_manifests: list[str] | None = None,
    root: Path = ROOT,
) -> list[str]:
    members = member_dirs(metadata, "workspace_members")
    failures: list[str] = []
    if tracked_manifests is None:
        tracked_manifests = tracked_crate_manifests()
    tracked = {
        crate_dir
        for crate_dir in (Path(m).parent.as_posix() for m in tracked_manifests)
        if not any(crate_dir.startswith(member + "/") for member in members)
    }

    for crate_dir in sorted(tracked - members):
        if crate_dir in KNOWN_ORPHANS:
            continue
        if crate_dir in STANDALONE_GATED:
            failures.extend(run_standalone(root, crate_dir))
            continue
        failures.append(
            f"{crate_dir} is git-tracked but is not a workspace member: no "
            f"cargo command in this repo compiles or lints it. Add it to "
            f"[workspace] members in Cargo.toml, list it in STANDALONE_GATED "
            f"(this check then runs its tests and lints it), or record it in "
            f"KNOWN_ORPHANS with the disposition that keeps it out."
        )

    for crate_dir in sorted(STANDALONE_GATED):
        if crate_dir in members:
            # A member is not in `tracked - members`, so the loop above never
            # runs it, and the workspace gate does not forbid the wildcard lints.
            failures.append(
                f"STANDALONE_GATED lists {crate_dir}, which is a workspace member -- this "
                f"check runs only crates outside [workspace], so its tests and its "
                f"forbidden-lint run would silently stop. Take it back out of [workspace] "
                f"or delete the entry."
            )
        elif crate_dir not in tracked:
            failures.append(
                f"STANDALONE_GATED lists {crate_dir}, which is not a tracked "
                f"standalone crate — delete the entry."
            )
        elif crate_dir in KNOWN_ORPHANS:
            failures.append(f"{crate_dir} is both STANDALONE_GATED and a KNOWN_ORPHAN.")

    for crate_dir, reason in sorted(KNOWN_ORPHANS.items()):
        if not (ROOT / crate_dir / "Cargo.toml").exists():
            failures.append(
                f"KNOWN_ORPHANS lists {crate_dir}, which no longer exists — "
                f"delete the entry (the list is shrink-only). Recorded reason: "
                f"{reason}"
            )
        elif crate_dir in members:
            failures.append(
                f"KNOWN_ORPHANS lists {crate_dir}, which is now a workspace "
                f"member — delete the entry (the list is shrink-only)."
            )
    return failures


def check_gate_sites() -> list[str]:
    failures: list[str] = []
    for site in GATE_SITES:
        path = ROOT / site
        if not path.exists():
            failures.append(f"gate site {site} is missing")
            continue
        if FULL_GATE not in path.read_text(encoding="utf-8"):
            failures.append(
                f"{site} no longer contains the full gate `{FULL_GATE}`. The "
                f"pre-push gate must select every workspace member and every "
                f"target kind; narrowing it re-opens the blind spot where "
                f"non-default members' test targets are never linted."
            )
    return failures


def coverage_summary(metadata: dict) -> str:
    """Live crate/target counts for both gates (build scripts excluded)."""
    members = set(metadata["workspace_members"])
    defaults = set(metadata["workspace_default_members"])
    fast_crates = fast_targets = full_crates = full_targets = 0
    for package in metadata["packages"]:
        if package["id"] not in members:
            continue
        targets = sum(
            1 for t in package["targets"] if t["kind"] != ["custom-build"]
        )
        full_crates += 1
        full_targets += targets
        if package["id"] in defaults:
            fast_crates += 1
            fast_targets += targets
    return (
        f"  fast inner loop (default-members, --all-targets): "
        f"{fast_crates}/{full_crates} crates, {fast_targets}/{full_targets} targets\n"
        f"  full gate (--workspace --all-targets):            "
        f"{full_crates}/{full_crates} crates, {full_targets}/{full_targets} targets"
    )


# ── SELF-TEST: the runner, against stub tools ──────────────────────────────
#
# Run FIRST on every invocation. A stub crate carries a marker naming the one
# defect the arm plants; stub `targo`, clippy and scanner behave as the real
# tools do on it. The clippy stub reports a lint only when the command line
# keeps it live: each `#[allow]`ed wildcard lint BY NAME only when that lint is
# FORBIDDEN, the unused function only under `-D warnings`, nothing at all when
# a cap reaches it -- and it prints the `Running` lines cargo prints and the
# dep-info rustc writes, with what a configuration file adds (only when
# CARGO_ENCODED_RUSTFLAGS does not replace it) or a profile or `[lints]` table
# adds (whatever the environment). Each arm requires the runner's verdict: the
# clean crate passes, every planted shape fails.

_STUB_CARGO = r"""#!/usr/bin/env bash
src="scripts/stub_crate/src/main.rs"
plant() { grep -q "$1" "$src"; }
# Every stub logs its call, so an arm can say what was RUN, not only the verdict.
printf 'targo %s\n' "$*" >> "$PWD/.stub-calls"
# `PLANT_CONFIG_LINE:<key>=<value>`: a line of a configuration file ABOVE the
# checkout (the owner's global one is such a file) ...
config_lines() { grep -o 'PLANT_CONFIG_LINE:[^ ]*' "$src" | sed 's/^PLANT_CONFIG_LINE://'; }
# ... and what cargo writes on every unit's line for a profile's debuginfo and
# codegen-unit keys (`build_base_args`).
profile_flags() {
  local line v out=""
  while IFS= read -r line; do
    v="${line#*=}"; v="${v//\"/}"
    case "${line%%=*}" in
      profile.*.debug) out="$out -C debuginfo=$v" ;;
      profile.*.split-debuginfo) out="$out -C split-debuginfo=$v" ;;
      profile.*.codegen-units) out="$out -C codegen-units=$v" ;;
    esac
  done < <(config_lines)
  printf '%s' "$out"
}
# targo: a compilation verb runs only under an explicit lane.
lane=0; [[ "$1" == --unverified ]] && { lane=1; shift; }
if [[ "$1" == fetch ]]; then
  plant PLANT_FETCH_FAIL && { echo 'dependency fetch refused' >&2; exit 101; }
  exit 0
fi
if [[ "$1" == -Zunstable-options && "$2 $3" == "config get" ]]; then
  plant PLANT_CONFIG_UNREADABLE && { echo "error: config is unstable" >&2; exit 101; }
  printf '# Environment variables\n# CARGO_BUILD_JOBS=3\n\n# %s/.cargo/config.toml\nbuild.jobs = 4\n' "$PWD"
  printf 'target.aarch64-apple-darwin.rustflags = ["-Ztrust-verify=off"]\n'
  # A CARGO_HOME's own configuration: cargo reads it, unless the home is private.
  [[ -f "$CARGO_HOME/config.toml" ]] && printf '\n# %s/config.toml\n%s\n' "$CARGO_HOME" "$(cat "$CARGO_HOME/config.toml")"
  plant PLANT_CONFIG_UNMODELED && printf '\n# /elsewhere/.cargo/config.toml\nprofile.dev.rustflags = ["--cap-lints=allow"]\n'
  plant PLANT_CONFIG_RUNNER && printf '\n# /elsewhere/.cargo/config.toml\ntarget.aarch64-apple-darwin.runner = "/usr/bin/env"\n'
  plant PLANT_CONFIG_NO_ORIGIN && printf '\nbuild.jobs = 1\n'
  plant PLANT_CONFIG_WSWRAPPER && printf '\n# /elsewhere/.cargo/config.toml\nbuild.rustc-workspace-wrapper = "/elsewhere/wrap"\n'
  above="$(config_lines)"
  [[ -n "$above" ]] && printf '\n# /elsewhere/above/.cargo/config.toml\n%s\n' "$above"
  exit 0
fi
[[ $lane -eq 1 ]] || { echo "stub targo: \`$1\` without a lane is refused" >&2; exit 101; }
# A `build.rustc-workspace-wrapper` in some configuration file compiles the
# workspace's units unless RUSTC_WORKSPACE_WRAPPER is SET (an empty value resets
# it): here it builds a scanner that refuses nothing.
wswrapped=0
plant PLANT_CONFIG_WSWRAPPER && [[ -z "${RUSTC_WORKSPACE_WRAPPER+set}" ]] && wswrapped=1
if [[ "$1" == build ]]; then
  plant PLANT_SCANNER_UNBUILT && { echo "error: could not compile" >&2; exit 101; }
  scanner=scanner; [[ $wswrapped -eq 1 ]] && scanner=scanner-lenient
  printf '{"reason":"compiler-artifact","manifest_path":"%s/scripts/lint_scan/Cargo.toml","target":{"name":"lint-scan"},"profile":{"test":false},"executable":"%s/bin/%s"}\n' "$PWD" "$PWD" "$scanner"
  exit 0
fi
# The typed driver's build (`cargo rustc ... -- -C link-arg=-Wl,-rpath,...`).
if [[ "$1" == rustc ]]; then
  plant PLANT_TYPES_UNBUILT && { echo "error: could not compile" >&2; exit 101; }
  printf '{"reason":"compiler-artifact","manifest_path":"%s/scripts/lint_types/Cargo.toml","target":{"name":"lint-types"},"profile":{"test":false},"executable":"%s/bin/typed"}\n' "$PWD" "$PWD"
  exit 0
fi
# The typed scan: cargo starts the workspace wrapper, if one is set, over each
# of the crate's units, and the driver prints its scan of each.
if [[ "$1" == check ]]; then
  deps="$CARGO_TARGET_DIR/debug/deps"; mkdir -p "$deps"
  prog="$PWD/bin/trustc"
  [[ -n "${RUSTC_WORKSPACE_WRAPPER:-}" ]] && prog="$RUSTC_WORKSPACE_WRAPPER $prog"
  plant PLANT_TYPES_OTHER_DRIVER && prog="$PWD/bin/scanner-lenient $PWD/bin/trustc"
  flags="$(profile_flags) --force-warn=unused_crate_dependencies"
  plant PLANT_TYPES_LINE_CFG && flags="$flags --cfg test"
  if plant PLANT_TYPES_UNUSED_DEPENDENCY; then
    printf '{"reason":"compiler-message","message":{"level":"warning","code":{"code":"unused_crate_dependencies"},"rendered":"warning: unused dependency"}}\n'
  fi
  if plant PLANT_TYPES_REFUSE; then
    printf '{"reason":"compiler-message","message":{"level":"error","rendered":"error: `_` stands for what another alternative of this pattern tells apart at the same place -- a catch-all over a gated enum compiles unchanged when the enum gains a variant"}}\n'
    exit 101
  fi
  unit() {
    echo "     Running \`$prog --crate-name stub --edition=2021 src/main.rs$1$flags -C extra-filename=-$2 --out-dir $deps -L dependency=$deps\`" >&2
    printf '%s/stub-%s.d: src/main.rs\n' "$deps" "$2" > "$deps/stub-$2.d"
    plant PLANT_TYPES_SILENT || echo "lint-types: scanned crate \`stub\` test=$3 bodies=1 pattern-sets=1 patterns=1 derived=0 refused=0" >&2
  }
  art() { printf '{"reason":"compiler-artifact","manifest_path":"%s/scripts/stub_crate/Cargo.toml","target":{"name":"stub"},"profile":{"test":%s,"debug_assertions":true,"overflow_checks":true}}\n' "$PWD" "$1"; }
  unit " --crate-type bin" bin0 false; art false
  plant PLANT_TYPES_FRESH || unit " --test" test0 true
  art true
  exit 0
fi
[[ "$1" == test ]] || { echo "stub targo: unexpected subcommand $1" >&2; exit 2; }
bin="$CARGO_TARGET_DIR/debug/deps/stub-0123abcd"
plant PLANT_MODERN_TEST_PATH && bin="$CARGO_TARGET_DIR/debug/build/stub/0123abcd/out/stub-0123abcd"
run() { echo "     Running \`$1\`" >&2; }
if plant PLANT_COLD_FETCH && { [[ "${CARGO_NET_OFFLINE:-}" != true ]] || ! grep -q '^targo fetch --locked --manifest-path scripts/stub_crate/Cargo.toml$' "$PWD/.stub-calls"; }; then
  run 'git -c core.fsmonitor=false fetch --no-tags https://example.invalid/dependency'
fi
if plant PLANT_DEPENDENCY_BUILD_SCRIPT; then
  script="$CARGO_TARGET_DIR/debug/build/dependency/0123abcd/out/build_script_build"
  plant PLANT_UNRECORDED_BUILD_SCRIPT || printf '{"reason":"compiler-artifact","target":{"kind":["custom-build"]},"profile":{"test":false},"filenames":["%s"]}\n' "$script"
  run "$script"
fi
compiler="$PWD/bin/trustc"
plant PLANT_TEST_WRAPPER && compiler="/usr/local/bin/sccache $compiler"
# A `build.rustc-wrapper` in some configuration file: cargo uses it unless
# RUSTC_WRAPPER is SET (an empty value resets it).
plant PLANT_CONFIG_WRAPPER && [[ -z "${RUSTC_WRAPPER+set}" ]] && compiler="/usr/local/bin/sccache $compiler"
[[ $wswrapped -eq 1 ]] && compiler="/elsewhere/wrap $compiler"
run "$compiler --crate-name stub --edition=2021 src/main.rs --test$(profile_flags)"
da=true; plant PLANT_TEST_PROFILE_SPLIT && da=false
mkdir -p "$(dirname "$bin")"
printf '%s.d: src/main.rs%s\n' "$bin" "$(grep -o 'PLANT_TEST_DEPINFO:[^ ]*' "$src" | sed 's/^PLANT_TEST_DEPINFO:/ /' | tr -d '\n')" > "$bin.d"
printf '{"reason":"compiler-artifact","manifest_path":"%s/scripts/stub_crate/Cargo.toml","target":{"name":"stub"},"profile":{"test":true,"debug_assertions":%s,"overflow_checks":true},"executable":"%s"}\n' "$PWD" "$da" "$bin"
plant PLANT_UNRECORDED_TEST_BIN && bin="${bin}-unrecorded"
ok='test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out'
if plant PLANT_FAILING_TEST; then
  run "$bin"; echo "test plant::planted ... FAILED"
  echo "test result: FAILED. 4 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out"
  exit 101
fi
plant PLANT_ZERO_TESTS && { run "$bin"; echo "running 0 tests"; echo "${ok/5 passed/0 passed}"; exit 0; }
plant PLANT_NO_RESULT_LINE && { run "$bin"; exit 0; }
plant PLANT_OK_BUT_EXIT_101 && { run "$bin"; echo "$ok"; exit 101; }
# A test binary built from OTHER bytes than the tree's (a failing test restored
# with an older mtime): under mtime freshness cargo runs the stale, passing one.
if plant PLANT_STALE_PASSING_ARTIFACT && [[ -z "${CARGO_UNSTABLE_CHECKSUM_FRESHNESS:-}" ]]; then
  run "$bin"; echo "running 5 tests"; echo "$ok"; exit 0
fi
plant PLANT_STALE_PASSING_ARTIFACT && { run "$bin"; echo "test plant::planted ... FAILED"; echo "${ok/ok./FAILED.}"; exit 101; }
plant PLANT_FAILED_BUT_EXIT_0 && { run "$bin"; echo "${ok/ok./FAILED.}"; exit 0; }
# A runner stands between cargo and a test binary and prints what it likes.
plant PLANT_TEST_RUNNER && { run "$bin"; run "/usr/bin/env ${bin}-it"; echo "$ok"; exit 0; }
plant PLANT_NO_EXEC_LINE || plant PLANT_ONLY_BUILD_SCRIPT || run "$bin"
echo "running 5 tests"; echo "$ok"
"""

_STUB_FRONTEND = r"""#!/usr/bin/env bash
printf 'frontend %s\n' "$*" >> "$PWD/.stub-calls"
[[ "$1" == clippy ]] || { echo "stub frontend: unexpected $1" >&2; exit 2; }
shift
manifest=""; prev=""; after=0; verbose=0; deny_warnings=0; forbidden=" "
for a in "$@"; do
  [[ "$prev" == "--manifest-path" ]] && manifest="$a"
  [[ $after -eq 0 && "$a" == -v ]] && verbose=1
  if [[ $after -eq 1 ]]; then
    [[ "$prev" == -D && "$a" == warnings ]] && deny_warnings=1
    [[ "$prev" == -F ]] && forbidden="$forbidden$a "
  fi
  [[ "$a" == "--" ]] && after=1
  prev="$a"
done
src="$(dirname "$manifest")/src/main.rs"
abs="$PWD/$manifest"
plant() { grep -q "$1" "$src"; }
# What cargo puts on the crate's command line: CARGO_ENCODED_RUSTFLAGS, which
# replaces every other source of rustflags; else RUSTFLAGS; else whatever a
# configuration file's rustflags say.
if [[ -n "${CARGO_ENCODED_RUSTFLAGS+set}" ]]; then
  flags=" ${CARGO_ENCODED_RUSTFLAGS//$'\x1f'/ }"
elif [[ -n "${RUSTFLAGS:-}" ]]; then
  flags=" $RUSTFLAGS"
else
  flags=""
  plant PLANT_CONFIG_CAP_LINTS && flags="$flags --cap-lints allow"
fi
# What a profile's debuginfo and codegen-unit keys in a configuration file above
# the checkout add (`PLANT_CONFIG_LINE:`, as the stub `targo` reports them),
# whatever the environment.
while IFS= read -r line; do
  v="${line#*=}"; v="${v//\"/}"
  case "${line%%=*}" in
    profile.*.debug) flags="$flags -C debuginfo=$v" ;;
    profile.*.split-debuginfo) flags="$flags -C split-debuginfo=$v" ;;
    profile.*.codegen-units) flags="$flags -C codegen-units=$v" ;;
  esac
done < <(grep -o 'PLANT_CONFIG_LINE:[^ ]*' "$src" | sed 's/^PLANT_CONFIG_LINE://')
# What a profile's rustflags or a `[lints]` table adds, whatever the environment.
plant PLANT_LINE_ALLOW_WARNINGS && flags="$flags -A warnings"
# An argument FILE: rustc expands it, and the `--cap-lints=allow` inside never
# reaches the line cargo prints (verifier r9 recheck, measured with real tippy).
plant PLANT_LINE_ARGFILE && flags="$flags @/cfg/lint.args"
plant PLANT_LINE_CFG_TEST && flags="$flags --cfg test"
plant PLANT_LINE_EXTERN && flags="$flags --extern trust_ir=/elsewhere/libtrust_ir.rmeta"
# Cargo's own tracking flag is present on ordinary compiler command lines.
flags="$flags --force-warn=unused_crate_dependencies"
plant PLANT_FORCE_OTHER && flags="$flags --force-warn=clippy::wildcard_enum_match_arm"
plant PLANT_FORCE_WARNINGS && flags="$flags --force-warn=warnings"
plant PLANT_FORCE_REPEATED && flags="$flags --force-warn=unused_crate_dependencies"
driver="$PWD/bin/tippy-driver"
plant PLANT_RUSTC_WRAPPER && driver="/usr/local/bin/sccache $driver"
capped=0
[[ "$flags" == *cap-lints* || "$flags" == *"-A warnings"* || "$flags" == *" @"* ]] && capped=1
# An inherited variable the toolchain honours and cargo never echoes (the class
# the environment allowlist exists for): it caps silently.
[[ -n "${CLEAN_STUB_INVISIBLE_CAP:-}" ]] && capped=1
deps="$CARGO_TARGET_DIR/debug/deps"
# What cargo prints for a unit, and the dep-info rustc writes for it: the
# sources it read -- `PLANT_DEPINFO:<path>` adds one, as rustc does for a module
# reached through a directory symlink, a `.RS` file, or a target path outside
# the crate.
running() {
  if [[ $verbose -eq 1 ]]; then
    printf '     Running `%s /stub/rustc --crate-name stub --edition=2021 src/main.rs%s -C extra-filename=-%s --out-dir %s -L dependency=%s%s`\n' \
      "$driver" "$1" "$2" "$deps" "$deps" "$flags" >&2
  fi
  plant PLANT_NO_DEPINFO && return 0
  mkdir -p "$deps"
  self_dep=""
  plant PLANT_DEPINFO_SELF && self_dep=" $driver"
  printf '%s/stub-%s.d: src/main.rs Cargo.toml%s%s\n\nsrc/main.rs:\n# env-dep:CLIPPY_ARGS=stub\n' \
    "$deps" "$2" "$(grep -o 'PLANT_DEPINFO:[^ ]*' "$src" | sed 's/^PLANT_DEPINFO:/ /' | tr -d '\n')" \
    "$self_dep" > "$deps/stub-$2.d"
}
err() { printf '{"reason":"compiler-message","message":{"level":"error","rendered":"error: %s"}}\n' "$1"; exit 101; }
if plant PLANT_CLIPPY_UNUSED_DEPENDENCY; then
  printf '{"reason":"compiler-message","message":{"level":"warning","code":{"code":"unused_crate_dependencies"},"rendered":"warning: unused dependency"}}\n'
fi
artifact() { printf '{"reason":"compiler-artifact","manifest_path":"%s","target":{"name":"stub"},"profile":{"test":%s,"debug_assertions":true,"overflow_checks":true}}\n' "$abs" "$1"; }
plant PLANT_FRONTEND_LINTS_NOTHING && exit 0
if [[ $capped -eq 0 ]]; then
  for lint in clippy::wildcard_enum_match_arm clippy::match_wildcard_for_single_variants \
              clippy::wildcard_in_or_patterns; do
    grep -q "PLANT_ALLOWED:$lint\$" "$src" && [[ "$forbidden" == *" $lint "* ]] \
      && err "allow($lint) incompatible with previous forbid"
  done
  plant PLANT_UNUSED_FN && [[ $deny_warnings -eq 1 ]] && err 'function `planted` is never used'
fi
running " --crate-type bin" bin0; artifact false
plant PLANT_BIN_ONLY && exit 0
plant PLANT_FRESH_TEST_UNIT || running " --test" test0
artifact true
exit 0
"""

# Refuses every file whose text holds SCAN_REFUSE, as the real one refuses what
# its rules say (their arms are the scanner crate's own tests).
_STUB_SCANNER = r"""#!/usr/bin/env bash
printf 'scanner %s\n' "$*" >> "$PWD/.stub-calls"
rc=0
for f in "$@"; do
  [[ "$f" == --forbidden ]] && { skip=1; continue; }
  [[ -n "${skip:-}" ]] && { skip=; continue; }
  grep -q SCAN_CRASH "$f" && exit 3
  grep -q SCAN_REFUSE "$f" && { echo "$f:1: planted refusal"; rc=1; }
done
exit $rc
"""

# `trustc --print=sysroot` -- the stub targo's sibling, for the typed driver's rpath.
_STUB_RUSTC = r"""#!/usr/bin/env bash
printf 'trustc %s\n' "$*" >> "$PWD/.stub-calls"
[[ "$#" == 1 && "$1" == "--print=sysroot" ]] || { echo "stub trustc: unexpected $*" >&2; exit 2; }
grep -q PLANT_NO_SYSROOT scripts/stub_crate/src/main.rs && { echo "error: no sysroot" >&2; exit 1; }
grep -q PLANT_SYSROOT_NO_LIB scripts/stub_crate/src/main.rs && { echo "$PWD/elsewhere"; exit 0; }
echo "$PWD/sysroot"
"""

_SELFTEST_CRATE = "scripts/stub_crate"
# The three [profile.dev] keys of the owner's global configuration, verbatim.
_PROFILE_CODEGEN_PLANT = ('PLANT_CONFIG_LINE:profile.dev.debug="line-tables-only" '
                          'PLANT_CONFIG_LINE:profile.dev.split-debuginfo="unpacked" '
                          'PLANT_CONFIG_LINE:profile.dev.codegen-units=16')
WILDCARD_LINTS_BY_NAME = (
    "clippy::wildcard_enum_match_arm",
    "clippy::match_wildcard_for_single_variants",
    "clippy::wildcard_in_or_patterns",
)
# (name, plant, expected-to-pass, extra environment). A plant is a marker the
# stubs read from a comment; `BUILD_RS`, `SYMLINK_DIR`, `UPPER_RS`, `ONLY_TESTED`
# and `HOME_CONFIG` shape the tree around it.
_SELFTEST_ARMS: tuple[tuple[str, str, bool, dict[str, str]], ...] = (
    ("0 CONTROL: a crate whose tests pass and whose lint is clean", "", True, {}),
    ("0b CONTROL: Cargo records and executes a modern isolated test artifact",
     "PLANT_MODERN_TEST_PATH", True, {}),
    ("0c an unrecorded executable in the legacy target directory",
     "PLANT_UNRECORDED_TEST_BIN", False, {}),
    ("0d an unrecorded executable in the modern isolated directory",
     "PLANT_MODERN_TEST_PATH PLANT_UNRECORDED_TEST_BIN", False, {}),
    ("0e a forced warning for a forbidden wildcard lint", "PLANT_FORCE_OTHER", False, {}),
    ("0f forced warnings for the warnings group", "PLANT_FORCE_WARNINGS", False, {}),
    ("0g a repeated unused-dependency tracking flag", "PLANT_FORCE_REPEATED", False, {}),
    ("0h a clippy unused-dependency warning under exit zero",
     "PLANT_CLIPPY_UNUSED_DEPENDENCY", False, {}),
    ("0i a typed-scan unused-dependency warning under exit zero",
     "PLANT_TYPES_UNUSED_DEPENDENCY", False, {}),
    ("0j CONTROL: a recorded dependency build script runs before a modern test",
     "PLANT_DEPENDENCY_BUILD_SCRIPT PLANT_MODERN_TEST_PATH", True, {}),
    ("0k an unrecorded program with a build-script name",
     "PLANT_DEPENDENCY_BUILD_SCRIPT PLANT_UNRECORDED_BUILD_SCRIPT", False, {}),
    ("0l only a recorded build script executes, with no test binary",
     "PLANT_DEPENDENCY_BUILD_SCRIPT PLANT_ONLY_BUILD_SCRIPT", False, {}),
    ("0m CONTROL: cold-cache downloads precede offline test execution",
     "PLANT_COLD_FETCH", True, {}),
    ("0n a dependency fetch failure refuses the run", "PLANT_FETCH_FAIL", False, {}),
    ("0o cold-cache preparation does not admit a test runner",
     "PLANT_COLD_FETCH PLANT_TEST_RUNNER", False, {}),
    ("1 a failing test", "PLANT_FAILING_TEST", False, {}),
    ("2 zero tests run (a filter, `--no-run`, tests cfg'd away)", "PLANT_ZERO_TESTS", False, {}),
    ("3 `targo --unverified test` exits 0 with no `test result:` line", "PLANT_NO_RESULT_LINE", False, {}),
    ("4 `test result: ok` but a non-zero exit", "PLANT_OK_BUT_EXIT_101", False, {}),
    ("5 a FAILED result line under exit 0", "PLANT_FAILED_BUT_EXIT_0", False, {}),
    ("5b a failing test whose stale, passing binary an mtime would call Fresh",
     "PLANT_STALE_PASSING_ARTIFACT", False, {}),
    # verifier r8b: FORBIDDEN_LINTS cut to its first lint passed every arm, so
    # each forbidden lint is planted by its own NAME (the list above is not
    # FORBIDDEN_LINTS, so cutting that one reddens these).
    *((f"6.{i} a catch-all the source `#[allow({lint})]`s (fails only while that lint is "
       f"forbidden on the command line)", f"PLANT_ALLOWED:{lint}", False, {})
      for i, lint in enumerate(WILDCARD_LINTS_BY_NAME)),
    ("7 an unused function (fails only under `-D warnings`)", "PLANT_UNUSED_FN", False, {}),
    ("8 a clippy frontend that exits 0 without linting anything",
     "PLANT_FRONTEND_LINTS_NOTHING", False, {}),
    ("9 clippy checked the binary but not the test target", "PLANT_BIN_ONLY", False, {}),
    # verifier r8b: an inherited RUSTFLAGS capped every lint and passed.
    ("10 an inherited RUSTFLAGS=--cap-lints=allow over an unused function",
     "PLANT_UNUSED_FN", False, {"RUSTFLAGS": "--cap-lints=allow"}),
    ("11 an inherited variable the toolchain honours and cargo never echoes caps the lint "
     "(only the environment ALLOWLIST stops it)", "PLANT_UNUSED_FN", False,
     {"CLEAN_STUB_INVISIBLE_CAP": "1"}),
    # lane r10: the runs are hermetic, so a configuration file's rustflags never
    # reach the line (CARGO_ENCODED_RUSTFLAGS replaces them) ...
    ("12 CONTROL: a configuration file's rustflags `--cap-lints allow` never reach the line",
     "PLANT_CONFIG_CAP_LINTS", True, {}),
    # ... while what a profile's rustflags or a `[lints]` table adds still does,
    # and the line is an allowlist (verifier r9 recheck: an `@argfile`).
    ("13 `-A warnings` on the crate's line", "PLANT_UNUSED_FN PLANT_LINE_ALLOW_WARNINGS",
     False, {}),
    ("13b an `@argfile` (holding `--cap-lints`) on the line",
     "PLANT_UNUSED_FN PLANT_LINE_ARGFILE", False, {}),
    ("13c `--cfg test` on the line (no lint is lowered; every `#[cfg(not(test))]` item leaves "
     "the lint)", "PLANT_LINE_CFG_TEST", False, {}),
    ("13d an `--extern` from outside this run's build dirs", "PLANT_LINE_EXTERN", False, {}),
    ("14 the test unit is Fresh: nothing was linted over this run's arguments",
     "PLANT_FRESH_TEST_UNIT", False, {}),
    ("15 a rustc wrapper stands between cargo and the clippy driver",
     "PLANT_RUSTC_WRAPPER", False, {}),
    ("16 a test runner stands between cargo and a second test binary", "PLANT_TEST_RUNNER",
     False, {}),
    ("17 `test result:` lines with no test binary executed", "PLANT_NO_EXEC_LINE", False, {}),
    ("17b a rustc wrapper stands between cargo and the test build", "PLANT_TEST_WRAPPER",
     False, {}),
    ("17c CONTROL: a configuration file's rustc-wrapper is reset by RUSTC_WRAPPER=''",
     "PLANT_CONFIG_WRAPPER", True, {}),
    ("18 a build script", "BUILD_RS", False, {}),
    # lane r10: cargo's own report of its configuration. Each refused arm says
    # NOTHING_RUNS: refused before any build or run, judged by the stubs' log
    # (2026-10-15 -- a configured runner used to launch the test binary anyway).
    ("19 a configuration file sets a key this check does not model (a profile's rustflags)",
     "PLANT_CONFIG_UNMODELED NOTHING_RUNS", False, {}),
    # 2026-09-29: the owner's global ~/.cargo/config.toml (a kernel-panic guard,
    # read through cargo's ancestor search from every checkout under the home
    # directory) sets exactly these three keys; they lower to codegen flags the
    # line allowlist admits (see _CONFIG_PROFILE). The arms after it keep every
    # other shape of `profile.*` refused, in that same file.
    ("19b CONTROL: a configuration file above the checkout sets a profile's `debug` "
     "(debuginfo on), `split-debuginfo` and `codegen-units`, and cargo writes their `-C` "
     "flags on every line", _PROFILE_CODEGEN_PLANT, True, {}),
    ("19c ... with the profile's rustflags beside them in the same file",
     f"{_PROFILE_CODEGEN_PLANT} PLANT_CONFIG_LINE:profile.dev.rustflags=[\"--cap-lints=allow\"] "
     "NOTHING_RUNS", False, {}),
    ("19d ... with the test profile's debug-assertions beside them in the same file",
     f"{_PROFILE_CODEGEN_PLANT} PLANT_CONFIG_LINE:profile.test.debug-assertions=false "
     "NOTHING_RUNS", False, {}),
    ("19e a profile's `opt-level` (`-C opt-level=3` drops `cfg(ub_checks)`)",
     "PLANT_CONFIG_LINE:profile.dev.opt-level=3 NOTHING_RUNS", False, {}),
    ("19f a profile's `debug = false` (every dependency's build script reads DEBUG=false)",
     "PLANT_CONFIG_LINE:profile.dev.debug=false NOTHING_RUNS", False, {}),
    ("19g a debuginfo key under the profile's build-override",
     "PLANT_CONFIG_LINE:profile.dev.build-override.debug=\"line-tables-only\" NOTHING_RUNS",
     False, {}),
    ("19h a codegen-units key under a package override",
     "PLANT_CONFIG_LINE:profile.dev.package.\"*\".codegen-units=16 NOTHING_RUNS", False, {}),
    ("19i a configuration file sets a test `runner` (the replay's /usr/bin/env dropped DYLD_* "
     "and the typed driver's test binary died in dyld)", "PLANT_CONFIG_RUNNER NOTHING_RUNS",
     False, {}),
    ("20 cargo cannot say which configuration it reads", "PLANT_CONFIG_UNREADABLE NOTHING_RUNS",
     False, {}),
    ("21 cargo's report has a section with no origin", "PLANT_CONFIG_NO_ORIGIN NOTHING_RUNS",
     False, {}),
    ("22 CONTROL: the caller's CARGO_HOME configuration (a `runner`) is never read",
     "HOME_CONFIG", True, {}),
    # verifier r9 recheck: each compiled source the walk-based scan never read;
    # lane r10: the scan set IS what rustc compiled, and it must be tracked.
    ("23 rustc compiled a module through a directory symlink",
     "SYMLINK_DIR PLANT_DEPINFO:src/sub/mod.rs", False, {}),
    ("24 rustc compiled `src/extra.rs`, which on disk is `src/extra.RS` (case-insensitive "
     "filesystem)", "UPPER_RS PLANT_DEPINFO:src/extra.rs", False, {}),
    ("25 rustc compiled a target path outside the crate",
     "PLANT_DEPINFO:../elsewhere/main.rs", False, {}),
    ("26 the lint run left no dep-info to tie it to its source", "PLANT_NO_DEPINFO", False, {}),
    ("26b CONTROL: a debug-assertions clippy driver records its OWN executable in the "
     "dep-info (clippy_driver `track_files`; Trust's stage2 tippy-driver, 2026-09-26)",
     "PLANT_DEPINFO_SELF", True, {}),
    ("27 the tests compiled a tracked file the lint never did",
     "ONLY_TESTED PLANT_TEST_DEPINFO:src/only_tested.rs", False, {}),
    ("28 the tests ran without the debug assertions the lint checked under",
     "PLANT_TEST_PROFILE_SPLIT", False, {}),
    ("29 the scanner refuses a compiled file", "SCAN_REFUSE", False, {}),
    ("30 the scanner crashes", "SCAN_CRASH", False, {}),
    ("31 the scanner cannot be built", "PLANT_SCANNER_UNBUILT", False, {}),
    # verifier r10: a configuration file's workspace wrapper built the real
    # scanner (a logging wrapper, measured; the check rc=0).
    ("31b a configuration file's rustc-workspace-wrapper builds the scanner",
     "PLANT_CONFIG_WSWRAPPER SCAN_REFUSE", False, {}),
    # lane r11: the typed scan (rustc_driver over THIR) replaces the syn walk's
    # hand-decided catch-all rule.
    ("34 the typed scan refuses a catch-all", "PLANT_TYPES_REFUSE", False, {}),
    ("35 the typed driver cannot be built", "PLANT_TYPES_UNBUILT", False, {}),
    ("36 the crate's units are checked through a program other than the typed driver",
     "PLANT_TYPES_OTHER_DRIVER", False, {}),
    ("37 the typed scan left the test unit Fresh: nothing was scanned in this run",
     "PLANT_TYPES_FRESH", False, {}),
    ("38 the typed driver checked a unit and printed no scan of it", "PLANT_TYPES_SILENT",
     False, {}),
    ("39 `--cfg test` on the typed scan's line", "PLANT_TYPES_LINE_CFG", False, {}),
    ("40 the tests and the lint compiled a tracked file the typed scan never read",
     "ONLY_TESTED PLANT_TEST_DEPINFO:src/only_tested.rs PLANT_DEPINFO:src/only_tested.rs",
     False, {}),
    ("41 `trustc --print=sysroot` names no sysroot for the typed driver's rpath",
     "PLANT_NO_SYSROOT", False, {}),
    ("41b `trustc --print=sysroot` names a directory with no `lib`", "PLANT_SYSROOT_NO_LIB",
     False, {}),
    # 2026-10-15: the rpath was read off the `trustc` PATH named, while targo
    # compiles with its own sibling; the two were different toolchains on this
    # box and the driver died in dyld. A decoy that fails loudly sits FIRST on
    # PATH; the control crate must still pass, so the rpath never came from it.
    ("41c a `trustc` first on PATH is never the one the typed driver's rpath is read from "
     "(control crate passes)", "DECOY_PATH_TRUSTC", True, {}),
    ("41d the targo the runs use has no sibling `trustc`: refused, never a pass",
     "TARGO_NO_SIBLING_TRUSTC", False, {}),
    # 2026-09-29: the runs took `targo` from PATH, and a rustup symlink first
    # on PATH (targo refuses to run as one) turned this leg RED on every tree
    # for one pusher and GREEN for another. A decoy that fails loudly sits
    # FIRST on PATH; the control crate must still pass, so no run reached it.
    ("43 a `targo` first on PATH is never the one the runs use (control crate passes)",
     "DECOY_PATH_TARGO", True, {}),
    ("44 TARGO names a symlink: refused before anything runs, never a pass",
     "TARGO_SYMLINK", False, {}),
)


def _selftest_non_runner_arms(work: Path) -> list[str]:
    """The arms that are not a run of the runner: orphan bookkeeping and the
    derived pin set."""
    problems = []
    # verifier r8b: a STANDALONE_GATED crate that joined [workspace] members left
    # `tracked - members`, so this check silently stopped running it.
    gated = sorted(STANDALONE_GATED)[0]
    joined = check_orphans(
        {"workspace_members": ["gated-member"],
         "packages": [{"id": "gated-member", "manifest_path": str(ROOT / gated / "Cargo.toml")}]},
        [f"{c}/Cargo.toml" for c in sorted(STANDALONE_GATED)], root=work)
    if not any("is a workspace member" in f for f in joined):
        problems.append(f"  ARM FAILED 32 a STANDALONE_GATED crate that became a workspace "
                        f"member was not reported: {joined}")
    # The pin set is DERIVED: a file added to a gated crate joins it without
    # anyone listing it, and the frontend and cargo configuration are in it.
    repo = work / "pins"
    want = {FRONTEND, RESOURCE_TRANSPORT, ".cargo/config.toml"}
    for crate in sorted(STANDALONE_GATED):
        want |= {f"{crate}/Cargo.toml", f"{crate}/src/main.rs"}
    extra = f"{gated}/src/extra.rs"
    for rel in sorted(want | {extra}):
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text("\n", encoding="utf-8")
    git = {k: v for k, v in os.environ.items() if k not in _GIT_LOCATION_VARS}
    ok = all(subprocess.run(argv, cwd=repo, env=git, capture_output=True).returncode == 0
             for argv in (["git", "init", "-q"], ["git", "add", "-A"]))
    got = pinned_inputs(repo) if ok else None
    if got != sorted(want | {extra}):
        problems.append(f"  ARM FAILED 33 the derived pin set of gated crates with an added "
                        f"file: expected {sorted(want | {extra})}, got {got}")
    return problems


def _selftest_both_scans(work: Path, stubs: Path) -> list[str]:
    """Arm 42: a typed-scan refusal does not hold back the source scan -- each
    says what it found (a catch-all written by `matches!` is both)."""
    fake = work / "arm-both-scans"
    _selftest_tree(fake, stubs, "PLANT_TYPES_REFUSE SCAN_REFUSE")
    env = _selftest_env(fake, stubs, "")
    env.pop("CARGO_TARGET_DIR", None)
    env.pop("CARGO_BUILD_BUILD_DIR", None)
    env["CARGO_HOME"] = str(work / "caller-cargo-home-empty")
    failures = " ".join(run_standalone(fake, _SELFTEST_CRATE, env))
    if "a catch-all over a gated enum" not in failures or "planted refusal" not in failures:
        return [f"  ARM FAILED 42 a typed-scan refusal and a source-scan refusal were not both "
                f"reported: {failures}"]
    return []


def _selftest_env(fake: Path, stubs: Path, plant: str) -> dict[str, str]:
    """One arm's environment: the stub tools first on PATH, and the stub targo
    named by TARGO -- the runs resolve targo through the frontend's rule, which
    never reads PATH, so the stub reaches them only this way."""
    env = dict(os.environ)
    env["PATH"] = f"{fake / 'bin'}{os.pathsep}{env.get('PATH', '')}"
    env["TARGO"] = str(stubs / "targo")
    if "DECOY_PATH_TARGO" in plant:
        decoy = fake / "decoy"
        decoy.mkdir()
        (decoy / "targo").write_text(
            "#!/usr/bin/env bash\necho 'DECOY PATH TARGO RAN' >&2\nexit 99\n", encoding="utf-8")
        (decoy / "targo").chmod(0o755)
        env["PATH"] = f"{decoy}{os.pathsep}{env['PATH']}"
    if "TARGO_SYMLINK" in plant:
        (fake / "targo-link").symlink_to(stubs / "targo")
        env["TARGO"] = str(fake / "targo-link")
    if "DECOY_PATH_TRUSTC" in plant:
        decoy = fake / "decoy-trustc"
        decoy.mkdir()
        (decoy / "trustc").write_text(
            "#!/usr/bin/env bash\necho 'DECOY PATH TRUSTC RAN' >&2\nexit 99\n", encoding="utf-8")
        (decoy / "trustc").chmod(0o755)
        env["PATH"] = f"{decoy}{os.pathsep}{env['PATH']}"
    if "TARGO_NO_SIBLING_TRUSTC" in plant:
        lonely = fake / "lonely"
        lonely.mkdir()
        shutil.copy2(stubs / "targo", lonely / "targo")
        env["TARGO"] = str(lonely / "targo")
    return env


def _selftest_tree(fake: Path, stubs: Path, plant: str) -> None:
    """One arm's stub repository: the stub crate carrying `plant`, git-tracked."""
    (fake / "scripts").mkdir(parents=True)
    (fake / "bin").symlink_to(stubs, target_is_directory=True)
    (fake / FRONTEND).symlink_to(stubs / "frontend")
    crate = fake / _SELFTEST_CRATE
    (crate / "src").mkdir(parents=True)
    (crate / "Cargo.toml").write_text('[package]\nname = "stub"\n', encoding="utf-8")
    (crate / "src" / "main.rs").write_text(f"// {plant}\nfn main() {{}}\n", encoding="utf-8")
    if plant == "BUILD_RS":
        (crate / "build.rs").write_text("fn main() {}\n", encoding="utf-8")
    # The file rustc reads behind each of these is one git does not track as it.
    if "SYMLINK_DIR" in plant:
        (fake / "elsewhere").mkdir()
        (fake / "elsewhere" / "mod.rs").write_text("\n", encoding="utf-8")
        (crate / "src" / "sub").symlink_to(fake / "elsewhere", target_is_directory=True)
    if "UPPER_RS" in plant:
        (crate / "src" / "extra.RS").write_text("\n", encoding="utf-8")
    if "../elsewhere/main.rs" in plant:
        (fake / "scripts" / "elsewhere").mkdir()
        (fake / "scripts" / "elsewhere" / "main.rs").write_text("\n", encoding="utf-8")
    if "ONLY_TESTED" in plant:
        (crate / "src" / "only_tested.rs").write_text("\n", encoding="utf-8")
    (fake / "sysroot" / "lib").mkdir(parents=True)
    (fake / ".gitignore").write_text("target/\n", encoding="utf-8")
    git = {k: v for k, v in os.environ.items() if k not in _GIT_LOCATION_VARS}
    for argv in (["git", "init", "-q"], ["git", "add", "-A"]):
        subprocess.run(argv, cwd=fake, env=git, capture_output=True, check=True)


def _selftest_arm(work: Path, stubs: Path, i: int, arm: tuple) -> str | None:
    """One arm on its own stub repository: its problem, or None."""
    name, plant, want, extra_env = arm
    fake = work / f"arm-{i}"
    _selftest_tree(fake, stubs, plant)
    env = _selftest_env(fake, stubs, plant)
    env.pop("CARGO_TARGET_DIR", None)
    env.pop("CARGO_BUILD_BUILD_DIR", None)
    env["CARGO_HOME"] = str(work / ("caller-cargo-home" if "HOME_CONFIG" in plant
                                    else "caller-cargo-home-empty"))
    env.update(extra_env)
    failures = run_standalone(fake, _SELFTEST_CRATE, env)
    if (not failures) != want:
        return (f"  ARM FAILED {name}: the runner {'FAILED' if failures else 'PASSED'} "
                f"the stub crate, expected it to {'pass' if want else 'fail'}"
                + (f" -- {failures}" if failures else ""))
    # Refused, but it must be refused for THIS reason: a later failure would
    # mean something ran through the symlink.
    if "TARGO_SYMLINK" in plant and not any("is a symlink" in f for f in failures):
        return f"  ARM FAILED {name}: refused for another reason -- {failures}"
    if "PLANT_FETCH_FAIL" in plant and not any("dependency fetch exited 101" in f for f in failures):
        return f"  ARM FAILED {name}: refused for another reason -- {failures}"
    if "TARGO_NO_SIBLING_TRUSTC" in plant and not any(
            "has no sibling `trustc`" in f for f in failures):
        return f"  ARM FAILED {name}: refused for another reason -- {failures}"
    if "NOTHING_RUNS" in plant:
        calls = (fake / ".stub-calls").read_text(encoding="utf-8").splitlines() \
            if (fake / ".stub-calls").is_file() else []
        ran = [c for c in calls if not c.startswith("targo -Zunstable-options config get")]
        if ran:
            return (f"  ARM FAILED {name}: refused, but something was built or run under the "
                    f"configuration it refused -- {ran}")
    return None


# Arms run on independent stub repositories, a few at a time: the self-test runs
# first on every invocation (twice per replayed demonstration arm), and serially
# it was more than half of a warm run (23.8 s of 44.7 s, measured 2026-10-15).
SELFTEST_WORKERS = 4


def selftest(root: Path = ROOT) -> int:
    from concurrent.futures import ThreadPoolExecutor
    work = root / "target" / f"lint-coverage-selftest-{os.getpid()}"
    problems = []
    try:
        # The stubs are written ONCE and linked into each arm: macOS evaluates a
        # newly written executable on its first exec, which cost ~0.25s per
        # stub when every arm wrote its own (measured 2026-09-25).
        stubs = work / "stubs"
        stubs.mkdir(parents=True)
        for name, text in (("targo", _STUB_CARGO), ("frontend", _STUB_FRONTEND),
                           ("scanner", _STUB_SCANNER), ("trustc", _STUB_RUSTC),
                           ("typed", "#!/usr/bin/env bash\nexit 0\n"),
                           ("scanner-lenient", "#!/usr/bin/env bash\nexit 0\n")):
            (stubs / name).write_text(text, encoding="utf-8")
            (stubs / name).chmod(0o755)
        home_with_config = work / "caller-cargo-home"
        home_with_config.mkdir()
        (home_with_config / "config.toml").write_text(
            '[target.aarch64-apple-darwin]\nrunner = "/usr/bin/env"\n', encoding="utf-8")
        with ThreadPoolExecutor(max_workers=SELFTEST_WORKERS) as pool:
            verdicts = list(pool.map(lambda ia: _selftest_arm(work, stubs, *ia),
                                     enumerate(_SELFTEST_ARMS)))
        problems += [v for v in verdicts if v]
        problems += _selftest_non_runner_arms(work)
        problems += _selftest_both_scans(work, stubs)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    for problem in problems:
        print(problem, file=sys.stderr)
    print(f"LINT_COVERAGE_SELFTEST arms={len(_SELFTEST_ARMS) + 3} failed={len(problems)}")
    return len(problems)


def main(argv: list[str]) -> int:
    unknown = [a for a in argv[1:] if a not in ("--quiet", "--selftest", "--pinned-inputs")]
    if unknown:
        print(f"lint-coverage check: unknown argument(s) {unknown}; usage: "
              f"check_lint_coverage.py [--quiet] [--selftest] [--pinned-inputs]",
              file=sys.stderr)
        return 2
    if "--pinned-inputs" in argv[1:]:
        # Read by check_gate_registry.py R7 (see THE PINNED INPUTS): no self-test,
        # no cargo -- a list, derived.
        try:
            print("\n".join(pinned_inputs(ROOT)))
        except CoverageFailure as exc:
            print(f"lint-coverage check: {exc}", file=sys.stderr)
            return 1
        return 0
    quiet = "--quiet" in argv[1:]
    if selftest():
        print("lint-coverage check FAILED: its own self-test is red", file=sys.stderr)
        return 1
    if "--selftest" in argv[1:]:
        return 0
    try:
        metadata = cargo_metadata()
        failures = check_orphans(metadata) + check_gate_sites()
    except CoverageFailure as exc:
        print(f"lint-coverage check FAILED: {exc}", file=sys.stderr)
        return 1

    if failures:
        print("lint-coverage check FAILED:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1

    if not quiet:
        print(coverage_summary(metadata))
        for crate_dir, reason in sorted(KNOWN_ORPHANS.items()):
            print(f"  known orphan (tracked, unbuilt): {crate_dir} — {reason}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
