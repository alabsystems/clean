#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Refresh every lock the dependency-boundary gate judges -- all of them, or none.

WHY THIS EXISTS (2026-11-19)
----------------------------
A release's version commit moves the version of every crate in this workspace.
The root lock records those versions, and so does the lock of every standalone
workspace that reaches those crates by path (bench-runner, cli-runner,
realtelem-harness and telemetry-harness today). `pub bump` rewrote `Cargo.toml`
and re-resolved the root lock alone (its default, `targo update --workspace`),
so `00e83f3313` (0.9.4 -> 0.9.5) left four runner locks recording 0.9.4. From
that commit the gate's `--locked` leg was red on main, `scripts/bump_ay_pin.py`
refused, and the release train's re-pin of 2026-11-19T07:00Z rolled back; the
four were refreshed by hand in `63ff84d574`. `scripts/bump-trust-ir-pin.sh`
refreshes them inside a pin move since then, but only in the release line's
commit, which main never takes: every version commit would stale main again.

`publish/config.sh` names this script as `POST_BUMP_CMD_DEFAULT`, so `pub bump`
runs it after the version edit and commits what it rewrote: the version commit
itself is one the gate accepts.

ONE SOURCE OF TRUTH. Nothing here names a lock. The locks are the gate's own
selection (`tracked_lock_paths` and `git_pinned_lock_paths` of
scripts/check_workspace_dependency_boundary.py: every tracked `*Cargo.lock`
that records a pinned Git source, the root lock among them), each refreshed as
the `Cargo.lock` Cargo keeps beside its manifest, and the acceptance is the
gate's own leg (`check_git_pinned_locks_resolve`), run over the refreshed
tree. A workspace that starts pinning a Git source is refreshed the day the
gate starts judging its lock.

ALL OR NONE. Each lock is read before the first refresh. If a refresh fails,
if the gate's leg refuses a lock afterwards (a resolver that exits 0 without
rewriting a stale lock), or on an interrupt, every lock is put back as found.
A lock whose workspace `Cargo.lock` is not a tracked file is refused before
anything is written: a refresh would create a file no commit carries.

`targo metadata` is a non-compiling subcommand: nothing is built, and success
here is a statement about lock files only, never about the code they resolve.

  python3 scripts/refresh_judged_locks.py [--targo PATH] [--list]

Exit codes: 0 every judged lock is current (rewritten or found so),
            1 refusal or failure (every lock as found), 2 usage error.
"""
from __future__ import annotations

import argparse
import os
import shutil
import signal
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

try:
    import check_workspace_dependency_boundary as boundary  # noqa: E402
except (ImportError, SyntaxError) as error:
    # `pub bump` runs this as `python3`: say which interpreter could not load
    # the gate (it parses TOML with tomllib, Python 3.11+) instead of a traceback.
    sys.exit(f"REFUSED: {sys.executable} cannot import the dependency-boundary gate ({error}); "
             "run this with a Python 3.11+ interpreter. Nothing was written.")

ROOT = boundary.ROOT


class Refusal(Exception):
    """Nothing may be claimed; the working tree is, or is put back, as found."""


def tracked_lock_texts() -> dict[str, str]:
    """Every tracked `*Cargo.lock`, as the gate reads them for its selection."""
    return {str(path.relative_to(ROOT)): path.read_text() for path in boundary.tracked_lock_paths()}


def lock_legs(texts: dict[str, str]) -> list[str]:
    """The locks to refresh: for each lock the gate selects, the `Cargo.lock`
    beside its manifest, which is the file the gate's `--manifest-path` question
    is about and the one a refresh writes. Each must be tracked (`texts` holds
    every tracked `*Cargo.lock`): for a selected lock kept under another name, a
    refresh would create an untracked `Cargo.lock`, the gate would accept it,
    and the tracked lock would stay as it was."""
    judged = boundary.git_pinned_lock_paths(texts)
    if not judged:
        raise Refusal("no tracked lock records a pinned Git source: the gate judges none")
    legs = set()
    for relative in judged:
        leg = str(Path(relative).with_name("Cargo.lock"))
        if leg not in texts:
            raise Refusal(
                f"{leg} is not a tracked file (the lock Cargo keeps for tracked {relative}): "
                "a refresh would write it and no commit would carry it")
        legs.add(leg)
    return sorted(legs)


def frontend(explicit: str | None) -> str:
    """`--targo`, then `$CLEAN_TARGO`, then `targo` on PATH -- the pin
    transaction's order (scripts/bump-trust-ir-pin.sh). Never stock cargo."""
    chosen = explicit or os.environ.get("CLEAN_TARGO") or shutil.which("targo")
    if not chosen:
        raise Refusal("no Targo frontend: pass --targo, set CLEAN_TARGO, or put targo on PATH")
    if not (Path(chosen).is_file() and os.access(chosen, os.X_OK)):
        raise Refusal(f"Targo frontend is not executable: {chosen}")
    return chosen


def refresh(targo: str, legs: list[str]) -> None:
    """Each lock, offline first: a version edit adds no dependency, so the local
    cache decides it and the network is not this step's to need. A lock the
    cache cannot decide is asked again with the network allowed (the order of
    the gate's own leg, and of `pub bump`'s default); that answer is the result."""
    for leg in legs:
        manifest = str(Path(leg).with_name("Cargo.toml"))
        command = [targo, "metadata", "--format-version", "1", "--manifest-path", manifest]
        try:
            fds = boundary.resource_fds(os.environ)
            result = subprocess.run(
                [*command, "--offline"], cwd=ROOT, stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, check=False, pass_fds=fds)
            if result.returncode:
                reason = (result.stderr.strip().splitlines() or ["no reason given"])[-1]
                print(f"{leg}: not refreshed offline ({reason}); asking with the network allowed",
                      file=sys.stderr, flush=True)
                result = subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                        stdout=subprocess.DEVNULL, check=False, pass_fds=fds)
        except (OSError, RuntimeError) as error:
            raise Refusal(f"{leg} refresh could not run: {error}") from error
        if result.returncode:
            raise Refusal(f"{leg} refresh failed (targo metadata exited {result.returncode})")


def accept(targo: str) -> None:
    """The gate's own `--locked` leg over the refreshed tree, selection included."""
    try:
        boundary.check_git_pinned_locks_resolve(tracked_lock_texts(), targo)
    except (boundary.BoundaryViolation, OSError, ValueError, RuntimeError,
            subprocess.CalledProcessError) as error:
        raise Refusal(str(error)) from error


def restore(before: dict[str, bytes]) -> list[str]:
    """Put every lock back as found; the legs that could not be, with the reason."""
    failed = []
    for leg, found in before.items():
        path = ROOT / leg
        try:
            if not path.is_file() or path.read_bytes() != found:
                path.write_bytes(found)
        except OSError as error:
            failed.append(f"{leg}: {error}")
    return failed


def interrupted(signum: int, _frame: object) -> None:
    # SystemExit unwinds through main's handler, which restores the locks.
    sys.exit(128 + signum)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    parser.add_argument("--targo", help="the Targo frontend; default $CLEAN_TARGO, then targo on PATH")
    parser.add_argument("--list", action="store_true",
                        help="print the locks that would be refreshed, one per line, and change nothing")
    args = parser.parse_args(argv)
    try:
        legs = lock_legs(tracked_lock_texts())
        if args.list:
            print("\n".join(legs))
            return 0
        targo = frontend(args.targo)
        before = {leg: (ROOT / leg).read_bytes() for leg in legs}
    except (Refusal, boundary.BoundaryViolation, OSError, ValueError,
            subprocess.CalledProcessError) as error:
        print(f"REFUSED: {error}\nNothing was written.", file=sys.stderr)
        return 1
    print(f"lock refresh frontend: {targo}")
    print(f"judged locks: {' '.join(legs)}", flush=True)
    signal.signal(signal.SIGTERM, interrupted)
    try:
        refresh(targo, legs)
        accept(targo)
    except BaseException as error:
        failed = restore(before)
        if failed:
            print("RESTORE INCOMPLETE -- the working tree is NOT guaranteed unchanged:\n  "
                  + "\n  ".join(failed), file=sys.stderr)
        else:
            print("RESTORED -- every lock is as it was found.", file=sys.stderr)
        if isinstance(error, Refusal):
            print(f"FAIL: {error}", file=sys.stderr)
            return 1
        raise
    for leg in legs:
        unchanged = (ROOT / leg).read_bytes() == before[leg]
        print(f"refreshed {leg}{' (unchanged)' if unchanged else ''}")
    print("every judged lock accepted under --locked by the dependency-boundary gate's leg")
    return 0


if __name__ == "__main__":
    sys.exit(main())
