#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Andrew Yates <andrewyates.name@gmail.com>
"""Ratchet check for the clean-Native mathverse shard's constructive-theorem set.

Ensures the set of constructive theorems (foundational-axiom-only transitive deps)
does not silently change. Drift is only accepted when
``data/constructive_ratchet.json`` is staged in the same commit.

`--update` REQUIRES `--notes`. Refreshing a ratchet without recording why the
set moved is the failure mode this gate exists to catch: a ratchet refreshed to
silence itself is not a ratchet. `do_update` used to carry the previous `notes`
string over verbatim, which is how the committed baseline came to say
"Current 84" above a count of 318 -- prose that had silently outlived three
re-baselines. The transition line is now GENERATED from the measurement, so the
recorded count can never disagree with the file it is stored in.

Usage:
    python3 scripts/check_constructive_ratchet.py          # --check (default)
    python3 scripts/check_constructive_ratchet.py --update --notes "why"
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_PATH = REPO_ROOT / "data" / "constructive_ratchet.json"
RATCHET_REL = "data/constructive_ratchet.json"
CARGO_BUILD_JOBS = os.environ.get("CARGO_BUILD_JOBS", "1")

# WHAT THE NUMBER ACTUALLY MEANS (2026-08-25, lane LOOSE). Carried in the
# baseline file and printed on every green, because "constructive" overstates
# it and the overstatement is measured, not hypothetical -- see
# `classical_choice_dependents`.
METRIC_MEANING = (
    "FOUNDATIONAL-AXIOM-ONLY theorems: kernel Theorems carrying a proof value "
    "whose transitive axiom closure contains no DOMAIN-specific axiom. This is "
    "the repo's 'prove' rule (CLAUDE.md: closure subseteq FOUNDATIONAL_AXIOMS = "
    "{propext, Quot.sound, Classical.choice, Eq builtins}), and it is WEAKER "
    "than constructive in the ordinary mathematical sense: Classical.choice is "
    "foundational here, so a theorem resting on classical choice is counted. "
    "The exact exception set is measured on every run into "
    "`classical_choice_dependents` and is part of this baseline."
)
BUILD_LOG_TAIL_LINES = int(os.environ.get("CONSTRUCTIVE_RATCHET_TAIL_LINES", "80"))


def _tail_text(path: Path, max_lines: int) -> str:
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return ""
    return "\n".join(lines[-max_lines:])


def build_native_shard() -> tuple[list[str], list[str]]:
    """Run ``mathverse_shard build-native``.

    Returns ``(accepted_names, classical_choice_dependents)`` — the accepted set
    AND, measured from the same build, the subset whose transitive FOUNDATIONAL
    closure reaches ``Classical.choice``.

    THE SECOND HALF IS THE POINT (2026-08-25, lane LOOSE). ``ProofQuality::
    Constructive`` means "transitive closure contains no DOMAIN-specific axiom",
    and ``FOUNDATIONAL_AXIOMS`` contains ``Classical.choice`` — so a theorem
    resting on classical choice is labelled Constructive by this predicate and
    counted in the number below. Lane CONSTR measured that exception set at 2 of
    396 (``Classical.em`` and ``Classical.byContradiction``, which ARE excluded
    middle) and wrote it down in ``data/constructive_ratchet_review.json``. A
    footnote in a static file does not stay true: nothing re-measured it, so the
    set could grow to 40 with the gate green. It is now a BASELINE FIELD, checked
    on every run exactly like the name set.

    The closure dump is the same one the review was adjudicated from
    (``MATHVERSE_DUMP_ACCEPTED_CLOSURE`` in
    crates/clean-mathverse/src/bin/mathverse_shard/native_build.rs), and its
    accepted set is cross-checked against the sidecar so the two cannot drift.
    """
    with tempfile.TemporaryDirectory(prefix="mathverse-ratchet-") as tmp:
        build_log = Path(tmp) / "cargo-build-native.log"
        closure_path = Path(tmp) / "accepted-closure.json"
        cmd = [
            "targo", "--unverified", "run", "--locked", "--release", "--quiet",
            "--message-format=short", "-j", CARGO_BUILD_JOBS,
            "-p", "clean-mathverse", "--bin", "mathverse_shard", "--",
            "build-native", tmp,
        ]
        env = dict(os.environ)
        env["MATHVERSE_DUMP_ACCEPTED_CLOSURE"] = str(closure_path)
        with build_log.open("w", encoding="utf-8") as log:
            result = subprocess.run(
                cmd,
                cwd=REPO_ROOT,
                check=False,
                stdout=log,
                stderr=subprocess.STDOUT,
                text=True,
                env=env,
            )
        if result.returncode != 0:
            sys.stderr.write(
                f"mathverse_shard build-native failed; log: {build_log}\n"
            )
            sys.stderr.write(
                f"Last {BUILD_LOG_TAIL_LINES} build log lines:\n"
            )
            tail = _tail_text(build_log, BUILD_LOG_TAIL_LINES)
            if tail:
                sys.stderr.write(tail + "\n")
            sys.exit(2)
        sidecar = Path(tmp) / "clean-native.mathverse.json"
        data = json.loads(sidecar.read_text())
        names = sorted(d["name"] for d in data["declarations"])
        try:
            closure = json.loads(closure_path.read_text())
        except (OSError, ValueError) as exc:  # fail closed
            sys.exit(
                "FAIL: MATHVERSE_DUMP_ACCEPTED_CLOSURE produced no readable dump "
                f"({exc}). The exception set cannot be measured, and an unmeasured "
                "exception set is not an empty one."
            )
    records = closure.get("declarations", [])
    dumped = sorted(r["name"] for r in records)
    if dumped != names:
        sys.exit(
            f"FAIL: the closure dump ({len(dumped)}) and the shard sidecar "
            f"({len(names)}) disagree about the accepted set. Refusing to "
            "adjudicate one from the other."
        )
    choice = sorted(
        r["name"]
        for r in records
        if "Classical.choice" in (r.get("foundational_axiom_closure") or [])
    )
    return names, choice


def load_ratchet() -> dict:
    if not RATCHET_PATH.exists():
        sys.stderr.write(f"Ratchet file missing: {RATCHET_PATH}\n")
        sys.exit(2)
    return json.loads(RATCHET_PATH.read_text())


def write_ratchet(names: list[str], choice: list[str], notes: str) -> None:
    payload = {
        "last_updated": dt.date.today().isoformat(),
        "metric": METRIC_MEANING,
        "count": len(names),
        "classical_choice_dependents": choice,
        "names": names,
        "notes": notes,
    }
    RATCHET_PATH.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")


def ratchet_staged_this_commit() -> bool:
    """True if the ratchet file is staged vs HEAD."""
    result = subprocess.run(
        ["git", "diff", "--cached", "--name-only", "HEAD", "--", RATCHET_REL],
        cwd=REPO_ROOT, check=False, capture_output=True, text=True,
    )
    return bool(result.stdout.strip())


def do_check() -> int:
    ratchet = load_ratchet()
    baseline = sorted(ratchet.get("names", []))
    current, choice = build_native_shard()

    # THE EXCEPTION SET IS PART OF THE BASELINE (lane LOOSE, 2026-08-25).
    # Checked before the name set, and NOT covered by the staged-file escape
    # hatch below: a name may legitimately join the accepted set in the same
    # commit that stages this file, but a theorem newly reaching
    # `Classical.choice` under a metric called "constructive" is exactly the
    # thing a reader must not learn about from a footnote. `--update --notes`
    # is the only way to move it, and that requires writing down why.
    choice_baseline = ratchet.get("classical_choice_dependents")
    if choice_baseline is None:
        sys.stderr.write(
            "RATCHET FAIL: data/constructive_ratchet.json has no "
            "`classical_choice_dependents` field. It records WHICH accepted "
            "theorems reach Classical.choice -- the measured gap between this "
            "metric's name and its predicate. An absent exception set is not an "
            "empty one; re-run with --update --notes.\n"
        )
        return 1
    if sorted(choice_baseline) != choice:
        sys.stderr.write(
            "RATCHET FAIL: the CLASSICAL-CHOICE exception set moved: "
            f"{sorted(choice_baseline)} -> {choice}.\n"
            "  These theorems are counted by a metric named 'constructive' while "
            "resting on Classical.choice (foundational in this repo, via "
            "Diaconescu for excluded middle).\n"
            "  Adjudicate the change and re-run --update --notes; do not stage "
            "it silently.\n"
        )
        return 1

    if baseline == current:
        sys.stdout.write(
            f"OK: {len(current)} foundational-axiom-only theorems match ratchet "
            f"({len(choice)} of them reach Classical.choice: "
            f"{', '.join(choice) if choice else 'none'}).\n"
        )
        return 0

    added = sorted(set(current) - set(baseline))
    removed = sorted(set(baseline) - set(current))
    if len(current) == len(baseline) and added and removed:
        sys.stderr.write(
            f"RATCHET FAIL: swap detected (count unchanged at {len(current)} "
            "but names differ).\n")
        sys.stderr.write(f"  added:   {added}\n")
        sys.stderr.write(f"  removed: {removed}\n")
        return 1

    if ratchet_staged_this_commit():
        sys.stdout.write(
            f"RATCHET UPDATE: {len(baseline)} -> {len(current)} "
            f"(+{len(added)} / -{len(removed)}). "
            "Ratchet file staged; accepting drift.\n")
        return 0

    sys.stderr.write(
        f"RATCHET FAIL: drift from {len(baseline)} -> {len(current)} "
        f"(added {len(added)}, removed {len(removed)}). "
        "Update data/constructive_ratchet.json and stage it in this commit.\n")
    if added:
        sys.stderr.write(f"  added:   {added}\n")
    if removed:
        sys.stderr.write(f"  removed: {removed}\n")
    return 1


def do_update(notes: str) -> int:
    """Rewrite the baseline, stamping the MEASURED transition into its notes.

    The caller's `notes` are appended to a generated transition line rather
    than replacing it, so the file always carries the count it was actually
    written from. Refuses an empty review.
    """
    review = (notes or "").strip()
    if not review:
        sys.stderr.write(
            "REFUSED: --update needs --notes.\n"
            "  Rewriting this baseline ACCEPTS every added theorem as reviewed.\n"
            "  Record which ones and why they are admissible, then re-run.\n"
        )
        return 2

    previous: list[str] = []
    if RATCHET_PATH.exists():
        try:
            previous = sorted(json.loads(RATCHET_PATH.read_text()).get("names", []))
        except (OSError, ValueError):
            previous = []

    current, choice = build_native_shard()
    added = sorted(set(current) - set(previous))
    removed = sorted(set(previous) - set(current))
    transition = (
        f"REFRESHED {dt.date.today().isoformat()}: "
        f"{len(previous)} -> {len(current)} "
        f"(+{len(added)} / -{len(removed)}). "
        f"MEASURED exception set: {len(choice)} of {len(current)} reach "
        f"Classical.choice ({', '.join(choice) if choice else 'none'}). "
    )
    write_ratchet(current, choice, transition + review)
    sys.stdout.write(
        f"Wrote {RATCHET_REL}: {len(previous)} -> {len(current)} "
        f"(+{len(added)} / -{len(removed)}).\n"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true",
                       help="compare current shard to ratchet (default)")
    group.add_argument("--update", action="store_true",
                       help="rewrite ratchet file from current shard "
                            "(requires --notes)")
    parser.add_argument("--notes", default="",
                        help="REQUIRED with --update: the review behind the "
                             "refresh -- which theorems moved and why each is "
                             "admissible")
    args = parser.parse_args()
    if args.update:
        return do_update(args.notes)
    return do_check()


if __name__ == "__main__":
    sys.exit(main())
