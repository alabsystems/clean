#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Every committed chain fixture still equals the digest its rebaseline recorded.

THE HOLE THIS FILLS, stated as it was found (2026-08-27, lane REV).

`crystal_fixture_freshness.py` closed the gap between the fixtures and a
LIVE trustc dump, and its module doc says exactly why that mattered: *"The gate
reads the FIXTURE. It has never read a dump."*  One level DOWN there was a
second copy of the same gap, and nothing had looked at it.

`crystal_fixture_rebaseline.py` writes, for every fixture it mints, the
sha256 and byte length of the text it wrote --- `new_sha256` / `new_bytes` in
`data/crystal_fixture_rebaseline_<...>.json`.  Measured 2026-08-27: those fields
are read by the minter itself and **by nothing else in either tree**.  No gate,
no suite row, no script.

So the arrangement was: twenty-one `*.trust-ir.txt` files pin the emitted IR that
every link-2a lane compares its spec module against; a committed record states
what those files contained when a real compiler produced them; and the two were
never compared.  Editing a fixture leaves every link-2a gate green, because every
link-2a gate reads the fixture --- the record sitting beside it in `data/`, which
would have said no, is not consulted by anything.

This script is that comparison.  Unlike `crystal_fixture_freshness.py` it needs
no compiler and no dump, so unlike that script it can be, and is, a GATE LEG that
runs on every invocation of `scripts/local_gate.sh`.

WHAT IT DECIDES, AND WHAT IT DOES NOT

It decides ONE question: are the committed fixtures byte-identical to what the
newest rebaseline recorded writing?  Three ways to fail, all RED:

  * a fixture's bytes differ from its recorded `new_sha256` / `new_bytes`;
  * a committed `*.trust-ir.txt` has no row in the record (arrived uncompared);
  * a recorded fixture is not committed (vanished).

It does NOT decide whether the fixtures still match what the compiler emits
TODAY.  Nothing here can: that needs a dump, it is
`crystal_fixture_freshness.py`, and it remains a manual duty with a
producer requirement.  A green here means "nobody has edited a fixture since the
last real measurement", never "the chains are revalidated".  Those are different
sentences and this file will not let them be confused.

The record is not named here.  It is read out of `CURRENT_REBASELINE` in
`crates/clean-verify/tests/crystal_a1_lineage/freshness.rs`, which is the same
const the Rust suite decides against, so this gate and that suite cannot come to
disagree about which record is current --- and a rename fails loudly instead of
silently checking a stale file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path
from typing import NoReturn

REPO = Path(__file__).resolve().parent.parent
FRESHNESS_RS = REPO / "crates/clean-verify/tests/crystal_a1_lineage/freshness.rs"
FIXTURE_DIR = REPO / "crates/clean-verify/tests/fixtures"
SUFFIX = ".trust-ir.txt"


def fail(message: str) -> NoReturn:
    raise SystemExit(f"CRYSTAL FIXTURE PINS: {message}")


def current_rebaseline(freshness_rs: Path) -> str:
    """Read the record path out of the suite's own const, never a second copy."""
    try:
        text = freshness_rs.read_text(encoding="utf-8")
    except OSError as exc:
        fail(f"cannot read {freshness_rs}: {exc}")
    match = re.search(
        r'const\s+CURRENT_REBASELINE\s*:\s*&str\s*=\s*"([^"]+)"\s*;', text, re.S
    )
    if not match:
        fail(
            f"{freshness_rs.relative_to(REPO) if freshness_rs.is_relative_to(REPO) else freshness_rs}"
            " no longer declares `const CURRENT_REBASELINE: &str = \"...\";` -- this gate"
            " reads that const so it cannot drift from the suite; re-point it, do not"
            " hard-code a record here"
        )
    return match.group(1)


def check(root: Path | None = None) -> list[str]:
    """Return one message per disagreement; empty means the pins hold."""
    base = root or REPO
    freshness_rs = base / "crates/clean-verify/tests/crystal_a1_lineage/freshness.rs"
    fixtures = base / "crates/clean-verify/tests/fixtures"
    rel = current_rebaseline(freshness_rs)
    record_path = base / rel
    if not record_path.is_file():
        fail(f"{rel} is named by CURRENT_REBASELINE but is not a file")
    try:
        record = json.loads(record_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"{rel} is unreadable or not JSON: {exc}")
    recorded = record.get("fixtures")
    if not isinstance(recorded, dict) or not recorded:
        fail(f"{rel} carries no `fixtures` object -- nothing to check against")

    problems: list[str] = []
    committed = {p.name[: -len(SUFFIX)] for p in fixtures.glob(f"*{SUFFIX}")}

    for stem in sorted(set(recorded) - committed):
        problems.append(
            f"{stem}{SUFFIX} is recorded by {rel} but is NOT committed -- a pinned "
            f"emitted body vanished from the tree"
        )
    for stem in sorted(committed - set(recorded)):
        problems.append(
            f"{stem}{SUFFIX} is committed but has no row in {rel} -- a fixture "
            f"arrived without ever being compared to a live dump"
        )
    for stem in sorted(set(recorded) & committed):
        entry = recorded[stem]
        expected = entry.get("new_sha256")
        expected_bytes = entry.get("new_bytes")
        if not isinstance(expected, str):
            problems.append(f"{rel} row {stem} carries no `new_sha256`")
            continue
        raw = (fixtures / f"{stem}{SUFFIX}").read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        if actual != expected:
            problems.append(
                f"{stem}{SUFFIX} DRIFTED from its pin: {actual[:16]} != recorded "
                f"{expected[:16]} ({len(raw)} bytes vs recorded {expected_bytes}). "
                f"The spec modules are compared against this text, so a theorem now "
                f"describes a body no measurement ever saw. Re-derive with a dump "
                f"(crystal_fixture_freshness.py), never by editing the pin"
            )
        elif isinstance(expected_bytes, int) and len(raw) != expected_bytes:
            problems.append(
                f"{stem}{SUFFIX} matches `new_sha256` but is {len(raw)} bytes where "
                f"{rel} records {expected_bytes} -- the record is internally inconsistent"
            )
    return problems


def selftest() -> None:
    """Four arms on a synthetic tree: prove it can say no before it says yes."""
    good = "rustcc fn @lvl.is_zero() -> bool {\n  ret [bool true]\n}\n"
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        rs = base / "crates/clean-verify/tests/crystal_a1_lineage"
        fx = base / "crates/clean-verify/tests/fixtures"
        rs.mkdir(parents=True)
        fx.mkdir(parents=True)
        (base / "data").mkdir()
        rec = base / "data/rb.json"

        def write_all(body: str, extra: dict | None = None) -> None:
            (fx / f"a{SUFFIX}").write_text(body)
            fixtures = {
                "a": {
                    "new_sha256": hashlib.sha256(good.encode()).hexdigest(),
                    "new_bytes": len(good.encode()),
                }
            }
            fixtures.update(extra or {})
            rec.write_text(json.dumps({"fixtures": fixtures}))

        (rs / "freshness.rs").write_text(
            'pub(crate) const CURRENT_REBASELINE: &str =\n    "data/rb.json";\n'
        )

        arms: list[tuple[str, bool]] = []
        write_all(good)
        arms.append(("pins hold", not check(base)))
        write_all(good.replace("true", "false"))  # one token: STRUCTURAL drift
        arms.append(("edited fixture", bool(check(base))))
        write_all(good, {"b": {"new_sha256": "0" * 64, "new_bytes": 1}})
        arms.append(("recorded but absent", bool(check(base))))
        write_all(good)
        (fx / f"c{SUFFIX}").write_text(good)
        arms.append(("committed but unrecorded", bool(check(base))))

        bad = [name for name, ok in arms if not ok]
        if bad:
            fail(f"SELFTEST FAILED -- these arms did not behave: {bad}")
        print(f"crystal fixture pins selftest: {len(arms)}/{len(arms)} arms behave")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--selftest", action="store_true", help="run the mutation arms only")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    if args.selftest:
        selftest()
        return 0

    selftest()
    problems = check()
    rel = current_rebaseline(FRESHNESS_RS)
    if problems:
        print(f"CRYSTAL FIXTURE PINS: {len(problems)} disagreement(s) with {rel}", file=sys.stderr)
        for message in problems:
            print(f"  - {message}", file=sys.stderr)
        return 1
    count = len(json.loads((REPO / rel).read_text())["fixtures"])
    if not args.quiet:
        print(
            f"OK: crystal fixture pins — {count} committed fixture(s) byte-identical to "
            f"{rel}; set matches exactly. (This is NOT a live-dump revalidation: see "
            f"crystal_fixture_freshness.py.)"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
