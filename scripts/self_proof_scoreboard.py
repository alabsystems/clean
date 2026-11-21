#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The kernel self-proof scoreboard (unit W0 of the self-proof execution plan).

WHY. On 2026-11-15 no verdict that `clean` or Trust issues was decided by
proved code, and nothing printed that fact in one place. Section 0 of
`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md` makes two figures lead
every report on the route:

  * the sites that mint a planted proof of `False` under a patched kernel
    (target 0), and
  * the real declarations whose accepted row was decided by the compiled
    `kcheck` (0 until an artifact says otherwise).

This script derives those and the route's other dated figures from the
artifacts that mint them, and writes `data/self_proof_scoreboard.json`. It
measures nothing itself and it types no figure: a figure whose artifact is
absent is reported as absent, with the reason, never as a number.

It is registered as `self_proof_scoreboard` in data/gate_registry.json and run by
the full local gate's `self-proof-scoreboard` leg, which refuses a committed
record that differs from a re-derivation.

  python3 scripts/self_proof_scoreboard.py              # print the board
  python3 scripts/self_proof_scoreboard.py --write      # re-mint the record
  python3 scripts/self_proof_scoreboard.py --check      # the record matches a re-derivation
  python3 scripts/self_proof_scoreboard.py --self-test
  python3 scripts/self_proof_scoreboard.py --pinned-inputs   # the scripts this one runs (gate registry, R7)
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from functools import partial
from pathlib import Path

ANSWERS_PINNED_INPUTS = True

CODE_ROOT = Path(__file__).resolve().parent.parent
ROOT = CODE_ROOT
RECORD = ROOT / "data" / "self_proof_scoreboard.json"

P3_CLEAN = "reports/self-proof-p3-2026-11-12/patched_kernel_control.json"
P3_TRUST = "reports/self-proof-p3-2026-11-12/patched_kernel_control_trust.json"
ELAB = "reports/self-proof-elab/baseline.json"
RULES = "data/cic_l_rule_inventory.json"
ISLAND_GAPS = "data/kcheck_island_gaps.json"
# Minted by scripts/kcheck_coverage.py (interim thread, step K3). Until it exists,
# and whenever its second reader refuses it or its sources have moved, the two
# figures read from it are absent with the reason, never a number.
COVERAGE = "data/kcheck_coverage.json"
COVERAGE_SCRIPT = "scripts/kcheck_coverage.py"
CHECKER_SOURCES = "theories/kcheck_labelled"
SELFTEST_SCRIPT = "scripts/self_proof_scoreboard_selftest.py"


class Absent(Exception):
    """An artifact a figure is read from is missing or has another shape."""


def load(rel: str, root: Path | None = None) -> dict:
    path = (ROOT if root is None else root) / rel
    if not path.is_file():
        raise Absent(f"{rel} does not exist")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as err:
        raise Absent(f"{rel} is not JSON: {err}") from err
    if not isinstance(value, dict):
        raise Absent(f"{rel} is not a JSON object")
    return value


def field(obj: dict, key: str, rel: str):
    if key not in obj:
        raise Absent(f"{rel} has no `{key}`")
    return obj[key]


def blank_noncode_lean(text: str) -> str:
    """Blank Lean comments and string literals, keeping every newline.

    A scan of raw source counts the prose that states a claim, so the headline
    search below runs on this instead. `--` runs to the end of the line; block
    comments `/- ... -/` nest; a string ends at an unescaped quote.
    """
    out = []
    i, n, depth = 0, len(text), 0
    in_string = False
    while i < n:
        two = text[i : i + 2]
        ch = text[i]
        if depth:
            if two in ("/-", "-/"):
                depth += 1 if two == "/-" else -1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif in_string:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            else:
                in_string = ch != '"'
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            in_string = ch == '"'
            out.append(" " if in_string else ch)
            i += 1
    return "".join(out)


# A theorem whose stated type is exactly `C3Owes` applied to the adopted
# checker: the type must end at `checker`, so `C3Owes checker → False` and
# `C3Owes checker ∧ P` are not counted.
HEADLINE = re.compile(
    r"\btheorem\s+(?P<name>[^\s:({\[]+)\s*:\s*"
    r"(?:KCheckSpec\.)?C3Owes(?:\.\{[^}]*\})?\s+(?:KCheck\.)?checker\s*:="
)
# An `include` command can bring a section hypothesis into every later
# theorem, so a headline in such a file may rest on an assumption its
# statement does not show. Such a file is refused, not read.
INCLUDE = re.compile(r"(?m)^\s*include\b")


def headline_theorems(source: str) -> list[str]:
    code = blank_noncode_lean(source)
    if INCLUDE.search(code):
        raise Absent("a checker source uses `include`, so a headline may rest on a hidden hypothesis")
    return [m.group("name") for m in HEADLINE.finditer(code)]


def figure(read, *args):
    """Run one reader; an absent artifact becomes a stated absence."""
    try:
        return read(*args)
    except Absent as err:
        return {"absent": str(err).encode("utf-8", "backslashreplace").decode("utf-8")}


def planted_false_clean(root: Path | None = None) -> dict:
    record = load(P3_CLEAN, root)
    summary = field(record, "summary", P3_CLEAN)
    return {
        "sites": field(summary, "sites", P3_CLEAN),
        "minted_under_mutant": field(summary, "minted_under_mutant", P3_CLEAN),
        "measured_commit": field(record, "measured_commit", P3_CLEAN),
        "source": P3_CLEAN,
    }


def planted_false_trust(root: Path | None = None) -> dict:
    return trust_pins_figure(load(P3_TRUST, root))


def trust_pins_figure(record: dict) -> dict:
    """The Trust leg's figure from its record: site rows grouped by test, each site counted once."""
    by_test = field(record, "pins", P3_TRUST)
    if not isinstance(by_test, dict) or not all(isinstance(rows, list) for rows in by_test.values()):
        raise Absent(f"{P3_TRUST}'s `pins` is not a map from test to a list of site rows")
    pins = [row for rows in by_test.values() for row in rows]
    if not all(isinstance(p, dict) and isinstance(p.get("site"), str) and p.get("mutant") in ("Minted", "Refused")
               for p in pins):
        raise Absent(f"{P3_TRUST} has a site row without a site name or a Minted/Refused mutant verdict")
    if len({p["site"] for p in pins}) != len(pins):
        raise Absent(f"{P3_TRUST} names a site twice across its tests; a site is counted once")
    minted = [p for p in pins if p["mutant"] == "Minted"]
    return {
        "sites": len(pins),
        "minted_under_mutant": len(minted),
        "measured_at": field(record, "measured_at", P3_TRUST),
        "source": P3_TRUST,
    }


def script_module(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def selftest_module():
    return script_module(CODE_ROOT / SELFTEST_SCRIPT)


def coverage_module():
    """Load the coverage reader from this script's checkout."""
    path = CODE_ROOT / COVERAGE_SCRIPT
    if not path.is_file():
        raise Absent(f"{COVERAGE_SCRIPT} does not exist")
    try:
        return script_module(path)
    except Exception as err:  # noqa: BLE001 - whatever stops the reader, the figure is absent, never a number
        raise Absent(f"{COVERAGE_SCRIPT} does not load ({type(err).__name__})") from err


def checked_coverage(module=None, *, root: Path | None = None) -> dict:
    """The coverage record, as its --check accepts it. A stale record is reported by its `reason`, one of two
    fixed texts, so that this board does not change each time another source file of the run moves."""
    module = module or coverage_module()
    try:
        return module.check() if root is None else module.check(root)
    except module.Stale as err:
        raise Absent(f"stale or absent: {err.reason}") from err
    except module.Refused as err:
        raise Absent(f"refused by {COVERAGE_SCRIPT}: {err}") from err
    except Exception as err:  # noqa: BLE001 - a crash of the reader is no figure either
        raise Absent(f"{COVERAGE_SCRIPT} crashed ({type(err).__name__})") from err


def decided_by_kcheck(coverage=checked_coverage) -> dict:
    record = coverage()
    return {
        "real_declarations_decided": field(record, "real_declarations_decided", COVERAGE),
        "reason": field(record, "real_declarations_decided_reason", COVERAGE),
        "source": COVERAGE,
    }


def accepted_by_kcheck(coverage=checked_coverage) -> dict:
    """Real declarations the checker accepted in a run no site consults."""
    record = coverage()
    figures = field(record, "figures", COVERAGE)
    return {
        "accepted": field(figures, "accepted", COVERAGE),
        "inside_fragment": field(figures, "inside_fragment", COVERAGE),
        "ordinary_declarations": field(figures, "ordinary_declarations", COVERAGE),
        "export": field(field(record, "export", COVERAGE), "path", COVERAGE),
        "labels": field(record, "labels", COVERAGE),
        "source": COVERAGE,
    }


def clean_elaborates(root: Path | None = None) -> dict:
    record = load(ELAB, root)
    modules = field(record, "modules", ELAB)
    by_package: dict[str, dict[str, int]] = {}
    for module in modules:
        row = by_package.setdefault(module["package"], {"elaborated": 0, "modules": 0})
        row["modules"] += 1
        if module["status"] == "elaborated":
            row["elaborated"] += 1
    return {
        "modules": len(modules),
        "elaborated": sum(row["elaborated"] for row in by_package.values()),
        "by_package": dict(sorted(by_package.items())),
        "producer_commit": field(record, "commit", ELAB),
        "source": ELAB,
    }


def rule_families(root: Path | None = None) -> dict:
    rows = [r for r in field(load(RULES, root), "rows", RULES) if r.get("kind") == "rule"]
    count = {"specified": 0, "partial": 0, "unspecified": 0}
    for row in rows:
        status = row.get("status")
        if status not in count:
            raise Absent(f"{RULES} has a rule row with status {status!r}")
        count[status] += 1
    return {"families": len(rows), **count, "source": RULES}


def checker_soundness(root: Path | None = None) -> dict:
    root = ROOT if root is None else root
    sources = root / CHECKER_SOURCES
    if not sources.is_dir():
        raise Absent(f"{CHECKER_SOURCES} does not exist")
    found = []
    for path in sorted(sources.rglob("*.lean")):
        relative = path.relative_to(root)
        if ".lake" in relative.parts:
            continue
        for name in headline_theorems(path.read_text(encoding="utf-8")):
            found.append({"theorem": name, "file": str(relative)})
    return {
        "headline_theorems_in_source": found,
        "reading": (
            "a theorem of type `KCheckSpec.C3Owes KCheck.checker` stated in source; "
            "it counts only when two kernels have re-checked it (plan section 4)"
        ),
        "source": CHECKER_SOURCES,
    }


def island_gaps(root: Path | None = None) -> dict:
    gaps = field(load(ISLAND_GAPS, root), "gaps", ISLAND_GAPS)
    # The plan's exit for W2: every row is closed or pinned by name.
    count = {"open": 0, "closed": 0, "pinned": 0}
    for gap in gaps:
        status = gap.get("status")
        if status not in count:
            raise Absent(f"{ISLAND_GAPS} has a gap row with status {status!r}")
        count[status] += 1
    return {"rows": len(gaps), "open": count["open"], "source": ISLAND_GAPS}


def derive(root: Path | None = None) -> dict:
    root = ROOT if root is None else root
    coverage = partial(checked_coverage, root=root)
    return {
        "schema": "clean.self_proof_scoreboard.v1",
        "what_this_is": (
            "Unit W0 of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md: the route's "
            "headline figures, each read from the artifact that mints it by "
            "scripts/self_proof_scoreboard.py. Every figure is as old as its source; "
            "this file measures nothing."
        ),
        "headline": {
            "planted_false_mints_clean": figure(planted_false_clean, root),
            "planted_false_mints_trust": figure(planted_false_trust, root),
            "decided_by_compiled_kcheck": figure(decided_by_kcheck, coverage),
        },
        "route": {
            "accepted_by_kcheck_no_site": figure(accepted_by_kcheck, coverage),
            "checker_soundness": figure(checker_soundness, root),
            "clean_elaborates_theories": figure(clean_elaborates, root),
            "island_gaps": figure(island_gaps, root),
            "lean_kernel_rule_families": figure(rule_families, root),
        },
    }


def render(board: dict) -> str:
    def show(value: dict, text) -> str:
        return f"ABSENT ({value['absent']})" if "absent" in value else text(value)

    head, route = board["headline"], board["route"]
    lines = [
        "SELF-PROOF SCOREBOARD (every figure is as old as its source)",
        "  planted False minted, Clean : "
        + show(head["planted_false_mints_clean"], lambda v: f"{v['minted_under_mutant']} of {v['sites']} sites"),
        "  planted False minted, Trust : "
        + show(head["planted_false_mints_trust"], lambda v: f"{v['minted_under_mutant']} of {v['sites']} sites"),
        "  decided by compiled kcheck  : "
        + show(head["decided_by_compiled_kcheck"], lambda v: f"{v['real_declarations_decided']} real declarations"),
        "  accepted by kcheck, no site : "
        + show(
            route["accepted_by_kcheck_no_site"],
            lambda v: f"{v['accepted']} of {v['inside_fragment']} in the fragment, of {v['ordinary_declarations']} real declarations"
            " (the run claims no soundness; built by upstream Lean; interim loader)",
        ),
        "  checker soundness headline  : "
        + show(
            route["checker_soundness"],
            lambda v: f"{len(v['headline_theorems_in_source'])} theorem(s) of type C3Owes KCheck.checker in source",
        ),
        "  Clean elaborates theories   : "
        + show(route["clean_elaborates_theories"], lambda v: f"{v['elaborated']} of {v['modules']} modules"),
        "  island gaps open            : "
        + show(route["island_gaps"], lambda v: f"{v['open']} of {v['rows']} rows"),
        "  Lean kernel rule families   : "
        + show(
            route["lean_kernel_rule_families"],
            lambda v: f"{v['specified']} of {v['families']} specified ({v['partial']} partial, {v['unspecified']} unspecified)",
        ),
    ]
    return "\n".join(lines)


def serialize(board: dict) -> str:
    return json.dumps(board, indent=2, sort_keys=True) + "\n"


def record_refusal(recorded: str | None, board: dict) -> str | None:
    """Why the committed record is refused, or None when it matches a re-derivation."""
    if recorded is None:
        return f"{RECORD.relative_to(ROOT)} does not exist"
    if recorded != serialize(board):
        return "the record differs from a re-derivation; run scripts/self_proof_scoreboard.py --write"
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true", help="re-mint the record")
    group.add_argument("--check", action="store_true", help="the record matches a re-derivation")
    group.add_argument("--self-test", action="store_true")
    group.add_argument("--pinned-inputs", action="store_true", help="the scripts this one runs, one path a line")
    args = parser.parse_args()

    if args.self_test:
        return selftest_module().self_test(sys.modules[__name__])
    if args.pinned_inputs:
        print(SELFTEST_SCRIPT)
        print(COVERAGE_SCRIPT)
        for line in coverage_module().pinned_inputs():
            print(line)
        return 0

    board = derive()
    if args.write:
        RECORD.write_text(serialize(board), encoding="utf-8")
        print(render(board))
        print(f"wrote {RECORD.relative_to(ROOT)}")
        return 0
    if args.check:
        recorded = RECORD.read_text(encoding="utf-8") if RECORD.is_file() else None
        refusal = record_refusal(recorded, board)
        if refusal is not None:
            print(f"SELF_PROOF_SCOREBOARD=stale {refusal}", file=sys.stderr)
            return 1
        print("SELF_PROOF_SCOREBOARD=ok the record matches its sources")
        return 0
    print(render(board))
    return 0


if __name__ == "__main__":
    sys.exit(main())
