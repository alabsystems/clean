#!/usr/bin/env python3
"""The A0 census's OUTPUT pin (audit r11 M11-4).

WHY THIS EXISTS. `check_census_arms.py` pins the census's REFUSALS: for each
guard, deleting it must redden the selftest. That is necessary and it is not
sufficient, because a verdict is not only its guards — it is also how they are
COMPOSED. Measured at r11: dropping `and bodyful(fid)[0]` from the criteria
dict in `crystal_a0_census.py` left `--selftest` at 34/34 arms, left
`check_census_arms.py` reporting every refusal site mutated or accounted, and
left every gate green. Only R7 FRESH fired — and its own printed remedy is to
re-pin, which replays the MUTATED file's selftest, which passes. Two further
axes fell the same way: a refusal written `if cond: return False` on one line
hides from the site enumerator, and `UNLISTED_OK`'s substring keys can absorb a
genuinely new refusal whose context happens to contain an accounted idiom.

An output pin closes all three at once, because it does not care what shape the
change takes: run the census on a committed synthetic dump and compare its
verdict surface to a committed expectation. Anything that moves a result on
these five functions fails.

WHAT IS PINNED, and what is not: the `criteria` list, the `totals` block, the
`semantic_only_bodies` list and `a0_complete_bodies`. NOT the provenance block
— it carries absolute paths and input digests that differ per checkout, and
pinning those would make this a path test rather than a verdict test.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

FIXTURE = Path("tests/fixtures/crystal_a0_census")
CENSUS = Path("scripts/crystal_a0_census.py")
PINNED = ("criteria", "totals", "semantic_only_bodies", "a0_complete_bodies")


def run_census(census: Path, fixture: Path, out: Path) -> tuple[int, str]:
    # M2 (2026-09-27): the census imports its first-party siblings (the shared
    # trust-ir symbol reader) from its own directory. A COPY of it in a temp dir
    # has none there, so the real census's directory follows it on the path: the
    # copy runs the modules the census runs, and a mutant of the census alone
    # still differs from it only by its mutation.
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(
        [str(CENSUS.resolve().parent)] + ([env["PYTHONPATH"]] if env.get("PYTHONPATH") else []))
    r = subprocess.run(
        [sys.executable, str(census), str(fixture / "dump"),
         str(fixture / "flips_O3.txt"), str(fixture / "flips_O0.txt"), str(out),
         f"discharge={fixture / 'discharge.json'}"],
        capture_output=True, text=True, env=env)
    return r.returncode, r.stdout + r.stderr


def compare(census: Path = CENSUS, fixture: Path = FIXTURE) -> list[str]:
    expected = json.loads((fixture / "expected.json").read_text())
    with tempfile.TemporaryDirectory() as d:
        out = Path(d) / "measured.json"
        rc, log = run_census(census, fixture, out)
        if rc != 0 or not out.exists():
            return [f"the census refused the committed fixture (rc={rc}); it must run "
                    f"clean on it, so a refusal here is a defect in the census or the "
                    f"fixture, never an expected state:\n{log.strip()[:600]}"]
        measured = json.loads(out.read_text())
    bad = []
    for key in PINNED:
        if measured.get(key) != expected.get(key):
            bad.append(
                f"{key} moved.\n  expected: {json.dumps(expected.get(key), sort_keys=True)[:300]}"
                f"\n  measured: {json.dumps(measured.get(key), sort_keys=True)[:300]}")
    return bad


def selftest() -> None:
    """Every refusal demonstrated on every invocation.

    The arms mutate a COPY of the census: one changes a guard, one changes the
    COMPOSITION (the axis that has no other pin), one leaves it alone.
    """
    ok = True
    src = CENSUS.read_text()
    with tempfile.TemporaryDirectory() as d:
        good = Path(d) / "good.py"
        good.write_text(src)
        if compare(census=good):
            print("  [RED] output-pin arm control: the unmutated census does not "
                  "reproduce the committed expectation")
            ok = False
        # AUDIT r12 M12-2: one arm per CRITERION, plus the composition, the
        # guard, and the escape-set cardinality. The old arm set watched one
        # cell of six; five constant-true cells meant a `-> True` mutation of
        # any of them reproduced the pinned output exactly.
        for tag, old, new in (
            ("composition", "and bodyful(fid)[0])", "and True)"),
            ("guard", "    if indirect:\n        return False\n",
                      "    if indirect:\n        pass\n"),
            ("criterion-lowered", '"lowered": bool(b.get("lowered")),',
                                  '"lowered": True,'),
            ("criterion-spliced", '"spliced": bool(b.get("spliced")),',
                                  '"spliced": True,'),
            ("criterion-unsupported", '"zero_unsupported": b.get("unsupported") == [],',
                                      '"zero_unsupported": True,'),
            ("criterion-derived-agreed", '"derived_agreed": dm.get("verdict") == "agreed",',
                                         '"derived_agreed": True,'),
            ("criterion-flip-O3", '"flip_event_O3": b["def_index"] in cod3,',
                                  '"flip_event_O3": True,'),
            ("escape-set-cardinality", "for e in sorted(escapes):",
                                       "for e in sorted(escapes)[:1]:"),
        ):
            if src.count(old) != 1:
                print(f"  [RED] output-pin arm {tag}: its anchor no longer matches "
                      f"exactly once ({src.count(old)}) -- the census moved; update this arm")
                ok = False
                continue
            m = Path(d) / f"mutant_{tag}.py"
            m.write_text(src.replace(old, new))
            if not compare(census=m):
                print(f"  [RED] output-pin arm {tag}: the mutant reproduced the pinned "
                      f"output, so this pin does not watch that change")
                ok = False
    # AUDIT r13 M13-7: ADEQUACY. More arms cannot keep up with a growing
    # criteria set -- five pinned cells were constant-valued after r12 added one
    # arm per criterion. Assert the property instead: every pinned per-body
    # boolean must take BOTH values across the fixture, so a cell that stops
    # discriminating fails here rather than silently going unwatched.
    try:
        measured = json.loads((FIXTURE / "expected.json").read_text())
    except (OSError, ValueError) as exc:
        print(f"  [RED] output-pin arm adequacy: cannot read the expectation: {exc}")
        ok = False
        measured = {}
    # `criteria` is a list of NAMES; the per-body booleans live in
    # a0_complete_bodies. Keying on the wrong one made this assertion vacuous
    # when first written -- the same shape it exists to forbid.
    cells = measured.get("a0_complete_bodies") or []
    if not (isinstance(cells, list) and len(cells) >= 2 and isinstance(cells[0], dict)):
        print("  [RED] output-pin arm adequacy: a0_complete_bodies must carry at least two "
              "bodies for any per-body cell to discriminate")
        ok = False
    else:
        names = {k for c in cells for k, v in c.items() if isinstance(v, bool)}
        if not names:
            print("  [RED] output-pin arm adequacy: no per-body booleans found to check")
            ok = False
        for nm in sorted(names):
            vals = {c.get(nm) for c in cells if nm in c}
            if len(vals) < 2:
                print(f"  [RED] output-pin arm adequacy: pinned cell {nm!r} takes only "
                      f"{vals} across the fixture, so a mutation of it cannot be seen")
                ok = False

    # AUDIT r16 M16-2: a fixture value the PRODUCER CANNOT EMIT is not evidence.
    # `markers_vacuous` discriminated on `md.startswith("0 marker line(s)")`, and
    # the only fixture body carrying a zero-marker detail said exactly
    # `"0 marker line(s)"` -- a string that occurs in this repo in ONE file, this
    # fixture, and nowhere in the producer's image. The consequence was that the
    # pin had the axis BACKWARDS: it FAILED the correct tightening
    # (`== "0 marker line(s) identical"`, the producer's real output) and PASSED
    # the wrong one, whose live effect is `a0_complete_with_nonvacuous_markers`
    # 36 -> 189 -- the degenerate "the channel extracts nothing from anything"
    # world that crystal_a1_lineage/markers_channel.rs exists to rule out, and a
    # direction-"up" ratchet row that would accept the inflation as a new floor.
    #
    # The general rule, not the instance: every `markers_detail` in any pin
    # fixture must lie in the producer's image, which is the seven assignment
    # sites of trust's mir_differential.rs.
    _PRODUCER_IMAGE = re.compile(
        r"^(?:\d+ marker line\(s\) identical|markers differ:.*|"
        r"marker channel\((?:built|derived)\):.*|not compared|identical|)$",
        re.S,
    )
    try:
        _dump = json.loads((FIXTURE / "dump" / "clean_kernel.coverage.json").read_text())
    except (OSError, ValueError) as exc:
        print(f"  [RED] output-pin arm producer-image: cannot read the dump: {exc}")
        ok = False
        _dump = {}
    _outside = []
    def _walk(node):
        if isinstance(node, dict):
            for k, v in node.items():
                if k == "markers_detail" and isinstance(v, str) \
                        and not _PRODUCER_IMAGE.match(v):
                    _outside.append(v)
                else:
                    _walk(v)
        elif isinstance(node, list):
            for v in node:
                _walk(v)
    _walk(_dump)
    if _outside:
        print(f"  [RED] output-pin arm producer-image: fixture `markers_detail` values "
              f"outside the producer's image: {_outside!r} -- a value no producer can "
              f"emit cannot discriminate anything the producer does")
        ok = False

    # audit r12 M12-2: the PINNED set itself was undefended -- reducing it to
    # ("totals",) left the selftest reporting 3/3 and rc=0 while two surfaces
    # stopped being compared.
    if set(PINNED) != {"criteria", "totals", "semantic_only_bodies", "a0_complete_bodies"}:
        print("  [RED] output-pin arm pinned-set: PINNED was narrowed; the surfaces this "
              "gate claims to compare are not the ones it compares")
        ok = False
    if not ok:
        raise SystemExit("check_census_output_pin selftest: arms misbehave")
    print(f"check_census_output_pin selftest: {2 + 8 + 1}/{2 + 8 + 1} arms behave")


def main(argv: list[str]) -> int:
    if len(argv) > 1 and argv[1] == "--selftest":
        selftest()
        return 0
    selftest()
    bad = compare()
    if bad:
        print("CENSUS OUTPUT PIN: FAIL — the census's verdict moved on the committed "
              "fixture:", file=sys.stderr)
        for b in bad:
            print(f"  {b}", file=sys.stderr)
        print("  If the new verdict is CORRECT, re-mint tests/fixtures/crystal_a0_census/"
              "expected.json in the same change and say in the commit what moved and why. "
              "A verdict change that nobody had to explain is what this pin exists to "
              "prevent.", file=sys.stderr)
        return 1
    print("CENSUS_OUTPUT_PIN=ok fixture=tests/fixtures/crystal_a0_census "
          f"pinned={len(PINNED)} surfaces")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
