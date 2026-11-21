#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The arms of `scripts/self_proof_scoreboard.py --self-test`, kept apart so each file stays short.

Run through the scoreboard (`python3 scripts/self_proof_scoreboard.py --self-test`),
which hands this module itself as `sb`.
"""

from __future__ import annotations

import sys


def self_test(sb) -> int:
    failures = []
    arms = []

    def expect(label: str, got, want) -> None:
        arms.append(label)
        if got != want:
            failures.append(f"{label}: got {got!r}, want {want!r}")

    stated = "theorem c3 : KCheckSpec.C3Owes KCheck.checker := by\n  exact proof\n"
    expect("a stated headline is found", sb.headline_theorems(stated), ["c3"])
    expect(
        "a universe-instantiated headline is found",
        sb.headline_theorems("theorem c3' : C3Owes.{u} checker := sorry_free\n"),
        ["c3'"],
    )
    expect(
        "a line comment that states the claim is not a theorem",
        sb.headline_theorems("-- theorem c3 : KCheckSpec.C3Owes KCheck.checker\n"),
        [],
    )
    expect(
        "a nested block comment is blanked whole",
        sb.headline_theorems("/- outer /- theorem c3 : C3Owes checker -/ still comment -/\n"),
        [],
    )
    expect(
        "a string that states the claim is not a theorem",
        sb.headline_theorems('def note := "theorem c3 : C3Owes checker"\n'),
        [],
    )
    expect(
        "soundness taken as a hypothesis is not the headline",
        sb.headline_theorems("theorem step (h : C3Owes checker) : True := trivial\n"),
        [],
    )
    expect(
        "another checker's soundness is not the headline",
        sb.headline_theorems("theorem other : C3Owes v1Checker := x\n"),
        [],
    )
    expect(
        "a theorem that refutes the obligation is not the headline",
        sb.headline_theorems("theorem refuted : C3Owes checker → False := x\n"),
        [],
    )
    expect(
        "a conjunction that starts with the obligation is not the headline",
        sb.headline_theorems("theorem both : C3Owes checker ∧ True := x\n"),
        [],
    )
    expect(
        "a source with `include` is refused, not read",
        "absent" in sb.figure(lambda: sb.headline_theorems("variable (h : False)\ninclude h\ntheorem c : C3Owes checker := h.elim\n")),
        True,
    )
    real_load = sb.load
    try:
        sb.load = lambda path, root=None: {"gaps": [{"status": "open"}, {"status": "Open"}]}  # noqa: E731
        expect("a gap row with an unknown status is refused", "absent" in sb.figure(sb.island_gaps), True)
        sb.load = lambda path, root=None: {"gaps": [{"status": "open"}, {"status": "pinned"}]}  # noqa: E731
        expect("open gap rows are counted", sb.figure(sb.island_gaps).get("open"), 1)
    finally:
        sb.load = real_load
    expect("blanking keeps line structure", sb.blank_noncode_lean("a -- b\nc").count("\n"), 1)
    def trust(pins) -> dict:
        return sb.figure(lambda: sb.trust_pins_figure({"pins": pins, "measured_at": "t"}))

    row = lambda site, mutant: {"site": site, "mutant": mutant, "unmodified": "Refused"}  # noqa: E731
    honest = trust({"a": [row("s1", "Minted"), row("s2", "Refused")], "b": [row("s3", "Minted")]})
    expect("the Trust pins of every test are counted", (honest.get("minted_under_mutant"), honest.get("sites")), (2, 3))
    expect("the old flat list of pins is refused", "absent" in trust([row("s1", "Minted")]), True)
    expect("a site counted in two tests is refused", "absent" in trust({"a": [row("s1", "Minted")], "b": [row("s1", "Minted")]}), True)
    expect("a site row with no verdict is refused", "absent" in trust({"a": [{"site": "s1"}]}), True)
    absent = sb.figure(lambda: sb.load("data/no-such-artifact.json"))
    expect("a missing artifact is a stated absence", sorted(absent), ["absent"])
    honest = {"headline": {"planted_false_mints_clean": {"minted_under_mutant": 16, "sites": 19}}}
    flattering = {"headline": {"planted_false_mints_clean": {"minted_under_mutant": 0, "sites": 19}}}
    expect("a record that matches its sources is accepted", sb.record_refusal(sb.serialize(honest), honest), None)
    expect(
        "a record that states a better figure than its sources is refused",
        sb.record_refusal(sb.serialize(flattering), honest) is not None,
        True,
    )
    expect("a missing record is refused", sb.record_refusal(None, honest) is not None, True)

    run = {"real_declarations_decided": 0, "real_declarations_decided_reason": "no site", "export": {"path": "x"},
           "labels": {}, "figures": {"accepted": 7, "inside_fragment": 22, "ordinary_declarations": 256}}

    class Reader:
        """A stand-in for the coverage script (sb.COVERAGE_SCRIPT) whose check() ends as told."""

        class Stale(Exception):
            reason = "the sources have moved"

        class Refused(Exception):
            pass

        def __init__(self, outcome) -> None:
            self.outcome = outcome

        def check(self) -> dict:
            if isinstance(self.outcome, Exception):
                raise self.outcome
            return self.outcome

    def through(outcome, reader=sb.accepted_by_kcheck):
        return sb.figure(lambda: reader(lambda: sb.checked_coverage(Reader(outcome))))

    expect("a stale record gives no accepted figure, by its fixed reason alone",
           through(Reader.Stale("the sources have moved (3 files, first theories/x.lean)")), {"absent": "stale or absent: the sources have moved"})
    expect("a stale record gives no decided figure", sorted(through(Reader.Stale("x"), sb.decided_by_kcheck)), ["absent"])
    expect("a refused record gives no figure", through(Reader.Refused("a figure raised")),
           {"absent": f"refused by {sb.COVERAGE_SCRIPT}: a figure raised"})
    expect("a reader that crashes gives no figure", through(KeyError("figures")), {"absent": f"{sb.COVERAGE_SCRIPT} crashed (KeyError)"})
    expect("a reason that cannot be printed is escaped", through(Reader.Refused("name \ud800")), {"absent": f"refused by {sb.COVERAGE_SCRIPT}: name \\ud800"})
    expect("an accepted declaration is not a decided one", through(run, sb.decided_by_kcheck)["real_declarations_decided"], 0)
    expect("the accepted figure is read from the record", through(run)["accepted"], 7)
    board = {"headline": {k: {"absent": "x"} for k in ("planted_false_mints_clean", "planted_false_mints_trust")},
             "route": {k: {"absent": "x"} for k in ("checker_soundness", "clean_elaborates_theories", "island_gaps", "lean_kernel_rule_families")}}
    board["headline"]["decided_by_compiled_kcheck"] = through(run, sb.decided_by_kcheck)
    board["route"]["accepted_by_kcheck_no_site"] = through(run)
    printed = sb.render(board).split("\n")
    expect("the decided line prints zero beside the accepted figure", printed[3], "  decided by compiled kcheck  : 0 real declarations")
    expect("the accepted line says what the run is not", printed[4],
           "  accepted by kcheck, no site : 7 of 22 in the fragment, of 256 real declarations (the run claims no soundness; built by upstream Lean; interim loader)")
    board["route"]["accepted_by_kcheck_no_site"] = through(Reader.Stale("x"))
    expect("a stale record prints ABSENT, never a number", sb.render(board).split("\n")[4],
           "  accepted by kcheck, no site : ABSENT (stale or absent: the sources have moved)")
    for failure in failures:
        print(f"SELF_PROOF_SCOREBOARD self-test FAILED: {failure}", file=sys.stderr)
    if not failures:
        print(f"SELF_PROOF_SCOREBOARD=self-test ok arms={len(arms)}")
    return 1 if failures else 0
