#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Fail closed when the navigation docs' prose stops matching the tree.

WHY THIS EXISTS
---------------
Every rule in `docs/GATE_REGISTRY.md` asks whether an *enforcement artifact* is
wired and whether it has been seen to fail. None of them asks whether the
**status prose** is true, and on 2026-08-26 four CLAUDE.md claims were proved
false by measurement in a single day -- two of which caused bricks to be opened
against things that were already fixed:

  1. "the everyday-language battery ... is 51/63"  -- the artifact the sentence
     itself cited, `reports/everyday-battery.json`, had read 63/63 since
     2026-08-24. The paragraph quoted 38/63 and then 51/63; both stood in it
     after the battery had gone green.
  2. "~75% of elaboration time is `ElabCtx::build_local_ctx`"  -- fixed
     2026-08-22, 10.5x.
  3. "the first kernel failure is `forall_true_iff`, a `Sort*` U2 universe
     mismatch"  -- fixed, and the diagnosis was wrong as well.
  4. "simp has NO conditional-lemma discharger"  -- it has had one since
     2026-08-02.

Lake's prose was wrong in the OTHER direction ("the native backend builds
nothing" -- it is native end-to-end), which is the same defect: a sentence
nobody re-derives.

WHAT THIS CATCHES, AND WHAT IT HONESTLY DOES NOT
------------------------------------------------
Of those four, exactly ONE is reachable by a cheap deterministic re-derivation:
claim 1, because the prose named the artifact that carries the number. That is
the whole mechanical purchase available here, and pretending otherwise would
make this gate the thing it exists to stop. Claims 2-4 are qualitative
assertions about program behaviour; no string-matching check can evaluate
"~75% of elaboration time" or "simp has no discharger" without running the
elaborator. What this gate does about them is structural rather than semantic:
D3 refuses a NEW quantitative claim that cites an artifact and does not bind
one, so the next claim of the shape that went stale cannot be written unbound.

Three rules, all fail-closed:

  D1 REF     A repo-rooted path cited in a governed doc must exist, unless the
             doc declares WHY it does not -- `absent` (deliberately gone, e.g.
             a `docs/GATE_REGISTRY.md` R8 retirement) or `elsewhere` (a
             sibling repo, verified there when that repo is on disk).
  D2 FIGURE  A `<!-- claim: figure ... -->` marker binds a prose figure to a
             key of a JSON artifact. The value is re-derived from the artifact
             and must appear in the BOUND SPAN -- the marker's own line and the
             three above it, clipped to its paragraph. There is no third copy
             of the number to drift: move the artifact and the prose is red
             until somebody reads it.

             The span is a backward window and not the whole paragraph, and
             that is load-bearing rather than fussy. The paragraph this gate
             was written for says the battery is 63/63 and then, three lines
             later, that it read 38/63 and 51/63 on two earlier dates -- which
             is exactly the right way to write it. Under a paragraph-wide
             span, a regression back to 51/63 would find "51/63" sitting in
             that history and report GREEN. So a marker is placed directly
             BELOW the sentence it binds, and only what is above it counts.
             A misplaced marker fails closed.
  D3 BIND    In a doc that opts in, a paragraph that BOTH cites a tracked
             `reports/`|`data/` JSON artifact AND quotes an `N/M` figure must
             carry a marker -- either a `figure` binding or an explicit
             `pointer-only` saying the figure is dated and not live. This is
             the forcing function: without it D2 is opt-in and nobody opts in.

SCOPE IS MEASURED, NOT ASSUMED
------------------------------
D1 is not switched on everywhere, because a first draft that was measured
2026-08-26 over every backticked path in seven docs produced 246 "missing" hits
of which the overwhelming majority were correct prose:

  * basename shorthand -- `local_gate.sh`, `x.py`, `coverage.json`, `mod.rs`.
    A path token only counts here if it contains `/` AND its first segment is a
    real top-level directory of THIS repo.
  * cross-repo paths -- `docs/CRYSTAL_STATUS.md` alone cites 76 that resolve in
    the sibling Trust repo (`crates/trust-*`, `tests/crystal_a2_mint*.rs`,
    `scripts/trust_ir_rowdiff.py`). Annotating those one by one is not worth
    it, so that doc is out of D1 with the reason recorded rather than being
    silently exempt.
  * deliberately-absent paths -- `docs/GATE_REGISTRY.md` NAMES retired files,
    and R8 requires that they be gone. A blanket "cited path must exist" rule
    contradicts a rule the repo already enforces. Hence `absent`, which makes
    the exemption a reviewable sentence instead of a hole.

On the four navigation docs D1 IS switched on, and there it found live rot on
the day it was written: `docs/AUDIT_LEAN4_REPLACEMENT_2026-07-23.md`, cited
five times across CLAUDE.md, AGENTS.md, README.md and VISION.md as "the
authoritative commit-pinned source interpretation", does not exist and never
did -- the file is `..._2026-07-22.md`, and the wrong date had propagated to
every doc that pointed at it.

This reads Markdown and JSON only. It never reads Rust or Lean source, so it
declares no `source_scan` (registry rule R9) -- and a declaration left behind by
a scanner that is not there is itself an R9 refusal.

MARKER SYNTAX
-------------
    <!-- claim: figure <artifact.json> <expr> -->
    <!-- claim: pointer-only <reason...> -->
    <!-- claim: absent <path> <reason...> -->
    <!-- claim: elsewhere <path> <repo> <reason...> -->

`<expr>` is deliberately tiny -- dotted/indexed lookup (`a.b`, `a[0].c`) and
one composite, `a/b`, rendering as "63/63". Anything larger becomes a language
nobody can review.

An ILLUSTRATIVE marker in a governed doc is a REAL marker, and there is no
escape hatch. Writing the D2 row of `docs/GATE_REGISTRY.md` with a literal
example turned this gate red on its own documentation, correctly: a comment
shaped like a binding either binds or it is a decoration that looks like a
guarantee, and this repo has enough of those. Document the syntax in backticks
without the comment delimiters, the way that row now does. An `example` kind
was considered and rejected -- it is a switch that turns a marker off, which is
the vacuous-green class wearing a different hat.

Usage:
    python3 scripts/check_doc_claims.py             # check, fail-closed
    python3 scripts/check_doc_claims.py --selftest  # mutation arms on a fixture
    python3 scripts/check_doc_claims.py --list      # what is governed, and how
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------- governed set
#
# Per-doc rule opt-in. A doc is in this table or it is not governed; there is no
# glob, because "every .md in docs/" would sweep in dated records and archived
# handoffs whose whole value is that they are NOT updated.
#
# rules: subset of {"ref", "bind"}. "figure" is unconditional -- a marker is
# honoured wherever it appears, because a marker is an explicit request to be
# checked and ignoring one would be the vacuous-green class in doc form.
GOVERNED = (
    ("CLAUDE.md", ("ref", "bind")),
    ("AGENTS.md", ("ref",)),
    ("README.md", ("ref",)),
    ("VISION.md", ("ref",)),
    # docs/GATE_REGISTRY.md and docs/SUITE_STATE.md: `figure` only for now.
    # Both name paths that are deliberately gone (R8 retirements) or that live
    # in the Trust repo; switching "ref" on for them is a real piece of work
    # (~16 annotations, measured 2026-08-26) and belongs to whoever does it.
    ("docs/GATE_REGISTRY.md", ()),
    ("docs/SUITE_STATE.md", ()),
    ("docs/CRYSTAL_STATUS.md", ()),
    # Added 2026-08-27. The repo's central "what is proved" document was NOT
    # governed here, which is the wrong way round: it is the doc most likely to
    # be quoted as evidence and the one where a rotted citation does the most
    # damage. Switching "ref" on cost exactly three fixes -- one real path error
    # (`tests/kernel_core_red_env_fidelity.rs`, actually under
    # `crates/clean-verify/`) and two `elsewhere` annotations for the Trust
    # sibling -- so the debt this row was avoiding did not exist.
    ("docs/SELF_VERIFICATION_CERTIFICATE.md", ("ref",)),
)

# Sibling repos a doc may point into with `elsewhere`. Absent from disk is not
# an error -- not every machine has every sibling -- but PRESENT and missing the
# path is, so a cross-repo citation cannot rot unnoticed on a box that could
# have checked it.
SIBLINGS = {
    "trust": ROOT.parent / "trust",
    "ay": ROOT.parent / "ay",
    "zani": ROOT.parent / "zani",
    "gamma-crown": ROOT.parent / "gamma-crown",
}

MARKER = re.compile(r"<!--\s*claim:\s*(.*?)\s*-->")
# A path token: backticked, contains a `/`, and no spaces. The leading-segment
# test against the real tree is what keeps `Mathlib/Logic/Basic.lean` and
# `elab_match/nested_ctor.rs` out -- neither names a directory of this repo.
PATH_TOKEN = re.compile(r"`([A-Za-z0-9_][A-Za-z0-9_.+-]*(?:/[A-Za-z0-9_.+-]+)+)`")
ARTIFACT_TOKEN = re.compile(r"`((?:reports|data)/[A-Za-z0-9_./-]+\.json)`")
FIGURE = re.compile(r"\b\d+/\d+\b")

# Lines above a `figure` marker that count as its bound span. Three is enough
# for a wrapped sentence and short enough to exclude the next one.
SPAN_LINES = 3


class Problem(str):
    """A single fail-closed refusal, rendered verbatim to stderr."""


def _top_dirs(root: Path):
    return {p.name for p in root.iterdir() if p.is_dir() and not p.name.startswith(".")}


def _paragraphs(text: str):
    """(start_line, end_line, body) for each blank-line-delimited paragraph.

    Line numbers are 1-based and inclusive, so a diagnostic points at something
    a human can open.
    """
    out = []
    start = None
    buf = []
    for i, line in enumerate(text.splitlines(), 1):
        if line.strip():
            if start is None:
                start = i
            buf.append(line)
        elif start is not None:
            out.append((start, i - 1, "\n".join(buf)))
            start, buf = None, []
    if start is not None:
        out.append((start, start + len(buf) - 1, "\n".join(buf)))
    return out


def _resolve(obj, expr: str):
    """Dotted/indexed lookup. Raises KeyError with a readable path on a miss."""
    cur = obj
    for part in re.findall(r"[^.\[\]]+|\[\d+\]", expr):
        if part.startswith("["):
            idx = int(part[1:-1])
            if not isinstance(cur, list) or idx >= len(cur):
                raise KeyError(expr)
            cur = cur[idx]
        else:
            if not isinstance(cur, dict) or part not in cur:
                raise KeyError(expr)
            cur = cur[part]
    return cur


def _render(obj, expr: str) -> str:
    if "/" in expr:
        parts = expr.split("/")
        if len(parts) != 2:
            raise ValueError(expr)
        return "/".join(_render(obj, p) for p in parts)
    val = _resolve(obj, expr)
    if isinstance(val, bool) or not isinstance(val, (int, float, str)):
        raise ValueError(expr)
    return str(val)


def _parse_markers(text: str):
    """[(line, paragraph_index, kind, args)] for every marker in the document."""
    paras = _paragraphs(text)
    found = []
    for m in MARKER.finditer(text):
        line = text[: m.start()].count("\n") + 1
        body = m.group(1).split()
        pidx = next(
            (i for i, (s, e, _) in enumerate(paras) if s <= line <= e),
            None,
        )
        found.append((line, pidx, body[0] if body else "", body[1:]))
    return paras, found


def _bound_span(text: str, paras, pidx, line: str) -> str:
    """The prose a `figure` marker speaks for: its line and SPAN_LINES above.

    Clipped to the marker's paragraph, so a window can never reach across a
    blank line into a sentence about something else.
    """
    if pidx is None:
        return ""
    start = max(paras[pidx][0], line - SPAN_LINES)
    lines = text.splitlines()
    return "\n".join(lines[start - 1 : line])


def check(root: Path, governed=GOVERNED, siblings=None):
    """Re-derive every governed claim. Returns a list of Problem strings."""
    siblings = SIBLINGS if siblings is None else siblings
    problems = []
    tops = _top_dirs(root)
    stats = {"docs": 0, "paths": 0, "figures": 0, "bound": 0}

    for rel, rules in governed:
        doc = root / rel
        if not doc.exists():
            problems.append(
                Problem(
                    "D0 GOVERNED: %s is in the governed set and is not in the "
                    "tree. Remove the row or restore the doc; a governed doc "
                    "that vanishes must not silently stop being checked." % rel
                )
            )
            continue
        stats["docs"] += 1
        text = doc.read_text()
        paras, markers = _parse_markers(text)

        # -- marker shape. A malformed marker is a refusal, never a skip: a
        # -- marker that silently does nothing is the vacuous-green class.
        absent, elsewhere, figures, pointer_paras = {}, {}, [], set()
        for line, pidx, kind, args in markers:
            where = "%s:%d" % (rel, line)
            if kind == "figure":
                if len(args) != 2:
                    problems.append(
                        Problem(
                            "D2 FIGURE: %s malformed -- expected `<!-- claim: "
                            "figure <artifact.json> <expr> -->`, got %r"
                            % (where, " ".join([kind] + args))
                        )
                    )
                    continue
                figures.append((where, pidx, line, args[0], args[1]))
            elif kind == "pointer-only":
                if not args:
                    problems.append(
                        Problem(
                            "D3 BIND: %s `pointer-only` needs a reason saying "
                            "why the figure beside it is not re-derivable "
                            "(dated measurement? different artifact?)." % where
                        )
                    )
                    continue
                pointer_paras.add(pidx)
            elif kind == "absent":
                if len(args) < 2:
                    problems.append(
                        Problem(
                            "D1 REF: %s `absent` needs `<path> <reason...>` -- "
                            "an unexplained exemption is a hole, not a record."
                            % where
                        )
                    )
                    continue
                absent[args[0]] = where
            elif kind == "elsewhere":
                if len(args) < 3:
                    problems.append(
                        Problem(
                            "D1 REF: %s `elsewhere` needs `<path> <repo> "
                            "<reason...>`." % where
                        )
                    )
                    continue
                elsewhere[args[0]] = (where, args[1])
            else:
                problems.append(
                    Problem(
                        "D0 MARKER: %s unknown claim kind %r. Known: figure, "
                        "pointer-only, absent, elsewhere." % (where, kind)
                    )
                )

        # -- D2 FIGURE (always on, wherever a marker appears)
        for where, pidx, mline, art, expr in figures:
            stats["bound"] += 1
            apath = root / art
            if not apath.exists():
                problems.append(
                    Problem(
                        "D2 FIGURE: %s binds a figure to %s, which is not in "
                        "the tree." % (where, art)
                    )
                )
                continue
            try:
                data = json.loads(apath.read_text())
            except (OSError, ValueError) as exc:
                problems.append(
                    Problem("D2 FIGURE: %s cannot read %s: %s" % (where, art, exc))
                )
                continue
            try:
                value = _render(data, expr)
            except (KeyError, ValueError, TypeError):
                problems.append(
                    Problem(
                        "D2 FIGURE: %s binds `%s`, which %s does not carry as a "
                        "scalar. The artifact moved or the expression is wrong."
                        % (where, expr, art)
                    )
                )
                continue
            span = _bound_span(text, paras, pidx, mline)
            if value not in span:
                problems.append(
                    Problem(
                        "D2 FIGURE: %s re-derives `%s` = %s from %s, and that "
                        "value does NOT appear in the %d lines above the "
                        "marker. Either the artifact moved and the prose did "
                        "not -- read the artifact and rewrite the sentence -- "
                        "or the marker sits above the sentence it binds "
                        "instead of below it."
                        % (where, expr, value, art, SPAN_LINES)
                    )
                )

        # -- D1 REF
        if "ref" in rules:
            for m in PATH_TOKEN.finditer(text):
                cited = m.group(1).rstrip("/")
                if cited.split("/")[0] not in tops:
                    continue  # basename shorthand or another repo's layout
                stats["paths"] += 1
                if (root / cited).exists():
                    continue
                line = text[: m.start()].count("\n") + 1
                if cited in absent:
                    continue
                if cited in elsewhere:
                    where, repo = elsewhere[cited]
                    sib = siblings.get(repo)
                    if sib is None:
                        problems.append(
                            Problem(
                                "D1 REF: %s declares %s `elsewhere` in unknown "
                                "repo %r." % (where, cited, repo)
                            )
                        )
                    elif sib.exists() and not (sib / cited).exists():
                        problems.append(
                            Problem(
                                "D1 REF: %s declares %s `elsewhere` in %s, and "
                                "it is NOT there either. A cross-repo citation "
                                "rots exactly like a local one."
                                % (where, cited, repo)
                            )
                        )
                    continue
                problems.append(
                    Problem(
                        "D1 REF: %s:%d cites `%s`, which is not in the tree. "
                        "Fix the path, or declare it: `<!-- claim: absent %s "
                        "<why> -->` if it is deliberately gone, `<!-- claim: "
                        "elsewhere %s <repo> <why> -->` if it lives in a "
                        "sibling repo." % (rel, line, cited, cited, cited)
                    )
                )

        # -- D3 BIND
        if "bind" in rules:
            for i, (s, e, body) in enumerate(paras):
                arts = ARTIFACT_TOKEN.findall(body)
                if not arts or not FIGURE.search(body):
                    continue
                stats["figures"] += 1
                if i in pointer_paras:
                    continue
                if any(pidx == i for _, pidx, _, _, _ in figures):
                    continue
                problems.append(
                    Problem(
                        "D3 BIND: %s:%d-%d quotes an N/M figure in a paragraph "
                        "that cites %s, and binds neither. This is the shape "
                        "that went stale: add `<!-- claim: figure %s <expr> "
                        "-->` so the number is re-derived, or `<!-- claim: "
                        "pointer-only <why> -->` if the figure is a dated "
                        "measurement the artifact does not carry."
                        % (rel, s, e, ", ".join(sorted(set(arts))), arts[0])
                    )
                )

    return problems, stats


# --------------------------------------------------------------------- selftest
#
# Arms run against a synthetic tree, never the real one. `check_add_decl_ratchet`
# plants into a tracked file and restores it in a `finally`; that arm is
# genuinely falsifying and it is also a measured hazard -- a concurrent
# `local_gate.sh` compiled the planted file and died on it (see the
# check_add_decl_ratchet note in data/gate_registry.json). Nothing here needs
# the real tree, so nothing here touches it.

_ART = '{"passed": 63, "total": 63, "rows": [{"n": 7}]}'


def _fixture(tmp: Path):
    (tmp / "docs").mkdir(parents=True)
    (tmp / "reports").mkdir()
    (tmp / "scripts").mkdir()
    (tmp / "reports/battery.json").write_text(_ART)
    (tmp / "docs/real.md").write_text("real\n")
    # Shaped like the real CLAUDE.md paragraph this gate was written for: the
    # live figure, the marker under it, and the superseded figures BELOW -- so
    # the arms exercise the span rule instead of a toy with no history in it.
    (tmp / "CLAUDE.md").write_text(
        "# Fixture\n"
        "\n"
        "The battery is 63/63 -- artifact `reports/battery.json`.\n"
        "<!-- claim: figure reports/battery.json passed/total -->\n"
        "It read 38/63 in July and 51/63 in August.\n"
        "\n"
        "See `docs/real.md` and `scripts/`.\n"
    )
    return tmp


def _run(tmp: Path):
    governed = (("CLAUDE.md", ("ref", "bind")),)
    return check(tmp, governed=governed, siblings={"trust": tmp / "no-such-sibling"})


def selftest() -> int:
    arms = [
        # (name, expected-prefix or "" for green, mutation)
        ("01 baseline is GREEN", "", lambda t: None),
        (
            "02 D2 artifact moves, prose stale -- THE 51/63 arm, and the arm "
            "that a paragraph-wide span would have passed: 51/63 IS in this "
            "paragraph, as superseded history one line below the marker",
            "D2 FIGURE",
            lambda t: (t / "reports/battery.json").write_text(
                '{"passed": 51, "total": 63}'
            ),
        ),
        (
            "03 D2 anti-correlation: prose follows the artifact -> GREEN",
            "",
            lambda t: (
                (t / "reports/battery.json").write_text('{"passed": 51, "total": 63}'),
                _sub(t, "CLAUDE.md", "is 63/63", "is 51/63"),
            ),
        ),
        (
            "04 D2 artifact deleted",
            "D2 FIGURE",
            lambda t: (t / "reports/battery.json").unlink(),
        ),
        (
            "05 D2 bound key gone from the artifact",
            "D2 FIGURE",
            lambda t: (t / "reports/battery.json").write_text('{"total": 63}'),
        ),
        (
            "06 D2 value sits in the paragraph but BELOW the marker",
            "D2 FIGURE",
            lambda t: (
                _sub(
                    t,
                    "CLAUDE.md",
                    "The battery is 63/63 -- artifact",
                    "The battery is 9/9 -- artifact",
                ),
                _sub(t, "CLAUDE.md", "It read 38/63", "It read 63/63 and 38/63"),
            ),
        ),
        (
            "06b D2 marker placed ABOVE the sentence it binds",
            "D2 FIGURE",
            lambda t: _sub(
                t,
                "CLAUDE.md",
                "The battery is 63/63 -- artifact `reports/battery.json`.\n"
                "<!-- claim: figure reports/battery.json passed/total -->\n",
                "<!-- claim: figure reports/battery.json passed/total -->\n"
                "The battery is 63/63 -- artifact `reports/battery.json`.\n",
            ),
        ),
        (
            "07 D2 malformed marker is a refusal, not a skip",
            "D2 FIGURE",
            lambda t: _sub(
                t, "CLAUDE.md", "figure reports/battery.json passed/total", "figure"
            ),
        ),
        (
            "08 D0 unknown marker kind",
            "D0 MARKER",
            lambda t: _sub(t, "CLAUDE.md", "claim: figure", "claim: figvre"),
        ),
        (
            "09 D1 rooted path that is not in the tree",
            "D1 REF",
            lambda t: (t / "docs/real.md").unlink(),
        ),
        (
            "10 D1 the same path, declared `absent` -> GREEN",
            "",
            lambda t: (
                (t / "docs/real.md").unlink(),
                _sub(
                    t,
                    "CLAUDE.md",
                    "See `docs/real.md`",
                    "<!-- claim: absent docs/real.md retired 2026-08-26 -->\n"
                    "See `docs/real.md`",
                ),
            ),
        ),
        (
            "11 D1 `absent` with no reason is still a refusal",
            "D1 REF",
            lambda t: (
                (t / "docs/real.md").unlink(),
                _sub(
                    t,
                    "CLAUDE.md",
                    "See `docs/real.md`",
                    "<!-- claim: absent docs/real.md -->\nSee `docs/real.md`",
                ),
            ),
        ),
        (
            "12 D1 `elsewhere` into a sibling that IS present and lacks it",
            "D1 REF",
            lambda t: (
                (t / "docs/real.md").unlink(),
                (t / "no-such-sibling").mkdir(),
                _sub(
                    t,
                    "CLAUDE.md",
                    "See `docs/real.md`",
                    "<!-- claim: elsewhere docs/real.md trust lives there -->\n"
                    "See `docs/real.md`",
                ),
            ),
        ),
        (
            "13 D1 basename shorthand is NOT a citation -> GREEN",
            "",
            lambda t: _sub(t, "CLAUDE.md", "See `docs/real.md`", "See `nothing.rs`"),
        ),
        (
            "14 D1 a first segment that is not a dir of this repo -> GREEN",
            "",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`", "See `Mathlib/Logic/Basic.lean`"
            ),
        ),
        (
            "15 D3 artifact + figure paragraph with no marker at all",
            "D3 BIND",
            lambda t: _sub(
                t, "CLAUDE.md", "<!-- claim: figure reports/battery.json passed/total -->\n", ""
            ),
        ),
        (
            "16 D3 the same paragraph with `pointer-only` -> GREEN",
            "",
            lambda t: _sub(
                t,
                "CLAUDE.md",
                "<!-- claim: figure reports/battery.json passed/total -->",
                "<!-- claim: pointer-only dated 2026-07-12 run, not a live key -->",
            ),
        ),
        (
            "17 D3 `pointer-only` with no reason is a refusal",
            "D3 BIND",
            lambda t: _sub(
                t,
                "CLAUDE.md",
                "<!-- claim: figure reports/battery.json passed/total -->",
                "<!-- claim: pointer-only -->",
            ),
        ),
        (
            "18 D0 a governed doc that disappears is a refusal, not a skip",
            "D0 GOVERNED",
            lambda t: (t / "CLAUDE.md").unlink(),
        ),
    ]

    failed = 0
    for name, expect, mutate in arms:
        tmp = Path(tempfile.mkdtemp(prefix="doc-claims-"))
        try:
            _fixture(tmp)
            mutate(tmp)
            problems, _ = _run(tmp)
            got = [p for p in problems]
            if expect == "":
                if got:
                    failed += 1
                    print("  ARM RED (expected green) %s: %s" % (name, got[0]))
                continue
            if not any(p.startswith(expect) for p in got):
                failed += 1
                print(
                    "  ARM GREEN (expected %s) %s: %s"
                    % (expect, name, got[0] if got else "<no problem reported>")
                )
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    print("DOC_CLAIMS_SELFTEST arms=%d failed=%d" % (len(arms), failed))
    return 1 if failed else 0


def _sub(tmp: Path, rel: str, old: str, new: str):
    p = tmp / rel
    text = p.read_text()
    if text.count(old) != 1:
        raise AssertionError(
            "selftest anchor %r occurs %d times in %s, not once"
            % (old, text.count(old), rel)
        )
    p.write_text(text.replace(old, new))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--selftest", action="store_true", help="mutation arms on a fixture")
    ap.add_argument("--list", action="store_true", help="print the governed set")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    if args.list:
        print("%-28s %s" % ("DOC", "RULES (figure is always on)"))
        for rel, rules in GOVERNED:
            print("%-28s %s" % (rel, ", ".join(rules) if rules else "figure only"))
        return 0

    # The self-test runs first on every invocation, for the reason the
    # gate-registry and add-decl legs do: a demonstrator whose falsifiability is
    # only checked when somebody remembers is the artifact this repo keeps
    # finding shipped.
    if selftest() != 0:
        print("DOC_CLAIMS=fail its own arms no longer fire", file=sys.stderr)
        return 1

    problems, stats = check(ROOT)
    if problems:
        print(
            "DOC_CLAIMS=fail docs=%d problems=%d" % (stats["docs"], len(problems)),
            file=sys.stderr,
        )
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    print(
        "DOC_CLAIMS=ok docs=%d rooted-paths=%d bound-figures=%d figure-paragraphs=%d"
        % (stats["docs"], stats["paths"], stats["bound"], stats["figures"])
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
