#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Compare a TrustCG LINK+RUN census against its pinned per-root verdicts.

WHY THIS EXISTS
---------------
`crates/clean-compiler/examples/trustcg_census.rs` routes every computable
prelude root through the trust-ir -> trust-cg -> object -> link -> run path
that `clean compile --emit obj` uses. Its own header calls it "an explicit
qualification utility, not a default test", and until the two-language
roadmap's WS6.0 nothing gated it. Its only machine verdict is a single
all-OK check (an `assert_eq!(n_ok, total)` until 2026-10-19, an exit status
since), so it is either all-green or a COUNT -- and a count
cannot say WHICH root regressed, nor tell a regression from a same-size swap
(one root starts failing while another starts passing).

This checker makes the census a per-row ratchet. The expected verdict of
every root is pinned in `crates/clean-compiler/examples/trustcg_census.expected.json`,
beside the example, and a run is compared ROW BY ROW: a root whose verdict
changed, a root that disappeared, and a root that appeared are each refused
by NAME.

A failing row pins its REASON as well as its tag. At the first pin 1001 of
1002 roots were TRUSTCG_FAIL for one reason (the codegen-license refusal of an
Ungated body), so a tag-only pin was blind to anything that happened inside
that population: a trust-cg that crashed on every module, or started refusing
the emitted module as malformed, was still TRUSTCG_FAIL on every row and the
leg stayed green (found in the WS6.0 review). The pinned reason is the row's
detail with only its run-specific parts normalised -- the per-run temporary
directory and the root's own name when quoted -- so a legitimate re-run is
never refused while any real change of reason is, by name (`REASON CHANGED`).
Distinct reasons are stored once, in `reasons`, and a failing verdict cites
one as `<TAG> ~<id>`. An improvement is refused too -- a row whose outcome changes for a
reason nobody reviewed is exactly what a ratchet exists to surface (roadmap
§2.4 rule 3); the fix re-pins with `--write-expected` in the same commit, and
the JSON diff is the review.

WHAT IT REFUSES BEFORE COMPARING ANYTHING (fail-closed, each named)
------------------------------------------------------------------
  * a missing or unreadable TSV (the census crashed before writing it);
  * a TSV with no `# scope=...` header line;
  * a LIMITED run (`TRUSTCG_LIMIT` set): its own header says
    "NOT FULL QUALIFICATION", and comparing a prefix to the full pin would
    report every truncated root as a regression -- or, worse, invite a pin
    of the prefix;
  * zero rows (a census that selected nothing cannot fail);
  * a row count that disagrees with the header's `selected_defs` or, in a
    FULL run, with its `full_population`, or an OK count that disagrees with
    the header's `ok` (a truncated or hand-edited file);
  * a duplicate root, or a verdict tag outside the census's own vocabulary;
  * a pin whose summary disagrees with its own verdicts: `counts` that is not
    the tally of their tags, a `full_population` that is not their number, or
    a `reasons` entry no verdict cites. `--write-expected` derives all three
    from the verdicts (`tag_counts` is the one tally both sides use), so a
    disagreement is a hand edit, and a reader of the summary would learn a
    figure the verdicts do not support;
  * a census exit status that disagrees with its rows (`--census-exit`): the
    example writes the file and THEN exits non-zero unless all OK, so a non-zero exit is
    expected exactly when some row is not OK;
  * a `trustcg_version` other than the pinned one. The pinned verdicts are a
    property of ONE backend; a different one needs a reviewed re-pin, not a
    silent comparison. NAMED LIMITATION: `trust-cg --version` prints only the
    package version (`trust-cg 0.6.0`), so two builds of the same version are
    indistinguishable here -- the row comparison is what catches their
    difference.

WHAT IT DOES NOT CHECK
----------------------
  * the pin's `measured_at`: free-text provenance written by whoever
    re-pinned (which Clean and trust-cg commits, which build). Nothing here
    can tell whether the commits it names produced the verdicts; the review of
    the re-pin commit is its only check. Likewise `what_this_is`.

Usage:
    scripts/check_trustcg_census.py --selftest
    scripts/check_trustcg_census.py <census.tsv> [--census-exit RC] [--expected <json>]
    scripts/check_trustcg_census.py <census.tsv> --write-expected '<where measured>'
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = ROOT / "crates/clean-compiler/examples/trustcg_census.expected.json"
SCHEMA = "clean.trustcg_census_expected.v1"

# The census's own vocabulary (`Verdict::tag` in trustcg_census.rs).
OK_TAGS = ("OK", "OK_CHECKED", "OK_SHIM")
FAIL_TAGS = (
    "LOWER_FAIL",
    "EMITIR_FAIL",
    "TRUSTCG_FAIL",
    "VERSION_FAIL",
    "LINK_FAIL",
    "RUN_FAIL",
    "NO_ENTRY",
)
TAGS = OK_TAGS + FAIL_TAGS

# `key=value` where value is a Rust `{:?}` string ("..." with escapes) or a
# bare token (`None`, `Some(5)`, `881`, `false`).
HEADER_FIELD = re.compile(r'(\w+)=("(?:[^"\\]|\\.)*"|\S+)')

# The census's per-run scratch directory (`tempfile::tempdir()`), e.g.
# /var/folders/kb/<..>/T/.tmpubJ3FC/root.tmbc or /tmp/.tmpAb12Cd/driver.c.
TEMP_DIR = re.compile(r"(?:/private)?/(?:var/folders|tmp)/(?:[^/'\"`\s]+/)*?\.tmp[A-Za-z0-9]+/")


def normalize_reason(name: str, detail: str) -> str:
    """A failing row's detail with only its run-specific parts replaced."""
    text = TEMP_DIR.sub("<tmp>/", detail)
    for quote_open, quote_close in (("`", "`"), ("'", "'"), ('"', '"')):
        text = text.replace(f"{quote_open}{name}{quote_close}", f"{quote_open}<root>{quote_close}")
    return text


def split_verdict(value: str) -> tuple[str, str | None]:
    tag, sep, rid = value.partition(" ~")
    return tag, (rid if sep else None)


def tag_counts(tags) -> dict[str, int]:
    """The pin's `counts`: written from a run's tags, re-derived from the pin's verdicts."""
    counts: dict[str, int] = {}
    for tag in tags:
        counts[tag] = counts.get(tag, 0) + 1
    return dict(sorted(counts.items()))


class Refusal(Exception):
    """A census output that cannot be compared, or that disagrees with the pin."""


def _unquote(value: str) -> str:
    if len(value) >= 2 and value[0] == '"' and value[-1] == '"':
        try:
            return json.loads(value)
        except ValueError:
            return value[1:-1]
    return value


def parse_tsv(text: str) -> tuple[dict[str, str], dict[str, tuple[str, str]]]:
    header: dict[str, str] | None = None
    rows: dict[str, tuple[str, str]] = {}
    for lineno, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        if line.startswith("# "):
            if header is not None:
                raise Refusal(f"line {lineno}: a second header line -- two census runs concatenated?")
            header = {k: _unquote(v) for k, v in HEADER_FIELD.findall(line[2:])}
            continue
        if header is None:
            raise Refusal(f"line {lineno}: a verdict row before the `# scope=...` header")
        parts = line.split("\t", 2)
        if len(parts) < 2:
            raise Refusal(f"line {lineno}: not a `<root>\\t<TAG>\\t<detail>` row: {line[:120]!r}")
        name, tag = parts[0], parts[1]
        detail = parts[2] if len(parts) == 3 else ""
        if tag not in TAGS:
            raise Refusal(f"line {lineno}: root {name!r} carries unknown verdict tag {tag!r}")
        if name in rows:
            raise Refusal(f"line {lineno}: duplicate root {name!r}")
        rows[name] = (tag, detail)
    if header is None:
        raise Refusal("no `# scope=...` header line: this is not a trustcg_census TRUSTCG_OUT file")
    return header, rows


def validate_run(header: dict[str, str], rows: dict[str, tuple[str, str]]) -> None:
    scope = header.get("scope")
    if scope != "FULL":
        raise Refusal(
            f"census scope is {scope!r}, not \"FULL\" (requested_limit={header.get('requested_limit')}): "
            f"a LIMITED run is not a qualification and is never compared against the full pin -- "
            f"unset TRUSTCG_LIMIT"
        )
    if not rows:
        raise Refusal("the census wrote ZERO verdict rows: a run that selected nothing cannot fail")
    # A FULL run selects its whole population (`computable.truncate` runs only
    # under TRUSTCG_LIMIT), so `full_population` must equal the row count too.
    for key, want in (("selected_defs", len(rows)),
                      ("full_population", len(rows)),
                      ("ok", sum(1 for t, _ in rows.values() if t in OK_TAGS))):
        got = header.get(key)
        if got is None or not got.isdigit():
            raise Refusal(f"header field {key!r} is missing or not a count ({got!r})")
        if int(got) != want:
            raise Refusal(
                f"header says {key}={got} but the file carries {want}: a truncated or edited census output"
            )


def load_expected(path: Path) -> dict:
    try:
        doc = json.loads(path.read_text())
    except OSError as exc:
        raise Refusal(f"pinned expectation {path} is unreadable: {exc}") from exc
    except ValueError as exc:
        raise Refusal(f"pinned expectation {path} is not JSON: {exc}") from exc
    if doc.get("schema") != SCHEMA:
        raise Refusal(f"pinned expectation {path} has schema {doc.get('schema')!r}, want {SCHEMA!r}")
    verdicts = doc.get("verdicts")
    if not isinstance(verdicts, dict) or not verdicts:
        raise Refusal(f"pinned expectation {path} pins ZERO verdicts: an empty pin cannot fail")
    reasons = doc.get("reasons")
    if not isinstance(reasons, dict):
        raise Refusal(f"pinned expectation {path} has no `reasons` table")
    bad = sorted(n for n, v in verdicts.items() if not isinstance(v, str) or split_verdict(v)[0] not in TAGS)
    if bad:
        raise Refusal(f"pinned expectation {path} carries unknown tags for {bad[:5]}")
    for name, value in verdicts.items():
        tag, rid = split_verdict(value)
        if tag in OK_TAGS and rid is not None:
            raise Refusal(f"pinned expectation {path}: OK root {name!r} cites a failure reason ~{rid}")
        if tag not in OK_TAGS and (rid is None or rid not in reasons):
            raise Refusal(
                f"pinned expectation {path}: failing root {name!r} cites reason {rid!r}, which is not "
                f"in the `reasons` table -- a failing row must pin WHY it fails"
            )
    # The summary is DERIVED from the verdicts by --write-expected; check it
    # against them, so it cannot state a figure the verdicts do not support.
    tally = tag_counts(split_verdict(v)[0] for v in verdicts.values())
    if doc.get("counts") != tally:
        raise Refusal(
            f"pinned expectation {path}: `counts` {doc.get('counts')!r} is not the tally of its own "
            f"verdicts {tally!r} -- a hand-edited summary; re-pin with --write-expected"
        )
    population = doc.get("full_population")
    if type(population) is not int or population != len(verdicts):
        raise Refusal(
            f"pinned expectation {path}: `full_population` {population!r} is not the number of its "
            f"verdicts ({len(verdicts)}) -- a hand-edited summary; re-pin with --write-expected"
        )
    uncited = sorted(set(reasons) - {split_verdict(v)[1] for v in verdicts.values()})
    if uncited:
        raise Refusal(
            f"pinned expectation {path}: reason(s) {uncited[:5]} are cited by no verdict -- a stale "
            f"`reasons` entry; re-pin with --write-expected"
        )
    if not doc.get("trustcg_version"):
        raise Refusal(f"pinned expectation {path} names no trustcg_version")
    return doc


def compare(expected: dict, header: dict[str, str], rows: dict[str, tuple[str, str]]) -> list[str]:
    problems: list[str] = []
    if header.get("trustcg_version") != expected["trustcg_version"]:
        problems.append(
            f"TRUSTCG VERSION: the run used {header.get('trustcg_version')!r}, the pin was measured "
            f"with {expected['trustcg_version']!r} -- re-pin under review with --write-expected"
        )
    want = {n: split_verdict(v) for n, v in expected["verdicts"].items()}
    reasons: dict[str, str] = expected["reasons"]
    for name in sorted(set(want) | set(rows)):
        if name not in rows:
            problems.append(f"MISSING ROOT: {name} (pinned {want[name][0]}) is no longer in the census population")
        elif name not in want:
            tag, detail = rows[name]
            problems.append(f"NEW ROOT: {name} -> {tag} is not pinned{': ' + detail if detail else ''}")
        elif rows[name][0] != want[name][0]:
            tag, detail = rows[name]
            pinned = want[name][0]
            direction = (
                "REGRESSED" if pinned in OK_TAGS and tag not in OK_TAGS
                else "IMPROVED" if tag in OK_TAGS and pinned not in OK_TAGS
                else "CHANGED"
            )
            problems.append(f"{direction}: {name}: pinned {pinned}, measured {tag}"
                            f"{': ' + detail if detail else ''}")
        elif want[name][1] is not None:
            measured = normalize_reason(name, rows[name][1])
            pinned_reason = reasons[want[name][1]]
            if measured != pinned_reason:
                problems.append(f"REASON CHANGED: {name}: still {want[name][0]}, but pinned "
                                f"~{want[name][1]} {pinned_reason!r}, measured {measured!r}")
    return problems


def validate_exit(census_exit: int | None, rows: dict[str, tuple[str, str]]) -> None:
    """The census's own exit status must agree with the rows it wrote.

    It writes TRUSTCG_OUT and THEN exits non-zero unless every row is OK (exit
    1 since 2026-10-19; before, an `assert_eq!` that a release build turned
    into SIGABRT, exit 134), so a non-zero exit is expected exactly when some
    row is not OK. Any other combination means the
    file does not describe the run: a zero exit beside a failing row (the
    check was removed or bypassed), or a non-zero exit with every row OK (the
    process died after writing -- a panic the rows do not show).
    """
    if census_exit is None:
        return
    non_ok = sum(1 for t, _ in rows.values() if t not in OK_TAGS)
    if census_exit == 0 and non_ok:
        raise Refusal(
            f"the census exited 0 while {non_ok} row(s) are not OK: its all-OK check did not "
            f"fire, so this output does not describe the run"
        )
    if census_exit != 0 and not non_ok:
        raise Refusal(
            f"the census exited {census_exit} with every row OK: it died after writing TRUSTCG_OUT, "
            f"so the rows are not the whole story -- read the census log"
        )


def check(tsv: Path, expected_path: Path, census_exit: int | None = None) -> int:
    try:
        text = tsv.read_text()
    except OSError as exc:
        print(f"TRUSTCG_CENSUS=fail reason=no-output: {tsv} is unreadable ({exc}) -- the census "
              f"crashed before writing TRUSTCG_OUT (census exit {census_exit})", file=sys.stderr)
        return 1
    try:
        header, rows = parse_tsv(text)
        validate_run(header, rows)
        validate_exit(census_exit, rows)
        expected = load_expected(expected_path)
    except Refusal as exc:
        print(f"TRUSTCG_CENSUS=fail reason=refused: {exc}", file=sys.stderr)
        return 1
    problems = compare(expected, header, rows)
    ok = sum(1 for t, _ in rows.values() if t in OK_TAGS)
    if problems:
        print(f"TRUSTCG_CENSUS=fail rows={len(rows)} ok={ok} differences={len(problems)}", file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
        print(f"  pin: {expected_path.relative_to(ROOT) if expected_path.is_relative_to(ROOT) else expected_path}",
              file=sys.stderr)
        return 1
    print(f"TRUSTCG_CENSUS=ok rows={len(rows)} ok={ok} non_ok={len(rows) - ok} "
          f"trustcg_version={header.get('trustcg_version')!r} (every row matches its pin)")
    return 0


def write_expected(tsv: Path, expected_path: Path, measured_at: str) -> int:
    try:
        header, rows = parse_tsv(tsv.read_text())
        validate_run(header, rows)
    except (OSError, Refusal) as exc:
        print(f"refusing to pin: {exc}", file=sys.stderr)
        return 1
    counts = tag_counts(t for t, _ in rows.values())
    normalized = {n: normalize_reason(n, d) for n, (t, d) in rows.items() if t not in OK_TAGS}
    reason_ids = {r: f"r{i}" for i, r in enumerate(sorted(set(normalized.values())))}
    doc = {
        "schema": SCHEMA,
        "what_this_is": (
            "The pinned per-root verdict of crates/clean-compiler/examples/trustcg_census.rs "
            "(FULL scope), compared row by row by scripts/check_trustcg_census.py in the "
            "`trustcg-census` gate leg (opt-in: CLEAN_TRUSTCG_CENSUS=1 + "
            "TRUSTCG_BIN). Any changed, missing or new row -- or a failing row whose normalised "
            "REASON changed -- fails the leg by name; re-pin with --write-expected in the commit "
            "that explains the change. A failing verdict is `<TAG> ~<id>`, citing `reasons`."
        ),
        "measured_at": measured_at,
        "trustcg_version": header.get("trustcg_version", ""),
        "full_population": int(header.get("full_population", "0") or 0),
        "counts": counts,
        "reasons": {rid: r for r, rid in sorted(reason_ids.items(), key=lambda kv: int(kv[1][1:]))},
        "verdicts": {
            name: rows[name][0] if name not in normalized else f"{rows[name][0]} ~{reason_ids[normalized[name]]}"
            for name in sorted(rows)
        },
    }
    expected_path.write_text(json.dumps(doc, indent=1, sort_keys=False) + "\n")
    print(f"pinned {len(rows)} verdicts ({counts}) to {expected_path}")
    return 0


# ── self-test ────────────────────────────────────────────────────────────────

def _tsv(rows: list[tuple[str, str, str]], *, scope: str = '"FULL"', limit: str = "None",
         version: str = '"trust-cg 0.6.0"', selected: int | None = None, ok: int | None = None,
         population: int | None = None, header: bool = True) -> str:
    n_ok = sum(1 for _, t, _ in rows if t in OK_TAGS)
    head = (f'# scope={scope} requested_limit={limit} trustcg_bin="/x/trust-cg" '
            f'trustcg_version={version} total_constants=9 non_computable=1 lower_err=0 '
            f'theorems=1 opaque=0 axiomkind=0 '
            f'full_population={len(rows) if population is None else population} '
            f'selected_defs={len(rows) if selected is None else selected} '
            f'ok={n_ok if ok is None else ok} tv_status_certified_roots=0 '
            f'tv_status_certified_decls=0 tv_status_rechecked=false\n')
    body = "".join(f"{n}\t{t}\t{d}\n" for n, t, d in rows)
    return (head if header else "") + body


BASE = [("Nat.add", "OK_CHECKED", ""), ("Nat.succ", "OK", ""),
        ("String.push", "LINK_FAIL", "undefined l_String_push")]
# The shape of the pinned reason, verbatim from a 2026-09-18 census row.
TCG_REASON = ("trust-cg: error: compilation of '{tmp}/root.tmbc' failed: adapter error: function "
              "`{root}` is affirmatively ungated (`body_gate: ungated`, trust-ir v41): the producer "
              "states that no verification gate was applied to this body, so codegen refuses it")
# A RUN_FAIL whose quoted driver output spans two lines, written raw.
BASE_TSV_SPLIT = _tsv(BASE[:2] + [("String.push", "RUN_FAIL", "wrong value: got `1\n2` want `1`")])


def selftest() -> int:
    passed = failed = 0
    with tempfile.TemporaryDirectory(prefix="trustcg-census-selftest.") as tmp:
        d = Path(tmp)
        exp = d / "expected.json"
        base_tsv = d / "base.tsv"
        base_tsv.write_text(_tsv(BASE))
        exp_tcg = d / "expected_tcg.json"
        tcg_tsv = d / "tcg.tsv"
        tcg_tsv.write_text(_tsv(BASE + [("Nat.pred", "TRUSTCG_FAIL", TCG_REASON.format(
            tmp="/var/folders/kb/wcv/T/.tmpubJ3FC", root="Nat.pred"))]))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            assert write_expected(base_tsv, exp, "selftest") == 0
            assert write_expected(tcg_tsv, exp_tcg, "selftest") == 0

        def arm(name: str, want_rc: int, text: str | None, needle: str = "",
                expected: Path = exp, census_exit: int | None = None) -> None:
            nonlocal passed, failed
            f = d / "run.tsv"
            if text is None:
                f.unlink(missing_ok=True)
            else:
                f.write_text(text)
            err = io.StringIO()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                rc = check(f, expected, census_exit)
            if rc == want_rc and needle in err.getvalue():
                passed += 1
                print(f"  ok   {name}")
            else:
                failed += 1
                print(f"  FAIL {name} (want rc={want_rc} needle={needle!r}, got rc={rc}): {err.getvalue()[:300]}")

        arm("the pinned run itself passes", 0, _tsv(BASE))
        arm("the pinned run passes with the census's expected non-zero exit", 0, _tsv(BASE),
            census_exit=101)
        arm("a zero exit beside a failing row is refused", 1, _tsv(BASE), "exited 0 while 1 row",
            census_exit=0)
        arm("a non-zero exit with every row OK is refused", 1, _tsv(BASE[:2]),
            "exited 101 with every row OK", census_exit=101)
        arm("a regressed root is refused BY NAME", 1,
            _tsv([BASE[0], ("Nat.succ", "TRUSTCG_FAIL", "unsupported"), BASE[2]]), "REGRESSED: Nat.succ")
        arm("an unreviewed improvement is refused BY NAME", 1,
            _tsv([BASE[0], BASE[1], ("String.push", "OK", "")]), "IMPROVED: String.push")
        arm("a same-count swap is refused (a count ratchet would pass it)", 1,
            _tsv([BASE[0], ("Nat.succ", "RUN_FAIL", "wrong"), ("String.push", "OK", "")]),
            "REGRESSED: Nat.succ")
        arm("a fail-to-fail change is refused", 1,
            _tsv([BASE[0], BASE[1], ("String.push", "TRUSTCG_FAIL", "x")]), "CHANGED: String.push")
        arm("a vanished root is refused", 1, _tsv(BASE[:2]), "MISSING ROOT: String.push")
        arm("a new root is refused", 1, _tsv(BASE + [("Nat.zero", "OK", "")]), "NEW ROOT: Nat.zero")
        arm("a LIMITED run is refused before comparison", 1,
            _tsv(BASE[:1], scope='"LIMITED — NOT FULL QUALIFICATION"', limit="Some(1)"), "not \"FULL\"")
        arm("a zero-row run is refused", 1, _tsv([]), "ZERO verdict rows")
        arm("a truncated file (header count > rows) is refused", 1, _tsv(BASE, selected=4),
            "selected_defs=4")
        arm("an edited OK count is refused", 1, _tsv(BASE, ok=3), "ok=3")
        arm("a FULL run whose full_population is not its row count is refused", 1,
            _tsv(BASE, population=4), "full_population=4")
        arm("a headerless file is refused", 1, _tsv(BASE, header=False), "before the `# scope=...` header")
        arm("an unknown verdict tag is refused", 1,
            _tsv([BASE[0], ("Nat.succ", "MAYBE", ""), BASE[2]]), "unknown verdict tag 'MAYBE'")
        arm("a duplicate root is refused", 1, _tsv(BASE + [BASE[0]]), "duplicate root")
        arm("a different trust-cg version is refused", 1, _tsv(BASE, version='"trust-cg 0.7.0"'),
            "TRUSTCG VERSION")
        arm("a missing TSV (census crashed early) is refused", 1, None, "no-output")
        # WS6.0 review, adversarial: a same-tag failure whose REASON changed.
        # With 1001 of 1002 roots TRUSTCG_FAIL for one reason, a trust-cg that
        # crashed on every module was still TRUSTCG_FAIL everywhere, and a
        # tag-only pin passed it.
        arm("a same-tag failure whose REASON changed is refused BY NAME", 1,
            _tsv([BASE[0], BASE[1], ("String.push", "LINK_FAIL", "undefined l_String_pop")]),
            "REASON CHANGED: String.push")
        arm("a reason differing only in its temp dir and own root name passes (a re-run is not refused)", 0,
            _tsv(BASE + [("Nat.pred", "TRUSTCG_FAIL", TCG_REASON.format(tmp="/tmp/.tmpZZ9", root="Nat.pred"))]),
            expected=exp_tcg)
        arm("a trust-cg crash in place of its pinned refusal is refused BY NAME", 1,
            _tsv(BASE + [("Nat.pred", "TRUSTCG_FAIL", "trust-cg nonzero, empty stderr")]),
            "REASON CHANGED: Nat.pred", expected=exp_tcg)
        arm("another root's name in the reason is NOT normalised away", 1,
            _tsv(BASE + [("Nat.pred", "TRUSTCG_FAIL", TCG_REASON.format(tmp="/tmp/.tmpZZ9", root="Nat.succ"))]),
            "REASON CHANGED: Nat.pred", expected=exp_tcg)
        arm("a detail split across lines is refused, naming the line", 1,
            BASE_TSV_SPLIT, "line 5: not a `<root>")
        cited = d / "cited.json"
        doc = json.loads(exp.read_text())
        doc["verdicts"]["String.push"] = "LINK_FAIL ~r9"
        cited.write_text(json.dumps(doc))
        arm("a pin whose failing row cites no known reason is refused", 1, _tsv(BASE),
            "must pin WHY it fails", cited)
        doc["verdicts"]["String.push"] = "LINK_FAIL"
        cited.write_text(json.dumps(doc))
        arm("a pin whose failing row pins no reason at all is refused", 1, _tsv(BASE),
            "must pin WHY it fails", cited)
        # The pin's summary is derived from its verdicts; each summary field,
        # edited alone over otherwise-valid verdicts, is refused.
        summary = d / "summary.json"
        for what, edit, needle in (
            ("`counts` that is not the tally of its verdicts",
             lambda s: s.update(counts={"OK": 3}), "not the tally of its own verdicts"),
            ("a `full_population` that is not the number of its verdicts",
             lambda s: s.update(full_population=4), "not the number of its verdicts"),
            ("a `reasons` entry no verdict cites",
             lambda s: s["reasons"].update(r9="a stale reason"), "cited by no verdict"),
        ):
            doc = json.loads(exp.read_text())
            edit(doc)
            summary.write_text(json.dumps(doc))
            arm(f"a pin with {what} is refused", 1, _tsv(BASE), needle, summary)
        empty = d / "empty.json"
        empty.write_text(json.dumps({"schema": SCHEMA, "trustcg_version": "trust-cg 0.6.0",
                                     "verdicts": {}}))
        arm("an EMPTY pin is refused (it could never fail)", 1, _tsv(BASE), "ZERO verdicts", empty)
    print(f"TRUSTCG_CENSUS_SELFTEST arms={passed + failed} passed={passed} failed={failed}")
    return 0 if failed == 0 else 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("tsv", nargs="?", type=Path, help="the census TRUSTCG_OUT file")
    ap.add_argument("--expected", type=Path, default=EXPECTED)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--census-exit", type=int, default=None,
                    help="the census process's exit status; checked against the rows it wrote")
    ap.add_argument("--write-expected", metavar="MEASURED_AT",
                    help="re-pin the expectation from this run (a reviewed act); the argument "
                         "records where it was measured, e.g. 'clean <sha>, trust-cg <sha>'")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    if args.tsv is None:
        ap.error("a census TSV is required (or --selftest)")
    if args.write_expected is not None:
        return write_expected(args.tsv, args.expected, args.write_expected)
    return check(args.tsv, args.expected, args.census_exit)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
