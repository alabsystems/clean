#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The two-way half of the tactic family gates: Clean's verdict per row, crossed.

WHY THIS EXISTS
---------------
family_gate.py counted what Clean CLOSES. A row Clean accepts and pinned Lean
rejects read as a pass, so the instrument every tactic fix is judged by could
not see the direction that matters most. Each family now carries a sealed
sidecar of pinned Lean's verdicts (lean_verdicts.py: its rule and checks;
mint_lean_verdicts.py: the only code that runs Lean). This module is what the
gate does with a validated sidecar, and it runs no process at all:

  * `cross` labels each measured row with Lean's verdict and the two-way
    outcome; `totals` counts every kind, plus the in-world subset (a PROBE
    whose every unknown tactic is a MATHLIB_TACTICS name is outside the
    `import Init` world);
  * `ratchet` fails a row that the baseline recorded fail/diverged, that now
    passes, and that Lean rejects (NEW-FALSE-ACCEPT). It is not the baseline
    regression failure, so CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION cannot waive
    it. Mathlib-tactic probes are exempt; a negative never is;
  * `unrecorded_false_accepts` names the in-world false acceptances a baseline
    does not record (a renamed row, a new negative, a deleted baseline), which
    `--update-baseline` refuses unless MANIFEST.json's reviewed
    `two_way_record_exemptions` names them -- so no false acceptance enters
    the record by the side door the ratchet does not watch;
  * `check_artifact` re-crosses a saved v2 artifact with no binary and no
    Lean: 0 ok, 1 failed, 3 UNKNOWN (a minted file it does not measure, or one
    whose bytes moved since -- never a soft green).
"""

from __future__ import annotations

import ast
import json
import re
from collections import Counter
from pathlib import Path

import lean_verdicts as lv

GATE_SCHEMA = "tactic-family-gate-v2"
AGREE_ACCEPT, AGREE_REJECT = "agree-accept", "agree-reject"
FALSE_ACCEPT, FALSE_REJECT = "clean-accepts-lean-rejects", "clean-rejects-lean-accepts"
DIV_ACCEPT, DIV_REJECT = "clean-diverged-lean-accept", "clean-diverged-lean-reject"
OUTCOMES = {("pass", "accept"): AGREE_ACCEPT, ("fail", "reject"): AGREE_REJECT,
            ("pass", "reject"): FALSE_ACCEPT, ("fail", "accept"): FALSE_REJECT,
            ("diverged", "accept"): DIV_ACCEPT, ("diverged", "reject"): DIV_REJECT}
# The tactics a PROBE may name and still be out of world: each is one a
# Mathlib-world file gets from `import Mathlib` (Mathlib.Tactic.*, or its Aesop
# dependency) and pinned Lean under `import Init` does not. Pinned by hand on
# 2026-10-27 (no Mathlib checkout on this host). A token NOT listed is in world
# (fail-closed): a typo, a Clean-only name, or `library_search`, renamed
# `exact?` in Lean v4.3.0 (crates/clean-elab/src/lean4_compat.rs), is a verdict
# on Clean, and Clean accepting it is a false acceptance like any other.
MATHLIB_TACTICS = frozenset({
    "aesop", "cc", "field_simp", "gcongr", "linarith", "nlinarith", "norm_num",
    "positivity", "ring", "tauto",
})
EXIT_UNKNOWN = 3
HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent


def cross(rows: list[dict], doc: dict) -> None:
    """Give each measured row pinned Lean's verdict, class, unknown tactics and
    the two-way outcome."""
    files = doc.get("files", {}) if isinstance(doc, dict) else {}
    for row in rows:
        rec = files.get(row["file"], {}).get("rows", {}).get(row["name"])
        rec = rec if isinstance(rec, dict) else {}
        row["lean_verdict"] = rec.get("verdict")
        row["lean_class"] = rec.get("class")
        row["lean_unknown_tactics"] = rec.get("unknown_tactics")
        row["two_way"] = OUTCOMES.get((row["verdict"], row["lean_verdict"]))


def in_world(row: dict) -> bool:
    """False only for a PROBE pinned Lean rejects as an unknown tactic, every
    one of whose unknown tactics is a MATHLIB_TACTICS name."""
    toks = row.get("lean_unknown_tactics")
    return not (row["kind"] == "probe" and row.get("lean_class") == "unknown-tactic"
                and isinstance(toks, list) and toks and set(toks) <= MATHLIB_TACTICS)


def _negatives(rows: list[dict]) -> tuple[list[str], list[str]]:
    by_name = {r["name"]: r for r in rows}
    ok, unconfirmed = [], []
    for r in rows:
        if r["kind"] != "negative":
            continue
        ctl = by_name.get(r.get("control") or "")
        confirmed = r["verdict"] == "fail" and ctl is not None and ctl["verdict"] == "pass"
        (ok if confirmed else unconfirmed).append(r["name"])
    return sorted(ok), sorted(unconfirmed)


def two_way_rows(rows: list[dict]) -> dict[str, list[str]]:
    """The names behind every count `totals` reports."""
    out = {o: sorted(r["name"] for r in rows if r.get("two_way") == o)
           for o in sorted(set(OUTCOMES.values()))}
    out["clean_accepts_lean_rejects_in_world"] = sorted(
        r["name"] for r in rows if r.get("two_way") == FALSE_ACCEPT and in_world(r))
    out["uncrossed"] = sorted(r["name"] for r in rows if r.get("two_way") is None)
    out["negatives_unconfirmed"] = _negatives(rows)[1]
    return out


def totals(rows: list[dict]) -> dict:
    probes = [r for r in rows if r["kind"] == "probe"]
    false_accepts = [r for r in rows if r.get("two_way") == FALSE_ACCEPT]
    ok, unconfirmed = _negatives(rows)

    def n(outcome: str) -> int:
        return sum(1 for r in rows if r.get("two_way") == outcome)
    return {
        "probes": len(probes),
        "passed": sum(1 for r in probes if r["verdict"] == "pass"),
        "failed": sum(1 for r in probes if r["verdict"] == "fail"),
        "diverged": sum(1 for r in probes if r["verdict"] == "diverged"),
        "rows": len(rows),
        "crossed": sum(1 for r in rows if r.get("two_way") is not None),
        "agree_accept": n(AGREE_ACCEPT),
        "agree_reject": n(AGREE_REJECT),
        "clean_accepts_lean_rejects": len(false_accepts),
        "clean_accepts_lean_rejects_in_world": sum(1 for r in false_accepts if in_world(r)),
        "clean_accepts_lean_rejects_by_kind": dict(sorted(Counter(r["kind"] for r in false_accepts).items())),
        "clean_accepts_lean_rejects_by_class": dict(sorted(
            Counter(str(r.get("lean_class")) for r in false_accepts).items())),
        "clean_rejects_lean_accepts": n(FALSE_REJECT),
        "clean_diverged_lean_accept": n(DIV_ACCEPT),
        "clean_diverged_lean_reject": n(DIV_REJECT),
        "negatives_confirmed": len(ok),
        "negatives_unconfirmed": len(unconfirmed),
    }


def _baseline_verdict(baseline: dict, row: dict) -> tuple[str | None, str | None]:
    """(Clean verdict, Lean verdict) the baseline recorded for this row."""
    rv = baseline.get("row_verdicts")
    if isinstance(rv, dict) and isinstance(rv.get(row["name"]), dict):
        return rv[row["name"]].get("clean"), rv[row["name"]].get("lean")
    if row["kind"] != "probe":
        return None, None  # a v1 baseline records probes only
    for verdict in ("pass", "fail", "diverged"):
        if row["name"] in (baseline.get(verdict) or []):
            return verdict, None
    return None, None


def unrecorded_false_accepts(rows: list[dict], baseline: dict | None, exempt: dict) -> list[str]:
    """In-world rows Clean accepts and Lean rejects that the baseline does not
    record and MANIFEST.json's exemptions do not name: `--update-baseline`
    refuses to record any of them."""
    return sorted(r["name"] for r in rows if r.get("two_way") == FALSE_ACCEPT and in_world(r)
                  and _baseline_verdict(baseline or {}, r)[0] is None and r["name"] not in exempt)


def ratchet(rows: list[dict], baseline: dict | None) -> tuple[list[str], list[str]]:
    """(failures, reports). A failure is NEW-FALSE-ACCEPT: an in-world row,
    baseline fail/diverged, now pass, and minted reject. Lean-side flips and
    rows the baseline does not record are reported here, never failed (the
    unrecorded false acceptances are refused at `--update-baseline`)."""
    failures, reports, unrecorded = [], [], []
    for row in rows:
        if row.get("two_way") is None:
            continue
        before, lean_before = _baseline_verdict(baseline or {}, row)
        if before is None:
            unrecorded.append(row["name"])
            continue
        if lean_before is not None and lean_before != row["lean_verdict"]:
            reports.append(f"Lean-side flip {row['name']}: {lean_before} -> {row['lean_verdict']}")
        if not in_world(row):
            continue
        if before in ("fail", "diverged") and row["verdict"] == "pass" and row["lean_verdict"] == "reject":
            failures.append(f"two-way ratchet -- NEW-FALSE-ACCEPT {row['name']} ({row['kind']} in "
                            f"{row['file']}: baseline {before}, now pass, and pinned Lean rejects "
                            f"it as {row['lean_class']}). Not waivable by "
                            f"CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION.")
    if unrecorded:
        reports.append(f"{len(unrecorded)} crossed row(s) the baseline does not record (reported, "
                       f"never failed): {', '.join(sorted(unrecorded)[:6])}"
                       f"{' ...' if len(unrecorded) > 6 else ''}")
    false_in = unrecorded_false_accepts(rows, baseline, {})
    if false_in:
        reports.append(f"{len(false_in)} of them in world, Clean accepting what pinned Lean rejects: "
                       f"{', '.join(false_in[:6])}{' ...' if len(false_in) > 6 else ''} -- "
                       f"--update-baseline refuses them unless MANIFEST.json "
                       f"{lv.EXEMPTIONS_KEY} names each with a reason")
    return failures, reports


def strict_failure(tot: dict, rows: list[dict]) -> list[str]:
    """Why `--strict` refuses this measurement (empty: it does not)."""
    out = []
    if tot["clean_accepts_lean_rejects"]:
        out.append(f"--strict: clean_accepts_lean_rejects={tot['clean_accepts_lean_rejects']} "
                   f"(in_world={tot['clean_accepts_lean_rejects_in_world']}) -- Clean accepts rows "
                   f"pinned Lean rejects")
    uncrossed = sorted(r["name"] for r in rows if r.get("two_way") is None)
    if uncrossed:
        out.append(f"--strict: {len(uncrossed)} row(s) carry no pinned-Lean verdict: {uncrossed[:6]}")
    if tot["negatives_unconfirmed"]:
        out.append(f"--strict: {tot['negatives_unconfirmed']} negative(s) not confirmed (Clean must "
                   f"fail the negative and pass its control): {_negatives(rows)[1][:6]}")
    return out


def baseline_fields(rows: list[dict], doc: dict) -> dict:
    """What `--update-baseline` records beside the probe lists (v2)."""
    return {
        "row_verdicts": {r["name"]: {"kind": r["kind"], "clean": r["verdict"], "lean": r.get("lean_verdict")}
                         for r in sorted(rows, key=lambda r: r["name"])},
        "lean_mint_seal": doc.get("seal"),
        "lean_world": (doc.get("lean_world") or {}).get("id"),
        "two_way_schema": GATE_SCHEMA,
    }


def _artifact_shape(gate: str, family: str, art) -> str | None:
    if not isinstance(art, dict) or art.get("schema_version") != GATE_SCHEMA:
        got = art.get("schema_version") if isinstance(art, dict) else None
        return (f"{gate}=failed reason=artifact-not-v2 (schema {got!r}; only a "
                f"{GATE_SCHEMA} artifact carries Lean verdicts)")
    if art.get("family") != family or art.get("gate_verdict") != "measured":
        return (f"{gate}=failed reason=artifact-not-a-measurement (family "
                f"{art.get('family')!r}, gate_verdict {art.get('gate_verdict')!r})")
    if not (isinstance(art.get("files"), list) and isinstance(art.get("rows"), list)
            and all(isinstance(x, dict) for x in art["files"] + art["rows"])
            and isinstance(art.get("lean_mint"), dict)):
        return f"{gate}=failed reason=artifact-malformed (files, rows and lean_mint must be present)"
    return None


def check_artifact(gate: str, family: str, art, doc: dict, baseline: dict | None,
                   strict: bool) -> tuple[int, list[str]]:
    """Re-cross a saved v2 artifact against the validated sidecar: no binary,
    no Lean. Exit 0 ok, 1 failed, EXIT_UNKNOWN when a minted file is not
    measured by it or moved since (those rows are UNKNOWN, never green)."""
    shape = _artifact_shape(gate, family, art)
    if shape:
        return 1, [shape]
    lines, bad = [], []
    minted = doc.get("files", {})
    art_files = {f.get("file"): f for f in art["files"]}
    stale = sorted(f for f, rec in art_files.items() if f not in minted
                   or rec.get("fixture_sha256") != minted[f].get("fixture_sha256"))
    missing = sorted(set(minted) - set(art_files))
    unknown = set(stale) | set(missing)
    rows = [dict(r) for r in art["rows"]]
    orphans = {r.get("file") for r in rows} - set(art_files)
    if orphans:
        bad.append(f"rows name file(s) the artifact does not list: {sorted(map(str, orphans))}")
    for fname in sorted(set(art_files) - unknown):
        got = sorted(str(r.get("name")) for r in rows if r.get("file") == fname)
        want = sorted(minted[fname].get("rows") or {})
        if got != want:
            bad.append(f"{fname}: the artifact's rows are not the minted rows (missing="
                       f"{sorted(set(want) - set(got))}, unlisted={sorted(set(got) - set(want))}, "
                       f"{len(got)} rows for {len(want)} names)")
    for r in rows:
        if r.get("file") in unknown or r.get("file") in orphans:
            continue
        rec = minted.get(r.get("file"), {}).get("rows", {}).get(r.get("name"), {})
        if (r.get("lean_verdict"), r.get("lean_class"), r.get("lean_unknown_tactics")) != (
                rec.get("verdict"), rec.get("class"), rec.get("unknown_tactics")):
            bad.append(f"{r.get('name')}: artifact lean_verdict {r.get('lean_verdict')!r} "
                       f"({r.get('lean_class')}, {r.get('lean_unknown_tactics')}) disagrees with the "
                       f"verdict file's {rec.get('verdict')!r} ({rec.get('class')}, "
                       f"{rec.get('unknown_tactics')})")
        elif r.get("two_way") != OUTCOMES.get((r.get("verdict"), r.get("lean_verdict"))):
            bad.append(f"{r.get('name')}: two_way {r.get('two_way')!r} does not follow from "
                       f"verdict {r.get('verdict')!r} and lean_verdict {r.get('lean_verdict')!r}")
    if art["lean_mint"].get("seal") != doc.get("seal"):
        lines.append(f"  NOTE: measured against verdicts sealed {str(art['lean_mint'].get('seal'))[:12]}; "
                     f"the committed ones are sealed {str(doc.get('seal'))[:12]} -- every fresh row is "
                     f"re-crossed against the committed verdicts below")
    derived = totals(rows)
    if any(art.get("totals", {}).get(k) != v for k, v in derived.items()) \
            or art.get("two_way_rows") != two_way_rows(rows):
        bad.append("totals or two_way_rows do not re-derive from the artifact's rows")
    fresh = [r for r in rows if r.get("file") not in unknown]
    failures, reports = ratchet(fresh, baseline)
    lines += [f"  STALE (UNKNOWN, not crossed): {f} changed since the artifact was measured" for f in stale]
    lines += [f"  MISSING (UNKNOWN, not crossed): {f} has minted verdicts the artifact never measured"
              for f in missing]
    lines += [f"  NOTE: {x}" for x in reports]
    problems = bad + failures
    if strict:
        uncrossed_fresh = [r if r.get("file") not in unknown else {**r, "two_way": None} for r in rows]
        problems += strict_failure(totals(uncrossed_fresh), uncrossed_fresh)
        if missing:
            problems.append(f"--strict: {len(missing)} minted file(s) the artifact never measured: {missing}")
    lines += [f"  FAIL: {p}" for p in problems]
    crossed = sum(1 for r in fresh if r.get("two_way") is not None)
    state = "ok" if not failures else f"NEW-FALSE-ACCEPT x{len(failures)}"
    head = ("failed reason=artifact" if problems else
            f"artifact-unknown files={len(unknown)}" if unknown else "artifact-ok")
    lines.append(f"{gate}={head} clean_accepts_lean_rejects={derived['clean_accepts_lean_rejects']} "
                 f"in_world={derived['clean_accepts_lean_rejects_in_world']} "
                 f"crossed={crossed}/{len(rows)} ratchet={state}" + (" strict=on" if strict else ""))
    return (1 if problems else EXIT_UNKNOWN if unknown else 0), lines


def check_saved_artifact(gate: str, family: str, path: Path, doc: dict, baseline_path: Path,
                         strict: bool) -> tuple[int, list[str]]:
    """`--check-artifact`: read a saved artifact and the baseline, then re-cross."""
    try:
        art = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return 1, [f"{gate}=failed reason=cannot-read-artifact ({path}: {exc})"]
    try:
        baseline = json.loads(baseline_path.read_text()) if baseline_path.is_file() else None
    except (OSError, ValueError) as exc:
        return 1, [f"{gate}=failed reason=cannot-read-baseline ({baseline_path}: {exc})"]
    return check_artifact(gate, family, art, doc, baseline, strict)


# `python3 -m unittest scripts.X ...` in an arm's command names a test module the
# arm's verdict depends on.
_ARM_TESTS = re.compile(r"-m\s+unittest((?:\s+scripts\.[\w.]+)+)")


def arm_test_modules(gate_id: str = "family_gate", root: Path = REPO_ROOT) -> list[str]:
    """The test files `gate_id`'s recorded arms run, repo-relative: an arm that
    asks a test BY NAME is vacuous the day that test is renamed or weakened, so
    the file is pinned with the gate (R7)."""
    demos = json.loads((root / "data" / "gate_demonstrations.json").read_text(encoding="utf-8"))
    found = {mod.replace(".", "/") + ".py"
             for arm in (demos.get("arms") or {}).get(gate_id) or []
             for m in _ARM_TESTS.finditer(str(arm.get("command", "")))
             for mod in m.group(1).split()}
    return sorted(found)


def first_party_inputs(gate: Path = HERE / "family_gate.py", root: Path = REPO_ROOT) -> list[str]:
    """The first-party modules `gate` imports, transitively, plus the test
    files its arms run; repo-relative. Derived, never a hand list (R7 pins it)."""
    found: set[str] = set(arm_test_modules(root=root))
    todo = [gate.resolve()]
    while todo:
        src = todo.pop()
        for node in ast.walk(ast.parse(src.read_text(encoding="utf-8"))):
            names = ([a.name for a in node.names] if isinstance(node, ast.Import)
                     else [node.module] if isinstance(node, ast.ImportFrom) and node.module else [])
            for name in names:
                for base in (src.parent, root / "scripts", root):
                    cand = (base / (name.replace(".", "/") + ".py")).resolve()
                    if cand.is_file() and cand != gate.resolve():
                        rel = cand.relative_to(root.resolve()).as_posix()
                        if rel not in found:
                            found.add(rel)
                            todo.append(cand)
                        break
    return sorted(found)
