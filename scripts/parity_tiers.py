#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Ring R3 — generate the frontend parity-tier statement from committed artifacts.

Spine & Lattice §5, Ring R3 (incorporated by reference into
designs/2026-08-22-one-trust-backward-design.md):

  "Parser/elaborator are outside the TCB (kernel re-checks output); their claim
   is fidelity, generated never hand-written: the everyday battery and
   Mathlib-source frontier as ratchets ... Gate R3: ratchets only move up; the
   tier statement is a generated artifact."

This script IS that generator. It emits `data/parity_tiers.json`:
one row per tier, each carrying a MEASURED value, its denominator, the committed
artifact it was read out of, that artifact's own commit/date, and an explicit
staleness label (does the artifact's commit match HEAD?).

THE HOUSE RULE (proven by scripts/evalir_coverage.py): authored/prose numbers
never count. A tier is derived ONLY from a machine-minted artifact that is
tracked by git and clean in the worktree. Where no such artifact exists, the tier
is UNKNOWN and carries the reason plus the exact command that would mint it.
A number typed into a design doc, a plan, a handoff or CLAUDE.md is not a
measurement and is never promoted to one here. Concretely: the
2026-07-12 Mathlib olean milestone's 357/357 + 1123/1123 + 8,908-constant
cross-section exist ONLY as prose in
docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md — the `stamp-verified --json`
output was never committed — so that tier is UNKNOWN, by rule, not by ignorance.

Ratchet semantics (`--check`):

  * A tier REGRESSED  -> hard FAIL, classified `regression`.  This is the Gate R3
    condition: "ratchets only move up".  Each row also carries `guards` —
    secondary quantities pinned in a direction (failures monotone DOWN, passes
    monotone UP) so that a tier cannot be held flat by growing its denominator.
  * A committed tier with no backing artifact -> hard FAIL, `unbacked-tier`.
    This covers both a fabricated row (a name no derivation produces) and
    evidence-loss (a row that claims MEASURED where derivation now says UNKNOWN).
  * Any other drift (value improved, denominator changed, artifact re-minted at a
    new commit, staleness label moved) -> FAIL, `stale`: regenerate. Failing on an
    IMPROVEMENT is deliberate — the committed tier statement is the thing other
    documents quote, so it must not silently understate either.
  * UNKNOWN NEVER SATISFIES AND NEVER VIOLATES. An UNKNOWN row is never
    classified `regression`, and it is never counted toward a green tier count.
    It is the absence of information; it is not rounded in either direction.

`--check` re-derives staleness against the COMMITTED file's `generated_at_head`,
not against the live HEAD, so the gate is stable as HEAD moves. Live staleness
(measured against the actual HEAD now) is printed as advisory, and `--strict-fresh`
promotes it to a failure.

Usage:
  python3 scripts/parity_tiers.py                # derive + write data/parity_tiers.json
  python3 scripts/parity_tiers.py --check        # ratchet gate over the committed file
  python3 scripts/parity_tiers.py --check --strict-fresh
  python3 scripts/parity_tiers.py --self-test    # mutation arms
  python3 scripts/parity_tiers.py --print        # derive + print the tier table
"""

from __future__ import annotations

import argparse
import copy
import datetime as _dt
import glob
import hashlib
import json
import os
import re
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

OUTPUT_PATH = "data/parity_tiers.json"
SCHEMA = "parity-tiers/v1"
RING = "R3"
DESIGN = (
    "designs/2026-08-22-spine-and-lattice-program.md §5 Ring R3, incorporated by reference as the "
    "kernel workstream of designs/2026-08-22-one-trust-backward-design.md (which cites R3's ratchet "
    "machinery at its Layer-B D1(b) obligation)"
)

EVERYDAY_PATH = "reports/everyday-battery.json"
U2_PATH = "reports/u2-battery.json"
SRCELAB_RATCHET_PATH = "data/source_elab_ratchet.json"
SRCELAB_REPORT_GLOB = "reports/source-elab/srcelab-*-g{commit}.json"
SWEEP_DIR = "reports/mathlib-kv-sweep-2026-07-08"
SWEEP_LEGS = ("rerun-results", "tail-results")
MILESTONE_DOC = "docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md"

# Where a committed olean-milestone artifact WOULD live. If any of these ever
# matches, the milestone tier must stop being UNKNOWN and the generator says so
# instead of quietly continuing to report UNKNOWN.
MILESTONE_ARTIFACT_GLOBS = (
    "data/mathlib_kv_milestone*.json",
    "data/mathlib_olean_milestone*.json",
    "reports/mathlib-kv-milestone*/*.json",
    "reports/mathlib-olean-milestone*/*.json",
)

SWEEP_LINE = re.compile(r"^kernel_verified=(\d+) \(values_checked=(\d+)\) failed=(\d+)$")
NO_TARGET = "no checkable target"


class TierError(Exception):
    """Fail-closed: any input we cannot fully account for aborts the run."""


# --------------------------------------------------------------------- git I/O


class Git:
    """The real repository. Every method is injectable for the self-test."""

    def __init__(self, root: str) -> None:
        self.root = root

    def _run(self, *args: str) -> str:
        return subprocess.run(
            ["git", *args],
            cwd=self.root,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()

    def head(self) -> str:
        return self._run("rev-parse", "HEAD")

    def resolve(self, rev: str) -> str | None:
        try:
            return self._run("rev-parse", "--verify", f"{rev}^{{commit}}")
        except subprocess.CalledProcessError:
            return None

    def commit_date(self, sha: str) -> str | None:
        try:
            return self._run("log", "-1", "--format=%ad", "--date=short", sha)
        except subprocess.CalledProcessError:
            return None

    def is_ancestor(self, a: str, b: str) -> bool:
        return (
            subprocess.run(
                ["git", "merge-base", "--is-ancestor", a, b],
                cwd=self.root,
                capture_output=True,
            ).returncode
            == 0
        )

    def commits_between(self, a: str, b: str) -> int | None:
        try:
            return int(self._run("rev-list", "--count", f"{a}..{b}"))
        except (subprocess.CalledProcessError, ValueError):
            return None

    def last_commit_touching(self, path: str) -> tuple[str, str] | None:
        try:
            out = self._run("log", "-1", "--format=%H|%ad", "--date=short", "--", path)
        except subprocess.CalledProcessError:
            return None
        if not out or "|" not in out:
            return None
        sha, date = out.split("|", 1)
        return sha, date

    def dirty_paths(self, path: str) -> list[str]:
        """Tracked-but-modified / untracked entries under `path`. Empty == clean."""
        out = subprocess.run(
            ["git", "status", "--porcelain", "--", path],
            cwd=self.root,
            capture_output=True,
            text=True,
        )
        if out.returncode != 0:
            raise TierError(f"git status failed for {path}: {out.stderr.strip()}")
        return [ln for ln in out.stdout.splitlines() if ln.strip()]

    def is_tracked(self, path: str) -> bool:
        return (
            subprocess.run(
                ["git", "ls-files", "--error-unmatch", "--", path],
                cwd=self.root,
                capture_output=True,
            ).returncode
            == 0
        )


# ------------------------------------------------------------------- utilities


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_json(root: str, rel: str) -> dict:
    path = os.path.join(root, rel)
    if not os.path.isfile(path):
        raise TierError(f"{rel}: artifact missing (nothing measured)")
    try:
        with open(path, encoding="utf-8") as f:
            doc = json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        raise TierError(f"{rel}: unreadable ({e})") from e
    if not isinstance(doc, dict):
        raise TierError(f"{rel}: top level is not an object (schema drift)")
    return doc


def require_committed(git: Git, root: str, rel: str, allow_uncommitted: bool) -> bool:
    """House rule: a tier may only be derived from a COMMITTED artifact."""
    if allow_uncommitted:
        return not git.dirty_paths(rel) and git.is_tracked(rel)
    if not git.is_tracked(rel):
        raise TierError(
            f"{rel}: not tracked by git — an uncommitted artifact is not evidence "
            f"(commit it, or re-run with --allow-uncommitted-sources)"
        )
    dirty = git.dirty_paths(rel)
    if dirty:
        raise TierError(
            f"{rel}: modified in the worktree ({len(dirty)} entr(y|ies)) — the number "
            f"on disk is not the committed number (commit it, or re-run with "
            f"--allow-uncommitted-sources)"
        )
    return True


def staleness(git: Git, head: str, measured_at: str | None) -> dict:
    """Is the artifact's commit HEAD, an ancestor of HEAD, or off-history?"""
    if measured_at is None:
        return {
            "measured_at_commit": None,
            "matches_head": False,
            "relation": "unresolved",
            "commits_behind_head": None,
            "label": "the artifact records no commit; its measurement cannot be placed in history",
        }
    if measured_at == head:
        return {
            "measured_at_commit": measured_at,
            "matches_head": True,
            "relation": "head",
            "commits_behind_head": 0,
            "label": "measured at HEAD",
        }
    if git.is_ancestor(measured_at, head):
        n = git.commits_between(measured_at, head)
        return {
            "measured_at_commit": measured_at,
            "matches_head": False,
            "relation": "ancestor",
            "commits_behind_head": n,
            "label": (
                f"STALE: measured at {measured_at[:9]}, an ANCESTOR of HEAD"
                + (f" ({n} commits behind)" if n is not None else "")
                + " — the value is true of that commit, not of HEAD"
            ),
        }
    return {
        "measured_at_commit": measured_at,
        "matches_head": False,
        "relation": "off-history",
        "commits_behind_head": None,
        "label": (
            f"STALE: measured at {measured_at[:9]}, which is NOT an ancestor of HEAD "
            f"— the measurement is off this history entirely"
        ),
    }


def measured_row(
    *,
    name: str,
    statement: str,
    value: int,
    denominator: int,
    unit: str,
    guards: list[dict],
    sources: list[dict],
    measured_at: dict,
    stale: dict,
    detail: dict,
    does_not_claim: str,
    mint_command: str,
) -> dict:
    if denominator <= 0:
        raise TierError(f"{name}: denominator {denominator} is not positive")
    if not 0 <= value <= denominator:
        raise TierError(f"{name}: value {value} outside 0..{denominator}")
    for g in guards:
        if g["direction"] not in ("up", "down"):
            raise TierError(f"{name}: guard {g['key']} has bad direction {g['direction']!r}")
    return {
        "name": name,
        "status": "measured",
        "statement": statement,
        "value": value,
        "denominator": denominator,
        "unit": unit,
        "ratchet": "up",
        "guards": guards,
        "sources": sources,
        "measured_at": measured_at,
        "staleness": stale,
        "detail": detail,
        "does_not_claim": does_not_claim,
        "mint_command": mint_command,
    }


def unknown_row(
    *,
    name: str,
    statement: str,
    reason: str,
    mint_command: str,
    searched: list[str],
    does_not_claim: str,
) -> dict:
    return {
        "name": name,
        "status": "unknown",
        "statement": statement,
        "value": None,
        "denominator": None,
        "unit": None,
        "ratchet": "up",
        "guards": [],
        "sources": [],
        "measured_at": None,
        "staleness": {
            "measured_at_commit": None,
            "matches_head": False,
            "relation": "unmeasured",
            "commits_behind_head": None,
            "label": "UNKNOWN — nothing was measured, so there is nothing to be stale",
        },
        "reason": reason,
        "searched": searched,
        "does_not_claim": does_not_claim,
        "mint_command": mint_command,
    }


# ---------------------------------------------------------- tier 1: everyday


def derive_everyday_counts(doc: dict, rel: str) -> dict:
    """Fail-closed read of everyday-battery-v1: counts come from per_snippet."""
    if doc.get("schema") != "everyday-battery-v1":
        raise TierError(f"{rel}: schema {doc.get('schema')!r} != 'everyday-battery-v1' (drift)")
    snippets = doc.get("per_snippet")
    if not isinstance(snippets, list) or not snippets:
        raise TierError(f"{rel}: per_snippet missing or empty (schema drift)")
    names, verdicts, provenance = [], [], {}
    for i, s in enumerate(snippets):
        if not isinstance(s, dict):
            raise TierError(f"{rel}: per_snippet[{i}] is not an object (schema drift)")
        for key in ("name", "verdict", "provenance"):
            if not isinstance(s.get(key), str):
                raise TierError(f"{rel}: per_snippet[{i}].{key} missing/not a string (drift)")
        if s["verdict"] not in ("pass", "fail", "diverge"):
            raise TierError(f"{rel}: per_snippet[{i}].verdict {s['verdict']!r} is not a known verdict")
        names.append(s["name"])
        verdicts.append(s["verdict"])
        provenance[s["provenance"]] = provenance.get(s["provenance"], 0) + 1
    if len(names) != len(set(names)):
        raise TierError(f"{rel}: per_snippet contains duplicate snippet names")
    total = len(snippets)
    passed = sum(1 for v in verdicts if v == "pass")
    # The summary fields must agree with the rows they summarize, or the artifact
    # is self-inconsistent and no number may be taken from it.
    if doc.get("total") != total:
        raise TierError(f"{rel}: total field {doc.get('total')} != len(per_snippet) {total}")
    if doc.get("passed") != passed:
        raise TierError(f"{rel}: passed field {doc.get('passed')} != pass verdicts {passed}")
    return {
        "total": total,
        "passed": passed,
        "failed": total - passed,
        "verdicts": {v: verdicts.count(v) for v in sorted(set(verdicts))},
        "provenance": dict(sorted(provenance.items())),
        "generated_at_commit": doc.get("generated_at_commit"),
        "generated_by": doc.get("generated_by"),
        "comparison_basis": doc.get("comparison_basis"),
    }


def tier_everyday(git: Git, root: str, head: str, allow_uncommitted: bool) -> dict:
    rel = EVERYDAY_PATH
    committed = require_committed(git, root, rel, allow_uncommitted)
    doc = load_json(root, rel)
    c = derive_everyday_counts(doc, rel)

    raw = c["generated_at_commit"]
    if not isinstance(raw, str) or not raw:
        raise TierError(f"{rel}: generated_at_commit missing (cannot place the measurement)")
    resolved = git.resolve(raw)
    date = git.commit_date(resolved) if resolved else None
    landed = git.last_commit_touching(rel)

    locked = c["provenance"].get("locked-2026-07-20", 0)
    recon = c["provenance"].get("reconstructed-2026-08-10", 0)

    return measured_row(
        name="everyday-language",
        statement=(
            f"{c['passed']}/{c['total']} everyday-language snippets elaborate through Clean's own "
            f"frontend and are accepted by Clean's kernel."
        ),
        value=c["passed"],
        denominator=c["total"],
        unit="snippets",
        guards=[
            {
                "key": "failed_snippets",
                "value": c["failed"],
                "direction": "down",
                "note": "a snippet added to the battery that FAILS trips this even though `passed` held flat",
            }
        ],
        sources=[
            {
                "path": rel,
                "schema": doc.get("schema"),
                "sha256": sha256_file(os.path.join(root, rel)),
                "tracked_and_clean": committed,
            }
        ],
        measured_at={
            "commit": resolved or raw,
            "commit_short": (resolved or raw)[:9],
            "commit_resolved": resolved is not None,
            "date": date,
            "landed_in_commit": landed[0] if landed else None,
            "landed_on_date": landed[1] if landed else None,
        },
        stale=staleness(git, head, resolved),
        detail={
            "verdicts": c["verdicts"],
            "snippet_provenance": c["provenance"],
            "byte_comparable_to_2026_07_20": locked,
            "reconstructed_not_byte_comparable": recon,
            "comparison_basis": c["comparison_basis"],
        },
        does_not_claim=(
            "Not soundness. The frontend is outside the TCB — every snippet's output is re-checked "
            "by the kernel, so a wrong elaboration shows up as a kernel rejection, not as an unsound "
            f"acceptance. Not Mathlib: these are {c['total']} hand-sized snippets, not library code. "
            f"And only {locked} of the {c['total']} are byte-identical to the 2026-07-20 battery; the "
            f"other {recon} were RECONSTRUCTED from recorded names and failure causes (the original "
            "inputs were lost with an ephemeral scratchpad) and are not byte-comparable to that run."
        ),
        mint_command=c["generated_by"] or "(artifact records no mint command)",
    )


# ---------------------------------------------------------------- tier 2: U2


def derive_u2_counts(doc: dict, rel: str) -> dict:
    if doc.get("schema") != "u2-battery-v1":
        raise TierError(f"{rel}: schema {doc.get('schema')!r} != 'u2-battery-v1' (drift)")
    fixtures = doc.get("fixtures")
    split = doc.get("split")
    if not isinstance(fixtures, dict) or not fixtures:
        raise TierError(f"{rel}: fixtures missing or empty (schema drift)")
    if not isinstance(split, dict):
        raise TierError(f"{rel}: split missing (schema drift)")
    for key in ("pass", "fail_pinned"):
        if not isinstance(split.get(key), list):
            raise TierError(f"{rel}: split.{key} missing or not a list (schema drift)")
    passing = split["pass"]
    failing = split["fail_pinned"]
    if len(passing) != len(set(passing)) or len(failing) != len(set(failing)):
        raise TierError(f"{rel}: split contains duplicate fixture ids")
    overlap = sorted(set(passing) & set(failing))
    if overlap:
        raise TierError(f"{rel}: fixture ids in BOTH split halves: {overlap}")

    by_id: dict[str, str] = {}
    for fname in fixtures:
        fid = fname.split("_", 1)[0]
        if fid in by_id:
            raise TierError(f"{rel}: two fixtures share the id {fid!r}")
        by_id[fid] = fname
    split_ids = set(passing) | set(failing)
    if split_ids != set(by_id):
        only_split = sorted(split_ids - set(by_id))
        only_fx = sorted(set(by_id) - split_ids)
        raise TierError(
            f"{rel}: split does not cover the fixture set exactly "
            f"(in split only: {only_split}; in fixtures only: {only_fx})"
        )

    # A negative pin is only honest if the fixture is declared MUST_FAIL. A
    # fixture that merely fails and got parked in `fail_pinned` is an OPEN GAP
    # wearing a pin's clothes; refuse to derive a tier over it.
    not_must_fail = sorted(f for f in failing if "MUST_FAIL" not in by_id[f])
    if not_must_fail:
        raise TierError(
            f"{rel}: fail_pinned entries whose fixture is NOT declared MUST_FAIL: "
            f"{[(f, by_id[f]) for f in not_must_fail]} — an open gap parked in the negative "
            f"split would silently shrink the denominator of the positive tier"
        )
    return {
        "total": len(by_id),
        "passing": len(passing),
        "fail_pinned": len(failing),
        "fail_pinned_ids": sorted(failing),
        "open_gaps_in_negative_split": len(not_must_fail),
        "commit": doc.get("commit"),
        "gate_command": doc.get("gate_command"),
        "clean_binary_sha256": doc.get("clean_binary_sha256"),
    }


def tier_u2(git: Git, root: str, head: str, allow_uncommitted: bool) -> dict:
    rel = U2_PATH
    committed = require_committed(git, root, rel, allow_uncommitted)
    doc = load_json(root, rel)
    c = derive_u2_counts(doc, rel)

    raw = c["commit"]
    if not isinstance(raw, str) or not raw:
        raise TierError(f"{rel}: commit field missing (cannot place the measurement)")
    resolved = git.resolve(raw)
    date = git.commit_date(resolved) if resolved else None
    landed = git.last_commit_touching(rel)

    return measured_row(
        name="universe-u2",
        statement=(
            f"{c['passing']}/{c['total']} U2 universe-level fixtures land on their pinned verdict as "
            f"POSITIVE passes; the remaining {c['fail_pinned']} are MUST_FAIL fixtures pinned to refuse."
        ),
        value=c["passing"],
        denominator=c["total"],
        unit="fixtures",
        guards=[
            {
                "key": "open_gaps_in_negative_split",
                "value": c["open_gaps_in_negative_split"],
                "direction": "down",
                "note": "must stay 0: every fail-pinned fixture is declared MUST_FAIL, i.e. a sound loud reject",
            }
        ],
        sources=[
            {
                "path": rel,
                "schema": doc.get("schema"),
                "sha256": sha256_file(os.path.join(root, rel)),
                "tracked_and_clean": committed,
            }
        ],
        measured_at={
            "commit": resolved or raw,
            "commit_short": (resolved or raw)[:9],
            "commit_resolved": resolved is not None,
            "date": date,
            "landed_in_commit": landed[0] if landed else None,
            "landed_on_date": landed[1] if landed else None,
        },
        stale=staleness(git, head, resolved),
        detail={
            "fail_pinned": c["fail_pinned"],
            "fail_pinned_ids": c["fail_pinned_ids"],
            "fail_pinned_are_all_must_fail": True,
            "clean_binary_sha256": c["clean_binary_sha256"],
            "negative_pin_semantics": (
                "MUST_FAIL fixtures are pinned REFUSALS (rigid-refusal / ill-typed-in-Lean-too "
                "shapes). They are counted in the denominator and excluded from the numerator: a "
                "MUST_FAIL fixture that starts PASSING is a soundness event, not an improvement."
            ),
        },
        does_not_claim=(
            "Not soundness, and not universe-solver completeness. This is a 45-fixture ladder over "
            "level-inference shapes, not a corpus; passing it says those shapes elaborate and "
            "kernel-check, not that the U2 level solver is complete. The 8 fail-pinned fixtures are "
            "not counted as passes in either direction — some of them (p06, p12) are pinned to refuse "
            "FOREVER because the input is genuinely ill-typed."
        ),
        mint_command=c["gate_command"] or "(artifact records no mint command)",
    )


# ------------------------------------------------- tier 3: Mathlib source elab


def derive_srcelab_counts(ratchet: dict, report: dict, rrel: str, prel: str) -> dict:
    if ratchet.get("schema_version") != "Clean-srcelab-ratchet-v1":
        raise TierError(f"{rrel}: schema {ratchet.get('schema_version')!r} drift")
    if report.get("schema_version") != "Clean-srcelab-report-v1":
        raise TierError(f"{prel}: schema {report.get('schema_version')!r} drift")
    if not ratchet.get("armed"):
        raise TierError(f"{rrel}: ratchet is NOT armed — an unarmed ratchet pins nothing")
    if ratchet.get("counting_basis") != report.get("counting_basis"):
        raise TierError(
            f"counting_basis disagrees: {rrel}={ratchet.get('counting_basis')!r} vs "
            f"{prel}={report.get('counting_basis')!r}"
        )

    files = report.get("files")
    totals = report.get("totals")
    if not isinstance(files, list) or not files:
        raise TierError(f"{prel}: files missing or empty (schema drift)")
    if not isinstance(totals, dict):
        raise TierError(f"{prel}: totals missing (schema drift)")
    for key in ("decl_count", "success_count", "sorry_axioms", "kernel_check_failures"):
        if not isinstance(totals.get(key), int):
            raise TierError(f"{prel}: totals.{key} missing or not an int (schema drift)")

    per_file, seen = {}, set()
    for i, f in enumerate(files):
        if not isinstance(f, dict):
            raise TierError(f"{prel}: files[{i}] is not an object (schema drift)")
        key = f.get("key")
        if not isinstance(key, str):
            raise TierError(f"{prel}: files[{i}].key missing (schema drift)")
        if key in seen:
            raise TierError(f"{prel}: duplicate file key {key!r}")
        seen.add(key)
        for k in ("success_count", "decl_count", "sorry_axioms"):
            if not isinstance(f.get(k), int):
                raise TierError(f"{prel}: files[{i}].{k} missing or not an int (schema drift)")
        per_file[key] = {
            "success": f["success_count"],
            "decls": f["decl_count"],
            "sorry_axioms": f["sorry_axioms"],
        }

    if sum(v["success"] for v in per_file.values()) != totals["success_count"]:
        raise TierError(f"{prel}: per-file success_count does not sum to totals.success_count")
    if sum(v["decls"] for v in per_file.values()) != totals["decl_count"]:
        raise TierError(f"{prel}: per-file decl_count does not sum to totals.decl_count")
    if totals["success_count"] > totals["decl_count"]:
        raise TierError(f"{prel}: success_count exceeds decl_count")

    # The ratchet's baselines are bound to THIS report, field for field. This is
    # the same evidence binding scripts/source_elab_gate.sh --check-artifact
    # enforces, re-derived here independently rather than trusted.
    rfiles = ratchet.get("files")
    if not isinstance(rfiles, dict) or not rfiles:
        raise TierError(f"{rrel}: files map missing or empty (schema drift)")
    if set(rfiles) != set(per_file):
        raise TierError(
            f"pinned-file sets disagree: only in {rrel}: {sorted(set(rfiles) - set(per_file))}; "
            f"only in {prel}: {sorted(set(per_file) - set(rfiles))}"
        )
    for key, rv in rfiles.items():
        pv = per_file[key]
        if rv.get("success_baseline") != pv["success"]:
            raise TierError(
                f"{key}: ratchet baseline {rv.get('success_baseline')} != measured "
                f"success_count {pv['success']} — the baseline is an un-evidenced number"
            )
        if rv.get("decl_count") != pv["decls"]:
            raise TierError(f"{key}: ratchet decl_count {rv.get('decl_count')} != report {pv['decls']}")
        if rv.get("sorry_axioms") != pv["sorry_axioms"]:
            raise TierError(
                f"{key}: ratchet sorry_axioms {rv.get('sorry_axioms')} != report {pv['sorry_axioms']}"
            )
    return {
        "value": totals["success_count"],
        "denominator": totals["decl_count"],
        "sorry_axioms": totals["sorry_axioms"],
        "kernel_check_failures": totals["kernel_check_failures"],
        "per_file": dict(sorted(per_file.items())),
        "counting_basis": report.get("counting_basis"),
        "counting_basis_note": report.get("counting_basis_note"),
        "invocation": report.get("invocation"),
        "commit": report.get("commit"),
        "date": report.get("date"),
        "armed_commit": ratchet.get("armed_commit"),
    }


def tier_source_elab(git: Git, root: str, head: str, allow_uncommitted: bool) -> dict:
    rrel = SRCELAB_RATCHET_PATH
    if not os.path.isfile(os.path.join(root, rrel)):
        return unknown_row(
            name="mathlib-source-elab",
            statement="Mathlib SOURCE elaboration through Clean's own frontend — UNKNOWN.",
            reason=f"{rrel} is not present: no armed source-elab ratchet exists in this checkout.",
            mint_command="scripts/source_elab_gate.sh --jobs 2 --update",
            searched=[rrel, "reports/source-elab/srcelab-*.json"],
            does_not_claim="Nothing. There is no number here to claim.",
        )
    require_committed(git, root, rrel, allow_uncommitted)
    ratchet = load_json(root, rrel)

    armed = ratchet.get("armed_commit")
    if not isinstance(armed, str) or not armed:
        raise TierError(f"{rrel}: armed_commit missing — the baselines are not bound to a measurement")
    pattern = SRCELAB_REPORT_GLOB.format(commit=armed)
    matches = sorted(glob.glob(os.path.join(root, pattern)))
    if not matches:
        return unknown_row(
            name="mathlib-source-elab",
            statement="Mathlib SOURCE elaboration through Clean's own frontend — UNKNOWN.",
            reason=(
                f"{rrel} is armed at {armed} but no committed report matches {pattern}: the "
                f"baselines have no evidence file in this checkout, so no tier may be derived."
            ),
            mint_command="scripts/source_elab_gate.sh --jobs 2 --update",
            searched=[rrel, pattern],
            does_not_claim="Nothing. There is no evidenced number here to claim.",
        )
    if len(matches) > 1:
        raise TierError(
            f"{pattern}: {len(matches)} reports match the armed commit; the evidence file is ambiguous"
        )
    prel = os.path.relpath(matches[0], root)
    pcommitted = require_committed(git, root, prel, allow_uncommitted)
    rcommitted = require_committed(git, root, rrel, allow_uncommitted)
    report = load_json(root, prel)
    c = derive_srcelab_counts(ratchet, report, rrel, prel)

    if c["commit"] != armed:
        raise TierError(f"{prel}: report commit {c['commit']!r} != ratchet armed_commit {armed!r}")

    resolved = git.resolve(armed)
    date = git.commit_date(resolved) if resolved else None
    landed = git.last_commit_touching(prel)
    per_file = c["per_file"]

    return measured_row(
        name="mathlib-source-elab",
        statement=(
            f"{c['value']}/{c['denominator']} declarations across {len(per_file)} pinned real "
            f"Mathlib SOURCE files elaborate through Clean's own frontend under "
            f"`{c['counting_basis']}`."
        ),
        value=c["value"],
        denominator=c["denominator"],
        unit="declarations",
        guards=[
            {
                "key": "kernel_check_failures",
                "value": c["kernel_check_failures"],
                "direction": "down",
                "note": "declarations the frontend produced that Clean's KERNEL then rejected",
            },
            {
                "key": "sorry_axioms",
                "value": c["sorry_axioms"],
                "direction": "down",
                "note": "run-wide sorry counter; the basis folds sorry-tainted decls into successes",
            },
        ]
        + [
            {
                "key": f"success:{k}",
                "value": v["success"],
                "direction": "up",
                "note": f"per-file floor, {v['success']}/{v['decls']}",
            }
            for k, v in per_file.items()
        ],
        sources=[
            {
                "path": prel,
                "schema": report.get("schema_version"),
                "sha256": sha256_file(matches[0]),
                "tracked_and_clean": pcommitted,
            },
            {
                "path": rrel,
                "schema": ratchet.get("schema_version"),
                "sha256": sha256_file(os.path.join(root, rrel)),
                "tracked_and_clean": rcommitted,
            },
        ],
        measured_at={
            "commit": resolved or armed,
            "commit_short": armed,
            "commit_resolved": resolved is not None,
            "date": c["date"] or date,
            "landed_in_commit": landed[0] if landed else None,
            "landed_on_date": landed[1] if landed else None,
        },
        stale=staleness(git, head, resolved),
        detail={
            "per_file": {k: f"{v['success']}/{v['decls']}" for k, v in per_file.items()},
            "counting_basis": c["counting_basis"],
            "counting_basis_note": c["counting_basis_note"],
            "invocation": c["invocation"],
            "corpus": "mathlib4 v4.30.0-rc2 (CLEAN_MATHLIB_DIR), per the ratchet's arming record",
        },
        does_not_claim=(
            "NOT sorry-free. counting_basis=allow_sorry_success: Clean-check-report-v1 carries no "
            f"per-decl sorry-taint field, so sorry-tainted declarations are folded into the "
            f"{c['value']} and taint is visible only as the run-wide sorry_axioms counter "
            f"({c['sorry_axioms']}). Not soundness either: {c['kernel_check_failures']} declarations "
            "were elaborated and then REJECTED by Clean's kernel — which is the frontend being outside "
            "the TCB working as designed, not a hole. And not Mathlib coverage: five files, chosen to "
            "span failure classes, are not the library."
        ),
        mint_command="scripts/source_elab_gate.sh --jobs 2 --update",
    )


# ------------------------------------------------ tier 4: olean recheck (KV)


def read_sweep_leg(root: str, leg: str) -> tuple[dict, list[str], list[str]]:
    """Machine-minted per-module records: `kernel_verified=N (values_checked=M) failed=K`."""
    d = os.path.join(root, SWEEP_DIR, leg)
    if not os.path.isdir(d):
        raise TierError(f"{SWEEP_DIR}/{leg}: sweep leg directory missing")
    rows, empty, no_target = {}, [], []
    for path in sorted(glob.glob(os.path.join(d, "*.txt"))):
        key = os.path.basename(path)
        try:
            with open(path, encoding="utf-8") as f:
                text = f.read().strip()
        except OSError as e:
            raise TierError(f"{leg}/{key}: unreadable ({e})") from e
        if not text:
            empty.append(key)
            continue
        lines = [ln for ln in text.splitlines() if ln.strip()]
        if len(lines) == 1 and lines[0].strip() == NO_TARGET:
            no_target.append(key)
            continue
        if len(lines) != 1:
            raise TierError(f"{leg}/{key}: expected one record line, found {len(lines)} (drift)")
        m = SWEEP_LINE.match(lines[0])
        if not m:
            raise TierError(f"{leg}/{key}: unparseable record {lines[0]!r} (drift)")
        kv, vc, failed = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if kv + failed != vc:
            raise TierError(
                f"{leg}/{key}: kernel_verified {kv} + failed {failed} != values_checked {vc} "
                f"(the record does not add up)"
            )
        rows[key] = (kv, vc, failed)
    if not rows:
        raise TierError(f"{SWEEP_DIR}/{leg}: no parseable module records")
    return rows, empty, no_target


def merge_sweep(legs: dict[str, dict]) -> dict:
    """Union by module, CONSERVATIVE on disagreement (fewest constants claimed)."""
    merged: dict[str, tuple[int, int, int]] = {}
    disagreements = []
    names = sorted(legs)
    for leg in names:
        for key, rec in legs[leg].items():
            if key not in merged:
                merged[key] = rec
                continue
            if merged[key] != rec:
                disagreements.append(key)
                if rec[0] < merged[key][0]:
                    merged[key] = rec
    kv = sum(v[0] for v in merged.values())
    vc = sum(v[1] for v in merged.values())
    failed = sum(v[2] for v in merged.values())
    if kv + failed != vc:
        raise TierError("merged sweep totals do not add up (kernel_verified + failed != values_checked)")
    return {
        "modules": len(merged),
        "kernel_verified": kv,
        "values_checked": vc,
        "failed": failed,
        "modules_with_failures": sum(1 for v in merged.values() if v[2] > 0),
        "disagreements": sorted(set(disagreements)),
    }


def tier_olean_sweep(git: Git, root: str, head: str, allow_uncommitted: bool) -> dict:
    require_committed(git, root, SWEEP_DIR, allow_uncommitted)
    legs, empties, no_targets, digest_parts = {}, {}, {}, []
    for leg in SWEEP_LEGS:
        rows, empty, no_target = read_sweep_leg(root, leg)
        legs[leg] = rows
        empties[leg] = len(empty)
        no_targets[leg] = len(no_target)
        for key in sorted(rows):
            digest_parts.append(f"{leg}/{key}={rows[key][0]},{rows[key][1]},{rows[key][2]}")
    m = merge_sweep(legs)
    landed = git.last_commit_touching(SWEEP_DIR)
    resolved = landed[0] if landed else None

    return measured_row(
        name="mathlib-olean-recheck-sweep-2026-07-08",
        statement=(
            f"{m['kernel_verified']}/{m['values_checked']} value-bearing Mathlib constants across "
            f"{m['modules']} modules were re-checked by Clean's KERNEL after .olean import "
            f"({m['failed']} rejected, in {m['modules_with_failures']} modules)."
        ),
        value=m["kernel_verified"],
        denominator=m["values_checked"],
        unit="constants",
        guards=[
            {
                "key": "failed_constants",
                "value": m["failed"],
                "direction": "down",
                "note": "constants the kernel REJECTED on re-check",
            },
            {
                "key": "modules_with_failures",
                "value": m["modules_with_failures"],
                "direction": "down",
                "note": "modules carrying at least one rejection",
            },
        ],
        sources=[
            {
                "path": f"{SWEEP_DIR}/{leg}/*.txt",
                "schema": "kernel_verified=N (values_checked=M) failed=K",
                "records": len(legs[leg]),
                "sha256": None,
                "tracked_and_clean": True,
            }
            for leg in SWEEP_LEGS
        ]
        + [
            {
                "path": f"{SWEEP_DIR} (merged record digest)",
                "schema": "sha256 over sorted leg/module=kv,vc,failed",
                "sha256": sha256_text("\n".join(sorted(digest_parts))),
                "tracked_and_clean": True,
            }
        ],
        measured_at={
            "commit": resolved,
            "commit_short": resolved[:9] if resolved else None,
            "commit_resolved": resolved is not None,
            "date": landed[1] if landed else None,
            "landed_in_commit": resolved,
            "landed_on_date": landed[1] if landed else None,
            "measurement_date": "2026-07-08 (the sweep itself; archived into git 2026-08-04)",
        },
        stale=staleness(git, head, resolved),
        detail={
            "merge_rule": (
                "union by module across rerun-results and tail-results; on disagreement the "
                "CONSERVATIVE record (fewest constants claimed) wins"
            ),
            "modules_disagreeing_between_legs": len(m["disagreements"]),
            "disagreeing_modules": m["disagreements"],
            "modules_excluded_no_checkable_target": no_targets,
            "modules_excluded_no_output": empties,
            "corpus": "mathlib4 pin fabf563a7c95a166b8d7b6efca11c8b4dc9d911f, lean4 v4.31.0",
            "verifier": "clean release binary built 2026-07-07 at clean a1d9aef8",
        },
        does_not_claim=(
            "This is NOT the 2026-07-12 milestone and NOT source elaboration. It is a PAUSED sweep "
            "over a DIFFERENT corpus pin (mathlib431 / lean4 v4.31.0, not v4.30.0-rc2), and it "
            "re-checks PRE-ELABORATED terms imported from .olean — Clean's parser and elaborator "
            "never ran on them. It therefore says nothing about the frontend and cannot be quoted as "
            "Mathlib coverage: the sweep stopped at 6,441 of ~8,169 modules on memory pressure. "
            "Excluded module files (no checkable target, no output) are reported above rather than "
            "folded into either side of the fraction."
        ),
        mint_command=(
            "clean mathverse per-constant-verify --all-declared <module.olean> "
            "--closure-root <mathlib>/.lake/build/lib/lean"
        ),
    )


def tier_olean_milestone(root: str) -> dict:
    """The 2026-07-12 milestone tier. Prose-only -> UNKNOWN, by the house rule."""
    found = []
    for pattern in MILESTONE_ARTIFACT_GLOBS:
        found.extend(sorted(os.path.relpath(p, root) for p in glob.glob(os.path.join(root, pattern))))
    if found:
        raise TierError(
            f"a committed olean-milestone artifact now EXISTS ({found}) but this generator still "
            f"reports the tier UNKNOWN — wire the artifact into tier_olean_milestone() rather than "
            f"letting an available measurement read as unmeasured"
        )
    doc_exists = os.path.isfile(os.path.join(root, MILESTONE_DOC))
    return unknown_row(
        name="mathlib-olean-recheck-milestone",
        statement=(
            "The 2026-07-12 Mathlib olean kernel-recheck milestone (Logic/Basic, "
            "Algebra/Group/Defs, and the 40-module cross-section) — UNKNOWN."
        ),
        reason=(
            f"The milestone's counts (357/357, 1123/1123, and a 40-module / 8,908-constant "
            f"cross-section) exist ONLY as prose in {MILESTONE_DOC}"
            + (" (present in this checkout)" if doc_exists else " (doc absent from this checkout)")
            + ". The commands that produced them wrote their JSON to a `--out-dir` that was never "
            "committed, so no machine-minted artifact backs those numbers here. Under the house rule "
            "(scripts/evalir_coverage.py: measured rows only, authored ones never), a number typed "
            "into a plan is not a measurement, and this generator will not promote one. UNKNOWN "
            "neither satisfies nor violates the R3 ratchet."
        ),
        mint_command=(
            "target/release/clean mathverse stamp-verified "
            "<mathlib>/.lake/build/lib/lean/Mathlib/Logic/Basic.olean "
            "--out-dir data/mathlib_kv_milestone --closure-root "
            "<mathlib>/.lake/build/lib/lean --json   # then commit the emitted summary JSON, "
            "and repeat for Mathlib/Algebra/Group/Defs.olean"
        ),
        searched=list(MILESTONE_ARTIFACT_GLOBS) + [MILESTONE_DOC + " (prose — not evidence)"],
        does_not_claim=(
            "Nothing is claimed. In particular this row must NOT be read as a denial that the "
            "milestone happened — only that no committed artifact in this checkout evidences it. "
            "The neighbouring mathlib-olean-recheck-sweep-2026-07-08 row is a DIFFERENT corpus pin "
            "and is not a substitute for it."
        ),
    )


# --------------------------------------------------------------------- derive


def derive(root: str, git: Git, head: str | None = None, allow_uncommitted: bool = False) -> dict:
    head = head or git.head()
    tiers = [
        tier_everyday(git, root, head, allow_uncommitted),
        tier_u2(git, root, head, allow_uncommitted),
        tier_source_elab(git, root, head, allow_uncommitted),
        tier_olean_milestone(root),
        tier_olean_sweep(git, root, head, allow_uncommitted),
    ]
    names = [t["name"] for t in tiers]
    if len(names) != len(set(names)):
        raise TierError(f"duplicate tier names: {names}")
    measured = [t for t in tiers if t["status"] == "measured"]
    unknown = [t for t in tiers if t["status"] == "unknown"]
    return {
        "schema": SCHEMA,
        "ring": RING,
        "design": DESIGN,
        "derived_by": "scripts/parity_tiers.py",
        "rule": (
            "Every tier is derived from a COMMITTED machine-minted artifact. Authored/prose numbers "
            "never count (the house rule proven by scripts/evalir_coverage.py). Where no such "
            "artifact exists the tier is UNKNOWN with its reason and the exact command that would "
            "mint it; UNKNOWN never satisfies and never violates the ratchet. `value` is monotone UP "
            "and each `guards` entry is monotone in its stated direction; `--check` fails a "
            "regression as `regression` and any other drift as `stale`. The MINT enforces the same "
            "directions: since 2026-09-14 a bare run REFUSES to write a fallen number and names it, "
            "because `--check` compares this file against a fresh derivation and re-minting first "
            "therefore compared the file with itself. A fall lands only through "
            "`--rebase \"<why>\"`, which records the exact (tier, guard, direction, from, to) it "
            "forgives in `rebases` and is matched on all five, so a landed rebase can never forgive "
            "the next fall as well."
        ),
        "outside_the_tcb": (
            "R3 tiers are FIDELITY, not soundness. Clean's parser and elaborator sit outside the "
            "trusted computing base: everything they produce is re-checked by the kernel, so a "
            "frontend defect surfaces as a REJECTION, never as an unsound acceptance. A tier moving "
            "up means more real input gets through; it never means more is trusted."
        ),
        "sources_committed": not allow_uncommitted,
        "generated_at_head": head,
        "rebases": [],
        "summary": {
            "tiers": len(tiers),
            "measured": len(measured),
            "unknown": len(unknown),
            "stale_vs_generation_head": sum(
                1 for t in measured if not t["staleness"]["matches_head"]
            ),
        },
        "tiers": tiers,
    }


def render(result: dict) -> str:
    return json.dumps(result, indent=2, sort_keys=False) + "\n"


def table(result: dict) -> str:
    rows = [
        ("TIER", "MEASURED", "DENOM", "SOURCE", "MEASURED AT", "STALE?"),
        ("-" * 4, "-" * 8, "-" * 5, "-" * 6, "-" * 11, "-" * 6),
    ]
    for t in result["tiers"]:
        if t["status"] == "unknown":
            rows.append((t["name"], "UNKNOWN", "—", "(none)", "—", "n/a"))
            continue
        src = t["sources"][0]["path"]
        m = t["measured_at"]
        st = t["staleness"]
        stale = "no (HEAD)" if st["matches_head"] else f"YES ({st['relation']})"
        rows.append(
            (
                t["name"],
                str(t["value"]),
                str(t["denominator"]),
                src,
                f"{m['commit_short']} {m['date'] or ''}".strip(),
                stale,
            )
        )
    widths = [max(len(r[i]) for r in rows) for i in range(6)]
    out = [
        "  ".join(r[i].ljust(widths[i]) for i in range(6)).rstrip()
        for r in rows
    ]
    s = result["summary"]
    out.append("")
    out.append(
        f"{s['measured']} measured, {s['unknown']} UNKNOWN, "
        f"{s['stale_vs_generation_head']} measured tier(s) stale vs "
        f"{result['generated_at_head'][:9]}"
    )
    return "\n".join(out)


# ---------------------------------------------------------------- check (gate)


def _row_index(doc: dict) -> dict:
    tiers = doc.get("tiers")
    if not isinstance(tiers, list):
        raise TierError("committed artifact: `tiers` missing or not a list")
    out = {}
    for t in tiers:
        if not isinstance(t, dict) or not isinstance(t.get("name"), str):
            raise TierError("committed artifact: a tier row has no name")
        out[t["name"]] = t
    return out


def ratchet_regressions(committed: dict, derived: dict) -> list[dict]:
    """Every ratcheted number that moved the WRONG WAY, structurally.

    `check_tiers` answers the same question in prose, for a human reading a gate
    failure. This answers it as records — {tier, guard, direction, from, to} —
    because the MINT has to act on it: a bare mint used to write whatever it
    derived, so re-minting before `--check` compared the file with itself and
    every ratchet passed. Measured 2026-09-14 on the sibling artifact
    data/spine_scoreboard.json, whose `--ratchet` had exactly this hole.
    """
    out: list[dict] = []
    try:
        cidx, didx = _row_index(committed), _row_index(derived)
    except TierError:
        return out
    for name, crow in cidx.items():
        drow = didx.get(name)
        if drow is None or crow.get("status") != "measured" or drow.get("status") != "measured":
            continue
        cval, dval = crow.get("value"), drow.get("value")
        if isinstance(cval, int) and isinstance(dval, int) and dval < cval:
            out.append({"tier": name, "guard": None, "direction": "up",
                        "from": cval, "to": dval})
        dguards = {g["key"]: g for g in drow.get("guards", []) if isinstance(g, dict)}
        for cg in crow.get("guards", []):
            if not isinstance(cg, dict):
                continue
            dg = dguards.get(cg.get("key"))
            if dg is None:
                continue
            cv, dv = cg.get("value"), dg.get("value")
            if not isinstance(cv, int) or not isinstance(dv, int):
                continue
            direction = cg.get("direction")
            if (direction == "up" and dv < cv) or (direction == "down" and dv > cv):
                out.append({"tier": name, "guard": cg.get("key"),
                            "direction": direction, "from": cv, "to": dv})
    return out


def rebase_entry_for(ledger: list, rec: dict):
    """The ledger entry forgiving EXACTLY this move, or None.

    Matched on all five of (tier, guard, direction, from, to): once the rebase is
    written the committed value IS `to`, so the same entry can never match again,
    and a later drift to a different value finds no entry at all.
    """
    for entry in ledger or []:
        if not isinstance(entry, dict):
            continue
        for row in entry.get("rows") or []:
            if isinstance(row, dict) and all(
                    row.get(k) == rec.get(k)
                    for k in ("tier", "guard", "direction", "from", "to")):
                return entry
    return None


def check_tiers(committed: dict, derived: dict) -> list[dict]:
    """Classify every difference. Empty list == gate green."""
    problems: list[dict] = []
    cidx = _row_index(committed)
    didx = _row_index(derived)

    for name, crow in cidx.items():
        drow = didx.get(name)
        cstatus = crow.get("status")
        if drow is None:
            problems.append(
                {
                    "tier": name,
                    "kind": "unbacked-tier",
                    "detail": (
                        "the committed file carries this tier but derivation produces no such row: "
                        "there is no artifact behind it"
                    ),
                }
            )
            continue
        dstatus = drow.get("status")
        if cstatus == "measured" and dstatus != "measured":
            problems.append(
                {
                    "tier": name,
                    "kind": "unbacked-tier",
                    "detail": (
                        f"committed claims MEASURED but derivation now says {dstatus!r}: the "
                        f"evidence behind the number is gone"
                    ),
                }
            )
            continue
        if cstatus != "measured":
            # UNKNOWN never violates the ratchet. It may still be STALE.
            if crow != drow:
                problems.append(
                    {
                        "tier": name,
                        "kind": "stale",
                        "detail": (
                            "UNKNOWN row differs from derivation (never a ratchet violation, "
                            "but the committed statement is out of date)"
                        ),
                    }
                )
            continue

        # Both measured: the ratchet first, then any other drift.
        cval, dval = crow.get("value"), drow.get("value")
        if not isinstance(cval, int) or not isinstance(dval, int):
            problems.append({"tier": name, "kind": "stale", "detail": "value is not an integer"})
            continue
        if dval < cval:
            problems.append(
                {
                    "tier": name,
                    "kind": "regression",
                    "detail": (
                        f"value REGRESSED {cval} -> {dval} (denominator "
                        f"{crow.get('denominator')} -> {drow.get('denominator')})"
                    ),
                }
            )
        cguards = {g["key"]: g for g in crow.get("guards", []) if isinstance(g, dict)}
        dguards = {g["key"]: g for g in drow.get("guards", []) if isinstance(g, dict)}
        for key, cg in cguards.items():
            dg = dguards.get(key)
            if dg is None:
                problems.append(
                    {"tier": name, "kind": "stale", "detail": f"guard {key!r} disappeared"}
                )
                continue
            cv, dv = cg.get("value"), dg.get("value")
            if not isinstance(cv, int) or not isinstance(dv, int):
                continue
            if cg.get("direction") == "up" and dv < cv:
                problems.append(
                    {
                        "tier": name,
                        "kind": "regression",
                        "detail": f"guard {key!r} (monotone up) REGRESSED {cv} -> {dv}",
                    }
                )
            elif cg.get("direction") == "down" and dv > cv:
                problems.append(
                    {
                        "tier": name,
                        "kind": "regression",
                        "detail": f"guard {key!r} (monotone down) REGRESSED {cv} -> {dv}",
                    }
                )
        if crow != drow and not any(
            p["tier"] == name and p["kind"] == "regression" for p in problems
        ):
            diff = sorted(
                k for k in set(crow) | set(drow) if crow.get(k) != drow.get(k)
            )
            problems.append(
                {
                    "tier": name,
                    "kind": "stale",
                    "detail": f"row differs from derivation in {diff}; regenerate",
                }
            )

    for name in didx:
        if name not in cidx:
            problems.append(
                {
                    "tier": name,
                    "kind": "stale",
                    "detail": "derivation produces this tier but the committed file has no such row",
                }
            )
    return problems


# ------------------------------------------------------------------ self-test


class FakeGit(Git):
    """A repository the arms control completely: no subprocess, no real history."""

    def __init__(self, head_sha: str, ancestors: set[str]) -> None:  # noqa: D107
        super().__init__("/nonexistent")
        self._head = head_sha
        self._ancestors = ancestors

    def head(self) -> str:
        return self._head

    def resolve(self, rev: str) -> str | None:
        return rev if rev in self._ancestors or rev == self._head else None

    def commit_date(self, sha: str) -> str | None:
        return "2026-01-01"

    def is_ancestor(self, a: str, b: str) -> bool:
        return a in self._ancestors and b == self._head

    def commits_between(self, a: str, b: str) -> int | None:
        return 7

    def last_commit_touching(self, path: str) -> tuple[str, str] | None:
        return (self._head, "2026-01-01")

    def dirty_paths(self, path: str) -> list[str]:
        return []

    def is_tracked(self, path: str) -> bool:
        return True


def self_test(root: str) -> int:
    failures = 0

    def ok(name: str, cond: bool, detail: str = "") -> None:
        nonlocal failures
        if cond:
            print(f"  self-test ARM ok: {name}{(' -> ' + detail) if detail else ''}")
        else:
            print(f"  self-test ARM FAILED: {name}{(' -> ' + detail) if detail else ''}")
            failures += 1

    def raises(name: str, fn) -> None:
        nonlocal failures
        try:
            fn()
        except TierError as e:
            print(f"  self-test ARM ok: {name} -> detected ({e})")
            return
        print(f"  self-test ARM FAILED: {name} -> mutation NOT detected")
        failures += 1

    git = Git(root)
    try:
        baseline = derive(root, git)
    except TierError as e:
        print(f"  self-test BASELINE FAILED: real derivation errored: {e}")
        return 1
    print(
        f"  self-test baseline ok: {baseline['summary']['measured']} measured, "
        f"{baseline['summary']['unknown']} UNKNOWN"
    )

    # --- ARM 1: planted regression (primary value goes down).
    def victim_name(doc):
        for t in doc["tiers"]:
            if t["status"] == "measured":
                return t["name"]
        raise TierError("no measured tier to mutate")

    v = victim_name(baseline)
    # The committed file is the FLOOR; the mutation goes on the DERIVED side, which
    # is what a real regression looks like: the artifact re-mints with a lower number.
    regressed = copy.deepcopy(baseline)
    for t in regressed["tiers"]:
        if t["name"] == v:
            t["value"] -= 1
    probs = check_tiers(baseline, regressed)
    ok(
        "planted regression (re-derived value below the committed floor)",
        any(p["kind"] == "regression" and p["tier"] == v for p in probs),
        f"{[p['detail'] for p in probs if p['tier'] == v]}",
    )
    improved = copy.deepcopy(baseline)
    for t in improved["tiers"]:
        if t["name"] == v:
            t["value"] += 1
    probs = check_tiers(baseline, improved)
    ok(
        "an IMPROVEMENT is never a regression (classified stale, so the statement regenerates)",
        bool(probs)
        and all(p["kind"] != "regression" for p in probs)
        and any(p["kind"] == "stale" and p["tier"] == v for p in probs),
        f"{[p['kind'] for p in probs if p['tier'] == v]}",
    )

    # --- ARM 2: planted GUARD regression (a monotone-down guard grew).
    guard_tier = next(
        (t for t in baseline["tiers"] if any(g["direction"] == "down" for g in t.get("guards", []))),
        None,
    )
    if guard_tier is None:
        ok("planted guard regression", False, "no monotone-down guard exists to mutate")
    else:
        regressed = copy.deepcopy(baseline)
        for t in regressed["tiers"]:
            if t["name"] == guard_tier["name"]:
                for g in t["guards"]:
                    if g["direction"] == "down":
                        g["value"] += 1  # failures GREW past the committed ceiling
                        break
        probs = check_tiers(baseline, regressed)
        ok(
            "planted guard regression (monotone-down guard grew past its committed ceiling)",
            any(p["kind"] == "regression" and p["tier"] == guard_tier["name"] for p in probs),
            f"{[p['detail'] for p in probs if p['tier'] == guard_tier['name']]}",
        )
        # And the same arm the other way: a monotone-up per-file floor that dropped.
        up_tier = next(
            (t for t in baseline["tiers"] if any(g["direction"] == "up" for g in t.get("guards", []))),
            None,
        )
        if up_tier is not None:
            regressed = copy.deepcopy(baseline)
            for t in regressed["tiers"]:
                if t["name"] == up_tier["name"]:
                    for g in t["guards"]:
                        if g["direction"] == "up":
                            g["value"] -= 1
                            break
            probs = check_tiers(baseline, regressed)
            ok(
                "planted guard regression (monotone-up per-file floor dropped)",
                any(p["kind"] == "regression" and p["tier"] == up_tier["name"] for p in probs),
                f"{[p['detail'] for p in probs if p['tier'] == up_tier['name']]}",
            )

    # --- ARM 3: planted FABRICATED tier — a row no artifact backs.
    planted = copy.deepcopy(baseline)
    planted["tiers"].append(
        {
            "name": "mathlib-whole-library-source-elab",
            "status": "measured",
            "value": 8169,
            "denominator": 8169,
            "guards": [],
            "sources": [],
        }
    )
    probs = check_tiers(planted, baseline)
    ok(
        "planted fabricated tier (no backing artifact)",
        any(
            p["kind"] == "unbacked-tier" and p["tier"] == "mathlib-whole-library-source-elab"
            for p in probs
        ),
        f"{[p['kind'] for p in probs]}",
    )

    # --- ARM 4: evidence LOST — committed claims measured, derivation says UNKNOWN.
    planted = copy.deepcopy(baseline)
    stripped = copy.deepcopy(baseline)
    for t in stripped["tiers"]:
        if t["name"] == v:
            t["status"] = "unknown"
            t["value"] = None
    probs = check_tiers(planted, stripped)
    ok(
        "evidence lost (committed MEASURED, derivation UNKNOWN)",
        any(p["kind"] == "unbacked-tier" and p["tier"] == v for p in probs),
        f"{[p['kind'] for p in probs]}",
    )

    # --- ARM 5: UNKNOWN never satisfies and never violates.
    unk = next((t for t in baseline["tiers"] if t["status"] == "unknown"), None)
    ok("an UNKNOWN tier exists to test", unk is not None)
    if unk is not None:
        probs = check_tiers(baseline, baseline)
        ok(
            "UNKNOWN never violates (identical file+derivation is green)",
            probs == [],
            f"{probs}",
        )
        ok(
            "UNKNOWN never satisfies (excluded from the measured count)",
            baseline["summary"]["measured"]
            == sum(1 for t in baseline["tiers"] if t["status"] == "measured")
            and unk["name"] not in [
                t["name"] for t in baseline["tiers"] if t["status"] == "measured"
            ],
        )
        # An UNKNOWN row can never be classified a regression, whatever it says.
        planted = copy.deepcopy(baseline)
        for t in planted["tiers"]:
            if t["name"] == unk["name"]:
                t["reason"] = "TAMPERED"
        probs = check_tiers(planted, baseline)
        ok(
            "UNKNOWN drift classifies as stale, never regression",
            probs and all(p["kind"] != "regression" for p in probs if p["tier"] == unk["name"]),
            f"{[p['kind'] for p in probs if p['tier'] == unk['name']]}",
        )

    # --- ARM 6: STALENESS is detected and labelled (pure, injected history).
    fresh = staleness(FakeGit("a" * 40, set()), "a" * 40, "a" * 40)
    ok(
        "staleness: artifact commit == HEAD labelled fresh",
        fresh["matches_head"] and fresh["relation"] == "head",
        f"{fresh['relation']}",
    )
    old = staleness(FakeGit("a" * 40, {"b" * 40}), "a" * 40, "b" * 40)
    ok(
        "staleness: artifact commit is an ANCESTOR of HEAD -> labelled STALE",
        (not old["matches_head"])
        and old["relation"] == "ancestor"
        and "STALE" in old["label"]
        and old["commits_behind_head"] == 7,
        f"{old['label']}",
    )
    off = staleness(FakeGit("a" * 40, set()), "a" * 40, "c" * 40)
    ok(
        "staleness: artifact commit off this history -> labelled STALE/off-history",
        (not off["matches_head"]) and off["relation"] == "off-history" and "STALE" in off["label"],
        f"{off['relation']}",
    )
    unresolved = staleness(FakeGit("a" * 40, set()), "a" * 40, None)
    ok(
        "staleness: artifact records no commit -> unresolved, never fresh",
        not unresolved["matches_head"] and unresolved["relation"] == "unresolved",
    )

    # --- ARM 7: a STALE committed row (its artifact was re-minted) is detected.
    planted = copy.deepcopy(baseline)
    for t in planted["tiers"]:
        if t["name"] == v:
            t["measured_at"]["commit"] = "0" * 40
            t["sources"][0]["sha256"] = "0" * 64
    probs = check_tiers(planted, baseline)
    ok(
        "staleness: committed row pinned to a different artifact commit/sha is detected",
        any(p["kind"] == "stale" and p["tier"] == v for p in probs),
        f"{[p['kind'] for p in probs]}",
    )

    # --- ARM 8: artifact-level fail-closed reads (schema/self-consistency drift).
    ev = load_json(root, EVERYDAY_PATH)

    def ev_mut(f):
        d = copy.deepcopy(ev)
        f(d)
        return d

    raises(
        "everyday: `passed` summary disagrees with per_snippet verdicts",
        lambda: derive_everyday_counts(ev_mut(lambda d: d.__setitem__("passed", d["passed"] - 1)), "<mut>"),
    )
    raises(
        "everyday: `total` summary disagrees with len(per_snippet)",
        lambda: derive_everyday_counts(ev_mut(lambda d: d.__setitem__("total", d["total"] + 1)), "<mut>"),
    )
    raises(
        "everyday: duplicate snippet name",
        lambda: derive_everyday_counts(
            ev_mut(lambda d: d["per_snippet"].append(copy.deepcopy(d["per_snippet"][0]))), "<mut>"
        ),
    )
    raises(
        "everyday: schema drift",
        lambda: derive_everyday_counts(ev_mut(lambda d: d.__setitem__("schema", "v2")), "<mut>"),
    )

    u2 = load_json(root, U2_PATH)

    def u2_mut(f):
        d = copy.deepcopy(u2)
        f(d)
        return d

    raises(
        "u2: a fixture missing from both split halves",
        lambda: derive_u2_counts(u2_mut(lambda d: d["split"]["pass"].pop()), "<mut>"),
    )
    raises(
        "u2: a fixture in BOTH split halves",
        lambda: derive_u2_counts(
            u2_mut(lambda d: d["split"]["fail_pinned"].append(d["split"]["pass"][0])), "<mut>"
        ),
    )
    raises(
        "u2: an OPEN GAP parked in fail_pinned (fixture not declared MUST_FAIL)",
        lambda: derive_u2_counts(
            u2_mut(
                lambda d: (
                    d["split"]["fail_pinned"].append(d["split"]["pass"][0]),
                    d["split"]["pass"].remove(d["split"]["pass"][0]),
                )
            ),
            "<mut>",
        ),
    )

    srr = load_json(root, SRCELAB_RATCHET_PATH)
    armed = srr.get("armed_commit")
    matches = sorted(glob.glob(os.path.join(root, SRCELAB_REPORT_GLOB.format(commit=armed))))
    if not matches:
        ok("srcelab: evidence report present for the armed commit", False, f"armed={armed}")
    else:
        srp = load_json(root, os.path.relpath(matches[0], root))

        def sr_mut(fr, fp):
            a, b = copy.deepcopy(srr), copy.deepcopy(srp)
            fr(a)
            fp(b)
            return a, b

        raises(
            "srcelab: a ratchet baseline that no report evidences",
            lambda: derive_srcelab_counts(
                *sr_mut(
                    lambda a: a["files"][sorted(a["files"])[0]].__setitem__("success_baseline", 999),
                    lambda b: None,
                ),
                "<ratchet>",
                "<report>",
            ),
        )
        raises(
            "srcelab: per-file successes do not sum to totals",
            lambda: derive_srcelab_counts(
                *sr_mut(lambda a: None, lambda b: b["totals"].__setitem__("success_count", 1)),
                "<ratchet>",
                "<report>",
            ),
        )
        raises(
            "srcelab: an UNARMED ratchet pins nothing",
            lambda: derive_srcelab_counts(
                *sr_mut(lambda a: a.__setitem__("armed", False), lambda b: None),
                "<ratchet>",
                "<report>",
            ),
        )
        raises(
            "srcelab: counting_basis disagrees between ratchet and report",
            lambda: derive_srcelab_counts(
                *sr_mut(lambda a: a.__setitem__("counting_basis", "sorry_free"), lambda b: None),
                "<ratchet>",
                "<report>",
            ),
        )

    # --- ARM 9: sweep record arithmetic is enforced.
    raises(
        "sweep: a module record where kernel_verified + failed != values_checked",
        lambda: merge_sweep({"x": {"m.txt": (10, 12, 1)}}),
    )
    merged = merge_sweep({"a": {"m.txt": (10, 10, 0)}, "b": {"m.txt": (4, 4, 0)}})
    ok(
        "sweep: leg disagreement resolves CONSERVATIVELY (fewest constants claimed)",
        merged["kernel_verified"] == 4 and merged["disagreements"] == ["m.txt"],
        f"{merged['kernel_verified']} claimed, disagreements={merged['disagreements']}",
    )

    # --- ARM 10: a committed artifact that is dirty in the worktree is refused.
    class DirtyGit(FakeGit):
        def dirty_paths(self, path: str) -> list[str]:
            return [f" M {path}"]

    raises(
        "uncommitted/dirty artifact is refused as evidence",
        lambda: require_committed(DirtyGit("a" * 40, set()), root, EVERYDAY_PATH, False),
    )

    class UntrackedGit(FakeGit):
        def is_tracked(self, path: str) -> bool:
            return False

    raises(
        "untracked artifact is refused as evidence",
        lambda: require_committed(UntrackedGit("a" * 40, set()), root, EVERYDAY_PATH, False),
    )

    # --- ARM 11: a bad row is refused at construction (value > denominator).
    raises(
        "a tier whose value exceeds its denominator is refused",
        lambda: measured_row(
            name="x",
            statement="",
            value=10,
            denominator=5,
            unit="u",
            guards=[],
            sources=[],
            measured_at={},
            stale={},
            detail={},
            does_not_claim="",
            mint_command="",
        ),
    )

    # --- ARM 12: the MINT's half of the ratchet. `--check` compares the
    # committed file against a fresh derivation, so re-minting first used to
    # make every ratchet pass vacuously. These arms pin the structural records
    # the mint refuses on, and the exact-match rule that keeps a landed rebase
    # from forgiving the NEXT fall as well.
    lowered = copy.deepcopy(baseline)
    vrow = next(r for r in lowered["tiers"] if r["name"] == v)
    committed_high = copy.deepcopy(baseline)
    chigh = next(r for r in committed_high["tiers"] if r["name"] == v)
    chigh["value"] = vrow["value"] + 7
    recs = ratchet_regressions(committed_high, lowered)
    ok("the mint sees a fallen tier value as a structural regression",
       any(r["tier"] == v and r["guard"] is None and r["direction"] == "up"
           and r["from"] == vrow["value"] + 7 and r["to"] == vrow["value"] for r in recs),
       f"{recs}")
    ok("a tier that did not fall produces no record",
       ratchet_regressions(baseline, baseline) == [])

    rec = next(r for r in recs if r["guard"] is None)
    entry = {"date": "2026-09-14", "reason": "self-test", "rows": [dict(rec)]}
    ok("a recorded rebase forgives exactly its own (tier, guard, direction, from, to)",
       rebase_entry_for([entry], rec) is entry)
    for field, value in (("from", rec["from"] + 1), ("to", rec["to"] - 1),
                         ("tier", "not-a-tier"), ("direction", "down")):
        other = dict(rec, **{field: value})
        ok(f"it forgives nothing when {field} differs",
           rebase_entry_for([entry], other) is None)
    ok("an empty ledger forgives nothing", rebase_entry_for([], rec) is None)

    guard_lowered = copy.deepcopy(baseline)
    guard_committed = copy.deepcopy(baseline)
    planted = None
    for crow2, drow2 in zip(guard_committed["tiers"], guard_lowered["tiers"]):
        for cg, dg in zip(crow2.get("guards", []), drow2.get("guards", [])):
            if crow2.get("status") != "measured" or not isinstance(cg.get("value"), int):
                continue
            if cg.get("direction") == "down" and planted is None:
                dg["value"] = cg["value"] + 5
                planted = (crow2["name"], cg["key"], cg["value"], dg["value"])
    if planted is None:
        ok("a monotone-down guard that rose is a regression", True,
           "no measured monotone-down guard in the tree to plant on")
    else:
        name2, key2, from2, to2 = planted
        grecs = ratchet_regressions(guard_committed, guard_lowered)
        ok("a monotone-down guard that rose is a regression",
           any(g["tier"] == name2 and g["guard"] == key2
               and g["from"] == from2 and g["to"] == to2 for g in grecs), f"{grecs}")

    if failures:
        print(f"self-test: {failures} arm(s) FAILED", file=sys.stderr)
        return 1
    print("self-test: all arms green")
    return 0


# ----------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="ratchet gate over the committed artifact")
    ap.add_argument(
        "--check-against",
        metavar="FILE",
        default=None,
        help="with --check: gate against FILE instead of the committed artifact (mutation arms)",
    )
    ap.add_argument(
        "--strict-fresh",
        action="store_true",
        help="with --check: also fail if any measured tier is stale vs the LIVE HEAD",
    )
    ap.add_argument("--self-test", action="store_true", help="run the mutation arms")
    ap.add_argument(
        "--rebase",
        metavar="WHY",
        default=None,
        help="record a dated permission for the ratcheted numbers that FELL, by exact "
             "(tier, guard, direction, from, to), then write. Refuses a reason under 12 "
             "characters and refuses when nothing regressed.",
    )
    ap.add_argument("--print", dest="do_print", action="store_true", help="print the tier table")
    ap.add_argument(
        "--allow-uncommitted-sources",
        action="store_true",
        help="derive from artifacts that are untracked or dirty; stamps sources_committed=false",
    )
    args = ap.parse_args()

    if args.self_test:
        return self_test(REPO_ROOT)

    git = Git(REPO_ROOT)
    out_path = os.path.join(REPO_ROOT, OUTPUT_PATH)

    if args.check:
        gate_path = args.check_against or out_path
        gate_rel = os.path.relpath(gate_path, REPO_ROOT)
        if not os.path.isfile(gate_path):
            print(
                f"parity_tiers: --check: {gate_rel} missing; run without --check first",
                file=sys.stderr,
            )
            return 1
        try:
            with open(gate_path, encoding="utf-8") as f:
                committed = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            print(f"parity_tiers: --check: {gate_rel} unreadable ({e})", file=sys.stderr)
            return 1
        ref_head = committed.get("generated_at_head")
        if not isinstance(ref_head, str) or not ref_head:
            print(f"parity_tiers: --check: {gate_rel} has no generated_at_head", file=sys.stderr)
            return 1
        try:
            derived = derive(
                REPO_ROOT, git, head=ref_head, allow_uncommitted=args.allow_uncommitted_sources
            )
            problems = check_tiers(committed, derived)
        except TierError as e:
            print(f"parity_tiers: --check: FAIL-CLOSED: {e}", file=sys.stderr)
            return 1

        regressions = [p for p in problems if p["kind"] == "regression"]
        unbacked = [p for p in problems if p["kind"] == "unbacked-tier"]
        stale = [p for p in problems if p["kind"] == "stale"]
        for p in regressions + unbacked + stale:
            print(f"  {p['kind'].upper():14s} {p['tier']}: {p['detail']}")

        live_head = git.head()
        live_stale = []
        for t in derived["tiers"]:
            if t["status"] != "measured":
                continue
            s = staleness(git, live_head, t["staleness"]["measured_at_commit"])
            if not s["matches_head"]:
                live_stale.append((t["name"], s["label"]))
        for name, label in live_stale:
            print(f"  {'FRESHNESS':14s} {name}: {label}")

        if problems:
            kinds = {p["kind"] for p in problems}
            print(
                f"parity_tiers: --check FAILED ({len(regressions)} regression, "
                f"{len(unbacked)} unbacked, {len(stale)} stale) [{','.join(sorted(kinds))}]",
                file=sys.stderr,
            )
            return 1
        if args.strict_fresh and live_stale:
            print(
                f"parity_tiers: --check --strict-fresh FAILED: {len(live_stale)} measured tier(s) "
                f"are stale vs live HEAD {live_head[:9]}",
                file=sys.stderr,
            )
            return 1
        s = derived["summary"]
        print(
            f"parity_tiers: --check GREEN — {s['measured']} measured tier(s) hold their ratchet, "
            f"{s['unknown']} UNKNOWN (neither satisfied nor violated), "
            f"{len(live_stale)} stale vs live HEAD"
        )
        return 0

    try:
        result = derive(REPO_ROOT, git, allow_uncommitted=args.allow_uncommitted_sources)
    except TierError as e:
        print(f"parity_tiers: FAIL-CLOSED: {e}", file=sys.stderr)
        return 1

    if args.do_print:
        print(table(result))
        return 0

    # THE MINT IS THE RATCHET'S OTHER HALF. --check compares the committed file
    # against a fresh derivation, so re-minting first made every ratchet pass
    # vacuously: the file it compares IS the file the mint had just rewritten.
    # A regression therefore has to be refused HERE, where the lowering happens,
    # and landed only through a dated --rebase that names the exact move.
    committed = None
    if os.path.isfile(out_path):
        try:
            with open(out_path, encoding="utf-8") as f:
                committed = json.load(f)
        except (OSError, ValueError):
            committed = None
    ledger = []
    if isinstance(committed, dict) and isinstance(committed.get("rebases"), list):
        ledger = [r for r in committed["rebases"] if isinstance(r, dict)]
    result["rebases"] = list(ledger)

    regressions = ratchet_regressions(committed or {}, result)
    fresh = [r for r in regressions if rebase_entry_for(ledger, r) is None]

    if args.rebase is not None:
        reason = args.rebase.strip()
        if len(reason) < 12:
            print(
                "parity_tiers: --rebase REFUSED — a rebase needs a real reason (>= 12 characters) "
                "naming WHY a ratcheted number may fall; it is the only thing a reviewer reads",
                file=sys.stderr)
            return 1
        if not fresh:
            print(
                f"parity_tiers: --rebase REFUSED — nothing regressed against {OUTPUT_PATH}. "
                "A rebase records a fall that HAPPENED; it is never issued in advance",
                file=sys.stderr)
            return 1
        result["rebases"] = ledger + [{
            "date": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%d"),
            "reason": reason,
            "rows": fresh,
        }]
        for r in fresh:
            where = r["tier"] + (f".guard.{r['guard']}" if r["guard"] else "")
            print(f"  REBASED {where}: {r['from']} -> {r['to']} (monotone {r['direction']})")
    elif fresh:
        for r in fresh:
            where = r["tier"] + (f".guard.{r['guard']}" if r["guard"] else "")
            print(f"  REGRESSION {where}: {r['from']} -> {r['to']} (monotone {r['direction']})",
                  file=sys.stderr)
        print(
            f"parity_tiers: REFUSED to write {OUTPUT_PATH} — {len(fresh)} ratcheted number(s) would "
            "fall. Minting is not a way past a ratchet: fix the regression, or record it with "
            'scripts/parity_tiers.py --rebase "<why it may fall>"',
            file=sys.stderr)
        return 1

    with open(out_path, "w", encoding="utf-8") as f:
        f.write(render(result))
    print(f"parity_tiers: wrote {OUTPUT_PATH}")
    print(table(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
