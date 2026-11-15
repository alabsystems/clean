#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Executable fail-closed tactic family gates (G-AUTO, G-SIMP).

Implements the first two §7 family gates of
docs/plans/TACTICS_TO_100_2026-07-29.md as a real script with a real exit
code, honoring the five non-negotiable gate properties (§7.2):

  1. Fail-closed and executable — missing fixtures, a fixture/manifest
     mismatch, an unattributable verdict, or a stub-prelude fallback is a
     gate FAILURE, never a skip.
  2. Axis (c) only — a row passes iff its declaration verdict is a pass with
     no sorry axiom and no kernel-check failure attributed to it. The
     verdict comes from `clean check --json`'s per-declaration accounting
     (success_count / trust_failures / kernel_failures), NEVER from grepping
     error strings as success. Error text is consulted only to ATTRIBUTE
     failures, and any failure that cannot be attributed to a declaration
     fails the gate (the attribution-mismatch check against success_count).

     A row verdict is THREE-WAY, not two-way: `pass`, `fail`, and `diverged`
     — a declaration that spent its whole per-declaration budget without
     finishing. `diverged` is not a pass (nothing was proved) and not a fail
     (nothing was refuted); it is folded into neither, and a baseline-pass row
     that starts diverging is a regression like any other. See DECL_BUDGET
     for why the budget is set at all and how its value was measured.
  3. Real imports — every fixture carries a real `import Init` header. The
     script never passes `--prelude` for a measurement, refuses fixtures
     without the header, and each fixture file carries a term-mode
     environment canary whose failure invalidates the run: builtin-prelude
     numbers overstate parity (§1 insight 3) and are rejected by the gate
     itself.

     The canary's DISCRIMINATING POWER is itself measured, never assumed
     (`--canary-check`, and unconditionally inside every measured run). A
     canary that also passes on `--prelude builtin` cannot detect the
     builtin/stub fallback it exists to detect, so the gate fails closed and
     names it DISARMED. This is not hypothetical: the original canary
     `List.reverse_reverse` was chosen on 2026-08-10 when it was absent from
     the builtin prelude, and commit 3df6e4aad (2026-08-23) registered a
     kernel-proved `List.reverse_reverse` INTO that prelude — silently
     disarming all 13 canaries in both families. Property 3 was thereafter
     asserted by a check that could no longer fail. Nothing detected it,
     because the gate only ever ran the canary in the environment it was
     supposed to be distinguishing FROM the other one.
  4. Family-count comparability — the manifest pins the family denominator
     to the 2026-07-29 measurement (g_auto 131 / g_simp 127); a differing
     fixture count is a gate failure. The comparison basis is
     family-count-level, not probe-identical (stated in the artifact).
  5. Teeth — see scripts/tactic_parity/TEETH.md. Once a baseline is
     recorded (data/tactic_family_baselines/<family>.json, written only by
     --update-baseline from a real run), any baseline-pass row that stops
     passing fails the gate.
  6. Two-way (item 17, 2026-10-27) — every declared row also carries PINNED
     LEAN's verdict, from the sealed LEAN_VERDICTS.json beside its fixture
     (lean_verdicts.py: what --static refuses, and what it cannot see;
     family_two_way.py: the cross, the in-world subset, the unwaivable
     NEW-FALSE-ACCEPT ratchet, --strict, --check-artifact). A measured run
     reports clean_accepts_lean_rejects; --strict, off by default, also
     fails on any false acceptance at all.

Exit codes:
  0  measured (artifact written; verdict line printed)
  1  gate FAILED (fail-closed: integrity violation, canary/required/baseline
     breach, or zero passing probes)
  2  SKIPPED — no prebuilt release binary (never invokes cargo; the machine's
     build capacity belongs to the central verifier)
  3  UNKNOWN (--check-artifact only) — a minted fixture the saved artifact
     does not measure, or one whose bytes moved since; never a soft green

The gate NEVER invokes cargo in any form. It drives the prebuilt release
binary (default target/release/clean, override CLEAN_BIN) and reads its JSON
report and process exit code directly — never through a pipeline that could
swallow the status (§5 cargo caveat).

Usage:
  scripts/tactic_parity/family_gate.py --family g_auto            # measure
  scripts/tactic_parity/family_gate.py --family g_simp --static   # fixture
        integrity only (no binary needed; wired into local_gate.sh fast path)
  scripts/tactic_parity/family_gate.py --family g_auto --update-baseline
  scripts/tactic_parity/family_gate.py --family g_auto --strict   # measure;
        also fail on any row Clean accepts and pinned Lean rejects
  scripts/tactic_parity/family_gate.py --family g_auto --check-artifact [PATH]
        re-check a saved artifact offline (default the family's -latest.json;
        a v1 artifact is refused, one stale against the committed verdicts is
        UNKNOWN). At most one of --static / --canary-check / --check-artifact.
  scripts/tactic_parity/family_gate.py --pinned-inputs   # the first-party
        files its verdict depends on besides itself (check_gate_registry R7)
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# The two-way half (pinned Lean's verdict per row, minted offline into each
# family's LEAN_VERDICTS.json: lean_verdicts.py owns the file, family_two_way.py
# the cross) and the `clean check --json` reader live beside this file and run
# no process. Tests reach them as `family_gate.lv` / `family_gate.ftw`, so only
# one copy of each module is ever loaded.
if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
import family_two_way as ftw  # noqa: E402
import lean_verdicts as lv  # noqa: E402
from clean_report import (  # noqa: E402,F401  (re-exported: the gate's report reader)
    attribute_diverged, attribute_failures, classify_file_verdicts, extract_json_report,
)

# R7 (scripts/check_gate_registry.py): the verdict also depends on the
# first-party modules this file imports and on the test files its arms run;
# `--pinned-inputs` names them, derived by ftw.first_party_inputs().
ANSWERS_PINNED_INPUTS = True

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
FIXTURE_ROOT = REPO_ROOT / "tests" / "fixtures" / "tactic_families"
REPORT_DIR = REPO_ROOT / "reports" / "tactic-families"
BASELINE_DIR = REPO_ROOT / "data" / "tactic_family_baselines"

GATE_NAMES = {"g_auto": "G-AUTO", "g_simp": "G-SIMP"}

# Per-fixture-file wall clock: one `import Init` load measured 108-129 s on
# 2026-07-29; leave generous headroom for a loaded machine before declaring
# the run dead (a timeout is an infrastructure FAILURE, not a skip).
PER_FILE_TIMEOUT_SECS = 1800

# The canary's builtin-prelude control loads no imports at all (measured 0.3 s
# per fixture on 2026-08-27); a minute is already three orders of headroom, and
# exceeding it is a failure, never a skip.
CANARY_CHECK_TIMEOUT_SECS = 60

# Per-declaration kernel-operation budget handed to `clean check`.
#
# WHY IT IS SET AT ALL. Without one, a SINGLE runaway declaration takes the
# whole file's report down with it, and the gate then reads rows it never
# measured as regressions. That is not hypothetical — it is the 2026-08-28
# G-SIMP failure verbatim:
#
#     G-SIMP=failed pass=78/127 baseline=REGRESSED
#       FAIL: local_simp_attrs.lean: timed out after 1800s
#       FAIL: baseline regression — rows recorded passing now fail:
#             [... 'p_simp_local_01', 'p_simp_local_04' ... 'p_simp_local_09']
#
# Seven of those eight "regressions" were rows the run never reached. ONE
# declaration diverges (`p_simp_local_03`, `lsf (lsf n) = n + 1 + 1 := by
# simp`) and fourteen measurements are lost with it. `clean check --decl-budget`
# (60e8747e7) bounds each declaration and reports the runaway as `diverged` —
# its own verdict, neither a pass nor a failure-to-prove — so the other
# fourteen are still measured. The same shape bites G-AUTO: `decide.lean` and
# `norm_num.lean` each hit PER_FILE_TIMEOUT_SECS on 2026-08-27 (see the cost
# note in scripts/local_gate.sh).
#
# WHY THIS VALUE. It is a measurement with a stated margin, not a preference.
# On 2026-08-28 with target/release/clean at 9f035774c, per-declaration ticks
# were read straight off `CLEAN_CHECK_DECL_BUDGET_TRACE=1` over `import Init`
# fixtures: every declaration that PASSES costs at most ~1.3e6 (the dearest
# observed being the module-level import work, itself charged as one
# declaration), while the diverging `simp` rows blow through 2e7 without
# finishing. 5e7 therefore sits ~38x above the dearest passing declaration and
# ~2.5x below nothing that has ever finished — so the budget cannot turn a
# passing row into `diverged`, which is the only direction that would corrupt
# a verdict.
#
# The artifact records this number and each file's `peak_decl_ticks`, so the
# margin above is re-derivable from the report instead of trusted from this
# comment. If a file with NO diverged row ever reports a peak near the budget,
# the margin is gone and this value must be re-measured, not raised by feel.
DECL_BUDGET = 50_000_000

# The row grammar, shared with the sealed sidecar and its minter.
DECL_RE = lv.DECL_RE


def _rel(path: Path) -> str:
    """`path` repo-relative when it is inside the repo (tests point the report
    and baseline directories elsewhere)."""
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def fail(gate: str, reason: str) -> "int":
    print(f"{gate}=failed reason={reason}", flush=True)
    return 1


def load_manifest(family: str) -> dict:
    path = FIXTURE_ROOT / family / "MANIFEST.json"
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        sys.exit(f"{GATE_NAMES.get(family, family)}=failed reason=cannot-read-manifest ({path}: {exc})")


def static_check(family: str, manifest: dict) -> list[str]:
    """Fixture/manifest integrity. Returns a list of violations (empty = ok)."""
    problems: list[str] = []
    fam_dir = FIXTURE_ROOT / family
    files = manifest.get("files", [])
    if not files:
        return [f"manifest lists no files ({fam_dir / 'MANIFEST.json'})"]

    listed = {entry["file"] for entry in files}
    on_disk = {p.name for p in fam_dir.glob("*.lean")}
    for stray in sorted(on_disk - listed):
        problems.append(f"fixture {stray} exists on disk but is not in the manifest (silent-skip hazard)")
    for missing in sorted(listed - on_disk):
        problems.append(f"manifest lists {missing} but the fixture file is missing")

    total_probes = 0
    seen: set[str] = set()
    for entry in files:
        fpath = fam_dir / entry["file"]
        if not fpath.is_file():
            continue  # already reported above
        text = fpath.read_text(encoding="utf-8")

        meaningful = [
            ln.strip()
            for ln in text.splitlines()
            if ln.strip() and not ln.strip().startswith("--") and not ln.strip().startswith("/-")
        ]
        if not meaningful or meaningful[0] != "import Init":
            problems.append(
                f"{entry['file']}: first meaningful line must be `import Init` — "
                f"builtin-prelude fixtures are forbidden (§7.2 property 3)"
            )
        if re.search(r"\bsorry\b|\badmit\b", text):
            problems.append(f"{entry['file']}: fixtures must not contain sorry/admit")

        expected = lv.declared_names(entry)
        for name in expected:
            if name in seen:
                problems.append(f"duplicate declaration name across family: {name}")
            seen.add(name)
        found = DECL_RE.findall(text)
        if sorted(found) != sorted(expected):
            missing_decls = sorted(set(expected) - set(found))
            extra_decls = sorted(set(found) - set(expected))
            problems.append(
                f"{entry['file']}: manifest/fixture declaration mismatch"
                + (f" missing={missing_decls}" if missing_decls else "")
                + (f" unlisted={extra_decls}" if extra_decls else "")
            )
        for req in entry.get("required", []):
            if req not in entry["probes"]:
                problems.append(f"{entry['file']}: required row {req} is not a listed probe")
        total_probes += len(entry["probes"])

    plan_total = manifest.get("plan_family_total")
    if total_probes != plan_total:
        problems.append(
            f"fixture probe count {total_probes} differs from the manifest's pinned "
            f"family denominator {plan_total} — the denominator may not drift "
            f"(family-count comparability vs 2026-07-29)"
        )
    if not manifest.get("comparison_basis"):
        problems.append("manifest is missing the comparison_basis statement")
    return problems


def slice_declaration(fixture_text: str, name: str) -> str | None:
    """Return the source of declaration `name`, from its own `theorem`/`def`
    keyword up to the start of the next declaration (or EOF)."""
    starts = [(m.start(), m.group(1)) for m in DECL_RE.finditer(fixture_text)]
    for i, (pos, decl) in enumerate(starts):
        if decl != name:
            continue
        end = starts[i + 1][0] if i + 1 < len(starts) else len(fixture_text)
        return fixture_text[pos:end]
    return None


def canary_is_disarmed(
    clean_bin: Path, fixture_text: str, canary: str, scratch: Path
) -> tuple[bool, str]:
    """Measure the canary's discriminating power.

    The canary exists to fail when `import Init` silently degrades to the
    builtin/stub prelude. That is only true if the canary CANNOT be proved
    against the builtin prelude — so prove that, per run, instead of
    inheriting it from whenever the name was chosen.

    Returns (disarmed, detail). `disarmed=True` means the canary also passes
    on `--prelude builtin` and is therefore worthless as a fallback detector.
    An unreadable verdict is reported as disarmed: fail-closed.
    """
    body = slice_declaration(fixture_text, canary)
    if body is None:
        return True, f"canary {canary} not found in the fixture text"
    probe = scratch / f"canary_disarm_{canary}.lean"
    probe.write_text(body, encoding="utf-8")
    try:
        proc = subprocess.run(
            [str(clean_bin), "check", "--prelude", "builtin", "--json", str(probe)],
            capture_output=True,
            text=True,
            timeout=CANARY_CHECK_TIMEOUT_SECS,
            cwd=REPO_ROOT,
        )
    except subprocess.TimeoutExpired:
        return True, f"canary {canary}: builtin-prelude control timed out"
    report = extract_json_report(proc.stdout)
    if report is None:
        return True, (
            f"canary {canary}: builtin-prelude control produced no parseable JSON "
            f"(exit {proc.returncode})"
        )
    if report.get("status") == "pass" and report.get("success_count") == report.get("decl_count"):
        return True, (
            f"canary {canary} DISARMED — it also passes on `--prelude builtin`, so it "
            f"cannot detect the builtin/stub fallback it exists to detect. Choose a "
            f"statement whose constants are absent from the builtin prelude (property 3)."
        )
    return False, f"canary {canary}: refuted on the builtin prelude (discriminates)"


def record_blockers(
    gate_failures: list[str], regression_failure: str | None, allow_regression: bool
) -> list[str]:
    """The gate failures that refuse `--update-baseline`.

    With the documented escape hatch open (CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION=1)
    exactly ONE entry is waived: the baseline-regression failure this run
    recorded, matched by identity, never by its text. A canary, a required row,
    a timeout, an unreadable baseline, or another failure that happens to read
    like a regression still refuses the record. Without the hatch nothing is
    waived. Pinned by scripts/test_family_gate.py's RecordBlockersTests.
    """
    blockers = list(gate_failures)
    if allow_regression and regression_failure is not None:
        for i, gf in enumerate(blockers):
            if gf is regression_failure:
                del blockers[i]
                break
    return blockers


def run_canary_checks(family: str, manifest: dict, clean_bin: Path) -> tuple[list[str], dict]:
    """Prove every fixture canary still discriminates. Returns (failures, per-file map)."""
    fam_dir = FIXTURE_ROOT / family
    failures: list[str] = []
    verdicts: dict[str, bool] = {}
    with tempfile.TemporaryDirectory(prefix=f"clean-{family}-canary-") as tmp:
        for entry in manifest["files"]:
            text = (fam_dir / entry["file"]).read_text(encoding="utf-8")
            disarmed, detail = canary_is_disarmed(clean_bin, text, entry["canary"], Path(tmp))
            verdicts[entry["file"]] = not disarmed
            if disarmed:
                failures.append(f"{entry['file']}: {detail}")
    return failures, verdicts


def run_family(
    family: str, manifest: dict, clean_bin: Path, update_baseline: bool, lean_doc: dict,
    strict: bool = False,
) -> int:
    """One measured run. `lean_doc` is the sidecar `main` validated (one read,
    lv.load_checked): every cross below is against it, never a re-read."""
    gate = GATE_NAMES[family]
    fam_dir = FIXTURE_ROOT / family
    rows: list[dict] = []
    file_reports: list[dict] = []

    # Property 3, first half: the canaries must still be able to fail. Measured
    # before the ten-minute import run so a disarmed canary is reported even if
    # the measurement itself goes sideways.
    gate_failures, canary_discriminates = run_canary_checks(family, manifest, clean_bin)
    # Pinned Lean's verdicts, minted offline over exact fixture bytes. Each file
    # is hashed before AND after Clean measures it: a verdict is of the bytes the
    # sidecar was minted over, or it is not crossed at all.
    for entry in manifest["files"]:
        fpath = fam_dir / entry["file"]
        fixture_bytes = fpath.read_bytes()
        digest = lv.sha256_bytes(fixture_bytes)
        if digest != lean_doc.get("files", {}).get(entry["file"], {}).get("fixture_sha256"):
            gate_failures.append(
                f"{entry['file']}: edited without a re-mint of pinned Lean's verdicts; run "
                f"{lv.mint_command(family)}"
            )
            continue
        fixture_text = fixture_bytes.decode("utf-8")
        all_names = lv.declared_names(entry)
        expected_decls = len(all_names)

        try:
            proc = subprocess.run(
                [
                    str(clean_bin),
                    "check",
                    "--json",
                    f"--decl-budget={DECL_BUDGET}",
                    str(fpath),
                ],
                capture_output=True,
                text=True,
                timeout=PER_FILE_TIMEOUT_SECS,
                cwd=REPO_ROOT,
            )
        except subprocess.TimeoutExpired:
            gate_failures.append(f"{entry['file']}: timed out after {PER_FILE_TIMEOUT_SECS}s")
            continue
        if lv.sha256_bytes(fpath.read_bytes()) != digest:
            gate_failures.append(
                f"{entry['file']}: the fixture changed while Clean measured it -- the verdict is "
                f"of bytes that are no longer there"
            )
            continue

        report = extract_json_report(proc.stdout)
        if report is None:
            gate_failures.append(
                f"{entry['file']}: no parseable JSON report on stdout (exit {proc.returncode})"
            )
            continue
        if proc.returncode not in (0, 1):
            gate_failures.append(
                f"{entry['file']}: abnormal binary exit {proc.returncode} (crash/panic is not a verdict)"
            )
            continue
        status = report.get("status")
        if (status == "pass") != (proc.returncode == 0):
            gate_failures.append(
                f"{entry['file']}: report status `{status}` contradicts exit code {proc.returncode}"
            )
            continue

        decl_count = report.get("decl_count")
        success_count = report.get("success_count")
        if decl_count != expected_decls:
            gate_failures.append(
                f"{entry['file']}: binary checked {decl_count} declarations but the manifest "
                f"declares {expected_decls} — a probe was silently skipped, merged, or lost"
            )
            continue

        # Three-way, never two-way: `diverged` is not a pass (nothing was
        # proved) and not a fail (nothing was refuted). Folding it either way
        # is the whole defect this gate is fixing, in miniature.
        verdicts, problems = classify_file_verdicts(
            report, all_names, fixture_text, entry["file"]
        )
        if problems:
            gate_failures.extend(problems)
            continue

        if verdicts[entry["canary"]] != "pass":
            gate_failures.append(
                f"{entry['file']}: environment canary {entry['canary']} did not pass "
                f"({verdicts[entry['canary']]}) — `import Init` did not load the real Lean "
                f"environment (stub/builtin fallback), or the canary did not finish; the whole "
                f"measurement is invalid (§7.2 property 3)"
            )

        for req in entry.get("required", []):
            if verdicts.get(req) == "fail":
                gate_failures.append(f"{entry['file']}: required row {req} failed")
            elif verdicts.get(req) == "diverged":
                gate_failures.append(
                    f"{entry['file']}: required row {req} did not finish within the "
                    f"{DECL_BUDGET} kernel-operation per-declaration budget"
                )

        controls = {n["name"]: n.get("control") for n in entry.get("negatives", [])}
        for name in all_names:
            row = {
                "name": name,
                "file": entry["file"],
                "label": entry["label"],
                "kind": lv.row_kind(entry, name),
                "verdict": verdicts[name],
                "required": name in entry.get("required", []),
            }
            if name in controls:
                row["control"] = controls[name]
            rows.append(row)
        file_reports.append(
            {
                "file": entry["file"],
                "fixture_sha256": digest,
                "exit_code": proc.returncode,
                "decl_count": decl_count,
                "success_count": success_count,
                "failed_count": report.get("failed_count"),
                "diverged_count": report.get("diverged_count"),
                # The dearest declaration in this file, in kernel operations.
                # For a file with `diverged_count == 0` this IS the margin
                # under DECL_BUDGET, so the budget's headroom is re-derivable
                # from the artifact rather than trusted from a comment.
                "peak_decl_ticks": report.get("peak_decl_ticks"),
                "sorry_axioms": report.get("trust_summary", {}).get("sorry_axioms"),
                "kernel_check_failures": report.get("trust_summary", {}).get("kernel_check_failures"),
                "canary_discriminates": canary_discriminates.get(entry["file"]),
            }
        )

    probe_rows = [r for r in rows if r["kind"] == "probe"]
    passed = sorted(r["name"] for r in probe_rows if r["verdict"] == "pass")
    failed = sorted(r["name"] for r in probe_rows if r["verdict"] == "fail")
    diverged_probes = sorted(r["name"] for r in probe_rows if r["verdict"] == "diverged")

    if not gate_failures and not passed:
        gate_failures.append(
            "zero probes passed — a binary or environment defect, not a plausible measurement"
        )

    # Two-way: every row, of every kind, crossed with pinned Lean's verdict.
    ftw.cross(rows, lean_doc)
    two_way_totals = ftw.totals(rows)

    # Baseline ratchet: once recorded, pass rows may only be added.
    baseline_path = BASELINE_DIR / f"{family}.json"
    baseline_state = "none"
    baseline = None
    # The baseline-regression failure, kept apart: it is the one failure the
    # documented escape hatch (CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION) answers.
    regression_failure: str | None = None
    if baseline_path.is_file():
        try:
            baseline = json.loads(baseline_path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            baseline = None
            gate_failures.append(f"cannot read baseline {baseline_path}: {exc}")
        if baseline is not None:
            # A baseline-pass row that now DIVERGES is a regression too, and is
            # caught here by construction: `passed` holds only verdict=="pass"
            # rows, so a pass -> diverged flip lands in this set difference.
            regressions = sorted(set(baseline.get("pass", [])) - set(passed))
            if regressions:
                baseline_state = "REGRESSED"
                now_diverged = sorted(set(regressions) & set(diverged_probes))
                detail = (
                    f" (of which {now_diverged} did not finish within the "
                    f"{DECL_BUDGET}-operation per-declaration budget)"
                    if now_diverged
                    else ""
                )
                regression_failure = (
                    f"baseline regression — rows recorded passing now fail: {regressions}{detail}"
                )
                gate_failures.append(regression_failure)
            else:
                baseline_state = "ok"

    # The two-way ratchet, armed whenever a baseline exists. Its failures are
    # their own entries, never `regression_failure`, so the escape hatch above
    # cannot waive a new false acceptance into the record.
    ratchet_failures, ratchet_reports = ftw.ratchet(rows, baseline)
    gate_failures.extend(ratchet_failures)
    if strict:
        gate_failures.extend(ftw.strict_failure(two_way_totals, rows))

    commit = "unknown"
    git = subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=REPO_ROOT
    )
    if git.returncode == 0:
        commit = git.stdout.strip()

    bin_stat = clean_bin.stat()
    sha = hashlib.sha256(clean_bin.read_bytes()).hexdigest()
    now = _dt.datetime.now(_dt.timezone.utc)
    gate_verdict = "failed" if gate_failures else "measured"

    artifact = {
        "schema_version": ftw.GATE_SCHEMA,
        "gate": gate,
        "family": family,
        "generated_by": f"scripts/tactic_parity/{family}.sh (scripts/tactic_parity/family_gate.py)",
        "generated_at_utc": now.isoformat(timespec="seconds"),
        "git_commit": commit,
        "binary": {
            "path": str(clean_bin),
            "sha256": sha,
            "mtime_utc": _dt.datetime.fromtimestamp(bin_stat.st_mtime, _dt.timezone.utc).isoformat(
                timespec="seconds"
            ),
        },
        "plan": manifest["plan"],
        "comparison_basis": manifest["comparison_basis"],
        "verdict_axis": "closes-real-goals (axis c): pass requires a per-declaration pass verdict with no sorry axiom and no kernel-check failure attributed to the declaration",
        "environment": "real `import Init` per fixture; builtin prelude rejected by header check + per-file term-mode canary",
        "canary_discriminates": canary_discriminates,
        "decl_budget": DECL_BUDGET,
        "decl_budget_basis": (
            "kernel operations per declaration, passed to `clean check --decl-budget`. A "
            "declaration that spends it is reported `diverged` — its own verdict, neither pass "
            "nor fail — so ONE runaway declaration no longer costs its file's whole report. "
            "Compare against each file's `peak_decl_ticks`: for a file with diverged_count == 0 "
            "that number is the true worst-case cost of a finishing declaration, and the gap to "
            "this budget is the margin."
        ),
        "gate_verdict": gate_verdict,
        "gate_failures": gate_failures,
        "lean_mint": {
            "path": _rel(fam_dir / lv.VERDICTS_FILE),
            "seal": lean_doc.get("seal"),
            "rule": lean_doc.get("rule"),
            "lean_world": (lean_doc.get("lean_world") or {}).get("id"),
        },
        "strict": strict,
        # probes/passed/failed/diverged count PROBES only (the pinned
        # denominator); every two-way count covers every row kind.
        "totals": {"plan_family_total": manifest["plan_family_total"], **two_way_totals},
        "two_way_rows": ftw.two_way_rows(rows),
        "two_way_ratchet": {"failures": ratchet_failures, "reports": ratchet_reports},
        "diverged_probes": diverged_probes,
        "baseline": {"path": _rel(baseline_path), "state": baseline_state},
        "files": file_reports,
        "rows": rows,
    }

    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    stamp = now.strftime("%Y-%m-%d-%H%M%S")
    artifact_path = REPORT_DIR / f"{family}-{stamp}.json"
    artifact_path.write_text(json.dumps(artifact, indent=2) + "\n")
    (REPORT_DIR / f"{family}-latest.json").write_text(json.dumps(artifact, indent=2) + "\n")

    if update_baseline:
        # Until 2026-10-18 the escape hatch below was unreachable: the regression
        # it names is itself a gate failure, and ANY gate failure refused the
        # record first. It now waives exactly that one failure; a canary, a
        # required row, a timeout or any other failure still refuses the record.
        allow_regression = os.environ.get("CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION") == "1"
        blocking = record_blockers(gate_failures, regression_failure, allow_regression)
        # A false acceptance enters the record by name or not at all: the ratchet
        # watches only rows a baseline records, so a renamed row, a new negative
        # or a deleted baseline would otherwise record one as a plain pass.
        blocking += [
            f"two-way record -- {n} is an in-world row Clean accepts and pinned Lean rejects that "
            f"the baseline does not record; it enters the record only by name, with a reason, in "
            f"MANIFEST.json {lv.EXEMPTIONS_KEY}"
            for n in ftw.unrecorded_false_accepts(rows, baseline, lv.exemptions(manifest))
        ]
        if blocking:
            print(f"{gate}=failed reason=refusing-to-record-baseline-from-a-failed-run", flush=True)
            for gf in blocking:
                print(f"  FAIL: {gf}", flush=True)
            return 1
        if baseline_path.is_file():
            old = json.loads(baseline_path.read_text())
            dropped = sorted(set(old.get("pass", [])) - set(passed))
            if dropped and os.environ.get("CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION") != "1":
                print(
                    f"{gate}=failed reason=baseline-update-would-drop-passing-rows {dropped} "
                    f"(ratchets only go down; set CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION=1 "
                    f"only with a written justification in the commit)",
                    flush=True,
                )
                return 1
        BASELINE_DIR.mkdir(parents=True, exist_ok=True)
        baseline_path.write_text(
            json.dumps(
                {
                    "family": family,
                    "recorded_at_utc": now.isoformat(timespec="seconds"),
                    "git_commit": commit,
                    "binary_sha256": sha,
                    "decl_budget": DECL_BUDGET,
                    "pass": passed,
                    "fail": failed,
                    # Recorded so the partition is complete and a later run can
                    # tell "still does not finish" from "stopped finishing".
                    # Only `pass` is ratcheted.
                    "diverged": diverged_probes,
                    # v2: every row's Clean and Lean verdict, so the two-way
                    # ratchet can see a negative/control/canary row too.
                    **ftw.baseline_fields(rows, lean_doc),
                },
                indent=2,
            )
            + "\n"
        )
        print(f"  recorded baseline {baseline_path} (pass={len(passed)})", flush=True)

    for note in ratchet_reports:
        print(f"  NOTE: {note}", flush=True)
    for gf in gate_failures:
        print(f"  FAIL: {gf}", flush=True)
    print(
        f"{gate}={gate_verdict} pass={len(passed)}/{manifest['plan_family_total']} "
        f"clean_accepts_lean_rejects={two_way_totals['clean_accepts_lean_rejects']} "
        f"in_world={two_way_totals['clean_accepts_lean_rejects_in_world']} "
        f"diverged={len(diverged_probes)} decl_budget={DECL_BUDGET} "
        f"files={len(manifest['files'])} baseline={baseline_state} "
        f"basis=family-count-level-vs-2026-07-29 artifact={_rel(artifact_path)}",
        flush=True,
    )
    return 1 if gate_failures else 0


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    if "--pinned-inputs" in argv:
        # Answered before argparse: R7 asks without a --family.
        print("\n".join(ftw.first_party_inputs()))
        return 0
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--family", required=True, choices=sorted(GATE_NAMES))
    # One mode at most; with none, measure. A second mode used to be dropped in
    # silence (`--static --check-artifact` ran --static and exited 0).
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument(
        "--static",
        action="store_true",
        help="fixture/manifest integrity only (no binary, no measurement)",
    )
    mode.add_argument(
        "--canary-check",
        action="store_true",
        help="prove every fixture canary still FAILS on `--prelude builtin` and exit "
        "(needs the binary, ~5 s; the same check runs inside every measured run)",
    )
    mode.add_argument(
        "--check-artifact",
        nargs="?",
        const="",
        default=None,
        metavar="PATH",
        help="re-cross a saved v2 artifact (default reports/tactic-families/<family>-latest.json) "
        "against LEAN_VERDICTS.json and the baseline; needs no binary and no Lean",
    )
    ap.add_argument(
        "--update-baseline",
        action="store_true",
        help="record data/tactic_family_baselines/<family>.json from this run (ratchet: refuses to drop passing rows)",
    )
    ap.add_argument(
        "--strict",
        action="store_true",
        help="also fail on any row Clean accepts and pinned Lean rejects, any row with no "
        "pinned-Lean verdict, or any unconfirmed negative (off by default: measured-only)",
    )
    args = ap.parse_args(argv)
    if args.strict and (args.static or args.canary_check):
        ap.error("--strict judges a measurement or a saved artifact; --static and --canary-check measure none")
    if args.update_baseline and (args.static or args.canary_check or args.check_artifact is not None):
        ap.error("--update-baseline records a measured run; --static, --canary-check and --check-artifact make none")

    gate = GATE_NAMES[args.family]
    manifest = load_manifest(args.family)

    problems = static_check(args.family, manifest)
    if problems:
        for p in problems:
            print(f"  FAIL: {p}", flush=True)
        return fail(gate, "fixture-manifest-integrity")
    lean_doc, problems, notes = lv.load_checked(args.family, manifest, FIXTURE_ROOT / args.family)
    for note in notes:
        print(f"  NOTE: {note}", flush=True)
    if problems or lean_doc is None:
        for p in problems:
            print(f"  FAIL: {p}", flush=True)
        return fail(gate, "lean-verdicts")

    if args.static:
        total = sum(len(e["probes"]) for e in manifest["files"])
        minted = sum(len(f["rows"]) for f in lean_doc["files"].values())
        print(
            f"{gate}=fixtures-ok probes={total} files={len(manifest['files'])} "
            f"lean_verdicts=sealed:{lean_doc['seal'][:12]} rows={minted} "
            f"(static integrity only — run scripts/tactic_parity/{args.family}.sh for the measured verdict)",
            flush=True,
        )
        return 0
    if args.check_artifact is not None:
        path = Path(args.check_artifact) if args.check_artifact else (
            REPORT_DIR / f"{args.family}-latest.json"
        )
        rc, lines = ftw.check_saved_artifact(
            gate, args.family, path, lean_doc, BASELINE_DIR / f"{args.family}.json", args.strict
        )
        print("\n".join(lines), flush=True)
        return rc

    clean_bin = Path(os.environ.get("CLEAN_BIN", REPO_ROOT / "target" / "release" / "clean"))
    if not (clean_bin.is_file() and os.access(clean_bin, os.X_OK)):
        # NEVER build here: cargo is reserved for the central verifier.
        print(
            f"{gate}=SKIPPED reason=no-prebuilt-binary ({clean_bin} missing; this gate never "
            f"invokes cargo — build separately, then re-run)",
            flush=True,
        )
        return 2

    if args.canary_check:
        failures, verdicts = run_canary_checks(args.family, manifest, clean_bin)
        for f in failures:
            print(f"  FAIL: {f}", flush=True)
        if failures:
            return fail(gate, "canary-disarmed")
        print(
            f"{gate}=canaries-discriminate files={len(verdicts)} "
            f"(each canary refuted on `--prelude builtin`, so a silent fallback to it "
            f"would fail the measured run)",
            flush=True,
        )
        return 0

    return run_family(args.family, manifest, clean_bin, args.update_baseline, lean_doc, args.strict)


if __name__ == "__main__":
    sys.exit(main())
