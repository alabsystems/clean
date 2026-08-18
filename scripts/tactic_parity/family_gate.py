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
  3. Real imports — every fixture carries a real `import Init` header. The
     script never passes `--prelude`, refuses fixtures without the header,
     and each fixture file carries a term-mode environment canary
     (`List.reverse_reverse`, absent from every builtin/stub prelude) whose
     failure invalidates the run: builtin-prelude numbers overstate parity
     (§1 insight 3) and are rejected by the gate itself.
  4. Family-count comparability — the manifest pins the family denominator
     to the 2026-07-29 measurement (g_auto 131 / g_simp 127); a differing
     fixture count is a gate failure. The comparison basis is
     family-count-level, not probe-identical (stated in the artifact).
  5. Teeth — see scripts/tactic_parity/TEETH.md. Once a baseline is
     recorded (data/tactic_family_baselines/<family>.json, written only by
     --update-baseline from a real run), any baseline-pass row that stops
     passing fails the gate.

Exit codes:
  0  measured (artifact written; verdict line printed)
  1  gate FAILED (fail-closed: integrity violation, canary/required/baseline
     breach, or zero passing probes)
  2  SKIPPED — no prebuilt release binary (never invokes cargo; the machine's
     build capacity belongs to the central verifier)

The gate NEVER invokes cargo in any form. It drives the prebuilt release
binary (default target/release/clean, override CLEAN_BIN) and reads its JSON
report and process exit code directly — never through a pipeline that could
swallow the status (§5 cargo caveat).

Usage:
  scripts/tactic_parity/family_gate.py --family g_auto            # measure
  scripts/tactic_parity/family_gate.py --family g_simp --static   # fixture
        integrity only (no binary needed; wired into local_gate.sh fast path)
  scripts/tactic_parity/family_gate.py --family g_auto --update-baseline
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
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
FIXTURE_ROOT = REPO_ROOT / "tests" / "fixtures" / "tactic_families"
REPORT_DIR = REPO_ROOT / "reports" / "tactic-families"
BASELINE_DIR = REPO_ROOT / "data" / "tactic_family_baselines"

GATE_NAMES = {"g_auto": "G-AUTO", "g_simp": "G-SIMP"}

# Per-fixture-file wall clock: one `import Init` load measured 108-129 s on
# 2026-07-29; leave generous headroom for a loaded machine before declaring
# the run dead (a timeout is an infrastructure FAILURE, not a skip).
PER_FILE_TIMEOUT_SECS = 1800

DECL_RE = re.compile(
    r"^(?:@\[[^\]]+\]\s*)?(?:theorem|def|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)


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

        expected = [entry["canary"], *entry.get("helpers", []), *entry["probes"]]
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


def extract_json_report(stdout: str) -> dict | None:
    lines = stdout.splitlines()
    for i, line in enumerate(lines):
        if line.strip() == "{" or line.startswith('{"'):
            try:
                return json.loads("\n".join(lines[i:]))
            except json.JSONDecodeError:
                return None
    return None


def attribute_failures(report: dict, names: list[str], fixture_text: str) -> tuple[set[str], list[str]]:
    """Attribute the report's failures to declarations. Returns (failed
    names, unattributable failure strings). Attribution uses (a) the
    `NAME:`-prefixed trust/kernel failure rows, (b) proof_state_feedback's
    declaration field, (c) `at line L` positions mapped through the fixture's
    declaration start lines, (d) a whole-word name scan — for ATTRIBUTION
    only, never for success."""
    failed: set[str] = set()
    unattributed: list[str] = []
    name_set = set(names)

    # Declaration start lines (1-indexed) for positional attribution.
    decl_lines: list[tuple[int, str]] = []
    for m in DECL_RE.finditer(fixture_text):
        line_no = fixture_text.count("\n", 0, m.start()) + 1
        decl_lines.append((line_no, m.group(1)))
    decl_lines.sort()

    def decl_at_line(line_no: int) -> str | None:
        best = None
        for start, name in decl_lines:
            if start <= line_no:
                best = name
            else:
                break
        return best

    for row in report.get("trust_failures", []) + report.get("kernel_failures", []):
        name = row.split(":", 1)[0].strip()
        if name in name_set:
            failed.add(name)
        else:
            unattributed.append(row)

    for fb in report.get("proof_state_feedback", []):
        decl = fb.get("declaration")
        if decl in name_set:
            failed.add(decl)

    line_re = re.compile(r"at line (\d+)")
    for err in report.get("errors", []):
        m = line_re.search(err)
        if m:
            name = decl_at_line(int(m.group(1)))
            if name in name_set:
                failed.add(name)
                continue
        hits = [n for n in names if re.search(rf"\b{re.escape(n)}\b", err)]
        if hits:
            failed.update(hits)
        else:
            unattributed.append(err)

    return failed, unattributed


def run_family(family: str, manifest: dict, clean_bin: Path, update_baseline: bool) -> int:
    gate = GATE_NAMES[family]
    fam_dir = FIXTURE_ROOT / family
    gate_failures: list[str] = []
    rows: list[dict] = []
    file_reports: list[dict] = []

    for entry in manifest["files"]:
        fpath = fam_dir / entry["file"]
        fixture_text = fpath.read_text(encoding="utf-8")
        all_names = [entry["canary"], *entry.get("helpers", []), *entry["probes"]]
        expected_decls = len(all_names)

        try:
            proc = subprocess.run(
                [str(clean_bin), "check", "--json", str(fpath)],
                capture_output=True,
                text=True,
                timeout=PER_FILE_TIMEOUT_SECS,
                cwd=REPO_ROOT,
            )
        except subprocess.TimeoutExpired:
            gate_failures.append(f"{entry['file']}: timed out after {PER_FILE_TIMEOUT_SECS}s")
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

        failed_names, unattributed = attribute_failures(report, all_names, fixture_text)
        passed_names = [n for n in all_names if n not in failed_names]
        if len(passed_names) != success_count:
            gate_failures.append(
                f"{entry['file']}: verdict attribution mismatch — binary reports "
                f"success_count={success_count} but {len(passed_names)} declarations have no "
                f"attributed failure (unattributable: {unattributed[:3]}). A verdict that cannot "
                f"be read from the declaration fails the gate (§7.2 property 5)."
            )
            continue

        if entry["canary"] in failed_names:
            gate_failures.append(
                f"{entry['file']}: environment canary {entry['canary']} FAILED — `import Init` "
                f"did not load the real Lean environment (stub/builtin fallback); the whole "
                f"measurement is invalid (§7.2 property 3)"
            )

        for req in entry.get("required", []):
            if req in failed_names:
                gate_failures.append(f"{entry['file']}: required row {req} failed")

        for name in all_names:
            kind = (
                "canary"
                if name == entry["canary"]
                else "helper"
                if name in entry.get("helpers", [])
                else "probe"
            )
            rows.append(
                {
                    "name": name,
                    "file": entry["file"],
                    "label": entry["label"],
                    "kind": kind,
                    "verdict": "fail" if name in failed_names else "pass",
                    "required": name in entry.get("required", []),
                }
            )
        file_reports.append(
            {
                "file": entry["file"],
                "exit_code": proc.returncode,
                "decl_count": decl_count,
                "success_count": success_count,
                "failed_count": report.get("failed_count"),
                "sorry_axioms": report.get("trust_summary", {}).get("sorry_axioms"),
                "kernel_check_failures": report.get("trust_summary", {}).get("kernel_check_failures"),
            }
        )

    probe_rows = [r for r in rows if r["kind"] == "probe"]
    passed = sorted(r["name"] for r in probe_rows if r["verdict"] == "pass")
    failed = sorted(r["name"] for r in probe_rows if r["verdict"] == "fail")

    if not gate_failures and not passed:
        gate_failures.append(
            "zero probes passed — a binary or environment defect, not a plausible measurement"
        )

    # Baseline ratchet: once recorded, pass rows may only be added.
    baseline_path = BASELINE_DIR / f"{family}.json"
    baseline_state = "none"
    if baseline_path.is_file():
        try:
            baseline = json.loads(baseline_path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            baseline = None
            gate_failures.append(f"cannot read baseline {baseline_path}: {exc}")
        if baseline is not None:
            regressions = sorted(set(baseline.get("pass", [])) - set(passed))
            if regressions:
                baseline_state = "REGRESSED"
                gate_failures.append(
                    f"baseline regression — rows recorded passing now fail: {regressions}"
                )
            else:
                baseline_state = "ok"

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
        "schema_version": "tactic-family-gate-v1",
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
        "gate_verdict": gate_verdict,
        "gate_failures": gate_failures,
        "totals": {
            "probes": len(probe_rows),
            "plan_family_total": manifest["plan_family_total"],
            "passed": len(passed),
            "failed": len(failed),
        },
        "baseline": {"path": str(baseline_path.relative_to(REPO_ROOT)), "state": baseline_state},
        "files": file_reports,
        "rows": rows,
    }

    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    stamp = now.strftime("%Y-%m-%d-%H%M%S")
    artifact_path = REPORT_DIR / f"{family}-{stamp}.json"
    artifact_path.write_text(json.dumps(artifact, indent=2) + "\n")
    (REPORT_DIR / f"{family}-latest.json").write_text(json.dumps(artifact, indent=2) + "\n")

    if update_baseline:
        if gate_failures:
            print(f"{gate}=failed reason=refusing-to-record-baseline-from-a-failed-run", flush=True)
            for gf in gate_failures:
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
                    "pass": passed,
                    "fail": failed,
                },
                indent=2,
            )
            + "\n"
        )
        print(f"  recorded baseline {baseline_path} (pass={len(passed)})", flush=True)

    for gf in gate_failures:
        print(f"  FAIL: {gf}", flush=True)
    print(
        f"{gate}={gate_verdict} pass={len(passed)}/{manifest['plan_family_total']} "
        f"files={len(manifest['files'])} baseline={baseline_state} "
        f"basis=family-count-level-vs-2026-07-29 artifact={artifact_path.relative_to(REPO_ROOT)}",
        flush=True,
    )
    return 1 if gate_failures else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--family", required=True, choices=sorted(GATE_NAMES))
    ap.add_argument(
        "--static",
        action="store_true",
        help="fixture/manifest integrity only (no binary, no measurement)",
    )
    ap.add_argument(
        "--update-baseline",
        action="store_true",
        help="record data/tactic_family_baselines/<family>.json from this run (ratchet: refuses to drop passing rows)",
    )
    args = ap.parse_args()

    gate = GATE_NAMES[args.family]
    manifest = load_manifest(args.family)

    problems = static_check(args.family, manifest)
    if problems:
        for p in problems:
            print(f"  FAIL: {p}", flush=True)
        return fail(gate, "fixture-manifest-integrity")

    if args.static:
        total = sum(len(e["probes"]) for e in manifest["files"])
        print(
            f"{gate}=fixtures-ok probes={total} files={len(manifest['files'])} "
            f"(static integrity only — run scripts/tactic_parity/{args.family}.sh for the measured verdict)",
            flush=True,
        )
        return 0

    clean_bin = Path(os.environ.get("CLEAN_BIN", REPO_ROOT / "target" / "release" / "clean"))
    if not (clean_bin.is_file() and os.access(clean_bin, os.X_OK)):
        # NEVER build here: cargo is reserved for the central verifier.
        print(
            f"{gate}=SKIPPED reason=no-prebuilt-binary ({clean_bin} missing; this gate never "
            f"invokes cargo — build separately, then re-run)",
            flush=True,
        )
        return 2

    return run_family(args.family, manifest, clean_bin, args.update_baseline)


if __name__ == "__main__":
    sys.exit(main())
