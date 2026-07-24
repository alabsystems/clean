#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Gate `constructive: true` claims in `data/axiom_audit.json`.

CANONICAL SOURCE: alabsystems/clean

Usage:
  python3 -m scripts.axiom_audit.verify
  python3 -m scripts.axiom_audit.verify --audit path/to/axiom_audit.json
  python3 -m scripts.axiom_audit.verify --row-check-snapshot /tmp/live.json
  python3 -m scripts.axiom_audit.verify --verbose
"""

from __future__ import annotations

__all__ = [
    "AuditFailure",
    "load_audit",
    "verify_conjecture_rows_match_live",
    "verify_conjecture",
    "verify_all_constructive_claims",
    "main",
]

import argparse
import json
import os
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from scripts.axiom_audit.reconcile import (
    ReconcileResult,
    check_drift,
    load_live_snapshot,
    run_verify_gamma_crown,
)
from scripts.axiom_audit.schema import load_audit


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


@dataclass
class AuditFailure:
    """One theorem that claimed constructive but failed the closure check."""

    conjecture: str
    theorem: str
    closure: list[str] = field(default_factory=list)

    def format(self) -> str:
        deps = ", ".join(self.closure) if self.closure else "(empty)"
        return f"  {self.conjecture} :: {self.theorem} -> {deps}"


def _resolve_invocation(repo_root: Path) -> list[str]:
    """Return the argv prefix for the unified constructive-claims audit."""
    env_bin = os.environ.get("clean_BIN")
    if env_bin and Path(env_bin).is_file() and os.access(env_bin, os.X_OK):
        if Path(env_bin).name == "verify_constructive_claims":
            return [env_bin]
        return [env_bin, "kernel", "verify-constructive-claims"]

    on_path = shutil.which("clean")
    if on_path:
        return [on_path, "kernel", "verify-constructive-claims"]

    for variant in ("release", "debug"):
        candidate = repo_root / "target" / variant / "clean"
        if candidate.is_file() and candidate.stat().st_mode & 0o111:
            return [str(candidate), "kernel", "verify-constructive-claims"]

    for variant in ("release", "debug"):
        candidate = repo_root / "target" / variant / "verify_constructive_claims"
        if candidate.is_file() and candidate.stat().st_mode & 0o111:
            return [str(candidate)]

    legacy_on_path = shutil.which("verify_constructive_claims")
    if legacy_on_path:
        return [legacy_on_path]

    return [
        "cargo",
        "run",
        "--locked",
        "--quiet",
        "--message-format=short",
        "-j",
        os.environ.get("CARGO_BUILD_JOBS", "1"),
        "-p",
        "clean",
        "--features",
        "math-overlays",
        "--bin",
        "clean",
        "--",
        "kernel",
        "verify-constructive-claims",
    ]


def verify_conjecture_rows_match_live(
    audit_path: Path,
    *,
    repo_root: Path,
    snapshot_path: Path | None = None,
    verbose: bool = False,
) -> ReconcileResult:
    """Compare checked-in per-conjecture counters against live state."""
    audit = load_audit(audit_path)
    live = (
        load_live_snapshot(snapshot_path)
        if snapshot_path is not None
        else run_verify_gamma_crown(repo_root=repo_root, verbose=verbose)
    )
    return check_drift(audit, live)


def _format_row_reconciliation(result: ReconcileResult) -> str:
    lines: list[str] = []
    if result.drift_rows:
        lines.append(f"Per-conjecture drift ({len(result.drift_rows)} rows):")
        for row in result.drift_rows:
            lines.append(row.format())
    if result.missing_from_live:
        lines.append("Conjectures in audit but NOT in verify_gamma_crown output:")
        for cid in result.missing_from_live:
            lines.append(f"  {cid}")
    if result.missing_from_audit:
        lines.append("Conjectures in verify_gamma_crown output but NOT in audit:")
        for cid in result.missing_from_audit:
            lines.append(f"  {cid}")
    return "\n".join(lines) if lines else "(no drift)"


def _run_rust_audit(
    conjecture_id: str, *, repo_root: Path, verbose: bool = False
) -> dict[str, Any]:
    base = _resolve_invocation(repo_root)
    cmd = [*base, "--conjecture", conjecture_id]
    if verbose:
        print(f"[verify_axiom_audit] $ {' '.join(cmd)}", file=sys.stderr)
    proc = subprocess.run(
        cmd,
        cwd=str(repo_root),
        capture_output=True,
        text=True,
        check=False,
    )
    if not proc.stdout.strip():
        raise ValueError(
            f"conjecture {conjecture_id}: Rust binary produced no stdout\n"
            f"stderr:\n{proc.stderr}"
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"conjecture {conjecture_id}: failed to parse JSON from Rust binary: {exc}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        ) from exc


def verify_conjecture(
    conjecture_id: str, *, repo_root: Path, verbose: bool = False
) -> list[AuditFailure]:
    """Return the list of failing theorems for `conjecture_id`."""
    report = _run_rust_audit(conjecture_id, repo_root=repo_root, verbose=verbose)
    theorems = report.get("theorems", [])
    if not theorems:
        return [
            AuditFailure(
                conjecture=conjecture_id,
                theorem="(no theorems found in namespace)",
                closure=[],
            )
        ]

    failures: list[AuditFailure] = []
    for theorem in theorems:
        if not theorem.get("is_constructive", False):
            failures.append(
                AuditFailure(
                    conjecture=conjecture_id,
                    theorem=str(theorem.get("name", "<unnamed>")),
                    closure=list(theorem.get("closure", [])),
                )
            )
    return failures


def verify_all_constructive_claims(
    audit_path: Path, *, repo_root: Path, verbose: bool = False
) -> tuple[int, list[AuditFailure]]:
    """Verify every `constructive` claim in the audit file."""
    audit = load_audit(audit_path)
    claimed = [
        cid
        for cid, entry in audit["conjectures"].items()
        if entry.get("proof_mechanism") == "constructive"
    ]
    failures: list[AuditFailure] = []
    for cid in claimed:
        failures.extend(verify_conjecture(cid, repo_root=repo_root, verbose=verbose))
    return len(claimed), failures


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="verify_axiom_audit",
        description=(
            "Gate `constructive: true` claims in data/axiom_audit.json via "
            "transitive axiom closure over the kernel environment."
        ),
    )
    parser.add_argument(
        "--audit",
        type=Path,
        default=None,
        help="Path to axiom_audit.json (default: <repo>/data/axiom_audit.json)",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Echo the resolved audit invocation to stderr.",
    )
    parser.add_argument(
        "--row-check-snapshot",
        type=Path,
        default=None,
        help=(
            "Use a pre-captured verify_gamma_crown --json snapshot for the "
            "per-conjecture row reconciliation gate. Implies the row check "
            "even for non-default --audit paths."
        ),
    )
    parser.add_argument(
        "--skip-live-row-check",
        action="store_true",
        help=(
            "Skip the per-conjecture row reconciliation gate. By default the "
            "gate runs when auditing the repo's checked-in data/axiom_audit.json."
        ),
    )
    return parser


def _validate_args(parser: argparse.ArgumentParser, args: argparse.Namespace) -> None:
    if args.skip_live_row_check and args.row_check_snapshot is not None:
        parser.error(
            "--skip-live-row-check cannot be combined with --row-check-snapshot"
        )


def _should_check_rows(
    args: argparse.Namespace,
    *,
    audit_path: Path,
    default_audit_path: Path,
) -> bool:
    return not args.skip_live_row_check and (
        args.row_check_snapshot is not None
        or audit_path.resolve() == default_audit_path.resolve()
    )


def _maybe_run_row_check(
    *,
    should_check_rows: bool,
    audit_path: Path,
    repo_root: Path,
    snapshot_path: Path | None,
    verbose: bool,
) -> int | None:
    if not should_check_rows:
        return None
    row_result = verify_conjecture_rows_match_live(
        audit_path,
        repo_root=repo_root,
        snapshot_path=snapshot_path,
        verbose=verbose,
    )
    if row_result.is_clean:
        return None
    sys.stderr.write(
        "verify_axiom_audit: per-conjecture rows drift from "
        "`verify_gamma_crown --json` output.\n"
    )
    sys.stderr.write(_format_row_reconciliation(row_result) + "\n")
    sys.stderr.write(
        "\nFix: run `python3 -m scripts.axiom_audit.reconcile` "
        "to refresh rows from live, then re-stage.\n"
    )
    return 1


def _render_result(
    *,
    checked: int,
    failures: list[AuditFailure],
    should_check_rows: bool,
) -> int:
    prefix = "row reconciliation passed; " if should_check_rows else ""
    if checked == 0:
        sys.stdout.write(
            "verify_axiom_audit: " + prefix + "no conjectures currently claim "
            "`proof_mechanism: constructive` — nothing to gate (pass).\n"
        )
        return 0
    if failures:
        sys.stderr.write(
            f"verify_axiom_audit: {len(failures)} theorem(s) failed the "
            f"constructive-closure check across {checked} audited conjecture(s):\n"
        )
        for failure in failures:
            sys.stderr.write(failure.format() + "\n")
        sys.stderr.write(
            "\nFix: either provide a genuine proof term whose transitive "
            "axiom closure is a subset of FOUNDATIONAL_AXIOMS (see "
            "crates/clean-kernel/src/env/axiom_audit.rs), or downgrade "
            "the claim to a non-constructive `proof_mechanism` label.\n"
        )
        return 1
    sys.stdout.write(
        "verify_axiom_audit: "
        + prefix
        + f"{checked} constructive-claimed conjecture(s) "
        "passed the closure check.\n"
    )
    return 0


def _handle_cli_error(exc: Exception, *, return_code: int) -> int:
    print(f"verify_axiom_audit: {exc}", file=sys.stderr)
    return return_code


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    _validate_args(parser, args)

    repo_root = _repo_root()
    default_audit_path = repo_root / "data" / "axiom_audit.json"
    audit_path = args.audit or default_audit_path
    should_check_rows = _should_check_rows(
        args, audit_path=audit_path, default_audit_path=default_audit_path
    )

    try:
        row_check_rc = _maybe_run_row_check(
            should_check_rows=should_check_rows,
            audit_path=audit_path,
            repo_root=repo_root,
            snapshot_path=args.row_check_snapshot,
            verbose=args.verbose,
        )
        if row_check_rc is not None:
            return row_check_rc
        checked, failures = verify_all_constructive_claims(
            audit_path,
            repo_root=repo_root,
            verbose=args.verbose,
        )
    except FileNotFoundError as exc:
        return _handle_cli_error(exc, return_code=2)
    except ValueError as exc:
        return _handle_cli_error(exc, return_code=2)
    except subprocess.CalledProcessError as exc:
        return _handle_cli_error(
            Exception(f"audit invocation failed: {exc}"),
            return_code=3,
        )

    return _render_result(
        checked=checked,
        failures=failures,
        should_check_rows=should_check_rows,
    )


if __name__ == "__main__":
    sys.exit(main())
