#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Generate bounded Lean4-vs-clean frontend run artifacts.

This helper writes the per-engine exit-status and diagnostic artifacts required
by generate_frontend_classification.py, then writes the cross-checked
Lean4-vs-clean run artifact for each requested Phase 1 elab file. The artifacts
remain fail-closed: replacement_ready is always false, even when both engines
return the same process status and first-error signature.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DATA_DIR = REPO_ROOT / "tests" / "lean4_compat"
ARTIFACT_ROOT = DATA_DIR / "frontend_run_artifacts"
LEAN4_TOOLCHAIN = "leanprover/lean4:v4.27.0"
LEAN4_VERSION_COMMAND = ["elan", "run", LEAN4_TOOLCHAIN, "lean", "--version"]
clean_VERSION_COMMAND = ["./target/debug/clean", "--version"]
EXIT_STATUS_SCHEMA_VERSION = "clean-frontend-exit-status-artifact-v1"
DIAGNOSTIC_SCHEMA_VERSION = "clean-frontend-diagnostic-artifact-v1"
RUN_SCHEMA_VERSION = "clean-frontend-lean4-vs-clean-run-artifact-v1"


@dataclass(frozen=True)
class EngineRun:
    command: list[str]
    exit_code: int
    stdout: str
    stderr: str
    elapsed_seconds: float
    process_status: str


@dataclass(frozen=True)
class DiagnosticSummary:
    diagnostic_category: str | None
    first_error_signature: str | None
    diagnostics: list[dict[str, object]]


def repo_rel(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT).as_posix()


def normalized_json(value: object) -> str:
    return json.dumps(value, indent=2, ensure_ascii=True) + "\n"


def read_manifest_checksums() -> dict[str, str]:
    manifest = json.loads((DATA_DIR / "MANIFEST.json").read_text())
    checksums = manifest.get("checksums")
    if not isinstance(checksums, dict):
        raise ValueError("MANIFEST.json must contain a checksums object")
    return {str(filename): str(sha) for filename, sha in checksums.items()}


def read_phase1_levels() -> dict[str, str]:
    levels: dict[str, str] = {}
    for raw_line in (DATA_DIR / "phase1_gate_manifest.txt").read_text().splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        filename, level = [part.strip() for part in line.split(",", 1)]
        levels[filename] = level
    return levels


def require_tools() -> None:
    missing = [tool for tool in ("elan", "timeout") if shutil.which(tool) is None]
    if missing:
        raise RuntimeError(f"missing required tool(s): {', '.join(missing)}")
    if not (REPO_ROOT / "target" / "debug" / "clean").exists():
        raise RuntimeError(
            "target/debug/clean is missing; build clean before generating artifacts"
        )


def capture_version(command: list[str]) -> str:
    result = subprocess.run(
        command,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    version = (result.stdout or result.stderr).strip()
    if result.returncode != 0 or not version:
        raise RuntimeError(
            f"failed to capture engine version with command: {' '.join(command)}"
        )
    return version


def run_command(command: list[str], *, process_timeout_seconds: int) -> EngineRun:
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
            timeout=process_timeout_seconds,
        )
        elapsed = time.monotonic() - started
        process_status = "timeout" if result.returncode == 124 else "exited"
        return EngineRun(
            command=command,
            exit_code=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            elapsed_seconds=round(elapsed, 3),
            process_status=process_status,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.monotonic() - started
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        return EngineRun(
            command=command,
            exit_code=124,
            stdout=stdout,
            stderr=stderr,
            elapsed_seconds=round(elapsed, 3),
            process_status="timeout",
        )


def lean4_command(filename: str) -> list[str]:
    return [
        "elan",
        "run",
        LEAN4_TOOLCHAIN,
        "lean",
        f"tests/lean4_compat/lean4_tests/{filename}",
    ]


def clean_command(filename: str, timeout_seconds: int) -> list[str]:
    return [
        "timeout",
        str(timeout_seconds),
        "./target/debug/clean",
        "check",
        "--verbose",
        f"tests/lean4_compat/lean4_tests/{filename}",
    ]


LEAN4_LOCATION_RE = re.compile(
    r"^(?P<path>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning|information)(?:\([^)]*\))?: (?P<message>.*)$"
)


def severity_from_lean4(text: str) -> str:
    if text == "warning":
        return "warning"
    if text == "information":
        return "information"
    return "error"


def extract_lean4_diagnostics(run: EngineRun) -> list[dict[str, object]]:
    diagnostics: list[dict[str, object]] = []
    for line in (run.stdout + run.stderr).splitlines():
        match = LEAN4_LOCATION_RE.match(line)
        if match:
            diagnostics.append(
                {
                    "severity": severity_from_lean4(match.group("severity")),
                    "message": match.group("message"),
                    "line": int(match.group("line")),
                    "column": int(match.group("column")),
                }
            )
        elif line.strip() and not diagnostics:
            diagnostics.append({"severity": "information", "message": line})
    return diagnostics


def extract_clean_diagnostics(run: EngineRun) -> list[dict[str, object]]:
    diagnostics: list[dict[str, object]] = []
    in_errors = False
    for line in (run.stdout + run.stderr).splitlines():
        stripped = line.strip()
        if stripped == "Errors:":
            in_errors = True
            continue
        if stripped.startswith("warning:"):
            diagnostics.append(
                {
                    "severity": "warning",
                    "message": stripped.removeprefix("warning:").strip(),
                }
            )
            continue
        if in_errors and stripped.startswith("\u2717 "):
            diagnostics.append(
                {
                    "severity": "error",
                    "message": stripped.removeprefix("\u2717 ").strip(),
                }
            )
    return diagnostics


def first_error_message(diagnostics: list[dict[str, object]]) -> str | None:
    for diagnostic in diagnostics:
        if diagnostic.get("severity") == "error":
            message = diagnostic.get("message")
            if isinstance(message, str) and message:
                return message
    return None


def classify_first_error(message: str | None) -> tuple[str | None, str | None]:
    if message is None:
        return None, None

    lower = message.lower()
    if "import lean.elab.tactic" in lower:
        return "clean_frontend_error", "unsupported_import_lean_elab_tactic"
    if "unknownfvar" in lower:
        return "internal_fvar_reconstruction_blocker", "unknown_fvar_type_mismatch"
    if "fail to show termination" in lower or "structural recursion" in lower:
        return "termination_check_failure", "termination_check_failure"
    if "toomanyarguments" in lower:
        return "clean_frontend_error", "too_many_arguments"
    if "unknown constant" in lower:
        return "unknown_identifier_or_scope", "unknown_constant"
    if "unknown identifier" in lower:
        return "unknown_identifier_or_scope", "unknown_identifier"
    if "unknownidentwithsuggestions" in lower:
        return "unknown_identifier_or_scope", "unknown_ident_with_suggestions"
    if "alternative `isfalse`" in lower:
        return "missing_cases_alternative", "missing_cases_alternative"
    if "unknowntactic" in lower:
        return "clean_frontend_error", "unknown_tactic"
    if lower.strip() == "error":
        return "user_thrown_tactic_error", "error"
    return "other_frontend_error", normalize_signature(message)


def normalize_signature(message: str) -> str:
    signature = []
    last_was_separator = True
    in_digit_run = False
    for ch in message.strip().lower():
        if ch.isascii() and ch.isalpha():
            signature.append(ch)
            last_was_separator = False
            in_digit_run = False
        elif ch.isdigit():
            if not in_digit_run:
                signature.append("n")
                last_was_separator = False
                in_digit_run = True
        else:
            if not last_was_separator and signature:
                signature.append("_")
                last_was_separator = True
            in_digit_run = False
    while signature and signature[-1] == "_":
        signature.pop()
    return "".join(signature) or "empty_frontend_error"


def diagnostic_summary(engine: str, run: EngineRun) -> DiagnosticSummary:
    if engine == "lean4":
        diagnostics = extract_lean4_diagnostics(run)
    elif engine == "clean":
        diagnostics = extract_clean_diagnostics(run)
    else:
        raise ValueError(f"unsupported engine: {engine}")
    category, signature = classify_first_error(first_error_message(diagnostics))
    return DiagnosticSummary(
        diagnostic_category=category,
        first_error_signature=signature,
        diagnostics=diagnostics,
    )


def exit_artifact_path(engine: str, filename: str) -> Path:
    return ARTIFACT_ROOT / engine / "exit_status" / f"{filename}.json"


def diagnostic_artifact_path(engine: str, filename: str) -> Path:
    return ARTIFACT_ROOT / engine / "diagnostic" / f"{filename}.json"


def run_artifact_path(filename: str) -> Path:
    return ARTIFACT_ROOT / "lean4_vs_clean" / "run" / f"{filename}.json"


def write_json(path: Path, value: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(normalized_json(value))


def write_exit_status_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
    engine_version: str,
    run: EngineRun,
    timeout_seconds: int,
) -> None:
    status = "success" if run.exit_code == 0 else "failure"
    artifact: dict[str, object] = {
        "schema_version": EXIT_STATUS_SCHEMA_VERSION,
        "kind": "frontend_exit_status",
        "engine": engine,
        "filename": filename,
        "source_sha256": source_sha256,
        "command": run.command,
        "exit_code": run.exit_code,
        "status": status,
        "engine_version": engine_version,
        "observed_process_status": run.process_status,
        "observed_elapsed_seconds": run.elapsed_seconds,
        "observed_stdout": run.stdout,
        "observed_stderr": run.stderr,
        "artifact_note": (
            f"Generated bounded {engine} frontend run evidence; "
            "this is not replacement-readiness evidence."
        ),
    }
    if run.process_status == "timeout":
        artifact["observed_timeout_seconds"] = timeout_seconds
        artifact["failure_mode"] = "process_timeout"
    write_json(exit_artifact_path(engine, filename), artifact)


def write_diagnostic_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
    engine_version: str,
    run: EngineRun,
    summary: DiagnosticSummary,
    timeout_seconds: int,
) -> None:
    artifact: dict[str, object] = {
        "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
        "kind": "frontend_diagnostic",
        "engine": engine,
        "filename": filename,
        "source_sha256": source_sha256,
        "command": run.command,
        "diagnostic_category": summary.diagnostic_category,
        "first_error_signature": summary.first_error_signature,
        "diagnostics": summary.diagnostics,
        "engine_version": engine_version,
        "observed_process_status": run.process_status,
        "observed_exit_code": run.exit_code,
        "observed_elapsed_seconds": run.elapsed_seconds,
        "observed_stdout": run.stdout,
        "observed_stderr": run.stderr,
        "artifact_note": (
            f"Generated bounded {engine} diagnostic evidence; "
            "this is not replacement-readiness evidence."
        ),
    }
    if run.process_status == "timeout":
        artifact["observed_timeout_seconds"] = timeout_seconds
        artifact["failure_mode"] = "process_timeout"
    write_json(diagnostic_artifact_path(engine, filename), artifact)


def comparison_status(
    lean4_status: str,
    clean_status: str,
    lean4_signature: str | None,
    clean_signature: str | None,
) -> str:
    exit_part = (
        "exit_status_match" if lean4_status == clean_status else "exit_status_mismatch"
    )
    diagnostic_part = (
        "first_error_signature_match"
        if lean4_signature == clean_signature
        else "first_error_signature_mismatch"
    )
    return f"{exit_part}_{diagnostic_part}"


def cross_check_status(status: str) -> str:
    if status == "exit_status_match_first_error_signature_match":
        return "matched_exit_status_and_first_error_signature"
    if status == "exit_status_match_first_error_signature_mismatch":
        return "matched_exit_status_but_frontend_diagnostic_diverges"
    if status.startswith("exit_status_mismatch"):
        return "frontend_exit_status_diverges"
    return "frontend_run_artifact_cross_checked"


def write_run_artifact(
    *,
    filename: str,
    source_sha256: str,
    script_command: list[str],
    lean4_run: EngineRun,
    clean_run: EngineRun,
    lean4_summary: DiagnosticSummary,
    clean_summary: DiagnosticSummary,
) -> None:
    lean4_status = "success" if lean4_run.exit_code == 0 else "failure"
    clean_status = "success" if clean_run.exit_code == 0 else "failure"
    status = comparison_status(
        lean4_status,
        clean_status,
        lean4_summary.first_error_signature,
        clean_summary.first_error_signature,
    )
    artifact = {
        "schema_version": RUN_SCHEMA_VERSION,
        "kind": "frontend_lean4_vs_clean_run",
        "engine": "lean4_vs_clean",
        "filename": filename,
        "source_sha256": source_sha256,
        "command": script_command,
        "lean4_artifact_path": repo_rel(exit_artifact_path("lean4", filename)),
        "clean_artifact_path": repo_rel(exit_artifact_path("clean", filename)),
        "lean4_diagnostic_artifact_path": repo_rel(
            diagnostic_artifact_path("lean4", filename)
        ),
        "clean_diagnostic_artifact_path": repo_rel(
            diagnostic_artifact_path("clean", filename)
        ),
        "comparison_basis": "exit_status_and_first_error_signature",
        "comparison_status": status,
        "lean4_status": lean4_status,
        "clean_status": clean_status,
        "lean4_diagnostic_category": lean4_summary.diagnostic_category,
        "clean_diagnostic_category": clean_summary.diagnostic_category,
        "lean4_first_error_signature": lean4_summary.first_error_signature,
        "clean_first_error_signature": clean_summary.first_error_signature,
        "cross_check_status": cross_check_status(status),
        "replacement_ready": False,
        "artifact_note": (
            "Generated bounded Lean4-vs-clean frontend run evidence. "
            "This records differential evidence only and does not claim "
            "replacement readiness."
        ),
    }
    write_json(run_artifact_path(filename), artifact)


def generate_for_file(
    *,
    filename: str,
    source_sha256: str,
    lean4_version: str,
    clean_version: str,
    clean_timeout_seconds: int,
    script_command: list[str],
) -> None:
    lean4_run = run_command(lean4_command(filename), process_timeout_seconds=30)
    clean_run = run_command(
        clean_command(filename, clean_timeout_seconds),
        process_timeout_seconds=clean_timeout_seconds + 2,
    )
    lean4_summary = diagnostic_summary("lean4", lean4_run)
    clean_summary = diagnostic_summary("clean", clean_run)

    write_exit_status_artifact(
        engine="lean4",
        filename=filename,
        source_sha256=source_sha256,
        engine_version=lean4_version,
        run=lean4_run,
        timeout_seconds=30,
    )
    write_exit_status_artifact(
        engine="clean",
        filename=filename,
        source_sha256=source_sha256,
        engine_version=clean_version,
        run=clean_run,
        timeout_seconds=clean_timeout_seconds,
    )
    write_diagnostic_artifact(
        engine="lean4",
        filename=filename,
        source_sha256=source_sha256,
        engine_version=lean4_version,
        run=lean4_run,
        summary=lean4_summary,
        timeout_seconds=30,
    )
    write_diagnostic_artifact(
        engine="clean",
        filename=filename,
        source_sha256=source_sha256,
        engine_version=clean_version,
        run=clean_run,
        summary=clean_summary,
        timeout_seconds=clean_timeout_seconds,
    )
    write_run_artifact(
        filename=filename,
        source_sha256=source_sha256,
        script_command=script_command,
        lean4_run=lean4_run,
        clean_run=clean_run,
        lean4_summary=lean4_summary,
        clean_summary=clean_summary,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--files",
        nargs="+",
        required=True,
        help="Phase 1 elab corpus filenames to run, for example 1673.lean",
    )
    parser.add_argument(
        "--clean-timeout-seconds",
        type=int,
        default=5,
        help="wall-clock timeout passed to the clean frontend probe",
    )
    args = parser.parse_args()

    if args.clean_timeout_seconds <= 0:
        raise ValueError("--clean-timeout-seconds must be positive")

    require_tools()
    checksums = read_manifest_checksums()
    levels = read_phase1_levels()
    filenames = [
        filename if filename.endswith(".lean") else f"{filename}.lean"
        for filename in args.files
    ]
    for filename in filenames:
        if filename not in checksums:
            raise ValueError(f"{filename} is not listed in MANIFEST.json")
        if levels.get(filename) != "elab":
            raise ValueError(f"{filename} is not a Phase 1 elab row")

    lean4_version = capture_version(LEAN4_VERSION_COMMAND)
    clean_version = capture_version(clean_VERSION_COMMAND)
    script_command = ["python3", repo_rel(Path(__file__).resolve()), *sys.argv[1:]]
    for filename in filenames:
        generate_for_file(
            filename=filename,
            source_sha256=checksums[filename],
            lean4_version=lean4_version,
            clean_version=clean_version,
            clean_timeout_seconds=args.clean_timeout_seconds,
            script_command=script_command,
        )
        print(f"Generated frontend run artifacts for {filename}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
