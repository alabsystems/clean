#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Validate and update the public benchmark publication contract."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import re
import subprocess
import sys
import tarfile
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from typing import Any

SUITE_VERSION = "public-benchmark-suite-v1"
PUBLIC_SUITES = ["kernel-perf", "server-perf"]
FRESHNESS_DAYS = 14
PENDING_STATUS = "pending-publication"
PUBLISHED_STATUS = "published"
STATUSES = {PENDING_STATUS, PUBLISHED_STATUS}
RUN_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
UTC_TIMESTAMP_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
FULL_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
RUN_CONTEXT_COMMIT_RE = re.compile(r"^[0-9a-f]{7,40}$")
PENDING_LAUNCH_GUIDANCE = (
    "Run ./scripts/run_public_benchmarks.sh from a clean checkout to create real "
    "benchmark artifacts, then commit reports/benchmarks/publication/current.json "
    "and the generated run directory, record a reachable publication_commit, and "
    "rerun --launch. Do not manually mark pending metadata as published."
)

CANONICAL_INPUTS = [
    "Cargo.toml",
    "Cargo.lock",
    "crates/clean-kernel/Cargo.toml",
    "crates/clean-kernel/benches/kernel_bench.rs",
    "crates/clean-kernel/benches/cert_macro_bench.rs",
    "crates/clean-server/Cargo.toml",
    "crates/clean-server/benches/server_ops.rs",
    "evals/registry/kernel-perf.yaml",
    "evals/registry/server-perf.yaml",
    "scripts/capture_benchmark_env.py",
    "scripts/check_benchmark_publication.py",
    "scripts/run_public_benchmarks.sh",
]

CANONICAL_COMMANDS = {
    "kernel_bench": "cargo bench --locked --message-format=short -j 1 --package clean-kernel --bench kernel_bench -- --output-format bencher",
    "cert_macro_bench": "cargo bench --locked --message-format=short -j 1 --package clean-kernel --bench cert_macro_bench -- --output-format bencher",
    "server_ops": "cargo bench --locked --message-format=short -j 1 --package clean-server --bench server_ops -- --output-format bencher",
}

REQUIRED_RUN_ARTIFACTS = [
    "run_context.json",
    "raw/kernel_bench.stdout.txt",
    "raw/cert_macro_bench.stdout.txt",
    "raw/server_ops.stdout.txt",
    "logs/kernel_bench.stderr.log",
    "logs/cert_macro_bench.stderr.log",
    "logs/server_ops.stderr.log",
    "raw/criterion/kernel_bench",
    "raw/criterion/cert_macro_bench",
    "raw/criterion/server_ops",
]


def contract_help_epilog() -> str:
    command_lines = "\n".join(
        f"  {name}: {command}" for name, command in CANONICAL_COMMANDS.items()
    )
    input_lines = "\n".join(f"  {rel_path}" for rel_path in CANONICAL_INPUTS)
    return f"""Public benchmark publication contract:
  Runner: ./scripts/run_public_benchmarks.sh
  Checker: python3 scripts/check_benchmark_publication.py --check
  Pre-publication source check: python3 scripts/check_benchmark_publication.py --check --prepublication-source-head
  Stale branch guard: python3 scripts/check_benchmark_publication.py --check --stale-branch-base origin/main
  Launch/public performance check: python3 scripts/check_benchmark_publication.py --check --launch
  Freshness: {FRESHNESS_DAYS} days after publication

Canonical benchmark commands:
{command_lines}

Canonical inputs:
{input_lines}
"""


def repo_root_from_script() -> Path:
    return Path(__file__).resolve().parent.parent


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def read_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def sha256_file(path: Path) -> dict[str, Any]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            size += len(chunk)
            digest.update(chunk)
    return {"bytes": size, "sha256": digest.hexdigest()}


def sha256_bytes(data: bytes) -> dict[str, Any]:
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def artifact_path_sort_key(rel_path: str) -> tuple[str, ...]:
    return tuple(rel_path.split("/"))


def sha256_directory(path: Path) -> dict[str, Any]:
    digest = hashlib.sha256()
    total_size = 0
    children = [
        (child.relative_to(path).as_posix(), child)
        for child in path.rglob("*")
        if child.is_file()
    ]
    for rel_path, child in sorted(
        children, key=lambda entry: artifact_path_sort_key(entry[0])
    ):
        digest.update(rel_path.encode("utf-8"))
        digest.update(b"\0")
        file_hash = sha256_file(child)
        total_size += int(file_hash["bytes"])
        digest.update(str(file_hash["bytes"]).encode("ascii"))
        digest.update(b"\0")
        digest.update(str(file_hash["sha256"]).encode("ascii"))
        digest.update(b"\0")
    return {"bytes": total_size, "sha256": digest.hexdigest()}


def sha256_artifact(path: Path) -> dict[str, Any]:
    if path.is_dir():
        return sha256_directory(path)
    return sha256_file(path)


def git_object_type(repo_root: Path, commit: str, rel_path: str) -> str | None:
    result = subprocess.run(
        ["git", "-C", str(repo_root), "cat-file", "-t", f"{commit}:{rel_path}"],
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        return None
    return result.stdout.strip()


def sha256_git_blob(
    repo_root: Path, object_name: str, display_path: str, errors: list[str]
) -> dict[str, Any] | None:
    result = subprocess.run(
        ["git", "-C", str(repo_root), "cat-file", "-p", object_name],
        check=False,
        capture_output=True,
    )
    if result.returncode != 0:
        errors.append(
            "unable to read committed benchmark artifact blob: "
            f"{display_path}: {result.stderr.decode('utf-8', errors='replace').strip()}"
        )
        return None
    return sha256_bytes(result.stdout)


def sha256_git_directory(
    repo_root: Path, commit: str, rel_path: str, errors: list[str]
) -> dict[str, Any] | None:
    result = subprocess.run(
        [
            "git",
            "-C",
            str(repo_root),
            "archive",
            "--format=tar",
            commit,
            rel_path,
        ],
        check=False,
        capture_output=True,
    )
    if result.returncode != 0:
        errors.append(
            "unable to archive committed benchmark artifact directory: "
            f"{commit}:{rel_path}: {result.stderr.decode('utf-8', errors='replace').strip()}"
        )
        return None

    prefix = rel_path.rstrip("/") + "/"
    entries: list[tuple[str, bytes]] = []
    try:
        archive = tarfile.open(fileobj=io.BytesIO(result.stdout), mode="r:")
    except tarfile.TarError as exc:
        errors.append(
            f"unable to read committed benchmark artifact archive {commit}:{rel_path}: {exc}"
        )
        return None
    with archive:
        for member in archive.getmembers():
            if member.isdir():
                continue
            if not member.isfile():
                errors.append(
                    "committed benchmark artifact tree contains non-file entry: "
                    f"{commit}:{member.name}"
                )
                return None
            if not member.name.startswith(prefix):
                errors.append(
                    "committed benchmark artifact path is outside expected root: "
                    f"{commit}:{member.name}"
                )
                return None
            extracted = archive.extractfile(member)
            if extracted is None:
                errors.append(
                    "unable to read committed benchmark artifact archive member: "
                    f"{commit}:{member.name}"
                )
                return None
            entries.append((member.name[len(prefix) :], extracted.read()))

    digest = hashlib.sha256()
    total_size = 0
    for child_rel_path, data in sorted(
        entries, key=lambda entry: artifact_path_sort_key(entry[0])
    ):
        file_hash = sha256_bytes(data)
        digest.update(child_rel_path.encode("utf-8"))
        digest.update(b"\0")
        total_size += int(file_hash["bytes"])
        digest.update(str(file_hash["bytes"]).encode("ascii"))
        digest.update(b"\0")
        digest.update(str(file_hash["sha256"]).encode("ascii"))
        digest.update(b"\0")
    return {"bytes": total_size, "sha256": digest.hexdigest()}


def sha256_git_artifact(
    repo_root: Path, commit: str, rel_path: str, errors: list[str]
) -> dict[str, Any] | None:
    object_type = git_object_type(repo_root, commit, rel_path)
    if object_type is None:
        errors.append(
            "publication_commit is missing committed benchmark artifact: "
            f"{commit}:{rel_path}"
        )
        return None
    if object_type == "blob":
        return sha256_git_blob(
            repo_root, f"{commit}:{rel_path}", f"{commit}:{rel_path}", errors
        )
    if object_type == "tree":
        return sha256_git_directory(repo_root, commit, rel_path, errors)
    errors.append(
        "publication_commit benchmark artifact must be a file or directory: "
        f"{commit}:{rel_path} is {object_type}"
    )
    return None


def run_git(repo_root: Path, args: list[str]) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        check=True,
        text=True,
        capture_output=True,
    )
    return result.stdout.rstrip("\n")


def dirty_canonical_inputs(repo_root: Path) -> list[str]:
    status = run_git(repo_root, ["status", "--porcelain=v1", "--", *CANONICAL_INPUTS])
    return parse_git_status_paths(status)


def parse_git_status_paths(status: str) -> list[str]:
    if not status:
        return []
    paths: list[str] = []
    for line in status.splitlines():
        if len(line) >= 4 and line[:2] in {"R ", "C "}:
            paths.append(line.split(" -> ", maxsplit=1)[-1])
        elif len(line) >= 3:
            paths.append(line[3:])
        else:
            paths.append(line)
    return paths


def dirty_repo_paths(repo_root: Path, rel_paths: list[str]) -> list[str]:
    if not rel_paths:
        return []
    status = run_git(repo_root, ["status", "--porcelain=v1", "--", *rel_paths])
    return parse_git_status_paths(status)


def resolve_commit(
    repo_root: Path, rev: str, errors: list[str], *, field: str
) -> str | None:
    result = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "--verify", f"{rev}^{{commit}}"],
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        errors.append(f"{field} is not a valid commit ref: {rev}")
        return None
    return result.stdout.strip()


def validate_stale_branch_guard(
    repo_root: Path, base_ref: str, errors: list[str]
) -> None:
    base_commit = resolve_commit(
        repo_root, base_ref, errors, field="--stale-branch-base"
    )
    if (
        base_commit is None
        or resolve_commit(repo_root, "HEAD", errors, field="HEAD") is None
    ):
        return

    diff = run_git(
        repo_root,
        ["diff", "--name-only", f"{base_ref}...HEAD", "--", *CANONICAL_INPUTS],
    )
    changed_inputs = [path for path in diff.splitlines() if path]
    if not changed_inputs:
        return

    merge_base = run_git(repo_root, ["merge-base", base_ref, "HEAD"])
    if merge_base == base_commit:
        return

    shown = ", ".join(changed_inputs[:5])
    if len(changed_inputs) > 5:
        shown += f", ... ({len(changed_inputs)} total)"
    errors.append(
        "canonical benchmark inputs changed on a branch that is not based on "
        f"{base_ref}: {shown}; rebase or merge the current base ref, regenerate "
        "reports/benchmarks/publication/current.json if hashes changed, then rerun "
        "--prepublication-source-head"
    )


def validate_canonical_inputs_clean(
    repo_root: Path, errors: list[str], *, allow_uncommitted_inputs: bool
) -> None:
    if allow_uncommitted_inputs:
        return
    dirty_paths = dirty_canonical_inputs(repo_root)
    if dirty_paths:
        shown = ", ".join(dirty_paths[:5])
        if len(dirty_paths) > 5:
            shown += f", ... ({len(dirty_paths)} total)"
        errors.append(
            "canonical benchmark inputs have uncommitted changes: "
            f"{shown}; commit them before publishing benchmark metadata"
        )


def collect_input_hashes(
    repo_root: Path, errors: list[str]
) -> dict[str, dict[str, Any]]:
    hashes: dict[str, dict[str, Any]] = {}
    for rel_path in CANONICAL_INPUTS:
        path = repo_root / rel_path
        if not path.is_file():
            errors.append(f"canonical benchmark input is missing: {rel_path}")
            continue
        hashes[rel_path] = sha256_file(path)
    return hashes


def collect_source_commit_input_hashes(
    repo_root: Path, source_commit: str, errors: list[str]
) -> dict[str, dict[str, Any]]:
    hashes: dict[str, dict[str, Any]] = {}
    for rel_path in CANONICAL_INPUTS:
        result = subprocess.run(
            ["git", "-C", str(repo_root), "show", f"{source_commit}:{rel_path}"],
            check=False,
            capture_output=True,
        )
        if result.returncode != 0:
            errors.append(
                "canonical benchmark input is missing from current.json "
                f"source_commit {source_commit}: {rel_path}"
            )
            continue
        hashes[rel_path] = sha256_bytes(result.stdout)
    return hashes


def collect_artifact_hashes(
    run_dir: Path, artifact_root: str, errors: list[str]
) -> dict[str, dict[str, Any]]:
    hashes: dict[str, dict[str, Any]] = {}
    for rel_path in REQUIRED_RUN_ARTIFACTS:
        path = run_dir / rel_path
        if not path.exists():
            errors.append(
                "current run directory is missing required artifact: "
                f"{artifact_root}/{rel_path}"
            )
            continue
        hashes[rel_path] = sha256_artifact(path)
    return hashes


def parse_iso_date(value: Any, *, field: str, errors: list[str]) -> date | None:
    if not isinstance(value, str) or not DATE_RE.fullmatch(value):
        errors.append(f"{field} must be an ISO date (YYYY-MM-DD)")
        return None
    try:
        return date.fromisoformat(value)
    except ValueError:
        errors.append(f"{field} must be a valid ISO date (YYYY-MM-DD)")
        return None


def parse_utc_timestamp(value: Any, *, field: str, errors: list[str]) -> None:
    if not isinstance(value, str) or not UTC_TIMESTAMP_RE.fullmatch(value):
        errors.append(f"{field} must be a UTC timestamp like YYYY-MM-DDTHH:MM:SSZ")
        return
    try:
        datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError:
        errors.append(f"{field} must be a valid UTC timestamp")


def validate_full_commit(value: Any, *, field: str, errors: list[str]) -> None:
    if not isinstance(value, str) or not FULL_COMMIT_RE.fullmatch(value):
        errors.append(f"{field} must be a full 40-character git SHA")


def validate_optional_full_commit(value: Any, *, field: str, errors: list[str]) -> None:
    if value is None:
        return
    validate_full_commit(value, field=field, errors=errors)


def validate_reachable_commit(
    repo_root: Path, commit: Any, *, field: str, errors: list[str]
) -> None:
    if not isinstance(commit, str) or not FULL_COMMIT_RE.fullmatch(commit):
        return
    result = subprocess.run(
        [
            "git",
            "-C",
            str(repo_root),
            "merge-base",
            "--is-ancestor",
            commit,
            "HEAD",
        ],
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        errors.append(
            f"{field} {commit} is not reachable from current repository history"
        )


def validate_source_commit_matches_head(
    repo_root: Path, source_commit: Any, errors: list[str]
) -> None:
    if not isinstance(source_commit, str) or not FULL_COMMIT_RE.fullmatch(
        source_commit
    ):
        return
    head_commit = run_git(repo_root, ["rev-parse", "HEAD"])
    if source_commit != head_commit:
        errors.append(
            "current.json source_commit must equal checked-out HEAD when "
            "--prepublication-source-head is set: "
            f"source_commit={source_commit} HEAD={head_commit}"
        )


def validate_reachable_publication_commit(
    repo_root: Path, publication_commit: Any, errors: list[str]
) -> None:
    validate_reachable_commit(
        repo_root,
        publication_commit,
        field="current.json publication_commit",
        errors=errors,
    )


def validate_launch_publication_evidence(
    repo_root: Path,
    publication_root: Path,
    current: dict[str, Any],
    errors: list[str],
) -> None:
    if current.get("status") != PUBLISHED_STATUS:
        errors.append(
            "launch benchmark publication requires current.json status "
            f"{PUBLISHED_STATUS!r}; pending-publication is not sufficient for "
            f"public performance claims. {PENDING_LAUNCH_GUIDANCE}"
        )
        return

    publication_commit = current.get("publication_commit")
    if not isinstance(publication_commit, str) or not FULL_COMMIT_RE.fullmatch(
        publication_commit
    ):
        errors.append(
            "launch benchmark publication requires current.json "
            "publication_commit to be a full 40-character git SHA"
        )

    evidence_paths = [publication_root / "current.json"]
    run_id = current.get("current_run")
    if isinstance(run_id, str) and validate_run_id(
        run_id, field="current.json current_run", errors=[]
    ):
        evidence_paths.append(publication_root / run_id)

    rel_paths: list[str] = []
    for path in evidence_paths:
        try:
            rel_paths.append(
                repo_relative_path(
                    repo_root, path, label="launch benchmark evidence path"
                )
            )
        except ValueError as exc:
            errors.append(
                "launch benchmark evidence must be committed inside the "
                f"repository: {exc}"
            )

    dirty_paths = dirty_repo_paths(repo_root, rel_paths)
    if dirty_paths:
        shown = ", ".join(dirty_paths[:5])
        if len(dirty_paths) > 5:
            shown += f", ... ({len(dirty_paths)} total)"
        errors.append(
            "launch benchmark evidence has uncommitted changes: "
            f"{shown}; commit current.json and current run artifacts before "
            "publishing public performance claims"
        )


def validate_publication_commit_artifacts(
    repo_root: Path, current: dict[str, Any], errors: list[str]
) -> None:
    publication_commit = current.get("publication_commit")
    if not isinstance(publication_commit, str) or not FULL_COMMIT_RE.fullmatch(
        publication_commit
    ):
        return
    artifact_root = current.get("artifact_root")
    if not isinstance(artifact_root, str) or not artifact_root:
        return
    expected_artifacts = current.get("artifacts")
    if not isinstance(expected_artifacts, dict):
        return

    for rel_path in REQUIRED_RUN_ARTIFACTS:
        expected = expected_artifacts.get(rel_path)
        if not isinstance(expected, dict):
            continue
        committed_path = f"{artifact_root}/{rel_path}"
        committed_hash = sha256_git_artifact(
            repo_root, publication_commit, committed_path, errors
        )
        if committed_hash is None:
            continue
        if expected.get("sha256") != committed_hash.get("sha256"):
            errors.append(
                "publication_commit artifact "
                f"{rel_path} sha256 mismatch: {publication_commit}:{committed_path}"
            )
        if expected.get("bytes") != committed_hash.get("bytes"):
            errors.append(
                "publication_commit artifact "
                f"{rel_path} byte count mismatch: {publication_commit}:{committed_path}"
            )


def validate_run_id(value: Any, *, field: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or not value:
        errors.append(f"{field} must be a non-empty run id")
        return None
    if Path(value).is_absolute() or "/" in value or "\\" in value or ".." in value:
        errors.append(
            f"{field} must be a safe slug without path separators or traversal"
        )
        return None
    if not RUN_ID_RE.fullmatch(value):
        errors.append(
            f"{field} must match {RUN_ID_RE.pattern!r} using ASCII letters, digits, dot, underscore, and dash"
        )
        return None
    return value


def validate_non_empty_string(value: Any, *, field: str, errors: list[str]) -> None:
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{field} must be a non-empty string")


def validate_run_context_schema(path: Path, errors: list[str]) -> None:
    try:
        context = read_json(path)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        errors.append(f"{path} must be a valid JSON object: {exc}")
        return

    command = context.get("command")
    if command != SUITE_VERSION:
        errors.append(f"{path} command must be {SUITE_VERSION!r}, got {command!r}")
    if context.get("dirty") is not False:
        errors.append(f"{path} dirty must be false for published benchmarks")

    commit = context.get("commit")
    if not isinstance(commit, str) or not RUN_CONTEXT_COMMIT_RE.fullmatch(commit):
        errors.append(f"{path} commit must be a 7-40 character lowercase git SHA")
    validate_non_empty_string(
        context.get("branch"), field=f"{path} branch", errors=errors
    )
    parse_utc_timestamp(
        context.get("timestamp"), field=f"{path} timestamp", errors=errors
    )

    machine = context.get("machine")
    if not isinstance(machine, dict):
        errors.append(f"{path} machine must be an object")
    else:
        for field in ["os", "cpu", "memory", "arch"]:
            validate_non_empty_string(
                machine.get(field), field=f"{path} machine.{field}", errors=errors
            )

    toolchain = context.get("toolchain")
    if not isinstance(toolchain, dict):
        errors.append(f"{path} toolchain must be an object")
    else:
        for field in ["rustc", "cargo"]:
            validate_non_empty_string(
                toolchain.get(field),
                field=f"{path} toolchain.{field}",
                errors=errors,
            )


def repo_relative_path(repo_root: Path, path: Path, *, label: str) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError as exc:
        raise ValueError(f"{label} must live inside repository root: {path}") from exc


def write_current(
    repo_root: Path,
    publication_root: Path,
    *,
    run_id: str | None,
    status: str,
    fresh_until: str | None,
    allow_uncommitted_inputs: bool,
) -> list[str]:
    errors: list[str] = []
    if status not in STATUSES:
        errors.append(f"--status must be one of {sorted(STATUSES)}")
    validate_canonical_inputs_clean(
        repo_root, errors, allow_uncommitted_inputs=allow_uncommitted_inputs
    )
    source_commit = run_git(repo_root, ["rev-parse", "HEAD"])
    validate_full_commit(source_commit, field="current source commit", errors=errors)
    input_hashes = collect_input_hashes(repo_root, errors)

    if status == PUBLISHED_STATUS:
        if run_id is None:
            errors.append("--run-id is required for published benchmark metadata")
        else:
            validate_run_id(run_id, field="--run-id", errors=errors)
        if fresh_until is None:
            errors.append("--fresh-until is required for published benchmark metadata")
        else:
            parse_iso_date(fresh_until, field="--fresh-until", errors=errors)
    elif fresh_until is not None:
        errors.append("--fresh-until is only valid with --status published")

    if errors:
        return errors

    current: dict[str, Any] = {
        "schema_version": 1,
        "suite_version": SUITE_VERSION,
        "status": status,
        "suites": PUBLIC_SUITES,
        "commands": CANONICAL_COMMANDS,
        "inputs": input_hashes,
        "freshness_days": FRESHNESS_DAYS,
        "source_commit": source_commit,
        "publication_commit": None,
        "updated_at": utc_now(),
        "runner": "./scripts/run_public_benchmarks.sh",
        "checker": "python3 scripts/check_benchmark_publication.py --check",
    }

    if status == PUBLISHED_STATUS:
        assert run_id is not None
        artifact_root = repo_relative_path(
            repo_root, publication_root / run_id, label="benchmark publication run"
        )
        artifact_hashes = collect_artifact_hashes(
            publication_root / run_id, artifact_root, errors
        )
        if errors:
            return errors
        current.update(
            {
                "current_run": run_id,
                "fresh_until": fresh_until,
                "artifact_root": artifact_root,
                "run_context": f"{artifact_root}/run_context.json",
                "required_artifacts": REQUIRED_RUN_ARTIFACTS,
                "artifacts": artifact_hashes,
            }
        )
    else:
        current.update(
            {
                "current_run": None,
                "fresh_until": None,
                "artifact_root": None,
                "run_context": None,
                "required_artifacts": REQUIRED_RUN_ARTIFACTS,
            }
        )

    write_json(publication_root / "current.json", current)
    return []


def validate_input_hashes(
    repo_root: Path,
    expected_inputs: Any,
    errors: list[str],
    *,
    source_commit: str | None,
) -> None:
    if not isinstance(expected_inputs, dict):
        errors.append("current.json inputs must be an object")
        return
    actual_inputs = collect_input_hashes(repo_root, errors)
    source_commit_inputs = (
        collect_source_commit_input_hashes(repo_root, source_commit, errors)
        if source_commit is not None
        else {}
    )
    expected_paths = set(CANONICAL_INPUTS)
    if set(expected_inputs) != expected_paths:
        errors.append(
            "current.json inputs must exactly match canonical benchmark inputs"
        )
        return
    for rel_path in CANONICAL_INPUTS:
        expected = expected_inputs.get(rel_path)
        if not isinstance(expected, dict):
            errors.append(f"input {rel_path} hash entry must be an object")
            continue
        actual = actual_inputs.get(rel_path)
        if actual is None:
            continue
        if expected.get("sha256") != actual.get("sha256"):
            errors.append(f"input {rel_path} sha256 mismatch")
        if expected.get("bytes") != actual.get("bytes"):
            errors.append(f"input {rel_path} byte count mismatch")
        source_commit_actual = source_commit_inputs.get(rel_path)
        if source_commit_actual is None:
            continue
        if expected.get("sha256") != source_commit_actual.get("sha256"):
            errors.append(f"source_commit input {rel_path} sha256 mismatch")
        if expected.get("bytes") != source_commit_actual.get("bytes"):
            errors.append(f"source_commit input {rel_path} byte count mismatch")


def validate_published_paths(
    repo_root: Path,
    publication_root: Path,
    current: dict[str, Any],
    errors: list[str],
) -> None:
    run_id = validate_run_id(
        current.get("current_run"), field="current.json current_run", errors=errors
    )
    if run_id is None:
        return
    run_dir = publication_root / run_id
    try:
        artifact_root = repo_relative_path(
            repo_root, run_dir, label="benchmark publication run"
        )
    except ValueError as exc:
        errors.append(str(exc))
        return
    if current.get("artifact_root") != artifact_root:
        errors.append(f"current.json artifact_root must point at {artifact_root}")
    if current.get("run_context") != f"{artifact_root}/run_context.json":
        errors.append(
            f"current.json run_context must point at {artifact_root}/run_context.json"
        )
    if current.get("required_artifacts") != REQUIRED_RUN_ARTIFACTS:
        errors.append("current.json required_artifacts must match the public contract")
    actual_artifacts = collect_artifact_hashes(run_dir, artifact_root, errors)
    expected_artifacts = current.get("artifacts")
    if not isinstance(expected_artifacts, dict):
        errors.append("current.json artifacts must be an object for published runs")
        return
    if set(expected_artifacts) != set(REQUIRED_RUN_ARTIFACTS):
        errors.append(
            "current.json artifacts must exactly match required public artifacts"
        )
        return
    for rel_path in REQUIRED_RUN_ARTIFACTS:
        expected = expected_artifacts.get(rel_path)
        if not isinstance(expected, dict):
            errors.append(f"artifact {rel_path} hash entry must be an object")
            continue
        actual = actual_artifacts.get(rel_path)
        if actual is None:
            continue
        if expected.get("sha256") != actual.get("sha256"):
            errors.append(f"artifact {rel_path} sha256 mismatch")
        if expected.get("bytes") != actual.get("bytes"):
            errors.append(f"artifact {rel_path} byte count mismatch")
    validate_run_context_schema(run_dir / "run_context.json", errors)


def validate_publication(
    repo_root: Path,
    publication_root: Path,
    *,
    today: date,
    allow_uncommitted_inputs: bool,
    prepublication_source_head: bool,
    launch: bool,
) -> list[str]:
    errors: list[str] = []
    validate_canonical_inputs_clean(
        repo_root, errors, allow_uncommitted_inputs=allow_uncommitted_inputs
    )
    current_path = publication_root / "current.json"
    if not current_path.is_file():
        return [f"missing benchmark publication pointer: {current_path}"]
    current = read_json(current_path)

    if current.get("schema_version") != 1:
        errors.append("current.json schema_version must be 1")
    if current.get("suite_version") != SUITE_VERSION:
        errors.append(f"current.json suite_version must be {SUITE_VERSION}")
    if current.get("suites") != PUBLIC_SUITES:
        errors.append(f"current.json suites must be {PUBLIC_SUITES}")
    if current.get("commands") != CANONICAL_COMMANDS:
        errors.append("current.json commands do not match canonical benchmark commands")
    if current.get("freshness_days") != FRESHNESS_DAYS:
        errors.append(f"current.json freshness_days must be {FRESHNESS_DAYS}")
    if current.get("runner") != "./scripts/run_public_benchmarks.sh":
        errors.append("current.json runner must be ./scripts/run_public_benchmarks.sh")
    if (
        current.get("checker")
        != "python3 scripts/check_benchmark_publication.py --check"
    ):
        errors.append(
            "current.json checker must be python3 scripts/check_benchmark_publication.py --check"
        )
    parse_utc_timestamp(
        current.get("updated_at"), field="current.json updated_at", errors=errors
    )
    validate_full_commit(
        current.get("source_commit"), field="current.json source_commit", errors=errors
    )
    validate_reachable_commit(
        repo_root,
        current.get("source_commit"),
        field="current.json source_commit",
        errors=errors,
    )
    if prepublication_source_head:
        validate_source_commit_matches_head(
            repo_root, current.get("source_commit"), errors
        )
    validate_optional_full_commit(
        current.get("publication_commit"),
        field="current.json publication_commit",
        errors=errors,
    )
    source_commit = current.get("source_commit")
    validate_input_hashes(
        repo_root,
        current.get("inputs"),
        errors,
        source_commit=source_commit
        if isinstance(source_commit, str) and FULL_COMMIT_RE.fullmatch(source_commit)
        else None,
    )

    status = current.get("status")
    if status not in STATUSES:
        errors.append(f"current.json status must be one of {sorted(STATUSES)}")
        return errors

    if status == PENDING_STATUS:
        errors.extend(
            f"current.json {field} must be null while pending"
            for field in ["current_run", "fresh_until", "artifact_root", "run_context"]
            if current.get(field) is not None
        )
        if current.get("required_artifacts") != REQUIRED_RUN_ARTIFACTS:
            errors.append(
                "current.json required_artifacts must match the public contract"
            )
        if launch:
            validate_launch_publication_evidence(
                repo_root, publication_root, current, errors
            )
        return errors

    validate_reachable_publication_commit(
        repo_root, current.get("publication_commit"), errors
    )
    fresh_until = parse_iso_date(
        current.get("fresh_until"), field="current.json fresh_until", errors=errors
    )
    if fresh_until is not None and fresh_until < today:
        errors.append(
            "benchmark publication metadata is stale: "
            f"fresh_until={fresh_until.isoformat()} today={today.isoformat()}"
        )
    validate_published_paths(repo_root, publication_root, current, errors)
    if launch:
        validate_launch_publication_evidence(
            repo_root, publication_root, current, errors
        )
        if not errors:
            validate_publication_commit_artifacts(repo_root, current, errors)
    return errors


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Validate public benchmark publication metadata.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=contract_help_epilog(),
    )
    parser.add_argument("--repo-root", type=Path, default=repo_root_from_script())
    parser.add_argument("--publication-root", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write-current", action="store_true")
    parser.add_argument("--run-id")
    parser.add_argument(
        "--status",
        choices=sorted(STATUSES),
        default=PENDING_STATUS,
        help="Publication state to write with --write-current.",
    )
    parser.add_argument("--fresh-until")
    parser.add_argument(
        "--fresh-days",
        default=str(FRESHNESS_DAYS),
        help="Freshness window for published metadata when --fresh-until is omitted.",
    )
    parser.add_argument("--today")
    parser.add_argument(
        "--allow-uncommitted-inputs",
        action="store_true",
        help="Allow dirty canonical inputs when bootstrapping metadata.",
    )
    parser.add_argument(
        "--prepublication-source-head",
        action="store_true",
        help=(
            "Local pre-publication check: require current.json source_commit to "
            "equal the checked-out HEAD before committing refreshed metadata."
        ),
    )
    parser.add_argument(
        "--stale-branch-base",
        metavar="REF",
        help=(
            "Fail if this branch changes canonical benchmark inputs but is not "
            "based on REF, for example origin/main after git fetch."
        ),
    )
    parser.add_argument(
        "--launch",
        "--release",
        dest="launch",
        action="store_true",
        help=(
            "Release/launch check for public performance claims: require "
            "fresh published benchmark artifacts, a publication_commit, and "
            "committed publication evidence."
        ),
    )
    return parser


def parse_fresh_days(value: str, errors: list[str]) -> int | None:
    if not re.fullmatch(r"\d+", value):
        errors.append("--fresh-days must be a non-negative integer")
        return None
    return int(value)


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    repo_root = args.repo_root.resolve()
    publication_root = (
        args.publication_root.resolve()
        if args.publication_root
        else repo_root / "reports" / "benchmarks" / "publication"
    )

    errors: list[str] = []
    today = (
        parse_iso_date(args.today, field="--today", errors=errors)
        if args.today is not None
        else date.today()
    )
    fresh_days = parse_fresh_days(args.fresh_days, errors)
    fresh_until = args.fresh_until
    if args.status == PUBLISHED_STATUS and fresh_until is None and today is not None:
        assert fresh_days is not None
        fresh_until = (today + timedelta(days=fresh_days)).isoformat()
    if fresh_until is not None:
        parse_iso_date(fresh_until, field="--fresh-until", errors=errors)
    if args.run_id is not None:
        validate_run_id(args.run_id, field="--run-id", errors=errors)
    if not args.check and not args.write_current:
        args.check = True

    if not errors and args.write_current:
        errors.extend(
            write_current(
                repo_root,
                publication_root,
                run_id=args.run_id,
                status=args.status,
                fresh_until=fresh_until,
                allow_uncommitted_inputs=args.allow_uncommitted_inputs,
            )
        )

    if not errors and args.check:
        if args.stale_branch_base is not None:
            validate_stale_branch_guard(repo_root, args.stale_branch_base, errors)
        assert today is not None
        errors.extend(
            validate_publication(
                repo_root,
                publication_root,
                today=today,
                allow_uncommitted_inputs=args.allow_uncommitted_inputs,
                prepublication_source_head=args.prepublication_source_head,
                launch=args.launch,
            )
        )

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print("CLEAN: benchmark publication contract is current")
    return 0


if __name__ == "__main__":
    sys.exit(main())
