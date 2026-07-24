# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Local research replay harness for clean research manifests.

This script is intentionally independent of GitHub Actions. It performs cheap,
deterministic checks that are useful for local and nightly replay:

- load and validate the cross-repo research lock JSON
- load and lightly validate the research program manifest JSON
- run `clean research status --json --manifest <manifest>` when a local clean
  binary exists and `--dry-run` was not requested

Missing `target/debug/clean` is reported as a skipped check by default. Use
`--require-clean-bin` to make an absent binary fail the replay.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections.abc import Sequence
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import tomllib

try:
    from scripts import research_lock
except ImportError:  # pragma: no cover - direct script execution fallback
    import research_lock  # type: ignore[no-redef]


SCHEMA_VERSION = 1
DEFAULT_LOCK = Path("data/research_program_lock.json")
DEFAULT_MANIFEST = Path("data/research_program_manifest.json")
DEFAULT_clean_BIN = Path("target/debug/clean")
DEFAULT_GAMMA_CROWN_REGISTRY = Path("../gamma-crown/conjectures/registry.toml")
DEFAULT_TIMEOUT_SEC = 120
DEFAULT_GIT_TIMEOUT_SEC = 10
DETERMINISTIC_GENERATED_AT = "1970-01-01T00:00:00Z"

STATUS_PASSED = "passed"
STATUS_FAILED = "failed"
STATUS_SKIPPED = "skipped"

RESEARCH_STATUSES = {
    "Refuted",
    "EmpiricalTested",
    "ExecutableChecked",
    "ProofCarrying",
    "KernelProved",
    "Axiomatized",
    "DerivedPending",
}
ARTIFACT_STATES = {
    "NotApplicable",
    "Planned",
    "FixtureOnly",
    "Replayable",
}
PROMOTION_GATES = {
    "KernelProofAndAxiomAudit",
    "TrustReportAgreement",
    "ArtifactReplayAndKernelImport",
}
GIT_COMPONENT_KINDS = {"git_repository", "git_dependency"}
FULL_GIT_REVISION_RE = re.compile(r"^(?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})$")
clean_PROOF_CLAIM_RE = re.compile(
    r"(?:Proved sound:\s*clean|clean proved|clean proved).*?\b([CT]\d{3})\b",
    re.IGNORECASE,
)
PROOF_RISK_PHRASES = (
    "experimental",
    "pending clean",
    "pending clean formalization",
    "hypothesis-wrapped",
    "hypothesis wrapped",
    "sorry",
)


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def display_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(Path.cwd().resolve()))
    except (OSError, ValueError):
        return str(path)


def is_nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def is_full_git_revision(value: Any) -> bool:
    return isinstance(value, str) and FULL_GIT_REVISION_RE.fullmatch(value) is not None


def is_null_git_revision(value: Any) -> bool:
    return isinstance(value, str) and bool(value) and set(value) == {"0"}


def validate_full_git_revision(
    value: Any,
    path: str,
    errors: list[str],
) -> None:
    if not is_nonempty_string(value):
        return
    if is_null_git_revision(value) or not is_full_git_revision(value):
        errors.append(
            f"{path}: revision must be a full non-null 40- or 64-character "
            "hexadecimal git revision"
        )


def lock_git_component_ids(lock: dict[str, Any]) -> set[str]:
    components = lock.get("components")
    if not isinstance(components, list):
        return set()

    ids: set[str] = set()
    for component in components:
        if not isinstance(component, dict):
            continue
        if component.get("kind") not in GIT_COMPONENT_KINDS:
            continue
        component_id = component.get("id")
        if is_nonempty_string(component_id):
            ids.add(component_id)
    return ids


def repo_matches_git_component(repo: Any, git_component_ids: set[str]) -> bool:
    if not is_nonempty_string(repo):
        return False
    return any(
        repo == component_id or repo.endswith(f"/{component_id}")
        for component_id in git_component_ids
    )


def registry_entry_producer_revision_errors(
    lock: dict[str, Any],
    git_component_ids: set[str],
) -> list[str]:
    registry = lock.get("artifact_registry")
    if not isinstance(registry, dict):
        return []

    entries = registry.get("entries")
    if not isinstance(entries, list):
        return []

    errors: list[str] = []
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            continue
        producer = entry.get("producer")
        if not isinstance(producer, dict):
            continue
        if not repo_matches_git_component(producer.get("repo"), git_component_ids):
            continue
        validate_full_git_revision(
            producer.get("revision"),
            f"$.artifact_registry.entries[{index}].producer.revision",
            errors,
        )
    return errors


def example_producer_revision_errors(
    lock: dict[str, Any],
    git_component_ids: set[str],
) -> list[str]:
    examples = lock.get("example")
    if not isinstance(examples, dict):
        return []

    errors: list[str] = []
    for name, payload in examples.items():
        if not isinstance(payload, dict):
            continue
        producer = payload.get("producer")
        if not isinstance(producer, dict):
            continue
        if not repo_matches_git_component(producer.get("repo"), git_component_ids):
            continue
        validate_full_git_revision(
            producer.get("revision"),
            f"$.example.{name}.producer.revision",
            errors,
        )
    return errors


def producer_revision_strength_errors(lock: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    git_component_ids = lock_git_component_ids(lock)

    components = lock.get("components")
    if isinstance(components, list):
        for index, component in enumerate(components):
            if not isinstance(component, dict):
                continue
            if component.get("kind") not in GIT_COMPONENT_KINDS:
                continue
            validate_full_git_revision(
                component.get("revision"),
                f"$.components[{index}].revision",
                errors,
            )

    errors.extend(registry_entry_producer_revision_errors(lock, git_component_ids))
    errors.extend(example_producer_revision_errors(lock, git_component_ids))
    return errors


def check_result(
    *,
    name: str,
    status: str,
    detail: str,
    path: Path | None = None,
    command: Sequence[str] | None = None,
    exit_code: int | None = None,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "name": name,
        "status": status,
        "detail": detail,
    }
    if path is not None:
        result["path"] = display_path(path)
    if command is not None:
        result["command"] = list(command)
    if exit_code is not None:
        result["exit_code"] = exit_code
    if extra:
        result.update(extra)
    return result


def load_json_file(path: Path) -> tuple[Any | None, dict[str, Any]]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None, check_result(
            name="load_json",
            status=STATUS_FAILED,
            detail="file not found",
            path=path,
        )
    except json.JSONDecodeError as exc:
        return None, check_result(
            name="load_json",
            status=STATUS_FAILED,
            detail=f"invalid JSON at line {exc.lineno}: {exc.msg}",
            path=path,
        )
    except OSError as exc:
        return None, check_result(
            name="load_json",
            status=STATUS_FAILED,
            detail=str(exc),
            path=path,
        )
    return payload, check_result(
        name="load_json",
        status=STATUS_PASSED,
        detail="loaded JSON",
        path=path,
    )


def validate_lock_shape(path: Path) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    payload, load_check = load_json_file(path)
    if payload is None:
        load_check["name"] = "load_lock_json"
        return None, load_check
    if not isinstance(payload, dict):
        return None, check_result(
            name="load_lock_json",
            status=STATUS_FAILED,
            detail="lock JSON must be an object",
            path=path,
        )

    validation = research_lock.validate_lock_payload(payload, path)
    if not validation.valid:
        errors = [f"{error.path}: {error.message}" for error in validation.errors]
        detail = "; ".join(errors[:5])
        if len(errors) > 5:
            detail += f"; +{len(errors) - 5} more"
        return None, check_result(
            name="load_lock_json",
            status=STATUS_FAILED,
            detail=detail,
            path=path,
            extra={
                "error_count": len(validation.errors),
                "warning_count": len(validation.warnings),
                "errors": errors,
                "warnings": [
                    f"{warning.path}: {warning.message}"
                    for warning in validation.warnings
                ],
            },
        )

    hardening_errors = producer_revision_strength_errors(payload)
    if hardening_errors:
        detail = "; ".join(hardening_errors[:5])
        if len(hardening_errors) > 5:
            detail += f"; +{len(hardening_errors) - 5} more"
        return None, check_result(
            name="load_lock_json",
            status=STATUS_FAILED,
            detail=detail,
            path=path,
            extra={
                "error_count": len(hardening_errors),
                "warning_count": len(validation.warnings),
                "errors": hardening_errors,
                "warnings": [
                    f"{warning.path}: {warning.message}"
                    for warning in validation.warnings
                ],
            },
        )

    return payload, check_result(
        name="load_lock_json",
        status=STATUS_PASSED,
        detail="validated research lock contract",
        path=path,
        extra={
            "error_count": 0,
            "warning_count": len(validation.warnings),
            "warnings": [
                f"{warning.path}: {warning.message}" for warning in validation.warnings
            ],
        },
    )


def resolve_declared_path(raw_path: str, lock_path: Path) -> Path:
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = lock_path.parent / path
    return path


def source_local_path(component: dict[str, Any], lock_path: Path) -> Path | None:
    source = component.get("source")
    if not is_nonempty_string(source) or not source.startswith("local:"):
        return None

    raw_path = source[len("local:") :]
    if not raw_path.strip():
        return None
    return resolve_declared_path(raw_path, lock_path)


def declared_checkout_workspace(
    component: dict[str, Any],
    lock_path: Path,
) -> tuple[Path | None, str | None]:
    workspace = component.get("workspace")
    workspace_field = "workspace"

    observed_checkout = component.get("observed_checkout")
    if workspace is None and isinstance(observed_checkout, dict):
        workspace = observed_checkout.get("workspace")
        workspace_field = "observed_checkout.workspace"

    if workspace is not None:
        if not is_nonempty_string(workspace):
            return None, f"{workspace_field} must be a non-empty string"
        return resolve_declared_path(workspace, lock_path), None

    path = source_local_path(component, lock_path)
    if path is not None:
        return path, None

    return None, "workspace not declared"


def has_local_checkout_declaration(component: dict[str, Any]) -> bool:
    if "workspace" in component or "observed_checkout" in component:
        return True
    source = component.get("source")
    return is_nonempty_string(source) and source.startswith("local:")


def is_cross_repo_producer_component(
    component: dict[str, Any],
    owner_repo: Any,
) -> bool:
    kind = component.get("kind")
    if kind not in GIT_COMPONENT_KINDS:
        return False

    component_id = component.get("id")
    if (
        is_nonempty_string(component_id)
        and is_nonempty_string(owner_repo)
        and (component_id == owner_repo or owner_repo.endswith(f"/{component_id}"))
    ):
        return False

    lock_role = component.get("lock_role")
    if not (isinstance(lock_role, str) and "producer" in lock_role.lower()):
        return False

    return has_local_checkout_declaration(component)


def short_revision(revision: Any) -> str:
    if not isinstance(revision, str):
        return str(revision)
    return revision[:12] if len(revision) > 12 else revision


def run_git(
    workspace: Path,
    args: Sequence[str],
    timeout_sec: int = DEFAULT_GIT_TIMEOUT_SEC,
) -> tuple[subprocess.CompletedProcess[str] | None, str | None]:
    env = dict(os.environ)
    env["GIT_OPTIONAL_LOCKS"] = "0"
    command = ["git", "-C", str(workspace), *args]
    try:
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
            env=env,
        )
    except subprocess.TimeoutExpired:
        return None, f"git {' '.join(args)} timed out after {timeout_sec}s"
    except OSError as exc:
        return None, f"could not run git {' '.join(args)}: {exc}"

    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).strip()
        return completed, detail or f"git {' '.join(args)} failed"
    return completed, None


def git_checkout_state(workspace: Path) -> tuple[dict[str, Any] | None, str | None]:
    if not workspace.exists():
        return None, f"workspace path does not exist: {workspace}"
    if not workspace.is_dir():
        return None, f"workspace path is not a directory: {workspace}"

    revision_proc, revision_error = run_git(workspace, ["rev-parse", "HEAD"])
    if revision_error is not None:
        return None, f"could not inspect git revision: {revision_error}"
    assert revision_proc is not None

    revision = revision_proc.stdout.strip()
    if not revision:
        return None, "git rev-parse returned an empty revision"

    status_proc, status_error = run_git(
        workspace,
        ["status", "--porcelain=v1", "--untracked-files=normal"],
    )
    if status_error is not None:
        return None, f"could not inspect git status: {status_error}"
    assert status_proc is not None

    dirty_entries = [
        line[3:] if len(line) > 3 else line
        for line in status_proc.stdout.splitlines()
        if line
    ]
    return {
        "revision": revision,
        "dirty": bool(dirty_entries),
        "dirty_path_count": len(dirty_entries),
        "dirty_paths": dirty_entries[:10],
    }, None


def checkout_issue_label(issue: str) -> str:
    return issue.split(":", 1)[0]


def inspect_local_producer_checkout(
    *,
    component: dict[str, Any],
    component_index: int,
    lock_path: Path,
) -> dict[str, Any]:
    component_id = component.get("id")
    if not is_nonempty_string(component_id):
        component_id = f"component[{component_index}]"

    workspace, workspace_error = declared_checkout_workspace(component, lock_path)
    observed_checkout = component.get("observed_checkout")
    if observed_checkout is None:
        observed_checkout = {}
    elif not isinstance(observed_checkout, dict):
        observed_checkout = {}
        workspace_error = workspace_error or "observed_checkout must be an object"

    issues: list[str] = []
    checkout: dict[str, Any] = {
        "id": component_id,
        "component_index": component_index,
        "status": STATUS_PASSED,
    }

    expected_revision = component.get("revision")
    observed_revision = observed_checkout.get("revision")
    observed_dirty = observed_checkout.get("dirty")

    if is_nonempty_string(expected_revision):
        checkout["expected_revision"] = expected_revision
        if is_null_git_revision(expected_revision) or not is_full_git_revision(
            expected_revision
        ):
            issues.append(
                "weak locked revision: revision must be a full non-null "
                "40- or 64-character hexadecimal git revision"
            )
    else:
        issues.append("missing locked revision: revision must be a non-empty string")

    if is_nonempty_string(observed_revision):
        checkout["observed_revision"] = observed_revision
        if is_null_git_revision(observed_revision) or not is_full_git_revision(
            observed_revision
        ):
            issues.append(
                "weak observed_checkout.revision: revision must be a full non-null "
                "40- or 64-character hexadecimal git revision"
            )
        if (
            is_nonempty_string(expected_revision)
            and observed_revision != expected_revision
        ):
            issues.append(
                "observed_checkout revision drift: "
                f"locked {short_revision(expected_revision)} "
                f"observed {short_revision(observed_revision)}"
            )
    elif observed_revision is not None:
        issues.append("invalid observed_checkout.revision: must be a non-empty string")

    if isinstance(observed_dirty, bool):
        checkout["observed_dirty"] = observed_dirty
        if observed_dirty:
            issues.append("observed_checkout dirty flag is true")
    elif observed_dirty is not None:
        issues.append("invalid observed_checkout.dirty: must be boolean")

    observed_ahead = observed_checkout.get("ahead_of_remote")
    if isinstance(observed_ahead, bool):
        checkout["observed_ahead_of_remote"] = observed_ahead
        if observed_ahead:
            issues.append("observed_checkout ahead_of_remote is true")
    elif isinstance(observed_ahead, int):
        checkout["observed_ahead_of_remote"] = observed_ahead
        if observed_ahead > 0:
            issues.append(
                "observed_checkout ahead_of_remote is positive: "
                f"{observed_ahead} commit(s)"
            )
    elif observed_ahead is not None:
        issues.append(
            "invalid observed_checkout.ahead_of_remote: must be boolean or integer"
        )

    if workspace_error is not None:
        issues.append(f"missing workspace: {workspace_error}")
    elif workspace is not None:
        checkout["workspace"] = display_path(workspace)
        state, state_error = git_checkout_state(workspace)
        if state_error is not None:
            issues.append(f"missing workspace: {state_error}")
        elif state is not None:
            actual_revision = state["revision"]
            checkout["actual_revision"] = actual_revision
            checkout["dirty"] = state["dirty"]
            checkout["dirty_path_count"] = state["dirty_path_count"]
            if state["dirty_paths"]:
                checkout["dirty_paths"] = state["dirty_paths"]

            if (
                is_nonempty_string(expected_revision)
                and actual_revision != expected_revision
            ):
                issues.append(
                    "revision mismatch: "
                    f"locked {short_revision(expected_revision)} "
                    f"actual {short_revision(actual_revision)}"
                )

            if (
                is_nonempty_string(observed_revision)
                and actual_revision != observed_revision
            ):
                issues.append(
                    "observed_checkout stale: "
                    f"observed {short_revision(observed_revision)} "
                    f"actual {short_revision(actual_revision)}"
                )

            if state["dirty"]:
                issues.append(
                    f"dirty checkout state: {state['dirty_path_count']} changed path(s)"
                )

    if issues:
        checkout["status"] = STATUS_FAILED
        checkout["issues"] = issues

    return checkout


def validate_local_producer_checkouts(
    lock: dict[str, Any],
    lock_path: Path,
) -> dict[str, Any]:
    components = lock.get("components")
    if not isinstance(components, list):
        return check_result(
            name="local_producer_checkouts",
            status=STATUS_SKIPPED,
            detail="lock components are unavailable",
            path=lock_path,
        )

    owner_repo = lock.get("owner_repo")
    selected = [
        (index, component)
        for index, component in enumerate(components)
        if isinstance(component, dict)
        and is_cross_repo_producer_component(component, owner_repo)
    ]

    if not selected:
        return check_result(
            name="local_producer_checkouts",
            status=STATUS_SKIPPED,
            detail="no cross-repo local producer checkouts declared",
            path=lock_path,
        )

    checkouts = [
        inspect_local_producer_checkout(
            component=component,
            component_index=index,
            lock_path=lock_path,
        )
        for index, component in selected
    ]
    failed = [checkout for checkout in checkouts if checkout["status"] == STATUS_FAILED]

    if failed:
        failed_details = []
        for checkout in failed:
            labels = "; ".join(
                dict.fromkeys(
                    checkout_issue_label(issue) for issue in checkout["issues"]
                )
            )
            failed_details.append(f"{checkout['id']} ({labels})")
        return check_result(
            name="local_producer_checkouts",
            status=STATUS_FAILED,
            detail="failed checkouts: " + "; ".join(failed_details),
            path=lock_path,
            extra={
                "checkout_count": len(checkouts),
                "checkouts": checkouts,
            },
        )

    ids = ", ".join(str(checkout["id"]) for checkout in checkouts)
    return check_result(
        name="local_producer_checkouts",
        status=STATUS_PASSED,
        detail=f"validated local producer checkouts: {ids}",
        path=lock_path,
        extra={
            "checkout_count": len(checkouts),
            "checkouts": checkouts,
        },
    )


def validate_manifest_shape(path: Path) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    payload, load_check = load_json_file(path)
    if payload is None:
        load_check["name"] = "load_manifest_json"
        return None, load_check
    if not isinstance(payload, dict):
        return None, check_result(
            name="load_manifest_json",
            status=STATUS_FAILED,
            detail="manifest JSON must be an object",
            path=path,
        )

    errors = []
    schema_version = payload.get("schema_version")
    if not isinstance(schema_version, int) or isinstance(schema_version, bool):
        errors.append("schema_version must be int")
    generated_at = payload.get("generated_at")
    if not isinstance(generated_at, str) or not generated_at:
        errors.append("generated_at must be non-empty string")
    source = payload.get("source")
    if not isinstance(source, str) or not source:
        errors.append("source must be non-empty string")
    items = payload.get("items")
    if not isinstance(items, list):
        errors.append("items must be list")
    elif not items:
        errors.append("items must be non-empty")
    else:
        seen_ids: set[str] = set()
        for index, item in enumerate(items):
            if not isinstance(item, dict):
                errors.append(f"items[{index}] must be object")
                continue
            item_id = item.get("id")
            if not isinstance(item_id, str) or not item_id:
                errors.append(f"items[{index}].id must be non-empty string")
                continue
            if item_id in seen_ids:
                errors.append(f"duplicate item id {item_id}")
            seen_ids.add(item_id)
            for field in (
                "title",
                "owner_repo",
                "domain",
                "family",
                "summary",
                "artifact_state",
                "promotion_gate",
            ):
                value = item.get(field)
                if not isinstance(value, str) or not value:
                    errors.append(f"items[{index}].{field} must be non-empty string")
            status = item.get("status")
            if not isinstance(status, str) or not status:
                errors.append(f"items[{index}].status must be non-empty string")
            elif status not in RESEARCH_STATUSES:
                errors.append(f"items[{index}].status must be a known research status")
            artifact_state = item.get("artifact_state")
            if (
                isinstance(artifact_state, str)
                and artifact_state not in ARTIFACT_STATES
            ):
                errors.append(
                    f"items[{index}].artifact_state must be a known artifact state"
                )
            promotion_gate = item.get("promotion_gate")
            if (
                isinstance(promotion_gate, str)
                and promotion_gate not in PROMOTION_GATES
            ):
                errors.append(
                    f"items[{index}].promotion_gate must be a known promotion gate"
                )
            dependencies = item.get("dependencies")
            if not isinstance(dependencies, list):
                errors.append(f"items[{index}].dependencies must be list")
            else:
                for dep_index, dep in enumerate(dependencies):
                    if not isinstance(dep, dict):
                        errors.append(
                            f"items[{index}].dependencies[{dep_index}] must be object"
                        )
                        continue
                    dep_id = dep.get("id")
                    reason = dep.get("reason")
                    if not isinstance(dep_id, str) or not dep_id:
                        errors.append(
                            f"items[{index}].dependencies[{dep_index}].id must be non-empty string"
                        )
                    if not isinstance(reason, str) or not reason:
                        errors.append(
                            f"items[{index}].dependencies[{dep_index}].reason must be non-empty string"
                        )
            for list_field in ("evidence", "references", "tags"):
                value = item.get(list_field)
                if not isinstance(value, list):
                    errors.append(f"items[{index}].{list_field} must be list")

    if errors:
        return None, check_result(
            name="load_manifest_json",
            status=STATUS_FAILED,
            detail="; ".join(errors[:6]),
            path=path,
        )

    return payload, check_result(
        name="load_manifest_json",
        status=STATUS_PASSED,
        detail=f"schema_version={schema_version}; items={len(items)}",
        path=path,
    )


def manifest_status_by_id(manifest: dict[str, Any]) -> dict[str, str]:
    items = manifest.get("items")
    if not isinstance(items, list):
        return {}
    statuses: dict[str, str] = {}
    for item in items:
        if not isinstance(item, dict):
            continue
        item_id = item.get("id")
        status = item.get("status")
        if isinstance(item_id, str) and isinstance(status, str):
            statuses[item_id] = status
    return statuses


def text_contains_proof_risk(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    lower = value.lower()
    return any(phrase in lower for phrase in PROOF_RISK_PHRASES)


def gamma_crown_claim_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for subdir in ("conjectures", "crates"):
        base = root / subdir
        if not base.exists() or not base.is_dir():
            continue
        for path in base.rglob("*"):
            if not path.is_file() or path.suffix not in {".md", ".rs", ".toml"}:
                continue
            files.append(path)
    return files


def stale_clean_doc_claim_errors(
    registry_path: Path,
    manifest_statuses: dict[str, str],
) -> list[str]:
    root = registry_path.parent.parent
    errors: list[str] = []
    for path in gamma_crown_claim_files(root):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError as exc:
            errors.append(
                f"{display_path(path)}: could not read for proof-claim scan: {exc}"
            )
            continue
        for line_no, line in enumerate(lines, start=1):
            for match in clean_PROOF_CLAIM_RE.finditer(line):
                claim_id = match.group(1)
                clean_status = manifest_statuses.get(claim_id)
                if clean_status != "KernelProved":
                    errors.append(
                        f"{display_path(path)}:{line_no}: clean proof claim for "
                        f"{claim_id} but manifest status is {clean_status or 'missing'}"
                    )
    return errors


def validate_gamma_crown_registry_truth(
    *,
    manifest: dict[str, Any],
    registry_path: Path,
) -> dict[str, Any]:
    if not registry_path.exists():
        return check_result(
            name="gamma_crown_registry_truth",
            status=STATUS_SKIPPED,
            detail="Gamma-Crown registry not found",
            path=registry_path,
        )

    try:
        registry = tomllib.loads(registry_path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as exc:
        return check_result(
            name="gamma_crown_registry_truth",
            status=STATUS_FAILED,
            detail=f"invalid TOML at line {exc.lineno}: {exc.msg}",
            path=registry_path,
        )
    except OSError as exc:
        return check_result(
            name="gamma_crown_registry_truth",
            status=STATUS_FAILED,
            detail=str(exc),
            path=registry_path,
        )

    conjectures = registry.get("conjecture")
    if not isinstance(conjectures, list):
        return check_result(
            name="gamma_crown_registry_truth",
            status=STATUS_FAILED,
            detail="registry must contain [[conjecture]] entries",
            path=registry_path,
        )

    manifest_statuses = manifest_status_by_id(manifest)
    errors: list[str] = []
    checked = 0
    for index, entry in enumerate(conjectures):
        if not isinstance(entry, dict):
            errors.append(f"conjecture[{index}] must be a table")
            continue
        claim_id = entry.get("id")
        status = entry.get("status")
        if not isinstance(claim_id, str) or not claim_id:
            errors.append(f"conjecture[{index}].id must be non-empty string")
            continue
        if not isinstance(status, str) or not status:
            errors.append(f"{claim_id}: status must be non-empty string")
            continue
        checked += 1

        clean_status = manifest_statuses.get(claim_id)
        if (
            status in {"PROVEN", "clean_KERNEL_PROVED"}
            and clean_status != "KernelProved"
        ):
            errors.append(
                f"{claim_id}: registry status {status} requires clean "
                f"KernelProved, got {clean_status or 'missing'}"
            )
        if status == "IMPLEMENTED":
            errors.append(
                f"{claim_id}: registry status IMPLEMENTED is not a proof status; "
                "use IMPLEMENTED_UNPROVEN or split proof and implementation fields"
            )
        if status == "PROVEN":
            for field in ("confirmed_by", "note", "description", "revision"):
                if text_contains_proof_risk(entry.get(field)):
                    errors.append(
                        f"{claim_id}: PROVEN registry entry contains proof-risk "
                        f"wording in {field}"
                    )

    errors.extend(stale_clean_doc_claim_errors(registry_path, manifest_statuses))

    if errors:
        detail = "; ".join(errors[:5])
        if len(errors) > 5:
            detail += f"; +{len(errors) - 5} more"
        return check_result(
            name="gamma_crown_registry_truth",
            status=STATUS_FAILED,
            detail=detail,
            path=registry_path,
            extra={"error_count": len(errors), "errors": errors, "checked": checked},
        )

    return check_result(
        name="gamma_crown_registry_truth",
        status=STATUS_PASSED,
        detail=f"validated {checked} registry entries against clean manifest",
        path=registry_path,
        extra={"error_count": 0, "checked": checked},
    )


def run_clean_research_status(
    *,
    clean_bin: Path,
    manifest: Path,
    dry_run: bool,
    require_clean_bin: bool,
    timeout_sec: int = DEFAULT_TIMEOUT_SEC,
) -> dict[str, Any]:
    command = [
        str(clean_bin),
        "research",
        "status",
        "--json",
        "--manifest",
        str(manifest),
    ]

    if dry_run:
        return check_result(
            name="clean_research_status",
            status=STATUS_SKIPPED,
            detail="dry-run requested",
            path=clean_bin,
            command=command,
        )

    if not clean_bin.exists():
        status = STATUS_FAILED if require_clean_bin else STATUS_SKIPPED
        detail = f"clean binary not found at {clean_bin}"
        if not require_clean_bin:
            detail += "; use --require-clean-bin to fail on this condition"
        return check_result(
            name="clean_research_status",
            status=status,
            detail=detail,
            path=clean_bin,
            command=command,
        )

    try:
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail=f"command timed out after {timeout_sec}s",
            path=clean_bin,
            command=command,
        )
    except OSError as exc:
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail=str(exc),
            path=clean_bin,
            command=command,
        )

    if completed.returncode != 0:
        stderr = completed.stderr.strip()
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail=stderr or f"command exited {completed.returncode}",
            path=clean_bin,
            command=command,
            exit_code=completed.returncode,
        )

    try:
        status_payload = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail=f"command stdout was not JSON at line {exc.lineno}: {exc.msg}",
            path=clean_bin,
            command=command,
            exit_code=completed.returncode,
        )

    if not isinstance(status_payload, dict):
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail="command stdout JSON must be an object",
            path=clean_bin,
            command=command,
            exit_code=completed.returncode,
        )

    total_entries = status_payload.get("total_entries")
    entries = status_payload.get("entries")
    status_counts = status_payload.get("status_counts")
    if not isinstance(total_entries, int) or isinstance(total_entries, bool):
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail="command JSON missing integer total_entries",
            path=clean_bin,
            command=command,
            exit_code=completed.returncode,
        )
    if not isinstance(entries, list):
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail="command JSON missing entries list",
            path=clean_bin,
            command=command,
            exit_code=completed.returncode,
        )
    if len(entries) != total_entries:
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail="command JSON total_entries does not match entries length",
            path=clean_bin,
            command=command,
            exit_code=completed.returncode,
        )
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            return check_result(
                name="clean_research_status",
                status=STATUS_FAILED,
                detail=f"command JSON entries[{index}] must be object",
                path=clean_bin,
                command=command,
                exit_code=completed.returncode,
            )
        for field in ("id", "owner_repo", "status", "artifact_state", "promotion_gate"):
            value = entry.get(field)
            if not isinstance(value, str) or not value:
                return check_result(
                    name="clean_research_status",
                    status=STATUS_FAILED,
                    detail=f"command JSON entries[{index}].{field} must be non-empty string",
                    path=clean_bin,
                    command=command,
                    exit_code=completed.returncode,
                )
    if not isinstance(status_counts, dict):
        return check_result(
            name="clean_research_status",
            status=STATUS_FAILED,
            detail="command JSON missing status_counts object",
            path=clean_bin,
            command=command,
            exit_code=completed.returncode,
        )

    return check_result(
        name="clean_research_status",
        status=STATUS_PASSED,
        detail="clean research status completed",
        path=clean_bin,
        command=command,
        exit_code=completed.returncode,
        extra={
            "manifest_item_count": total_entries,
            "status_counts": status_counts,
        },
    )


def overall_status(checks: Sequence[dict[str, Any]]) -> str:
    return (
        STATUS_FAILED
        if any(check["status"] == STATUS_FAILED for check in checks)
        else STATUS_PASSED
    )


def build_summary(
    *,
    lock: Path,
    manifest: Path,
    clean_bin: Path,
    dry_run: bool,
    require_clean_bin: bool,
    gamma_crown_registry: Path = DEFAULT_GAMMA_CROWN_REGISTRY,
    skip_local_producer_checkouts: bool = False,
    skip_gamma_crown_truth_gate: bool = False,
    generated_at: str | None = None,
) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    lock_payload, lock_check = validate_lock_shape(lock)
    checks.append(lock_check)
    if lock_payload is not None:
        if skip_local_producer_checkouts:
            checks.append(
                check_result(
                    name="local_producer_checkouts",
                    status=STATUS_SKIPPED,
                    detail="skipped by --skip-local-producer-checkouts",
                    path=lock,
                )
            )
        else:
            checks.append(validate_local_producer_checkouts(lock_payload, lock))
    manifest_payload, manifest_check = validate_manifest_shape(manifest)
    checks.append(manifest_check)
    if skip_gamma_crown_truth_gate:
        checks.append(
            check_result(
                name="gamma_crown_registry_truth",
                status=STATUS_SKIPPED,
                detail="skipped by --skip-gamma-crown-truth-gate",
                path=gamma_crown_registry,
            )
        )
    elif manifest_payload is None:
        checks.append(
            check_result(
                name="gamma_crown_registry_truth",
                status=STATUS_SKIPPED,
                detail="manifest validation failed",
                path=gamma_crown_registry,
            )
        )
    else:
        checks.append(
            validate_gamma_crown_registry_truth(
                manifest=manifest_payload,
                registry_path=gamma_crown_registry,
            )
        )
    checks.append(
        run_clean_research_status(
            clean_bin=clean_bin,
            manifest=manifest,
            dry_run=dry_run,
            require_clean_bin=require_clean_bin,
        )
    )

    return {
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": "research_replay",
        "generated_at": generated_at or utc_now(),
        "overall_status": overall_status(checks),
        "inputs": {
            "lock": display_path(lock),
            "manifest": display_path(manifest),
            "clean_bin": display_path(clean_bin),
            "gamma_crown_registry": display_path(gamma_crown_registry),
            "dry_run": dry_run,
            "require_clean_bin": require_clean_bin,
            "skip_local_producer_checkouts": skip_local_producer_checkouts,
            "skip_gamma_crown_truth_gate": skip_gamma_crown_truth_gate,
        },
        "checks": checks,
    }


def markdown_escape(value: Any) -> str:
    if value is None:
        return "-"
    return str(value).replace("\n", " ").replace("|", "\\|")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# clean Research Replay",
        "",
        f"Generated: `{summary['generated_at']}`",
        f"Overall status: `{summary['overall_status']}`",
        "",
        "## Inputs",
        "",
    ]
    inputs = summary["inputs"]
    lines.extend(
        f"- {key}: `{inputs[key]}`"
        for key in (
            "lock",
            "manifest",
            "clean_bin",
            "gamma_crown_registry",
            "dry_run",
            "require_clean_bin",
            "skip_local_producer_checkouts",
            "skip_gamma_crown_truth_gate",
        )
        if key in inputs
    )

    lines.extend(
        [
            "",
            "## Checks",
            "",
            "| Check | Status | Detail |",
            "| --- | --- | --- |",
        ]
    )
    lines.extend(
        (
            "| {name} | {status} | {detail} |".format(
                name=markdown_escape(check["name"]),
                status=markdown_escape(check["status"]),
                detail=markdown_escape(check["detail"]),
            )
        )
        for check in summary["checks"]
    )

    command_checks = [check for check in summary["checks"] if check.get("command")]
    if command_checks:
        lines.extend(["", "## Commands", ""])
        lines.extend(
            f"- `{check['name']}`: `{' '.join(check['command'])}`"
            for check in command_checks
        )

    return "\n".join(lines) + "\n"


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run local/nightly replay checks for clean research manifests."
    )
    parser.add_argument(
        "--lock", type=Path, default=DEFAULT_LOCK, help="research lock JSON"
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help="research program manifest JSON",
    )
    parser.add_argument(
        "--clean-bin",
        type=Path,
        default=DEFAULT_clean_BIN,
        help="local clean binary",
    )
    parser.add_argument(
        "--gamma-crown-registry",
        type=Path,
        default=DEFAULT_GAMMA_CROWN_REGISTRY,
        help="Gamma-Crown conjecture registry TOML",
    )
    parser.add_argument("--json-output", type=Path, help="write JSON summary to PATH")
    parser.add_argument(
        "--markdown-output", type=Path, help="write Markdown report to PATH"
    )
    parser.add_argument("--dry-run", action="store_true", help="skip command execution")
    parser.add_argument(
        "--require-clean-bin",
        action="store_true",
        help="fail if --clean-bin does not exist",
    )
    parser.add_argument(
        "--skip-local-producer-checkouts",
        action="store_true",
        help="skip local cross-repo producer checkout validation",
    )
    parser.add_argument(
        "--skip-gamma-crown-truth-gate",
        action="store_true",
        help="skip Gamma-Crown registry/doc proof-claim validation",
    )
    parser.add_argument(
        "--generated-at", help="override generated_at for reproducible output"
    )
    parser.add_argument(
        "--deterministic",
        action="store_true",
        help="use a stable generated_at value when --generated-at is omitted",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    generated_at = args.generated_at
    if generated_at is None and args.deterministic:
        generated_at = DETERMINISTIC_GENERATED_AT
    summary = build_summary(
        lock=args.lock,
        manifest=args.manifest,
        clean_bin=args.clean_bin,
        gamma_crown_registry=args.gamma_crown_registry,
        dry_run=args.dry_run,
        require_clean_bin=args.require_clean_bin,
        skip_local_producer_checkouts=args.skip_local_producer_checkouts,
        skip_gamma_crown_truth_gate=args.skip_gamma_crown_truth_gate,
        generated_at=generated_at,
    )
    json_text = json.dumps(summary, indent=2, sort_keys=True) + "\n"
    markdown_text = render_markdown(summary)

    if args.json_output:
        write_text(args.json_output, json_text)
    else:
        print(json_text, end="")

    if args.markdown_output:
        write_text(args.markdown_output, markdown_text)

    return 0 if summary["overall_status"] == STATUS_PASSED else 1


if __name__ == "__main__":
    sys.exit(main())
