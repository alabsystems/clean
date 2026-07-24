#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Generate fail-closed frontend corpus classification evidence.

The artifact is intentionally conservative: it classifies every pinned Lean 4
corpus file across frontend evidence dimensions, but it never upgrades any row
to replacement readiness. Tests mechanically validate the checked-in JSON
against the source manifests and corpus checksums.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import TypeGuard, cast


def is_json_number(value: object) -> TypeGuard[int | float]:
    return type(value) in {int, float}


REPO_ROOT = Path(__file__).resolve().parents[2]
DATA_DIR = REPO_ROOT / "tests" / "lean4_compat"
DEFAULT_OUTPUT = DATA_DIR / "frontend_corpus_classification.json"
EXIT_STATUS_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_exit_status_artifact_schema.json"
)
EXIT_STATUS_ARTIFACT_SCHEMA_VERSION = "clean-frontend-exit-status-artifact-v1"
EXIT_STATUS_ARTIFACT_KIND = "frontend_exit_status"
EXIT_STATUS_ARTIFACT_PATH_TEMPLATE = (
    "tests/lean4_compat/frontend_run_artifacts/{engine}/exit_status/{filename}.json"
)
EXIT_STATUS_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "exit_code",
    "status",
]
EXIT_STATUS_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_timeout_seconds",
    "observed_elapsed_seconds",
    "observed_stdout",
    "observed_stderr",
    "failure_mode",
    "artifact_note",
]
DIAGNOSTIC_ARTIFACT_SCHEMA_PATH = DATA_DIR / "frontend_diagnostic_artifact_schema.json"
DIAGNOSTIC_ARTIFACT_SCHEMA_VERSION = "clean-frontend-diagnostic-artifact-v1"
DIAGNOSTIC_ARTIFACT_KIND = "frontend_diagnostic"
DIAGNOSTIC_ARTIFACT_PATH_TEMPLATE = (
    "tests/lean4_compat/frontend_run_artifacts/{engine}/diagnostic/{filename}.json"
)
DIAGNOSTIC_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "diagnostic_category",
    "first_error_signature",
    "diagnostics",
]
DIAGNOSTIC_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_exit_code",
    "observed_timeout_seconds",
    "observed_elapsed_seconds",
    "observed_stdout",
    "observed_stderr",
    "failure_mode",
    "artifact_note",
]
LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_lean4_vs_clean_run_schema.json"
)
LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_VERSION = (
    "clean-frontend-lean4-vs-clean-run-artifact-v1"
)
LEAN4_VS_clean_RUN_ARTIFACT_KIND = "frontend_lean4_vs_clean_run"
LEAN4_VS_clean_RUN_ARTIFACT_ENGINE = "lean4_vs_clean"
LEAN4_VS_clean_RUN_ARTIFACT_PATH_TEMPLATE = (
    "tests/lean4_compat/frontend_run_artifacts/{engine}/run/{filename}.json"
)
LEAN4_VS_clean_RUN_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "lean4_artifact_path",
    "clean_artifact_path",
    "comparison_basis",
    "comparison_status",
    "lean4_status",
    "clean_status",
    "replacement_ready",
]
LEAN4_VS_clean_RUN_ARTIFACT_EVIDENCE_FIELDS = [
    "lean4_diagnostic_artifact_path",
    "clean_diagnostic_artifact_path",
    "lean4_diagnostic_category",
    "clean_diagnostic_category",
    "lean4_first_error_signature",
    "clean_first_error_signature",
    "cross_check_status",
    "artifact_note",
]
KERNEL_ARTIFACT_SCHEMA_PATH = DATA_DIR / "frontend_kernel_artifact_schema.json"
KERNEL_ARTIFACT_SCHEMA_VERSION = "clean-frontend-kernel-artifact-v1"
KERNEL_ARTIFACT_KIND = "frontend_kernel"
KERNEL_ARTIFACT_PATH_TEMPLATE = (
    "tests/lean4_compat/frontend_run_artifacts/{engine}/kernel/{filename}.json"
)
KERNEL_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "kernel_status",
    "declarations_checked",
    "declarations_failed",
]
KERNEL_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_exit_code",
    "observed_timeout_seconds",
    "observed_elapsed_seconds",
    "observed_stdout",
    "observed_stderr",
    "failure_mode",
    "artifact_note",
]
MACRO_ARTIFACT_SCHEMA_PATH = DATA_DIR / "frontend_macro_artifact_schema.json"
MACRO_ARTIFACT_SCHEMA_VERSION = "clean-frontend-macro-artifact-v1"
MACRO_ARTIFACT_KIND = "frontend_macro"
MACRO_ARTIFACT_PATH_TEMPLATE = (
    "tests/lean4_compat/frontend_run_artifacts/{engine}/macro/{filename}.json"
)
MACRO_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "macro_status",
    "expansions_checked",
    "expansions_failed",
    "notations_checked",
]
MACRO_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_exit_code",
    "observed_stdout",
    "observed_stderr",
    "checked_expansions",
    "checked_notations",
    "artifact_note",
]
SYNTAX_QUOTATION_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_syntax_quotation_artifact_schema.json"
)
SYNTAX_QUOTATION_ARTIFACT_SCHEMA_VERSION = "clean-frontend-syntax-quotation-artifact-v1"
SYNTAX_QUOTATION_ARTIFACT_KIND = "frontend_syntax_quotation"
SYNTAX_QUOTATION_ARTIFACT_PATH_TEMPLATE = "tests/lean4_compat/frontend_run_artifacts/{engine}/syntax_quotation/{filename}.json"
SYNTAX_QUOTATION_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "syntax_quotation_status",
    "quotations_checked",
    "antiquotations_checked",
    "hygiene_contexts_checked",
    "quotation_failures",
]
SYNTAX_QUOTATION_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_exit_code",
    "observed_stdout",
    "observed_stderr",
    "checked_quotations",
    "checked_antiquotations",
    "checked_hygiene_contexts",
    "observed_eval_results",
    "artifact_note",
]
NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_namespace_open_scoping_artifact_schema.json"
)
NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_VERSION = (
    "clean-frontend-namespace-open-scoping-artifact-v1"
)
NAMESPACE_OPEN_SCOPING_ARTIFACT_KIND = "frontend_namespace_open_scoping"
NAMESPACE_OPEN_SCOPING_ARTIFACT_PATH_TEMPLATE = "tests/lean4_compat/frontend_run_artifacts/{engine}/namespace_open_scoping/{filename}.json"
NAMESPACE_OPEN_SCOPING_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "namespace_open_scoping_status",
    "namespace_commands_checked",
    "open_commands_checked",
    "scoping_rules_checked",
    "scoping_failures",
]
MODULE_IMPORT_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_module_import_artifact_schema.json"
)
MODULE_IMPORT_ARTIFACT_SCHEMA_VERSION = "clean-frontend-module-import-artifact-v1"
MODULE_IMPORT_ARTIFACT_KIND = "frontend_module_import"
MODULE_IMPORT_ARTIFACT_PATH_TEMPLATE = (
    "tests/lean4_compat/frontend_run_artifacts/{engine}/module_import/{filename}.json"
)
MODULE_IMPORT_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "module_import_status",
    "imports_requested",
    "imports_resolved",
    "imports_failed",
]
MODULE_IMPORT_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_exit_code",
    "observed_timeout_seconds",
    "observed_elapsed_seconds",
    "observed_stdout",
    "observed_stderr",
    "failure_mode",
    "stack_sample_summary",
    "artifact_note",
]
LEVEL_TYPECLASS_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_level_typeclass_artifact_schema.json"
)
LEVEL_TYPECLASS_ARTIFACT_SCHEMA_VERSION = "clean-frontend-level-typeclass-artifact-v1"
LEVEL_TYPECLASS_ARTIFACT_KIND = "frontend_level_typeclass"
LEVEL_TYPECLASS_ARTIFACT_PATH_TEMPLATE = (
    "tests/lean4_compat/frontend_run_artifacts/{engine}/level_typeclass/{filename}.json"
)
LEVEL_TYPECLASS_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "level_typeclass_status",
    "level_constraints_checked",
    "typeclass_goals_checked",
    "resolution_failures",
]
LEVEL_TYPECLASS_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_exit_code",
    "observed_elapsed_seconds",
    "observed_stdout",
    "observed_stderr",
    "failure_mode",
    "level_constraints",
    "typeclass_goals",
    "artifact_note",
]
DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_deriving_attribute_instance_artifact_schema.json"
)
DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_VERSION = (
    "clean-frontend-deriving-attribute-instance-artifact-v1"
)
DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_KIND = "frontend_deriving_attribute_instance"
DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_PATH_TEMPLATE = "tests/lean4_compat/frontend_run_artifacts/{engine}/deriving_attribute_instance/{filename}.json"
DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "deriving_attribute_instance_status",
    "deriving_outputs_checked",
    "attributes_checked",
    "instances_checked",
    "metadata_failures",
]
DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_EVIDENCE_FIELDS = [
    "engine_version",
    "observed_process_status",
    "observed_exit_code",
    "observed_stdout",
    "observed_stderr",
    "checked_deriving_outputs",
    "checked_attributes",
    "checked_instances",
    "artifact_note",
]
STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_PATH = (
    DATA_DIR / "frontend_structure_inductive_recursor_artifact_schema.json"
)
STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_VERSION = (
    "clean-frontend-structure-inductive-recursor-artifact-v1"
)
STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_KIND = "frontend_structure_inductive_recursor"
STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_PATH_TEMPLATE = "tests/lean4_compat/frontend_run_artifacts/{engine}/structure_inductive_recursor/{filename}.json"
STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_REQUIRED_FIELDS = [
    "schema_version",
    "kind",
    "engine",
    "filename",
    "source_sha256",
    "command",
    "structure_inductive_recursor_status",
    "structure_fields_checked",
    "inductives_checked",
    "recursors_checked",
    "match_compilations_checked",
    "construction_failures",
]
STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_EVIDENCE_FIELDS = [
    "checked_structures",
    "checked_inductives",
    "checked_recursors",
    "checked_match_compilations",
    "engine_version",
    "observed_exit_code",
    "artifact_note",
]

DIMENSIONS = [
    "parse",
    "elab",
    "kernel",
    "lean4_kernel_artifact",
    "clean_kernel_artifact",
    "tactic",
    "lean4_tactic_artifact",
    "clean_tactic_artifact",
    "macro_notation",
    "lean4_macro_artifact",
    "clean_macro_artifact",
    "syntax_quotation",
    "lean4_syntax_quotation_artifact",
    "clean_syntax_quotation_artifact",
    "namespace_open_scoping",
    "lean4_namespace_open_scoping_artifact",
    "clean_namespace_open_scoping_artifact",
    "module_import_resolution",
    "lean4_module_import_artifact",
    "clean_module_import_artifact",
    "level_typeclass_resolution",
    "lean4_level_typeclass_artifact",
    "clean_level_typeclass_artifact",
    "deriving_attribute_instance",
    "lean4_deriving_attribute_instance_artifact",
    "clean_deriving_attribute_instance_artifact",
    "structure_inductive_recursor",
    "lean4_structure_inductive_recursor_artifact",
    "clean_structure_inductive_recursor_artifact",
    "trust",
    "lean4_trust_artifact",
    "clean_trust_artifact",
    "diagnostic",
    "diagnostic_category",
    "first_error_signature",
    "phase1_transition",
    "expected_success_accountability",
    "lean4_vs_clean_run_artifact",
    "lean4_exit_status",
    "clean_exit_status",
    "lean4_diagnostic_artifact",
    "clean_diagnostic_artifact",
    "expected_failure",
]

TACTIC_PATTERNS = [
    ("by", r"\bby\b"),
    ("tactic", r"\btactic\b"),
    ("syntax", r"\bsyntax\b"),
    ("macro", r"\bmacro(?:_rules|_inline)?\b"),
    ("elab", r"\belab(?:_rules|orator)?\b"),
    ("simp", r"\bsimp\b"),
    ("rw", r"\brw\b"),
    ("native_decide", r"\bnative_decide\b"),
]

MACRO_NOTATION_PATTERNS = [
    ("declare_syntax_cat", r"\bdeclare_syntax_cat\b"),
    ("infix", r"\b(?:infix|infixl|infixr)\b"),
    ("macro", r"\bmacro(?:_rules|_inline)?\b"),
    ("notation", r"\b(?:local\s+|scoped\s+)?notation\b|\breserve\s+notation\b"),
    ("postfix", r"\bpostfix\b"),
    ("prefix", r"\bprefix\b"),
    ("syntax", r"\bsyntax\b"),
]

SYNTAX_QUOTATION_PATTERNS = [
    ("antiquotation", r"\$\(|\$\[|\$[A-Za-z_]|\$_"),
    ("syntax_quote", r"`\("),
    ("unhygienic_run", r"\bUnhygienic\.run\b"),
]

NAMESPACE_OPEN_SCOPING_PATTERNS = [
    ("local_notation", r"\blocal\s+notation\b"),
    ("namespace", r"\bnamespace\b"),
    ("open", r"\bopen\b"),
    ("scoped_notation", r"\bscoped\s+notation\b"),
    ("section", r"\bsection\b"),
]

MODULE_IMPORT_PATTERNS = [
    ("import_command", r"(?m)^\s*import\b"),
    ("import_modules_api", r"\bimportModules\b"),
]

TRUST_PATTERNS = [
    ("sorry", r"\bsorry\b"),
    ("admit", r"\badmit\b"),
    ("axiom", r"\baxiom\b"),
    ("opaque", r"\bopaque\b"),
    ("implemented_by", r"\bimplemented_by\b"),
    ("unsafe", r"\bunsafe\b"),
    ("native_decide", r"\bnative_decide\b"),
    ("decreasing_by", r"\bdecreasing_by\b"),
    ("partial", r"\bpartial\b"),
]

LEVEL_TYPECLASS_PATTERNS = [
    ("class", r"\bclass\b"),
    ("default_instance", r"\bdefault_instance\b"),
    ("infer_instance", r"\binfer_instance\b"),
    ("instance", r"\binstance\b"),
    ("instance_attr", r"\battribute\s*\[[^\]]*\b-?instance\b"),
    ("level_params", r"\.\{\s*[A-Za-z_]"),
    ("sort", r"\bSort\b"),
    ("type_level_var", r"\bType\s+[A-Za-z_][A-Za-z0-9_']*\b"),
    ("universe_decl", r"\buniverse\b"),
    ("universe_option", r"\bpp\.universes\b"),
]

DERIVING_ATTRIBUTE_INSTANCE_PATTERNS = [
    ("attribute_command", r"(?m)^\s*attribute\b"),
    ("attribute_syntax", r"@\[[^\]]+\]"),
    ("default_instance", r"\bdefault_instance\b"),
    ("deriving", r"\bderiving\b"),
    ("instance_attr", r"\battribute\s*\[[^\]]*\b-?instance\b"),
    ("instance_attr_kind_query", r"\bgetInstanceAttrKind\?"),
    ("instance_decl", r"\binstance\b"),
    ("instance_priority", r"\bpriority\s*:=|\binstance\s+\d+\b"),
    ("instance_priority_query", r"\bgetInstancePriority\?"),
    ("scoped_instance", r"\bscoped\s+instance\b"),
]

STRUCTURE_INDUCTIVE_RECURSOR_PATTERNS = [
    ("inductive", r"\binductive\b"),
    ("match", r"\bmatch\b"),
    ("recursor", r"\brecursor\b|\b[A-Za-z0-9_'.]+\.(?:rec|recOn|casesOn)\b"),
    ("structure", r"\bstructure\b"),
]

DIAGNOSTIC_PATTERNS = [
    ("#check", r"(?m)^\s*#check\b"),
    ("#eval", r"(?m)^\s*#eval\b"),
    ("#print", r"(?m)^\s*#print\b"),
    ("set_option", r"\bset_option\b"),
    ("throwError", r"\bthrowError\b"),
    (
        "expected_error_comment",
        r"(?i)\b(error|should fail|expected failure|should not elaborate)\b",
    ),
]


def repo_rel(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def read_manifest(path: Path) -> dict[str, str]:
    entries: dict[str, str] = {}
    for line in path.read_text().splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        filename, level = [part.strip() for part in stripped.split(",", 1)]
        entries[filename] = level
    return entries


def markers(source: str, patterns: list[tuple[str, str]]) -> list[str]:
    found = [
        name
        for name, pattern in patterns
        if re.search(pattern, source, flags=re.MULTILINE)
    ]
    return sorted(found)


def import_command_module_count(source: str) -> int:
    count = 0
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped.startswith("import "):
            continue
        import_text = stripped[len("import ") :].split("--", 1)[0]
        count += len(
            [module for module in re.split(r"[\s,]+", import_text.strip()) if module]
        )
    return count


def dimension(
    status: str,
    *,
    reason: str,
    markers: list[str] | None = None,
    **extra: object,
) -> dict[str, object]:
    result: dict[str, object] = {
        "status": status,
        "replacement_ready": False,
        "reason": reason,
    }
    if markers:
        result["markers"] = markers
    result.update({key: value for key, value in extra.items() if value is not None})
    return result


def expected_exit_status_artifact_path(*, engine: str, filename: str) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / engine
        / "exit_status"
        / f"{filename}.json"
    )


def expected_diagnostic_artifact_path(*, engine: str, filename: str) -> Path:
    return (
        DATA_DIR / "frontend_run_artifacts" / engine / "diagnostic" / f"{filename}.json"
    )


def expected_lean4_vs_clean_run_artifact_path(*, filename: str) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / LEAN4_VS_clean_RUN_ARTIFACT_ENGINE
        / "run"
        / f"{filename}.json"
    )


def expected_kernel_artifact_path(*, engine: str, filename: str) -> Path:
    return DATA_DIR / "frontend_run_artifacts" / engine / "kernel" / f"{filename}.json"


def expected_macro_artifact_path(*, engine: str, filename: str) -> Path:
    return DATA_DIR / "frontend_run_artifacts" / engine / "macro" / f"{filename}.json"


def expected_syntax_quotation_artifact_path(*, engine: str, filename: str) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / engine
        / "syntax_quotation"
        / f"{filename}.json"
    )


def expected_namespace_open_scoping_artifact_path(
    *, engine: str, filename: str
) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / engine
        / "namespace_open_scoping"
        / f"{filename}.json"
    )


def expected_module_import_artifact_path(*, engine: str, filename: str) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / engine
        / "module_import"
        / f"{filename}.json"
    )


def expected_level_typeclass_artifact_path(*, engine: str, filename: str) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / engine
        / "level_typeclass"
        / f"{filename}.json"
    )


def expected_deriving_attribute_instance_artifact_path(
    *, engine: str, filename: str
) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / engine
        / "deriving_attribute_instance"
        / f"{filename}.json"
    )


def expected_structure_inductive_recursor_artifact_path(
    *, engine: str, filename: str
) -> Path:
    return (
        DATA_DIR
        / "frontend_run_artifacts"
        / engine
        / "structure_inductive_recursor"
        / f"{filename}.json"
    )


def validate_command_field(artifact: dict[str, object], errors: list[str]) -> None:
    command = artifact.get("command")
    if "command" in artifact and (
        not isinstance(command, list)
        or not command
        or any(not isinstance(part, str) or not part for part in command)
    ):
        errors.append("`command` must be a non-empty array of non-empty strings")


def validate_string_list_field(
    artifact: dict[str, object], errors: list[str], field: str
) -> None:
    value = artifact.get(field)
    if field not in artifact:
        return
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item for item in value
    ):
        errors.append(f"`{field}` must be an array of non-empty strings")


def validate_exit_status_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_exit_status_artifact_path(engine=engine, filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(EXIT_STATUS_ARTIFACT_SCHEMA_PATH),
        "schema_version": EXIT_STATUS_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in EXIT_STATUS_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": EXIT_STATUS_ARTIFACT_SCHEMA_VERSION,
            "kind": EXIT_STATUS_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        exit_code = artifact.get("exit_code")
        if "exit_code" in artifact and type(exit_code) is not int:
            errors.append("`exit_code` must be an integer")

        status = artifact.get("status")
        if "status" in artifact and status not in {"success", "failure"}:
            errors.append("`status` must be either `success` or `failure`")
        if type(exit_code) is int and status in {"success", "failure"}:
            expected_status = "success" if exit_code == 0 else "failure"
            if status != expected_status:
                errors.append(
                    f"`status` must be {expected_status!r} for exit_code {exit_code}"
                )

        observed_process_status = artifact.get("observed_process_status")
        if "observed_process_status" in artifact and observed_process_status not in {
            "exited",
            "timeout",
        }:
            errors.append("`observed_process_status` must be `exited` or `timeout`")

        observed_timeout_seconds = artifact.get("observed_timeout_seconds")
        failure_mode = artifact.get("failure_mode")
        has_timeout_evidence = (
            observed_process_status == "timeout"
            or "observed_timeout_seconds" in artifact
            or (isinstance(failure_mode, str) and "timeout" in failure_mode.lower())
        )
        if has_timeout_evidence:
            if observed_process_status != "timeout":
                errors.append(
                    "`observed_process_status` must be `timeout` when timeout evidence is recorded"
                )
            if not (
                is_json_number(observed_timeout_seconds)
                and observed_timeout_seconds > 0
            ):
                errors.append(
                    "`observed_timeout_seconds` must be a positive number when timeout evidence is recorded"
                )
            if not (
                isinstance(failure_mode, str) and "timeout" in failure_mode.lower()
            ):
                errors.append(
                    "`failure_mode` must explicitly name the timeout when timeout evidence is recorded"
                )
            if exit_code == 0 or status == "success":
                errors.append(
                    "timeout exit-status evidence cannot claim successful process completion"
                )

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "exit_code": artifact["exit_code"],
        "status": artifact["status"],
    }
    for field in EXIT_STATUS_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_diagnostic_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_diagnostic_artifact_path(engine=engine, filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(DIAGNOSTIC_ARTIFACT_SCHEMA_PATH),
        "schema_version": DIAGNOSTIC_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in DIAGNOSTIC_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": DIAGNOSTIC_ARTIFACT_SCHEMA_VERSION,
            "kind": DIAGNOSTIC_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        diagnostic_category = artifact.get("diagnostic_category")
        if "diagnostic_category" in artifact and not (
            diagnostic_category is None
            or (isinstance(diagnostic_category, str) and diagnostic_category)
        ):
            errors.append("`diagnostic_category` must be null or a non-empty string")

        first_error = artifact.get("first_error_signature")
        if "first_error_signature" in artifact and not (
            first_error is None or (isinstance(first_error, str) and first_error)
        ):
            errors.append("`first_error_signature` must be null or a non-empty string")

        diagnostics = artifact.get("diagnostics")
        if "diagnostics" in artifact and not isinstance(diagnostics, list):
            errors.append("`diagnostics` must be an array")
        elif isinstance(diagnostics, list):
            for index, diagnostic in enumerate(diagnostics):
                if not isinstance(diagnostic, dict):
                    errors.append(f"`diagnostics[{index}]` must be an object")
                    continue
                severity = diagnostic.get("severity")
                if severity not in {"error", "warning", "information"}:
                    errors.append(
                        f"`diagnostics[{index}].severity` must be error, warning, or information"
                    )
                message = diagnostic.get("message")
                if not isinstance(message, str) or not message:
                    errors.append(
                        f"`diagnostics[{index}].message` must be a non-empty string"
                    )
                for location_field in ("line", "column"):
                    location = diagnostic.get(location_field)
                    if location is not None and type(location) is not int:
                        errors.append(
                            f"`diagnostics[{index}].{location_field}` must be an integer when present"
                        )

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "diagnostic_category": artifact["diagnostic_category"],
        "first_error_signature": artifact["first_error_signature"],
    }
    for field in DIAGNOSTIC_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def expected_lean4_vs_clean_comparison_status(
    *,
    lean4_exit_status_artifact: dict[str, object],
    clean_exit_status_artifact: dict[str, object],
    lean4_diagnostic_artifact: dict[str, object],
    clean_diagnostic_artifact: dict[str, object],
) -> str | None:
    if (
        lean4_exit_status_artifact.get("state") != "valid"
        or clean_exit_status_artifact.get("state") != "valid"
    ):
        return None

    exit_status_match = lean4_exit_status_artifact.get(
        "status"
    ) == clean_exit_status_artifact.get("status")
    exit_status_part = (
        "exit_status_match" if exit_status_match else "exit_status_mismatch"
    )

    if (
        lean4_diagnostic_artifact.get("state") == "valid"
        and clean_diagnostic_artifact.get("state") == "valid"
    ):
        first_error_match = lean4_diagnostic_artifact.get(
            "first_error_signature"
        ) == clean_diagnostic_artifact.get("first_error_signature")
        diagnostic_part = (
            "first_error_signature_match"
            if first_error_match
            else "first_error_signature_mismatch"
        )
    else:
        diagnostic_part = "diagnostic_artifacts_missing"

    return f"{exit_status_part}_{diagnostic_part}"


def validate_lean4_vs_clean_run_artifact(
    *,
    filename: str,
    source_sha256: str,
    lean4_exit_status_artifact: dict[str, object],
    clean_exit_status_artifact: dict[str, object],
    lean4_diagnostic_artifact: dict[str, object],
    clean_diagnostic_artifact: dict[str, object],
) -> dict[str, object]:
    path = expected_lean4_vs_clean_run_artifact_path(filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_PATH),
        "schema_version": LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in LEAN4_VS_clean_RUN_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_VERSION,
            "kind": LEAN4_VS_clean_RUN_ARTIFACT_KIND,
            "engine": LEAN4_VS_clean_RUN_ARTIFACT_ENGINE,
            "filename": filename,
            "source_sha256": source_sha256,
            "comparison_basis": "exit_status_and_first_error_signature",
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        replacement_ready = artifact.get("replacement_ready")
        if "replacement_ready" in artifact and replacement_ready is not False:
            errors.append("`replacement_ready` must be false for differential evidence")

        expected_lean4_path = lean4_exit_status_artifact.get("path")
        expected_clean_path = clean_exit_status_artifact.get("path")
        if artifact.get("lean4_artifact_path") != expected_lean4_path:
            errors.append(
                "`lean4_artifact_path` must reference the validated Lean4 exit-status artifact"
            )
        if artifact.get("clean_artifact_path") != expected_clean_path:
            errors.append(
                "`clean_artifact_path` must reference the validated clean exit-status artifact"
            )

        if lean4_exit_status_artifact.get("state") != "valid":
            errors.append("referenced Lean4 exit-status artifact must be valid")
        if clean_exit_status_artifact.get("state") != "valid":
            errors.append("referenced clean exit-status artifact must be valid")

        if lean4_exit_status_artifact.get("state") == "valid" and artifact.get(
            "lean4_status"
        ) != lean4_exit_status_artifact.get("status"):
            errors.append("`lean4_status` must match the Lean4 exit-status artifact")
        if clean_exit_status_artifact.get("state") == "valid" and artifact.get(
            "clean_status"
        ) != clean_exit_status_artifact.get("status"):
            errors.append("`clean_status` must match the clean exit-status artifact")

        expected_comparison_status = expected_lean4_vs_clean_comparison_status(
            lean4_exit_status_artifact=lean4_exit_status_artifact,
            clean_exit_status_artifact=clean_exit_status_artifact,
            lean4_diagnostic_artifact=lean4_diagnostic_artifact,
            clean_diagnostic_artifact=clean_diagnostic_artifact,
        )
        if (
            expected_comparison_status is not None
            and artifact.get("comparison_status") != expected_comparison_status
        ):
            errors.append(
                "`comparison_status` must be "
                f"{expected_comparison_status!r} for the referenced artifacts"
            )

        diagnostic_path_fields = [
            (
                "lean4_diagnostic_artifact_path",
                lean4_diagnostic_artifact.get("path"),
            ),
            (
                "clean_diagnostic_artifact_path",
                clean_diagnostic_artifact.get("path"),
            ),
        ]
        for field, expected_path in diagnostic_path_fields:
            if field in artifact and artifact[field] != expected_path:
                errors.append(
                    f"`{field}` must reference the validated diagnostic artifact"
                )

        diagnostic_value_fields = [
            (
                "lean4_diagnostic_category",
                lean4_diagnostic_artifact.get("diagnostic_category"),
            ),
            (
                "clean_diagnostic_category",
                clean_diagnostic_artifact.get("diagnostic_category"),
            ),
            (
                "lean4_first_error_signature",
                lean4_diagnostic_artifact.get("first_error_signature"),
            ),
            (
                "clean_first_error_signature",
                clean_diagnostic_artifact.get("first_error_signature"),
            ),
        ]
        for field, expected_value in diagnostic_value_fields:
            if field in artifact and artifact[field] != expected_value:
                errors.append(f"`{field}` must match the validated diagnostic artifact")

        for text_field in (
            "lean4_artifact_path",
            "clean_artifact_path",
            "comparison_basis",
            "comparison_status",
            "lean4_status",
            "clean_status",
            "cross_check_status",
            "artifact_note",
        ):
            value = artifact.get(text_field)
            if text_field in artifact and not (isinstance(value, str) and value):
                errors.append(f"`{text_field}` must be a non-empty string")

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "engine": artifact["engine"],
        "comparison_basis": artifact["comparison_basis"],
        "comparison_status": artifact["comparison_status"],
        "lean4_artifact_path": artifact["lean4_artifact_path"],
        "clean_artifact_path": artifact["clean_artifact_path"],
        "lean4_status": artifact["lean4_status"],
        "clean_status": artifact["clean_status"],
        "replacement_ready": artifact["replacement_ready"],
    }
    for field in LEAN4_VS_clean_RUN_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_kernel_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_kernel_artifact_path(engine=engine, filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(KERNEL_ARTIFACT_SCHEMA_PATH),
        "schema_version": KERNEL_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in KERNEL_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": KERNEL_ARTIFACT_SCHEMA_VERSION,
            "kind": KERNEL_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        kernel_status = artifact.get("kernel_status")
        kernel_status_valid = isinstance(kernel_status, str) and kernel_status in {
            "success",
            "failure",
        }
        if "kernel_status" in artifact and not kernel_status_valid:
            errors.append("`kernel_status` must be either `success` or `failure`")

        declarations_checked = artifact.get("declarations_checked")
        if "declarations_checked" in artifact and (
            type(declarations_checked) is not int or declarations_checked < 0
        ):
            errors.append("`declarations_checked` must be a non-negative integer")

        declarations_failed = artifact.get("declarations_failed")
        if "declarations_failed" in artifact and (
            type(declarations_failed) is not int or declarations_failed < 0
        ):
            errors.append("`declarations_failed` must be a non-negative integer")

        if type(declarations_checked) is int and type(declarations_failed) is int:
            if declarations_failed > declarations_checked:
                errors.append(
                    "`declarations_failed` must be less than or equal to `declarations_checked`"
                )
            if kernel_status_valid:
                expected_status = "success" if declarations_failed == 0 else "failure"
                if kernel_status != expected_status:
                    errors.append(
                        f"`kernel_status` must be {expected_status!r} for declarations_failed {declarations_failed}"
                    )

        observed_process_status = artifact.get("observed_process_status")
        if "observed_process_status" in artifact and observed_process_status not in {
            "exited",
            "timeout",
        }:
            errors.append("`observed_process_status` must be `exited` or `timeout`")

        observed_exit_code = artifact.get("observed_exit_code")
        if "observed_exit_code" in artifact and type(observed_exit_code) is not int:
            errors.append("`observed_exit_code` must be an integer")
        if (
            type(observed_exit_code) is int
            and kernel_status == "success"
            and observed_exit_code != 0
        ):
            errors.append(
                "successful kernel evidence cannot record a nonzero `observed_exit_code`"
            )

        observed_timeout_seconds = artifact.get("observed_timeout_seconds")
        failure_mode = artifact.get("failure_mode")
        has_timeout_evidence = (
            observed_process_status == "timeout"
            or "observed_timeout_seconds" in artifact
            or (isinstance(failure_mode, str) and "timeout" in failure_mode.lower())
        )
        if has_timeout_evidence:
            if observed_process_status != "timeout":
                errors.append(
                    "`observed_process_status` must be `timeout` when timeout evidence is recorded"
                )
            if not (
                is_json_number(observed_timeout_seconds)
                and observed_timeout_seconds > 0
            ):
                errors.append(
                    "`observed_timeout_seconds` must be a positive number when timeout evidence is recorded"
                )
            if not (
                isinstance(failure_mode, str) and "timeout" in failure_mode.lower()
            ):
                errors.append(
                    "`failure_mode` must explicitly name the timeout when timeout evidence is recorded"
                )
            if kernel_status == "success":
                errors.append(
                    "timeout kernel evidence cannot claim successful checking"
                )

        observed_elapsed_seconds = artifact.get("observed_elapsed_seconds")
        if "observed_elapsed_seconds" in artifact and not (
            is_json_number(observed_elapsed_seconds) and observed_elapsed_seconds >= 0
        ):
            errors.append("`observed_elapsed_seconds` must be a non-negative number")

        for text_field in (
            "engine_version",
            "observed_stdout",
            "observed_stderr",
            "failure_mode",
            "artifact_note",
        ):
            value = artifact.get(text_field)
            if text_field in artifact and not isinstance(value, str):
                errors.append(f"`{text_field}` must be a string")

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "kernel_status": artifact["kernel_status"],
        "declarations_checked": artifact["declarations_checked"],
        "declarations_failed": artifact["declarations_failed"],
    }
    for field in KERNEL_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_macro_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_macro_artifact_path(engine=engine, filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(MACRO_ARTIFACT_SCHEMA_PATH),
        "schema_version": MACRO_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in MACRO_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": MACRO_ARTIFACT_SCHEMA_VERSION,
            "kind": MACRO_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        macro_status = artifact.get("macro_status")
        macro_status_valid = isinstance(macro_status, str) and macro_status in {
            "success",
            "failure",
        }
        if "macro_status" in artifact and not macro_status_valid:
            errors.append("`macro_status` must be either `success` or `failure`")

        expansions_checked = artifact.get("expansions_checked")
        if "expansions_checked" in artifact and (
            type(expansions_checked) is not int or expansions_checked < 0
        ):
            errors.append("`expansions_checked` must be a non-negative integer")

        expansions_failed = artifact.get("expansions_failed")
        if "expansions_failed" in artifact and (
            type(expansions_failed) is not int or expansions_failed < 0
        ):
            errors.append("`expansions_failed` must be a non-negative integer")

        notations_checked = artifact.get("notations_checked")
        if "notations_checked" in artifact and (
            type(notations_checked) is not int or notations_checked < 0
        ):
            errors.append("`notations_checked` must be a non-negative integer")

        if type(expansions_checked) is int and type(expansions_failed) is int:
            if expansions_failed > expansions_checked:
                errors.append(
                    "`expansions_failed` must be less than or equal to `expansions_checked`"
                )
            if macro_status_valid:
                expected_status = "success" if expansions_failed == 0 else "failure"
                if macro_status != expected_status:
                    errors.append(
                        f"`macro_status` must be {expected_status!r} for expansions_failed {expansions_failed}"
                    )

        observed_process_status = artifact.get("observed_process_status")
        if "observed_process_status" in artifact and observed_process_status not in {
            "exited",
            "timeout",
        }:
            errors.append("`observed_process_status` must be `exited` or `timeout`")
        if observed_process_status == "timeout" and macro_status == "success":
            errors.append("timeout macro evidence cannot claim successful expansion")

        observed_exit_code = artifact.get("observed_exit_code")
        if "observed_exit_code" in artifact and type(observed_exit_code) is not int:
            errors.append("`observed_exit_code` must be an integer")

        for text_field in (
            "engine_version",
            "observed_stdout",
            "observed_stderr",
            "artifact_note",
        ):
            value = artifact.get(text_field)
            if text_field in artifact and not isinstance(value, str):
                errors.append(f"`{text_field}` must be a string")

        evidence_count_fields = {
            "checked_expansions": "expansions_checked",
            "checked_notations": "notations_checked",
        }
        for list_field, count_field in evidence_count_fields.items():
            validate_string_list_field(artifact, errors, list_field)
            evidence_items = artifact.get(list_field)
            count_value = artifact.get(count_field)
            if (
                isinstance(evidence_items, list)
                and all(isinstance(item, str) and item for item in evidence_items)
                and type(count_value) is int
                and len(evidence_items) != count_value
            ):
                errors.append(
                    f"`{list_field}` length must equal `{count_field}` when present"
                )

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "macro_status": artifact["macro_status"],
        "expansions_checked": artifact["expansions_checked"],
        "expansions_failed": artifact["expansions_failed"],
        "notations_checked": artifact["notations_checked"],
    }
    for field in MACRO_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_syntax_quotation_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_syntax_quotation_artifact_path(engine=engine, filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(SYNTAX_QUOTATION_ARTIFACT_SCHEMA_PATH),
        "schema_version": SYNTAX_QUOTATION_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in SYNTAX_QUOTATION_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": SYNTAX_QUOTATION_ARTIFACT_SCHEMA_VERSION,
            "kind": SYNTAX_QUOTATION_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        syntax_quotation_status = artifact.get("syntax_quotation_status")
        syntax_quotation_status_valid = isinstance(
            syntax_quotation_status, str
        ) and syntax_quotation_status in {
            "success",
            "failure",
        }
        if "syntax_quotation_status" in artifact and not syntax_quotation_status_valid:
            errors.append(
                "`syntax_quotation_status` must be either `success` or `failure`"
            )

        checked_fields = [
            "quotations_checked",
            "antiquotations_checked",
            "hygiene_contexts_checked",
        ]
        checked_counts: list[int] = []
        for field in checked_fields:
            value = artifact.get(field)
            if field in artifact and (type(value) is not int or value < 0):
                errors.append(f"`{field}` must be a non-negative integer")
            if type(value) is int:
                checked_counts.append(value)

        quotation_failures = artifact.get("quotation_failures")
        if "quotation_failures" in artifact and (
            type(quotation_failures) is not int or quotation_failures < 0
        ):
            errors.append("`quotation_failures` must be a non-negative integer")

        if (
            len(checked_counts) == len(checked_fields)
            and type(quotation_failures) is int
        ):
            total_checked = sum(checked_counts)
            if quotation_failures > total_checked:
                errors.append(
                    "`quotation_failures` must be less than or equal to the total checked syntax quotation items"
                )
            if syntax_quotation_status_valid:
                expected_status = "success" if quotation_failures == 0 else "failure"
                if syntax_quotation_status != expected_status:
                    errors.append(
                        f"`syntax_quotation_status` must be {expected_status!r} for quotation_failures {quotation_failures}"
                    )

        observed_process_status = artifact.get("observed_process_status")
        if "observed_process_status" in artifact and observed_process_status not in {
            "exited",
            "timeout",
        }:
            errors.append("`observed_process_status` must be `exited` or `timeout`")
        if (
            observed_process_status == "timeout"
            and syntax_quotation_status == "success"
        ):
            errors.append(
                "timeout syntax-quotation evidence cannot claim successful checking"
            )

        observed_exit_code = artifact.get("observed_exit_code")
        if "observed_exit_code" in artifact and type(observed_exit_code) is not int:
            errors.append("`observed_exit_code` must be an integer")
        if (
            type(observed_exit_code) is int
            and syntax_quotation_status == "success"
            and observed_exit_code != 0
        ):
            errors.append(
                "successful syntax-quotation evidence cannot record a nonzero `observed_exit_code`"
            )

        for text_field in (
            "engine_version",
            "observed_stdout",
            "observed_stderr",
            "artifact_note",
        ):
            value = artifact.get(text_field)
            if text_field in artifact and not isinstance(value, str):
                errors.append(f"`{text_field}` must be a string")

        evidence_count_fields = {
            "checked_quotations": "quotations_checked",
            "checked_antiquotations": "antiquotations_checked",
            "checked_hygiene_contexts": "hygiene_contexts_checked",
        }
        for list_field, count_field in evidence_count_fields.items():
            validate_string_list_field(artifact, errors, list_field)
            evidence_items = artifact.get(list_field)
            count_value = artifact.get(count_field)
            if (
                isinstance(evidence_items, list)
                and all(isinstance(item, str) and item for item in evidence_items)
                and type(count_value) is int
                and len(evidence_items) != count_value
            ):
                errors.append(
                    f"`{list_field}` length must equal `{count_field}` when present"
                )
        validate_string_list_field(artifact, errors, "observed_eval_results")

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "syntax_quotation_status": artifact["syntax_quotation_status"],
        "quotations_checked": artifact["quotations_checked"],
        "antiquotations_checked": artifact["antiquotations_checked"],
        "hygiene_contexts_checked": artifact["hygiene_contexts_checked"],
        "quotation_failures": artifact["quotation_failures"],
    }
    for field in SYNTAX_QUOTATION_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_namespace_open_scoping_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_namespace_open_scoping_artifact_path(
        engine=engine, filename=filename
    )
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_PATH),
        "schema_version": NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in NAMESPACE_OPEN_SCOPING_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_VERSION,
            "kind": NAMESPACE_OPEN_SCOPING_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        scoping_status = artifact.get("namespace_open_scoping_status")
        scoping_status_valid = isinstance(scoping_status, str) and scoping_status in {
            "success",
            "failure",
        }
        if "namespace_open_scoping_status" in artifact and not scoping_status_valid:
            errors.append(
                "`namespace_open_scoping_status` must be either `success` or `failure`"
            )

        checked_fields = [
            "namespace_commands_checked",
            "open_commands_checked",
            "scoping_rules_checked",
        ]
        checked_counts: list[int] = []
        for field in checked_fields:
            value = artifact.get(field)
            if field in artifact and (type(value) is not int or value < 0):
                errors.append(f"`{field}` must be a non-negative integer")
            if type(value) is int:
                checked_counts.append(value)

        scoping_failures = artifact.get("scoping_failures")
        if "scoping_failures" in artifact and (
            type(scoping_failures) is not int or scoping_failures < 0
        ):
            errors.append("`scoping_failures` must be a non-negative integer")

        if len(checked_counts) == len(checked_fields) and type(scoping_failures) is int:
            total_checked = sum(checked_counts)
            if scoping_failures > total_checked:
                errors.append(
                    "`scoping_failures` must be less than or equal to the total checked namespace/open/scoping items"
                )
            if scoping_status_valid:
                expected_status = "success" if scoping_failures == 0 else "failure"
                if scoping_status != expected_status:
                    errors.append(
                        f"`namespace_open_scoping_status` must be {expected_status!r} for scoping_failures {scoping_failures}"
                    )

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    return {
        **metadata,
        "state": "valid",
        "namespace_open_scoping_status": artifact["namespace_open_scoping_status"],
        "namespace_commands_checked": artifact["namespace_commands_checked"],
        "open_commands_checked": artifact["open_commands_checked"],
        "scoping_rules_checked": artifact["scoping_rules_checked"],
        "scoping_failures": artifact["scoping_failures"],
    }


def validate_module_import_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_module_import_artifact_path(engine=engine, filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(MODULE_IMPORT_ARTIFACT_SCHEMA_PATH),
        "schema_version": MODULE_IMPORT_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in MODULE_IMPORT_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": MODULE_IMPORT_ARTIFACT_SCHEMA_VERSION,
            "kind": MODULE_IMPORT_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        module_import_status = artifact.get("module_import_status")
        module_import_status_valid = isinstance(
            module_import_status, str
        ) and module_import_status in {
            "success",
            "failure",
        }
        if "module_import_status" in artifact and not module_import_status_valid:
            errors.append(
                "`module_import_status` must be either `success` or `failure`"
            )

        observed_process_status = artifact.get("observed_process_status")
        observed_timeout_seconds = artifact.get("observed_timeout_seconds")
        failure_mode = artifact.get("failure_mode")
        has_timeout_evidence = (
            observed_process_status == "timeout"
            or "observed_timeout_seconds" in artifact
            or (isinstance(failure_mode, str) and "timeout" in failure_mode.lower())
        )
        if has_timeout_evidence:
            if observed_process_status != "timeout":
                errors.append(
                    "`observed_process_status` must be `timeout` when timeout evidence is recorded"
                )
            if not (
                is_json_number(observed_timeout_seconds)
                and observed_timeout_seconds > 0
            ):
                errors.append(
                    "`observed_timeout_seconds` must be a positive number when timeout evidence is recorded"
                )
            if not (
                isinstance(failure_mode, str) and "timeout" in failure_mode.lower()
            ):
                errors.append(
                    "`failure_mode` must explicitly name the timeout when timeout evidence is recorded"
                )
            if module_import_status == "success":
                errors.append(
                    "timeout module-import evidence cannot claim `module_import_status` `success`"
                )

        count_fields = [
            "imports_requested",
            "imports_resolved",
            "imports_failed",
        ]
        for field in count_fields:
            value = artifact.get(field)
            if field in artifact and (type(value) is not int or value < 0):
                errors.append(f"`{field}` must be a non-negative integer")

        imports_requested = artifact.get("imports_requested")
        imports_resolved = artifact.get("imports_resolved")
        imports_failed = artifact.get("imports_failed")
        if type(imports_requested) is int:
            if type(imports_resolved) is int and imports_resolved > imports_requested:
                errors.append(
                    "`imports_resolved` must be less than or equal to `imports_requested`"
                )
            if type(imports_failed) is int and imports_failed > imports_requested:
                errors.append(
                    "`imports_failed` must be less than or equal to `imports_requested`"
                )
            if (
                has_timeout_evidence
                and type(imports_failed) is int
                and imports_failed == 0
            ):
                errors.append(
                    "`imports_failed` must be greater than 0 when timeout evidence is recorded"
                )
            if (
                type(imports_resolved) is int
                and type(imports_failed) is int
                and imports_resolved + imports_failed > imports_requested
            ):
                errors.append(
                    "`imports_resolved` plus `imports_failed` must be less than or equal to `imports_requested`"
                )
            if (
                type(imports_resolved) is int
                and type(imports_failed) is int
                and module_import_status_valid
            ):
                expected_status = (
                    "success"
                    if imports_failed == 0 and imports_resolved == imports_requested
                    else "failure"
                )
                if module_import_status != expected_status:
                    errors.append(
                        "`module_import_status` must be "
                        f"{expected_status!r} for imports_requested "
                        f"{imports_requested}, imports_resolved {imports_resolved}, "
                        f"and imports_failed {imports_failed}"
                    )

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "module_import_status": artifact["module_import_status"],
        "imports_requested": artifact["imports_requested"],
        "imports_resolved": artifact["imports_resolved"],
        "imports_failed": artifact["imports_failed"],
    }
    for field in MODULE_IMPORT_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_level_typeclass_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_level_typeclass_artifact_path(engine=engine, filename=filename)
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(LEVEL_TYPECLASS_ARTIFACT_SCHEMA_PATH),
        "schema_version": LEVEL_TYPECLASS_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in LEVEL_TYPECLASS_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": LEVEL_TYPECLASS_ARTIFACT_SCHEMA_VERSION,
            "kind": LEVEL_TYPECLASS_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        level_typeclass_status = artifact.get("level_typeclass_status")
        level_typeclass_status_valid = isinstance(
            level_typeclass_status, str
        ) and level_typeclass_status in {
            "success",
            "failure",
        }
        if "level_typeclass_status" in artifact and not level_typeclass_status_valid:
            errors.append(
                "`level_typeclass_status` must be either `success` or `failure`"
            )

        checked_fields = [
            "level_constraints_checked",
            "typeclass_goals_checked",
        ]
        checked_counts: list[int] = []
        for field in checked_fields:
            value = artifact.get(field)
            if field in artifact and (type(value) is not int or value < 0):
                errors.append(f"`{field}` must be a non-negative integer")
            if type(value) is int:
                checked_counts.append(value)

        resolution_failures = artifact.get("resolution_failures")
        if "resolution_failures" in artifact and (
            type(resolution_failures) is not int or resolution_failures < 0
        ):
            errors.append("`resolution_failures` must be a non-negative integer")

        if (
            len(checked_counts) == len(checked_fields)
            and type(resolution_failures) is int
        ):
            total_checked = sum(checked_counts)
            if resolution_failures > total_checked:
                errors.append(
                    "`resolution_failures` must be less than or equal to the total checked level/typeclass items"
                )
            if level_typeclass_status_valid:
                expected_status = "success" if resolution_failures == 0 else "failure"
                if level_typeclass_status != expected_status:
                    errors.append(
                        f"`level_typeclass_status` must be {expected_status!r} for resolution_failures {resolution_failures}"
                    )

        for field in ("level_constraints", "typeclass_goals"):
            value = artifact.get(field)
            if field not in artifact:
                continue
            if not isinstance(value, list) or any(
                not isinstance(item, str) or not item for item in value
            ):
                errors.append(f"`{field}` must be an array of non-empty strings")
                continue
            count_field = (
                "level_constraints_checked"
                if field == "level_constraints"
                else "typeclass_goals_checked"
            )
            count = artifact.get(count_field)
            if type(count) is int and len(value) != count:
                errors.append(f"`{field}` length must equal `{count_field}`")

        observed_process_status = artifact.get("observed_process_status")
        if "observed_process_status" in artifact and observed_process_status not in {
            "exited",
            "timeout",
        }:
            errors.append("`observed_process_status` must be `exited` or `timeout`")

        observed_exit_code = artifact.get("observed_exit_code")
        if "observed_exit_code" in artifact and type(observed_exit_code) is not int:
            errors.append("`observed_exit_code` must be an integer")

        observed_elapsed_seconds = artifact.get("observed_elapsed_seconds")
        if "observed_elapsed_seconds" in artifact and not (
            is_json_number(observed_elapsed_seconds) and observed_elapsed_seconds >= 0
        ):
            errors.append("`observed_elapsed_seconds` must be a non-negative number")

        for field in ("observed_stdout", "observed_stderr"):
            value = artifact.get(field)
            if field in artifact and not isinstance(value, str):
                errors.append(f"`{field}` must be a string")

        for field in ("engine_version", "failure_mode", "artifact_note"):
            value = artifact.get(field)
            if field in artifact and not (isinstance(value, str) and value):
                errors.append(f"`{field}` must be a non-empty string")

        if observed_process_status == "timeout" and level_typeclass_status == "success":
            errors.append(
                "timeout level/typeclass evidence cannot claim `level_typeclass_status` `success`"
            )

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "level_typeclass_status": artifact["level_typeclass_status"],
        "level_constraints_checked": artifact["level_constraints_checked"],
        "typeclass_goals_checked": artifact["typeclass_goals_checked"],
        "resolution_failures": artifact["resolution_failures"],
    }
    for field in LEVEL_TYPECLASS_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_deriving_attribute_instance_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_deriving_attribute_instance_artifact_path(
        engine=engine, filename=filename
    )
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_PATH),
        "schema_version": DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_VERSION,
            "kind": DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        deriving_attribute_instance_status = artifact.get(
            "deriving_attribute_instance_status"
        )
        deriving_attribute_instance_status_valid = isinstance(
            deriving_attribute_instance_status, str
        ) and deriving_attribute_instance_status in {
            "success",
            "failure",
        }
        if (
            "deriving_attribute_instance_status" in artifact
            and not deriving_attribute_instance_status_valid
        ):
            errors.append(
                "`deriving_attribute_instance_status` must be either `success` or `failure`"
            )

        checked_fields = [
            "deriving_outputs_checked",
            "attributes_checked",
            "instances_checked",
        ]
        checked_counts: list[int] = []
        for field in checked_fields:
            value = artifact.get(field)
            if field in artifact and (type(value) is not int or value < 0):
                errors.append(f"`{field}` must be a non-negative integer")
            if type(value) is int:
                checked_counts.append(value)

        metadata_failures = artifact.get("metadata_failures")
        if "metadata_failures" in artifact and (
            type(metadata_failures) is not int or metadata_failures < 0
        ):
            errors.append("`metadata_failures` must be a non-negative integer")

        if (
            len(checked_counts) == len(checked_fields)
            and type(metadata_failures) is int
        ):
            total_checked = sum(checked_counts)
            if metadata_failures > total_checked:
                errors.append(
                    "`metadata_failures` must be less than or equal to the total checked deriving/attribute/instance items"
                )
            if deriving_attribute_instance_status_valid:
                expected_status = "success" if metadata_failures == 0 else "failure"
                if deriving_attribute_instance_status != expected_status:
                    errors.append(
                        f"`deriving_attribute_instance_status` must be {expected_status!r} for metadata_failures {metadata_failures}"
                    )

        for field in [
            "checked_deriving_outputs",
            "checked_attributes",
            "checked_instances",
        ]:
            validate_string_list_field(artifact, errors, field)
        for field, count_field in {
            "checked_deriving_outputs": "deriving_outputs_checked",
            "checked_attributes": "attributes_checked",
            "checked_instances": "instances_checked",
        }.items():
            value = artifact.get(field)
            count = artifact.get(count_field)
            if isinstance(value, list) and type(count) is int and len(value) != count:
                errors.append(f"`{field}` length must equal `{count_field}`")

        observed_process_status = artifact.get("observed_process_status")
        if "observed_process_status" in artifact and observed_process_status not in {
            "exited",
            "timeout",
        }:
            errors.append("`observed_process_status` must be `exited` or `timeout`")
        if (
            observed_process_status == "timeout"
            and deriving_attribute_instance_status == "success"
        ):
            errors.append(
                "timeout deriving/attribute/instance evidence cannot claim `deriving_attribute_instance_status` `success`"
            )

        observed_exit_code = artifact.get("observed_exit_code")
        if "observed_exit_code" in artifact and type(observed_exit_code) is not int:
            errors.append("`observed_exit_code` must be an integer")
        if (
            deriving_attribute_instance_status == "success"
            and type(observed_exit_code) is int
            and observed_exit_code != 0
        ):
            errors.append(
                "`observed_exit_code` must be 0 when deriving_attribute_instance_status is `success`"
            )

        for field in ("observed_stdout", "observed_stderr"):
            value = artifact.get(field)
            if field in artifact and not isinstance(value, str):
                errors.append(f"`{field}` must be a string")

        for field in ["engine_version", "artifact_note"]:
            value = artifact.get(field)
            if field in artifact and (not isinstance(value, str) or not value):
                errors.append(f"`{field}` must be a non-empty string")

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "deriving_attribute_instance_status": artifact[
            "deriving_attribute_instance_status"
        ],
        "deriving_outputs_checked": artifact["deriving_outputs_checked"],
        "attributes_checked": artifact["attributes_checked"],
        "instances_checked": artifact["instances_checked"],
        "metadata_failures": artifact["metadata_failures"],
    }
    for field in DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def validate_structure_inductive_recursor_artifact(
    *,
    engine: str,
    filename: str,
    source_sha256: str,
) -> dict[str, object]:
    path = expected_structure_inductive_recursor_artifact_path(
        engine=engine, filename=filename
    )
    rel_path = repo_rel(path)
    metadata: dict[str, object] = {
        "path": rel_path,
        "schema": repo_rel(STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_PATH),
        "schema_version": STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_VERSION,
        "state": "missing",
    }
    if not path.exists():
        return metadata

    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": [f"artifact is not readable JSON: {exc}"],
        }

    errors: list[str] = []
    if not isinstance(artifact, dict):
        errors.append("artifact root must be a JSON object")
    else:
        errors.extend(
            f"missing required field `{field}`"
            for field in STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_REQUIRED_FIELDS
            if field not in artifact
        )

        expected_values = {
            "schema_version": STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_VERSION,
            "kind": STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_KIND,
            "engine": engine,
            "filename": filename,
            "source_sha256": source_sha256,
        }
        for field, expected in expected_values.items():
            if field in artifact and artifact[field] != expected:
                errors.append(
                    f"`{field}` must be {expected!r}, got {artifact[field]!r}"
                )

        validate_command_field(artifact, errors)

        structure_inductive_recursor_status = artifact.get(
            "structure_inductive_recursor_status"
        )
        structure_inductive_recursor_status_valid = isinstance(
            structure_inductive_recursor_status, str
        ) and structure_inductive_recursor_status in {
            "success",
            "failure",
        }
        if (
            "structure_inductive_recursor_status" in artifact
            and not structure_inductive_recursor_status_valid
        ):
            errors.append(
                "`structure_inductive_recursor_status` must be either `success` or `failure`"
            )

        checked_fields = [
            "structure_fields_checked",
            "inductives_checked",
            "recursors_checked",
            "match_compilations_checked",
        ]
        checked_counts: list[int] = []
        for field in checked_fields:
            value = artifact.get(field)
            if field in artifact and (type(value) is not int or value < 0):
                errors.append(f"`{field}` must be a non-negative integer")
            if type(value) is int:
                checked_counts.append(value)

        construction_failures = artifact.get("construction_failures")
        if "construction_failures" in artifact and (
            type(construction_failures) is not int or construction_failures < 0
        ):
            errors.append("`construction_failures` must be a non-negative integer")

        if (
            len(checked_counts) == len(checked_fields)
            and type(construction_failures) is int
        ):
            total_checked = sum(checked_counts)
            if construction_failures > total_checked:
                errors.append(
                    "`construction_failures` must be less than or equal to the total checked structure/inductive/recursor items"
                )
            if structure_inductive_recursor_status_valid:
                expected_status = "success" if construction_failures == 0 else "failure"
                if structure_inductive_recursor_status != expected_status:
                    errors.append(
                        f"`structure_inductive_recursor_status` must be {expected_status!r} for construction_failures {construction_failures}"
                    )

        for field in [
            "checked_structures",
            "checked_inductives",
            "checked_recursors",
            "checked_match_compilations",
        ]:
            validate_string_list_field(artifact, errors, field)
        for field, count_field in {
            "checked_structures": "structure_fields_checked",
            "checked_inductives": "inductives_checked",
            "checked_recursors": "recursors_checked",
            "checked_match_compilations": "match_compilations_checked",
        }.items():
            value = artifact.get(field)
            count = artifact.get(count_field)
            if isinstance(value, list) and type(count) is int and len(value) != count:
                errors.append(f"`{field}` length must equal `{count_field}`")

        observed_exit_code = artifact.get("observed_exit_code")
        if "observed_exit_code" in artifact and type(observed_exit_code) is not int:
            errors.append("`observed_exit_code` must be an integer")

        if (
            structure_inductive_recursor_status == "success"
            and type(observed_exit_code) is int
            and observed_exit_code != 0
        ):
            errors.append(
                "`observed_exit_code` must be 0 when structure_inductive_recursor_status is `success`"
            )

        for field in ["engine_version", "artifact_note"]:
            value = artifact.get(field)
            if field in artifact and (not isinstance(value, str) or not value):
                errors.append(f"`{field}` must be a non-empty string")

    if errors:
        return {
            **metadata,
            "state": "stale_or_invalid",
            "validation_errors": errors,
        }

    validated = {
        **metadata,
        "state": "valid",
        "structure_inductive_recursor_status": artifact[
            "structure_inductive_recursor_status"
        ],
        "structure_fields_checked": artifact["structure_fields_checked"],
        "inductives_checked": artifact["inductives_checked"],
        "recursors_checked": artifact["recursors_checked"],
        "match_compilations_checked": artifact["match_compilations_checked"],
        "construction_failures": artifact["construction_failures"],
    }
    for field in STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_EVIDENCE_FIELDS:
        if field in artifact:
            validated[field] = artifact[field]
    return validated


def exit_status_dimension_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_exit_status_artifact"
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_exit_status_artifact"
        return f"excluded_stale_or_invalid_{engine}_exit_status_artifact"
    if artifact_state == "valid":
        result_status = artifact.get("status")
        result_bucket = "success" if result_status == "success" else "failure"
        if level == "elab":
            return f"elab_valid_{engine}_exit_status_{result_bucket}_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_exit_status_{result_bucket}_artifact_no_target"
        return f"excluded_unexpected_{engine}_exit_status_{result_bucket}_artifact_no_target"

    if level == "elab":
        return f"elab_missing_{engine}_exit_status_result"
    if level == "parse_only":
        return f"parse_only_no_{engine}_exit_status_target"
    return f"excluded_no_{engine}_exit_status_target"


def lean4_vs_clean_run_artifact_status(
    *,
    level: str | None,
    artifact: dict[str, object],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return "elab_stale_or_invalid_lean4_vs_clean_run_artifact"
        if level == "parse_only":
            return "parse_only_stale_or_invalid_lean4_vs_clean_run_artifact_no_target"
        return "excluded_stale_or_invalid_lean4_vs_clean_run_artifact_no_target"
    if artifact_state == "valid":
        if level == "elab":
            return (
                "elab_valid_lean4_vs_clean_run_artifact_"
                f"{artifact['comparison_status']}"
            )
        if level == "parse_only":
            return "parse_only_unexpected_lean4_vs_clean_run_artifact_no_target"
        return "excluded_unexpected_lean4_vs_clean_run_artifact_no_target"

    if level == "elab":
        return "elab_missing_lean4_vs_clean_run_artifact"
    if level == "parse_only":
        return "parse_only_no_lean4_vs_clean_run_target"
    return "excluded_no_lean4_vs_clean_run_target"


def diagnostic_artifact_dimension_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_diagnostic_artifact"
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_diagnostic_artifact"
        return f"excluded_stale_or_invalid_{engine}_diagnostic_artifact"
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_diagnostic_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_diagnostic_artifact_no_target"
        return f"excluded_unexpected_{engine}_diagnostic_artifact_no_target"

    if level == "elab":
        return f"elab_missing_{engine}_diagnostic_artifact"
    if level == "parse_only":
        return f"parse_only_no_{engine}_diagnostic_artifact_target"
    return f"excluded_no_{engine}_diagnostic_artifact_target"


def kernel_artifact_dimension_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_kernel_artifact"
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_kernel_artifact"
        return f"excluded_stale_or_invalid_{engine}_kernel_artifact"
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_kernel_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_kernel_artifact_no_target"
        return f"excluded_unexpected_{engine}_kernel_artifact_no_target"

    if level == "elab":
        return f"elab_missing_{engine}_kernel_artifact"
    if level == "parse_only":
        return f"parse_only_no_{engine}_kernel_artifact_target"
    return f"excluded_no_{engine}_kernel_artifact_target"


def tactic_artifact_status(
    *,
    engine: str,
    level: str | None,
    tactic_markers: list[str],
) -> str:
    tactic_surface = bool(tactic_markers)
    if level == "elab" and tactic_surface:
        return f"elab_tactic_surface_missing_{engine}_tactic_artifact"
    if level == "elab":
        return f"elab_no_tactic_surface_no_{engine}_tactic_artifact_target"
    if level == "parse_only" and tactic_surface:
        return f"parse_only_tactic_surface_no_{engine}_tactic_artifact_target"
    if level == "parse_only":
        return f"parse_only_no_tactic_surface_no_{engine}_tactic_artifact_target"
    if tactic_surface:
        return f"excluded_tactic_surface_no_{engine}_tactic_artifact_target"
    return f"excluded_no_tactic_surface_no_{engine}_tactic_artifact_target"


def macro_artifact_dimension_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
    macro_notation_markers: list[str],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_macro_artifact"
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_macro_artifact"
        return f"excluded_stale_or_invalid_{engine}_macro_artifact"
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_macro_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_macro_artifact_no_target"
        return f"excluded_unexpected_{engine}_macro_artifact_no_target"

    macro_notation_surface = bool(macro_notation_markers)
    if level == "elab" and macro_notation_surface:
        return f"elab_macro_notation_surface_missing_{engine}_macro_artifact"
    if level == "elab":
        return f"elab_no_macro_notation_surface_no_{engine}_macro_artifact_target"
    if level == "parse_only" and macro_notation_surface:
        return f"parse_only_macro_notation_surface_no_{engine}_macro_artifact_target"
    if level == "parse_only":
        return f"parse_only_no_macro_notation_surface_no_{engine}_macro_artifact_target"
    if macro_notation_surface:
        return f"excluded_macro_notation_surface_no_{engine}_macro_artifact_target"
    return f"excluded_no_macro_notation_surface_no_{engine}_macro_artifact_target"


def syntax_quotation_artifact_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
    syntax_quotation_markers: list[str],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_syntax_quotation_artifact"
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_syntax_quotation_artifact"
        return f"excluded_stale_or_invalid_{engine}_syntax_quotation_artifact"
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_syntax_quotation_artifact_pending_cross_check"
        if level == "parse_only" and syntax_quotation_markers:
            return f"parse_only_valid_{engine}_syntax_quotation_artifact_pending_elab_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_syntax_quotation_artifact_no_target"
        if syntax_quotation_markers:
            return f"excluded_valid_{engine}_syntax_quotation_artifact_no_phase1_cross_check"
        return f"excluded_unexpected_{engine}_syntax_quotation_artifact_no_target"

    syntax_quotation_surface = bool(syntax_quotation_markers)
    artifact_name = f"{engine}_syntax_quotation_artifact"
    if level == "elab" and syntax_quotation_surface:
        return f"elab_syntax_quotation_surface_missing_{artifact_name}"
    if level == "elab":
        return f"elab_no_syntax_quotation_surface_no_{artifact_name}_target"
    if level == "parse_only" and syntax_quotation_surface:
        return f"parse_only_syntax_quotation_surface_no_{artifact_name}_target"
    if level == "parse_only":
        return f"parse_only_no_syntax_quotation_surface_no_{artifact_name}_target"
    if syntax_quotation_surface:
        return f"excluded_syntax_quotation_surface_no_{artifact_name}_target"
    return f"excluded_no_syntax_quotation_surface_no_{artifact_name}_target"


def namespace_open_scoping_artifact_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
    namespace_open_scoping_markers: list[str],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_namespace_open_scoping_artifact"
        if level == "parse_only":
            return (
                f"parse_only_stale_or_invalid_{engine}_namespace_open_scoping_artifact"
            )
        return f"excluded_stale_or_invalid_{engine}_namespace_open_scoping_artifact"
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_namespace_open_scoping_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_namespace_open_scoping_artifact_no_target"
        return f"excluded_unexpected_{engine}_namespace_open_scoping_artifact_no_target"

    namespace_open_scoping_surface = bool(namespace_open_scoping_markers)
    artifact_name = f"{engine}_namespace_open_scoping_artifact"
    if level == "elab" and namespace_open_scoping_surface:
        return f"elab_namespace_open_scoping_surface_missing_{artifact_name}"
    if level == "elab":
        return f"elab_no_namespace_open_scoping_surface_no_{artifact_name}_target"
    if level == "parse_only" and namespace_open_scoping_surface:
        return f"parse_only_namespace_open_scoping_surface_no_{artifact_name}_target"
    if level == "parse_only":
        return f"parse_only_no_namespace_open_scoping_surface_no_{artifact_name}_target"
    if namespace_open_scoping_surface:
        return f"excluded_namespace_open_scoping_surface_no_{artifact_name}_target"
    return f"excluded_no_namespace_open_scoping_surface_no_{artifact_name}_target"


def module_import_artifact_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
    module_import_markers: list[str],
    expected_imports_requested: int,
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_module_import_artifact"
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_module_import_artifact"
        return f"excluded_stale_or_invalid_{engine}_module_import_artifact"
    if artifact_state == "valid":
        if level == "elab":
            if module_import_artifact_cross_checked(
                artifact=artifact,
                module_import_markers=module_import_markers,
                expected_imports_requested=expected_imports_requested,
            ):
                if module_import_artifact_imports_resolved(artifact):
                    return f"elab_valid_{engine}_module_import_artifact_cross_checked"
                if module_import_artifact_timeout_blocked(artifact):
                    return (
                        f"elab_valid_{engine}_module_import_artifact_"
                        "bounded_timeout_count_matched"
                    )
                return (
                    f"elab_valid_{engine}_module_import_artifact_"
                    "import_resolution_failure_count_matched"
                )
            return f"elab_valid_{engine}_module_import_artifact_cross_check_mismatch"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_module_import_artifact_no_target"
        return f"excluded_unexpected_{engine}_module_import_artifact_no_target"

    module_import_surface = bool(module_import_markers)
    artifact_name = f"{engine}_module_import_artifact"
    if level == "elab" and module_import_surface:
        return f"elab_module_import_surface_missing_{artifact_name}"
    if level == "elab":
        return f"elab_no_module_import_surface_no_{artifact_name}_target"
    if level == "parse_only" and module_import_surface:
        return f"parse_only_module_import_surface_no_{artifact_name}_target"
    if level == "parse_only":
        return f"parse_only_no_module_import_surface_no_{artifact_name}_target"
    if module_import_surface:
        return f"excluded_module_import_surface_no_{artifact_name}_target"
    return f"excluded_no_module_import_surface_no_{artifact_name}_target"


def module_import_artifact_cross_checked(
    *,
    artifact: dict[str, object],
    module_import_markers: list[str],
    expected_imports_requested: int,
) -> bool:
    if artifact["state"] != "valid":
        return False
    imports_requested = artifact.get("imports_requested")
    if type(imports_requested) is not int:
        return False
    if expected_imports_requested > 0:
        return imports_requested == expected_imports_requested
    if module_import_markers:
        return imports_requested > 0
    return imports_requested == 0


def module_import_artifact_imports_resolved(artifact: dict[str, object]) -> bool:
    imports_requested = artifact.get("imports_requested")
    imports_resolved = artifact.get("imports_resolved")
    imports_failed = artifact.get("imports_failed")
    return (
        artifact.get("module_import_status") == "success"
        and type(imports_requested) is int
        and type(imports_resolved) is int
        and type(imports_failed) is int
        and imports_resolved == imports_requested
        and imports_failed == 0
    )


def module_import_artifact_timeout_blocked(artifact: dict[str, object]) -> bool:
    observed_timeout_seconds = artifact.get("observed_timeout_seconds")
    failure_mode = artifact.get("failure_mode")
    return (
        artifact.get("module_import_status") == "failure"
        and artifact.get("observed_process_status") == "timeout"
        and is_json_number(observed_timeout_seconds)
        and observed_timeout_seconds > 0
        and isinstance(failure_mode, str)
        and "timeout" in failure_mode.lower()
    )


def module_import_artifact_cross_check_status(
    *,
    artifact: dict[str, object],
    module_import_markers: list[str],
    expected_imports_requested: int,
) -> str:
    if not module_import_artifact_cross_checked(
        artifact=artifact,
        module_import_markers=module_import_markers,
        expected_imports_requested=expected_imports_requested,
    ):
        return "cross_check_mismatch"
    if module_import_artifact_imports_resolved(artifact):
        return "cross_checked"
    if module_import_artifact_timeout_blocked(artifact):
        return "bounded_timeout_count_matched"
    return "import_resolution_failure_count_matched"


def module_import_artifact_cross_check(
    *,
    artifact: dict[str, object],
    module_import_markers: list[str],
    expected_imports_requested: int,
) -> dict[str, object]:
    result: dict[str, object] = {
        "path": artifact["path"],
        "state": artifact["state"],
        "expected_imports_requested": expected_imports_requested,
    }
    artifact_state = artifact["state"]
    if artifact_state == "valid":
        result["status"] = module_import_artifact_cross_check_status(
            artifact=artifact,
            module_import_markers=module_import_markers,
            expected_imports_requested=expected_imports_requested,
        )
        result["module_import_status"] = artifact["module_import_status"]
        result["imports_requested"] = artifact["imports_requested"]
        result["imports_resolved"] = artifact["imports_resolved"]
        result["imports_failed"] = artifact["imports_failed"]
        for field in MODULE_IMPORT_ARTIFACT_EVIDENCE_FIELDS:
            if field in artifact:
                result[field] = artifact[field]
    elif artifact_state == "missing":
        result["status"] = "missing_real_artifact"
    else:
        result["status"] = "stale_or_invalid_real_artifact"
    return result


def trust_artifact_status(
    *,
    engine: str,
    level: str | None,
    trust_markers: list[str],
) -> str:
    requires_trust_evidence = bool(trust_markers)
    if level == "elab" and requires_trust_evidence:
        return f"elab_trust_marker_missing_{engine}_trust_artifact"
    if level == "elab":
        return f"elab_no_trust_marker_no_{engine}_trust_artifact_target"
    if level == "parse_only" and requires_trust_evidence:
        return f"parse_only_trust_marker_no_{engine}_trust_artifact_target"
    if level == "parse_only":
        return f"parse_only_no_trust_marker_no_{engine}_trust_artifact_target"
    if requires_trust_evidence:
        return f"excluded_trust_marker_no_{engine}_trust_artifact_target"
    return f"excluded_no_trust_marker_no_{engine}_trust_artifact_target"


def level_typeclass_artifact_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
    level_typeclass_markers: list[str],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return f"elab_stale_or_invalid_{engine}_level_typeclass_artifact"
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_level_typeclass_artifact"
        return f"excluded_stale_or_invalid_{engine}_level_typeclass_artifact"
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_level_typeclass_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_level_typeclass_artifact_no_target"
        return f"excluded_unexpected_{engine}_level_typeclass_artifact_no_target"

    level_typeclass_surface = bool(level_typeclass_markers)
    artifact_name = f"{engine}_level_typeclass_artifact"
    if level == "elab" and level_typeclass_surface:
        return f"elab_level_typeclass_surface_missing_{artifact_name}"
    if level == "elab":
        return f"elab_no_level_typeclass_surface_no_{artifact_name}_target"
    if level == "parse_only" and level_typeclass_surface:
        return f"parse_only_level_typeclass_surface_no_{artifact_name}_target"
    if level == "parse_only":
        return f"parse_only_no_level_typeclass_surface_no_{artifact_name}_target"
    if level_typeclass_surface:
        return f"excluded_level_typeclass_surface_no_{artifact_name}_target"
    return f"excluded_no_level_typeclass_surface_no_{artifact_name}_target"


def deriving_attribute_instance_artifact_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
    deriving_attribute_instance_markers: list[str],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return (
                f"elab_stale_or_invalid_{engine}_deriving_attribute_instance_artifact"
            )
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_deriving_attribute_instance_artifact"
        return (
            f"excluded_stale_or_invalid_{engine}_deriving_attribute_instance_artifact"
        )
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_deriving_attribute_instance_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_deriving_attribute_instance_artifact_no_target"
        return f"excluded_unexpected_{engine}_deriving_attribute_instance_artifact_no_target"

    deriving_attribute_instance_surface = bool(deriving_attribute_instance_markers)
    artifact_name = f"{engine}_deriving_attribute_instance_artifact"
    if level == "elab" and deriving_attribute_instance_surface:
        return f"elab_deriving_attribute_instance_surface_missing_{artifact_name}"
    if level == "elab":
        return f"elab_no_deriving_attribute_instance_surface_no_{artifact_name}_target"
    if level == "parse_only" and deriving_attribute_instance_surface:
        return (
            f"parse_only_deriving_attribute_instance_surface_no_{artifact_name}_target"
        )
    if level == "parse_only":
        return f"parse_only_no_deriving_attribute_instance_surface_no_{artifact_name}_target"
    if deriving_attribute_instance_surface:
        return f"excluded_deriving_attribute_instance_surface_no_{artifact_name}_target"
    return f"excluded_no_deriving_attribute_instance_surface_no_{artifact_name}_target"


def structure_inductive_recursor_artifact_status(
    *,
    engine: str,
    level: str | None,
    artifact: dict[str, object],
    structure_inductive_recursor_markers: list[str],
) -> str:
    artifact_state = artifact["state"]
    if artifact_state == "stale_or_invalid":
        if level == "elab":
            return (
                f"elab_stale_or_invalid_{engine}_structure_inductive_recursor_artifact"
            )
        if level == "parse_only":
            return f"parse_only_stale_or_invalid_{engine}_structure_inductive_recursor_artifact"
        return (
            f"excluded_stale_or_invalid_{engine}_structure_inductive_recursor_artifact"
        )
    if artifact_state == "valid":
        if level == "elab":
            return f"elab_valid_{engine}_structure_inductive_recursor_artifact_pending_cross_check"
        if level == "parse_only":
            return f"parse_only_unexpected_{engine}_structure_inductive_recursor_artifact_no_target"
        return f"excluded_unexpected_{engine}_structure_inductive_recursor_artifact_no_target"

    structure_inductive_recursor_surface = bool(structure_inductive_recursor_markers)
    artifact_name = f"{engine}_structure_inductive_recursor_artifact"
    if level == "elab" and structure_inductive_recursor_surface:
        return f"elab_structure_inductive_recursor_surface_missing_{artifact_name}"
    if level == "elab":
        return f"elab_no_structure_inductive_recursor_surface_no_{artifact_name}_target"
    if level == "parse_only" and structure_inductive_recursor_surface:
        return (
            f"parse_only_structure_inductive_recursor_surface_no_{artifact_name}_target"
        )
    if level == "parse_only":
        return f"parse_only_no_structure_inductive_recursor_surface_no_{artifact_name}_target"
    if structure_inductive_recursor_surface:
        return (
            f"excluded_structure_inductive_recursor_surface_no_{artifact_name}_target"
        )
    return f"excluded_no_structure_inductive_recursor_surface_no_{artifact_name}_target"


def expected_diagnostic_categories(entries: list[dict[str, object]]) -> list[str]:
    categories: set[str] = set()
    for entry in entries:
        if entry.get("outcome") != "fail":
            continue
        contains = str(entry.get("contains", "")).lower()
        if "alternative `isfalse`" in contains:
            categories.add("missing_cases_alternative")
        elif "unknownfvar" in contains:
            categories.add("internal_fvar_reconstruction_blocker")
        elif "unknown identifier" in contains or contains == "unknown":
            categories.add("unknown_identifier_or_scope")
        elif contains == "error":
            categories.add("user_thrown_tactic_error")
        else:
            categories.add("other_profiled_expected_diagnostic")
    return sorted(categories)


def first_error_signature(entries: list[dict[str, object]]) -> str | None:
    for entry in entries:
        if entry.get("outcome") != "fail":
            continue
        contains = str(entry.get("contains", "")).strip().lower()
        signature = re.sub(r"\d+", "n", contains)
        signature = re.sub(r"[^a-z0-9]+", "_", signature).strip("_")
        return signature or "empty_expected_failure_pattern"
    return None


def generate() -> dict[str, object]:
    manifest_path = DATA_DIR / "MANIFEST.json"
    phase1_path = DATA_DIR / "phase1_gate_manifest.txt"
    slice_path = DATA_DIR / "frontend_slice_manifest.txt"
    profiles_path = DATA_DIR / "phase1_expected_outcomes.json"

    corpus_manifest = json.loads(manifest_path.read_text())
    phase1_manifest = read_manifest(phase1_path)
    slice_manifest = set(read_manifest(slice_path))
    profiles = json.loads(profiles_path.read_text())

    checksums: dict[str, str] = corpus_manifest["checksums"]
    filenames = sorted(checksums)
    expected_failure_files = {
        filename
        for filename, entries in profiles.items()
        if any(entry.get("outcome") == "fail" for entry in entries)
    }
    excluded_files = sorted(set(filenames) - set(phase1_manifest))

    files: list[dict[str, object]] = []
    status_counts: dict[str, Counter[str]] = {
        dimension_name: Counter() for dimension_name in DIMENSIONS
    }
    diagnostic_category_counts: Counter[str] = Counter()
    first_error_signature_counts: Counter[str] = Counter()

    for filename in filenames:
        source_path = DATA_DIR / "lean4_tests" / filename
        source_bytes = source_path.read_bytes()
        sha256 = "sha256:" + hashlib.sha256(source_bytes).hexdigest()
        if sha256 != checksums[filename]:
            raise SystemExit(
                f"{repo_rel(source_path)} checksum mismatch: expected {checksums[filename]}, got {sha256}"
            )

        source = source_bytes.decode("utf-8", errors="replace")
        tactic_markers = markers(source, TACTIC_PATTERNS)
        macro_notation_markers = markers(source, MACRO_NOTATION_PATTERNS)
        syntax_quotation_markers = markers(source, SYNTAX_QUOTATION_PATTERNS)
        namespace_open_scoping_markers = markers(
            source, NAMESPACE_OPEN_SCOPING_PATTERNS
        )
        module_import_markers = markers(source, MODULE_IMPORT_PATTERNS)
        level_typeclass_markers = markers(source, LEVEL_TYPECLASS_PATTERNS)
        deriving_attribute_instance_markers = markers(
            source, DERIVING_ATTRIBUTE_INSTANCE_PATTERNS
        )
        structure_inductive_recursor_markers = markers(
            source, STRUCTURE_INDUCTIVE_RECURSOR_PATTERNS
        )
        trust_markers = markers(source, TRUST_PATTERNS)
        diagnostic_markers = markers(source, DIAGNOSTIC_PATTERNS)
        profiled_diagnostic_categories = expected_diagnostic_categories(
            profiles.get(filename, [])
        )
        for category in profiled_diagnostic_categories:
            diagnostic_category_counts[category] += 1
        profiled_first_error_signature = first_error_signature(
            profiles.get(filename, [])
        )
        if profiled_first_error_signature is not None:
            first_error_signature_counts[profiled_first_error_signature] += 1

        level = phase1_manifest.get(filename)
        is_excluded = level is None

        parse_status = (
            "phase1_gate_parse_required"
            if level is not None
            else "excluded_from_phase1_gate"
        )
        if level == "elab":
            elab_status = (
                "phase1_elab_profiled"
                if filename in profiles
                else "phase1_elab_must_pass"
            )
        elif level == "parse_only":
            elab_status = "parse_only_not_elab"
        else:
            elab_status = "not_claimed"

        kernel_status = (
            "bounded_slice_parse_elab_kernel_pass"
            if filename in slice_manifest
            else "not_claimed"
        )
        lean4_kernel_artifact = validate_kernel_artifact(
            engine="lean4", filename=filename, source_sha256=sha256
        )
        clean_kernel_artifact = validate_kernel_artifact(
            engine="clean", filename=filename, source_sha256=sha256
        )
        lean4_kernel_artifact_status = kernel_artifact_dimension_status(
            engine="lean4", level=level, artifact=lean4_kernel_artifact
        )
        clean_kernel_artifact_status = kernel_artifact_dimension_status(
            engine="clean", level=level, artifact=clean_kernel_artifact
        )
        tactic_status = (
            "contains_tactic_surface" if tactic_markers else "no_tactic_surface_marker"
        )
        lean4_tactic_artifact_status = tactic_artifact_status(
            engine="lean4", level=level, tactic_markers=tactic_markers
        )
        clean_tactic_artifact_status = tactic_artifact_status(
            engine="clean", level=level, tactic_markers=tactic_markers
        )
        macro_notation_status = (
            "contains_macro_notation_surface"
            if macro_notation_markers
            else "no_macro_notation_surface_marker"
        )
        lean4_macro_artifact = validate_macro_artifact(
            engine="lean4", filename=filename, source_sha256=sha256
        )
        clean_macro_artifact = validate_macro_artifact(
            engine="clean", filename=filename, source_sha256=sha256
        )
        lean4_macro_artifact_status = macro_artifact_dimension_status(
            engine="lean4",
            level=level,
            artifact=lean4_macro_artifact,
            macro_notation_markers=macro_notation_markers,
        )
        clean_macro_artifact_status = macro_artifact_dimension_status(
            engine="clean",
            level=level,
            artifact=clean_macro_artifact,
            macro_notation_markers=macro_notation_markers,
        )
        syntax_quotation_status = (
            "contains_syntax_quotation_surface"
            if syntax_quotation_markers
            else "no_syntax_quotation_surface_marker"
        )
        lean4_syntax_quotation_artifact = validate_syntax_quotation_artifact(
            engine="lean4", filename=filename, source_sha256=sha256
        )
        clean_syntax_quotation_artifact = validate_syntax_quotation_artifact(
            engine="clean", filename=filename, source_sha256=sha256
        )
        lean4_syntax_quotation_artifact_status = syntax_quotation_artifact_status(
            engine="lean4",
            level=level,
            artifact=lean4_syntax_quotation_artifact,
            syntax_quotation_markers=syntax_quotation_markers,
        )
        clean_syntax_quotation_artifact_status = syntax_quotation_artifact_status(
            engine="clean",
            level=level,
            artifact=clean_syntax_quotation_artifact,
            syntax_quotation_markers=syntax_quotation_markers,
        )
        namespace_open_scoping_status = (
            "contains_namespace_open_scoping_surface"
            if namespace_open_scoping_markers
            else "no_namespace_open_scoping_surface_marker"
        )
        lean4_namespace_open_scoping_artifact = (
            validate_namespace_open_scoping_artifact(
                engine="lean4", filename=filename, source_sha256=sha256
            )
        )
        clean_namespace_open_scoping_artifact = (
            validate_namespace_open_scoping_artifact(
                engine="clean", filename=filename, source_sha256=sha256
            )
        )
        lean4_namespace_open_scoping_artifact_status = (
            namespace_open_scoping_artifact_status(
                engine="lean4",
                level=level,
                artifact=lean4_namespace_open_scoping_artifact,
                namespace_open_scoping_markers=namespace_open_scoping_markers,
            )
        )
        clean_namespace_open_scoping_artifact_status = (
            namespace_open_scoping_artifact_status(
                engine="clean",
                level=level,
                artifact=clean_namespace_open_scoping_artifact,
                namespace_open_scoping_markers=namespace_open_scoping_markers,
            )
        )
        module_import_status = (
            "contains_module_import_surface"
            if module_import_markers
            else "no_module_import_surface_marker"
        )
        expected_imports_requested = import_command_module_count(source)
        lean4_module_import_artifact = validate_module_import_artifact(
            engine="lean4", filename=filename, source_sha256=sha256
        )
        clean_module_import_artifact = validate_module_import_artifact(
            engine="clean", filename=filename, source_sha256=sha256
        )
        lean4_module_import_artifact_status = module_import_artifact_status(
            engine="lean4",
            level=level,
            artifact=lean4_module_import_artifact,
            module_import_markers=module_import_markers,
            expected_imports_requested=expected_imports_requested,
        )
        clean_module_import_artifact_status = module_import_artifact_status(
            engine="clean",
            level=level,
            artifact=clean_module_import_artifact,
            module_import_markers=module_import_markers,
            expected_imports_requested=expected_imports_requested,
        )
        module_import_artifact_cross_checks = {
            "lean4": module_import_artifact_cross_check(
                artifact=lean4_module_import_artifact,
                module_import_markers=module_import_markers,
                expected_imports_requested=expected_imports_requested,
            ),
            "clean": module_import_artifact_cross_check(
                artifact=clean_module_import_artifact,
                module_import_markers=module_import_markers,
                expected_imports_requested=expected_imports_requested,
            ),
        }
        level_typeclass_status = (
            "contains_level_typeclass_surface"
            if level_typeclass_markers
            else "no_level_typeclass_surface_marker"
        )
        lean4_level_typeclass_artifact = validate_level_typeclass_artifact(
            engine="lean4", filename=filename, source_sha256=sha256
        )
        clean_level_typeclass_artifact = validate_level_typeclass_artifact(
            engine="clean", filename=filename, source_sha256=sha256
        )
        lean4_level_typeclass_artifact_status = level_typeclass_artifact_status(
            engine="lean4",
            level=level,
            artifact=lean4_level_typeclass_artifact,
            level_typeclass_markers=level_typeclass_markers,
        )
        clean_level_typeclass_artifact_status = level_typeclass_artifact_status(
            engine="clean",
            level=level,
            artifact=clean_level_typeclass_artifact,
            level_typeclass_markers=level_typeclass_markers,
        )
        deriving_attribute_instance_status = (
            "contains_deriving_attribute_instance_surface"
            if deriving_attribute_instance_markers
            else "no_deriving_attribute_instance_surface_marker"
        )
        lean4_deriving_attribute_instance_artifact = (
            validate_deriving_attribute_instance_artifact(
                engine="lean4", filename=filename, source_sha256=sha256
            )
        )
        clean_deriving_attribute_instance_artifact = (
            validate_deriving_attribute_instance_artifact(
                engine="clean", filename=filename, source_sha256=sha256
            )
        )
        lean4_deriving_attribute_instance_artifact_status = (
            deriving_attribute_instance_artifact_status(
                engine="lean4",
                level=level,
                artifact=lean4_deriving_attribute_instance_artifact,
                deriving_attribute_instance_markers=deriving_attribute_instance_markers,
            )
        )
        clean_deriving_attribute_instance_artifact_status = (
            deriving_attribute_instance_artifact_status(
                engine="clean",
                level=level,
                artifact=clean_deriving_attribute_instance_artifact,
                deriving_attribute_instance_markers=deriving_attribute_instance_markers,
            )
        )
        structure_inductive_recursor_status = (
            "contains_structure_inductive_recursor_surface"
            if structure_inductive_recursor_markers
            else "no_structure_inductive_recursor_surface_marker"
        )
        lean4_structure_inductive_recursor_artifact = (
            validate_structure_inductive_recursor_artifact(
                engine="lean4", filename=filename, source_sha256=sha256
            )
        )
        clean_structure_inductive_recursor_artifact = (
            validate_structure_inductive_recursor_artifact(
                engine="clean", filename=filename, source_sha256=sha256
            )
        )
        lean4_structure_inductive_recursor_artifact_status = structure_inductive_recursor_artifact_status(
            engine="lean4",
            level=level,
            artifact=lean4_structure_inductive_recursor_artifact,
            structure_inductive_recursor_markers=structure_inductive_recursor_markers,
        )
        clean_structure_inductive_recursor_artifact_status = structure_inductive_recursor_artifact_status(
            engine="clean",
            level=level,
            artifact=clean_structure_inductive_recursor_artifact,
            structure_inductive_recursor_markers=structure_inductive_recursor_markers,
        )
        trust_status = "requires_trust_audit" if trust_markers else "no_trust_marker"
        lean4_trust_artifact_status = trust_artifact_status(
            engine="lean4", level=level, trust_markers=trust_markers
        )
        clean_trust_artifact_status = trust_artifact_status(
            engine="clean", level=level, trust_markers=trust_markers
        )
        if filename in expected_failure_files:
            diagnostic_status = "profiled_expected_diagnostic"
            diagnostic_category_status = "profiled_expected_diagnostic_category"
            first_error_signature_status = "profiled_first_error_signature"
            expected_failure_status = "profiled_decl_expected_failure"
        elif is_excluded:
            diagnostic_status = "excluded_parse_or_fuzz_diagnostic"
            diagnostic_category_status = "excluded_parse_or_fuzz_unbucketed"
            first_error_signature_status = "excluded_parse_or_fuzz_unprofiled"
            expected_failure_status = "excluded_expected_parse_failure_or_fuzz"
        elif diagnostic_markers:
            diagnostic_status = "diagnostic_surface_marker"
            diagnostic_category_status = "diagnostic_surface_unprofiled"
            first_error_signature_status = "diagnostic_surface_unprofiled_first_error"
            expected_failure_status = "none_profiled"
        elif filename in profiles:
            diagnostic_status = "not_profiled"
            diagnostic_category_status = "no_profiled_expected_diagnostic"
            first_error_signature_status = "profiled_no_expected_failure"
            expected_failure_status = "none_profiled"
        else:
            diagnostic_status = "not_profiled"
            diagnostic_category_status = "no_profiled_expected_diagnostic"
            first_error_signature_status = "no_profiled_first_error"
            expected_failure_status = "none_profiled"

        if level == "elab" and filename in expected_failure_files:
            phase1_transition_status = "elab_profiled_expected_failure"
        elif level == "elab" and filename in profiles:
            phase1_transition_status = "elab_profiled_all_decl_success"
        elif level == "elab":
            phase1_transition_status = "elab_unprofiled_must_succeed"
        elif level == "parse_only":
            phase1_transition_status = "parse_only_elab_not_entered"
        else:
            phase1_transition_status = "excluded_no_phase1_transition"

        if level == "elab" and filename in expected_failure_files:
            expected_success_accountability_status = (
                "elab_profiled_expected_failure_no_success_credit"
            )
        elif level == "elab" and filename in profiles:
            expected_success_accountability_status = (
                "elab_profiled_all_decl_success_contract"
            )
        elif level == "elab":
            expected_success_accountability_status = (
                "elab_unprofiled_must_succeed_contract"
            )
        elif level == "parse_only":
            expected_success_accountability_status = "parse_only_no_elab_success_credit"
        else:
            expected_success_accountability_status = "excluded_no_success_contract"

        lean4_exit_status_artifact = validate_exit_status_artifact(
            engine="lean4", filename=filename, source_sha256=sha256
        )
        clean_exit_status_artifact = validate_exit_status_artifact(
            engine="clean", filename=filename, source_sha256=sha256
        )
        lean4_exit_status = exit_status_dimension_status(
            engine="lean4", level=level, artifact=lean4_exit_status_artifact
        )
        clean_exit_status = exit_status_dimension_status(
            engine="clean", level=level, artifact=clean_exit_status_artifact
        )
        lean4_diagnostic_artifact = validate_diagnostic_artifact(
            engine="lean4", filename=filename, source_sha256=sha256
        )
        clean_diagnostic_artifact = validate_diagnostic_artifact(
            engine="clean", filename=filename, source_sha256=sha256
        )
        lean4_diagnostic_artifact_status = diagnostic_artifact_dimension_status(
            engine="lean4", level=level, artifact=lean4_diagnostic_artifact
        )
        clean_diagnostic_artifact_status = diagnostic_artifact_dimension_status(
            engine="clean", level=level, artifact=clean_diagnostic_artifact
        )
        lean4_vs_clean_run_artifact = validate_lean4_vs_clean_run_artifact(
            filename=filename,
            source_sha256=sha256,
            lean4_exit_status_artifact=lean4_exit_status_artifact,
            clean_exit_status_artifact=clean_exit_status_artifact,
            lean4_diagnostic_artifact=lean4_diagnostic_artifact,
            clean_diagnostic_artifact=clean_diagnostic_artifact,
        )
        lean4_vs_clean_run_artifact_dimension_status = (
            lean4_vs_clean_run_artifact_status(
                level=level, artifact=lean4_vs_clean_run_artifact
            )
        )

        dimensions = {
            "parse": dimension(
                parse_status,
                reason=(
                    "listed in phase1_gate_manifest.txt"
                    if level is not None
                    else "present in MANIFEST.json but intentionally outside the Phase 1 gate"
                ),
            ),
            "elab": dimension(
                elab_status,
                reason=(
                    "Phase 1 elab row"
                    if level == "elab"
                    else "Phase 1 parse-only row"
                    if level == "parse_only"
                    else "no elaboration claim"
                ),
            ),
            "kernel": dimension(
                kernel_status,
                reason=(
                    "bounded frontend slice manifest requires parse, elab, and kernel registration"
                    if filename in slice_manifest
                    else "outside the bounded all-pass kernel slice"
                ),
            ),
            "lean4_kernel_artifact": dimension(
                lean4_kernel_artifact_status,
                reason=(
                    "deterministic kernel-artifact guard: Lean4 kernel artifacts "
                    "must exist at the expected per-file path and satisfy the "
                    "frontend kernel artifact schema before they can be "
                    "cross-checked against the bounded kernel dimension"
                ),
                expected_artifact=lean4_kernel_artifact,
            ),
            "clean_kernel_artifact": dimension(
                clean_kernel_artifact_status,
                reason=(
                    "deterministic kernel-artifact guard: clean kernel artifacts "
                    "must exist at the expected per-file path and satisfy the "
                    "frontend kernel artifact schema before they can be "
                    "cross-checked against the bounded kernel dimension"
                ),
                expected_artifact=clean_kernel_artifact,
            ),
            "tactic": dimension(
                tactic_status,
                reason="lexical tactic/metaprogramming surface marker scan",
                markers=tactic_markers,
            ),
            "lean4_tactic_artifact": dimension(
                lean4_tactic_artifact_status,
                reason=(
                    "deterministic tactic-artifact guard: no generated per-file "
                    "Lean4 tactic artifact or check result is recorded for rows "
                    "where the tactic dimension found elab-relevant tactic surface"
                ),
                markers=tactic_markers,
            ),
            "clean_tactic_artifact": dimension(
                clean_tactic_artifact_status,
                reason=(
                    "deterministic tactic-artifact guard: no generated per-file "
                    "clean tactic artifact or check result is recorded for rows "
                    "where the tactic dimension found elab-relevant tactic surface"
                ),
                markers=tactic_markers,
            ),
            "macro_notation": dimension(
                macro_notation_status,
                reason="lexical macro/notation surface marker scan",
                markers=macro_notation_markers,
            ),
            "lean4_macro_artifact": dimension(
                lean4_macro_artifact_status,
                reason=(
                    "deterministic macro-artifact guard: Lean4 macro/notation "
                    "artifacts must exist at the expected per-file path and "
                    "satisfy the frontend macro artifact schema before they "
                    "can be cross-checked against the macro_notation dimension"
                ),
                markers=macro_notation_markers,
                expected_artifact=lean4_macro_artifact,
            ),
            "clean_macro_artifact": dimension(
                clean_macro_artifact_status,
                reason=(
                    "deterministic macro-artifact guard: clean macro/notation "
                    "artifacts must exist at the expected per-file path and "
                    "satisfy the frontend macro artifact schema before they "
                    "can be cross-checked against the macro_notation dimension"
                ),
                markers=macro_notation_markers,
                expected_artifact=clean_macro_artifact,
            ),
            "syntax_quotation": dimension(
                syntax_quotation_status,
                reason=(
                    "lexical syntax quotation, antiquotation, and hygienic syntax "
                    "construction surface marker scan"
                ),
                markers=syntax_quotation_markers,
            ),
            "lean4_syntax_quotation_artifact": dimension(
                lean4_syntax_quotation_artifact_status,
                reason=(
                    "deterministic syntax-quotation artifact guard: Lean4 syntax "
                    "quotation, antiquotation, and hygiene artifacts must exist "
                    "at the expected per-file path and satisfy the frontend syntax "
                    "quotation artifact schema before they can be cross-checked "
                    "against parse and elaboration classifications"
                ),
                markers=syntax_quotation_markers,
                expected_artifact=lean4_syntax_quotation_artifact,
            ),
            "clean_syntax_quotation_artifact": dimension(
                clean_syntax_quotation_artifact_status,
                reason=(
                    "deterministic syntax-quotation artifact guard: clean syntax "
                    "quotation, antiquotation, and hygiene artifacts must exist "
                    "at the expected per-file path and satisfy the frontend syntax "
                    "quotation artifact schema before they can be cross-checked "
                    "against parse and elaboration classifications"
                ),
                markers=syntax_quotation_markers,
                expected_artifact=clean_syntax_quotation_artifact,
            ),
            "namespace_open_scoping": dimension(
                namespace_open_scoping_status,
                reason=(
                    "lexical namespace/open/section/local-notation scoping surface "
                    "marker scan"
                ),
                markers=namespace_open_scoping_markers,
            ),
            "lean4_namespace_open_scoping_artifact": dimension(
                lean4_namespace_open_scoping_artifact_status,
                reason=(
                    "deterministic namespace/open/scoping artifact guard: Lean4 "
                    "namespace, open, section, and local-notation scoping artifacts "
                    "must exist at the expected per-file path and satisfy the "
                    "frontend namespace/open/scoping artifact schema before they "
                    "can be cross-checked against the namespace_open_scoping dimension"
                ),
                markers=namespace_open_scoping_markers,
                expected_artifact=lean4_namespace_open_scoping_artifact,
            ),
            "clean_namespace_open_scoping_artifact": dimension(
                clean_namespace_open_scoping_artifact_status,
                reason=(
                    "deterministic namespace/open/scoping artifact guard: clean "
                    "namespace, open, section, and local-notation scoping artifacts "
                    "must exist at the expected per-file path and satisfy the "
                    "frontend namespace/open/scoping artifact schema before they "
                    "can be cross-checked against the namespace_open_scoping dimension"
                ),
                markers=namespace_open_scoping_markers,
                expected_artifact=clean_namespace_open_scoping_artifact,
            ),
            "module_import_resolution": dimension(
                module_import_status,
                reason=(
                    "lexical module import command and importModules API surface "
                    "marker scan"
                ),
                markers=module_import_markers,
                artifact_cross_checks=module_import_artifact_cross_checks,
            ),
            "lean4_module_import_artifact": dimension(
                lean4_module_import_artifact_status,
                reason=(
                    "deterministic module/import artifact guard: Lean4 import "
                    "resolution artifacts must exist at the expected per-file path "
                    "and satisfy the frontend module/import artifact schema before "
                    "they can be cross-checked against parse and elaboration "
                    "classifications"
                ),
                markers=module_import_markers,
                expected_artifact=lean4_module_import_artifact,
            ),
            "clean_module_import_artifact": dimension(
                clean_module_import_artifact_status,
                reason=(
                    "deterministic module/import artifact guard: clean import "
                    "resolution artifacts must exist at the expected per-file path "
                    "and satisfy the frontend module/import artifact schema before "
                    "they can be cross-checked against parse and elaboration "
                    "classifications"
                ),
                markers=module_import_markers,
                expected_artifact=clean_module_import_artifact,
            ),
            "level_typeclass_resolution": dimension(
                level_typeclass_status,
                reason="lexical universe/level and typeclass-resolution surface marker scan",
                markers=level_typeclass_markers,
            ),
            "lean4_level_typeclass_artifact": dimension(
                lean4_level_typeclass_artifact_status,
                reason=(
                    "deterministic universe/typeclass artifact guard: Lean4 "
                    "universe-level and typeclass-resolution artifacts must exist "
                    "at the expected per-file path and satisfy the frontend "
                    "level/typeclass artifact schema before they can be "
                    "cross-checked against parse, elaboration, and kernel "
                    "classifications"
                ),
                markers=level_typeclass_markers,
                expected_artifact=lean4_level_typeclass_artifact,
            ),
            "clean_level_typeclass_artifact": dimension(
                clean_level_typeclass_artifact_status,
                reason=(
                    "deterministic universe/typeclass artifact guard: clean "
                    "universe-level and typeclass-resolution artifacts must exist "
                    "at the expected per-file path and satisfy the frontend "
                    "level/typeclass artifact schema before they can be "
                    "cross-checked against parse, elaboration, and kernel "
                    "classifications"
                ),
                markers=level_typeclass_markers,
                expected_artifact=clean_level_typeclass_artifact,
            ),
            "deriving_attribute_instance": dimension(
                deriving_attribute_instance_status,
                reason=(
                    "lexical deriving, attribute, and instance metadata surface "
                    "marker scan"
                ),
                markers=deriving_attribute_instance_markers,
            ),
            "lean4_deriving_attribute_instance_artifact": dimension(
                lean4_deriving_attribute_instance_artifact_status,
                reason=(
                    "deterministic deriving/attribute/instance artifact guard: Lean4 "
                    "deriving output, attribute state, and instance metadata artifacts "
                    "must exist at the expected per-file path and satisfy the frontend "
                    "deriving/attribute/instance artifact schema before they can be "
                    "cross-checked against parse and elaboration classifications"
                ),
                markers=deriving_attribute_instance_markers,
                expected_artifact=lean4_deriving_attribute_instance_artifact,
            ),
            "clean_deriving_attribute_instance_artifact": dimension(
                clean_deriving_attribute_instance_artifact_status,
                reason=(
                    "deterministic deriving/attribute/instance artifact guard: clean "
                    "deriving output, attribute state, and instance metadata artifacts "
                    "must exist at the expected per-file path and satisfy the frontend "
                    "deriving/attribute/instance artifact schema before they can be "
                    "cross-checked against parse and elaboration classifications"
                ),
                markers=deriving_attribute_instance_markers,
                expected_artifact=clean_deriving_attribute_instance_artifact,
            ),
            "structure_inductive_recursor": dimension(
                structure_inductive_recursor_status,
                reason=(
                    "lexical structure, inductive, match, and recursor surface "
                    "marker scan"
                ),
                markers=structure_inductive_recursor_markers,
            ),
            "lean4_structure_inductive_recursor_artifact": dimension(
                lean4_structure_inductive_recursor_artifact_status,
                reason=(
                    "deterministic structure/inductive/recursor artifact guard: "
                    "Lean4 structure field, inductive declaration, match compilation, "
                    "and recursor artifacts must exist at the expected per-file path "
                    "and satisfy the frontend structure/inductive/recursor artifact "
                    "schema before they can be cross-checked against parse, "
                    "elaboration, and kernel classifications"
                ),
                markers=structure_inductive_recursor_markers,
                expected_artifact=lean4_structure_inductive_recursor_artifact,
            ),
            "clean_structure_inductive_recursor_artifact": dimension(
                clean_structure_inductive_recursor_artifact_status,
                reason=(
                    "deterministic structure/inductive/recursor artifact guard: "
                    "clean structure field, inductive declaration, match compilation, "
                    "and recursor artifacts must exist at the expected per-file path "
                    "and satisfy the frontend structure/inductive/recursor artifact "
                    "schema before they can be cross-checked against parse, "
                    "elaboration, and kernel classifications"
                ),
                markers=structure_inductive_recursor_markers,
                expected_artifact=clean_structure_inductive_recursor_artifact,
            ),
            "trust": dimension(
                trust_status,
                reason="lexical trusted-feature marker scan",
                markers=trust_markers,
            ),
            "lean4_trust_artifact": dimension(
                lean4_trust_artifact_status,
                reason=(
                    "deterministic trust-artifact guard: no generated per-file "
                    "Lean4 trust, sorry, or fallback artifact is recorded for "
                    "rows where the trust dimension found elab-relevant trusted "
                    "surface"
                ),
                markers=trust_markers,
            ),
            "clean_trust_artifact": dimension(
                clean_trust_artifact_status,
                reason=(
                    "deterministic trust-artifact guard: no generated per-file "
                    "clean trust, sorry, or fallback artifact is recorded for "
                    "rows where the trust dimension found elab-relevant trusted "
                    "surface"
                ),
                markers=trust_markers,
            ),
            "diagnostic": dimension(
                diagnostic_status,
                reason="expected diagnostics are profiled or conservatively marked as unclaimed",
                markers=diagnostic_markers,
            ),
            "diagnostic_category": dimension(
                diagnostic_category_status,
                reason=(
                    "coarse bucket derived from phase1 expected-failure diagnostic substrings; "
                    "not a Lean4 diagnostic parity check"
                ),
                markers=profiled_diagnostic_categories,
            ),
            "first_error_signature": dimension(
                first_error_signature_status,
                reason=(
                    "deterministic first expected-failure substring signature from "
                    "phase1_expected_outcomes.json; not a Lean4 first-diagnostic parity check"
                ),
                markers=(
                    [profiled_first_error_signature]
                    if profiled_first_error_signature is not None
                    else None
                ),
            ),
            "phase1_transition": dimension(
                phase1_transition_status,
                reason=(
                    "deterministic Phase 1 parse/elab/profile transition bucket; "
                    "expected-success and expected-failure buckets are status evidence only"
                ),
            ),
            "expected_success_accountability": dimension(
                expected_success_accountability_status,
                reason=(
                    "deterministic expected-success accountability bucket; profiled and "
                    "unprofiled success contracts are evidence only and do not imply launch "
                    "readiness"
                ),
            ),
            "lean4_vs_clean_run_artifact": dimension(
                lean4_vs_clean_run_artifact_dimension_status,
                reason=(
                    "deterministic replacement-readiness guard: paired "
                    "Lean4-vs-clean run artifacts must exist and be cross-checked "
                    "before this corpus bucket can support frontend readiness"
                ),
                expected_artifact=lean4_vs_clean_run_artifact,
            ),
            "lean4_exit_status": dimension(
                lean4_exit_status,
                reason=(
                    "deterministic exit-status artifact guard: Lean4 result "
                    "artifacts must exist at the expected per-file path and satisfy "
                    "the frontend exit-status artifact schema before they can count "
                    "as cross-check evidence"
                ),
                expected_artifact=lean4_exit_status_artifact,
            ),
            "clean_exit_status": dimension(
                clean_exit_status,
                reason=(
                    "deterministic exit-status artifact guard: clean result "
                    "artifacts must exist at the expected per-file path and satisfy "
                    "the frontend exit-status artifact schema before they can count "
                    "as cross-check evidence"
                ),
                expected_artifact=clean_exit_status_artifact,
            ),
            "lean4_diagnostic_artifact": dimension(
                lean4_diagnostic_artifact_status,
                reason=(
                    "deterministic diagnostic-text artifact guard: Lean4 "
                    "diagnostic artifacts must exist at the expected per-file "
                    "path and satisfy the frontend diagnostic artifact schema "
                    "before they can be cross-checked against diagnostic_category "
                    "and first_error_signature"
                ),
                expected_artifact=lean4_diagnostic_artifact,
            ),
            "clean_diagnostic_artifact": dimension(
                clean_diagnostic_artifact_status,
                reason=(
                    "deterministic diagnostic-text artifact guard: clean "
                    "diagnostic artifacts must exist at the expected per-file "
                    "path and satisfy the frontend diagnostic artifact schema "
                    "before they can be cross-checked against diagnostic_category "
                    "and first_error_signature"
                ),
                expected_artifact=clean_diagnostic_artifact,
            ),
            "expected_failure": dimension(
                expected_failure_status,
                reason="derived from phase1_expected_outcomes.json or Phase 1 exclusions",
            ),
        }

        for dimension_name, data in dimensions.items():
            status_counts[dimension_name][str(data["status"])] += 1

        files.append(
            {
                "filename": filename,
                "sha256": sha256,
                "phase1_level": level,
                "profiled": filename in profiles,
                "dimensions": dimensions,
            }
        )

    def frontend_run_artifact_comparison_status(
        file: dict[str, object],
    ) -> str | None:
        if file.get("phase1_level") != "elab":
            return None
        dimensions = file.get("dimensions")
        if not isinstance(dimensions, dict):
            return None
        run_artifact = dimensions.get("lean4_vs_clean_run_artifact")
        if not isinstance(run_artifact, dict):
            return None
        expected_artifact = run_artifact.get("expected_artifact")
        if not isinstance(expected_artifact, dict):
            return None
        if expected_artifact.get("state") != "valid":
            return None
        comparison_status = expected_artifact.get("comparison_status")
        return comparison_status if isinstance(comparison_status, str) else None

    def frontend_run_artifact_expected_artifact(
        file: dict[str, object],
    ) -> dict[str, object] | None:
        if file.get("phase1_level") != "elab":
            return None
        dimensions = file.get("dimensions")
        if not isinstance(dimensions, dict):
            return None
        run_artifact = dimensions.get("lean4_vs_clean_run_artifact")
        if not isinstance(run_artifact, dict):
            return None
        expected_artifact = run_artifact.get("expected_artifact")
        if not isinstance(expected_artifact, dict):
            return None
        if expected_artifact.get("state") != "valid":
            return None
        return expected_artifact

    def frontend_run_artifact_signature_evidence(
        bucket_files: list[str],
    ) -> list[dict[str, object]]:
        bucket_file_set = set(bucket_files)
        evidence = []
        for file in files:
            filename = str(file["filename"])
            if filename not in bucket_file_set:
                continue
            artifact = frontend_run_artifact_expected_artifact(file)
            if artifact is None:
                continue
            evidence.append(
                {
                    "filename": filename,
                    "run_artifact_path": artifact.get("path"),
                    "comparison_status": artifact.get("comparison_status"),
                    "lean4_status": artifact.get("lean4_status"),
                    "clean_status": artifact.get("clean_status"),
                    "lean4_diagnostic_category": artifact.get(
                        "lean4_diagnostic_category"
                    ),
                    "clean_diagnostic_category": artifact.get(
                        "clean_diagnostic_category"
                    ),
                    "lean4_first_error_signature": artifact.get(
                        "lean4_first_error_signature"
                    ),
                    "clean_first_error_signature": artifact.get(
                        "clean_first_error_signature"
                    ),
                }
            )
        return sorted(evidence, key=lambda record: str(record["filename"]))

    exit_status_cross_checked_frontend_run_files = sorted(
        str(file["filename"])
        for file in files
        if (
            frontend_run_artifact_comparison_status(file)
            in {
                "exit_status_match_first_error_signature_match",
                "exit_status_match_first_error_signature_mismatch",
            }
        )
    )
    diagnostic_artifact_cross_checked_frontend_run_files = sorted(
        str(file["filename"])
        for file in files
        if (
            frontend_run_artifact_comparison_status(file)
            == "exit_status_match_first_error_signature_match"
        )
    )
    incomplete_or_mismatched_frontend_run_files = sorted(
        str(file["filename"])
        for file in files
        if file.get("phase1_level") == "elab"
        and str(file["filename"])
        not in diagnostic_artifact_cross_checked_frontend_run_files
    )
    exit_status_mismatched_frontend_run_files = sorted(
        str(file["filename"])
        for file in files
        if (
            frontend_run_artifact_comparison_status(file)
            == "exit_status_mismatch_first_error_signature_mismatch"
        )
    )
    exit_status_mismatch_clean_unexpected_success_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
        )
    )
    exit_status_mismatch_clean_unexpected_success_unexpected_token_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and artifact.get("lean4_first_error_signature")
            == "unexpected_token_expected"
        )
    )
    exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
            and artifact.get("clean_diagnostic_category") is None
            and artifact.get("lean4_first_error_signature")
            == "unexpected_token_expected"
            and artifact.get("clean_first_error_signature") is None
        )
    )
    exit_status_mismatch_clean_unexpected_success_dependent_elim_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and str(artifact.get("lean4_first_error_signature")).startswith(
                "dependent_elimination_failed"
            )
        )
    )
    exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
            and artifact.get("clean_diagnostic_category") is None
            and artifact.get("lean4_first_error_signature")
            == "dependent_elimination_failed_type_mismatch_when_solving_this_alternative_it_has_type"
            and artifact.get("clean_first_error_signature") is None
        )
    )
    exit_status_mismatch_clean_unexpected_success_implicit_arg_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and "synthesize_implicit_argument"
            in str(artifact.get("lean4_first_error_signature"))
        )
    )
    exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_files = (
        sorted(
            str(file["filename"])
            for file in files
            if (
                (artifact := frontend_run_artifact_expected_artifact(file)) is not None
                and artifact.get("comparison_status")
                == "exit_status_mismatch_first_error_signature_mismatch"
                and artifact.get("lean4_status") == "failure"
                and artifact.get("clean_status") == "success"
                and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
                and artifact.get("clean_diagnostic_category") is None
                and artifact.get("lean4_first_error_signature")
                == "don_t_know_how_to_synthesize_implicit_argument_z"
                and artifact.get("clean_first_error_signature") is None
            )
        )
    )
    exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and str(artifact.get("lean4_first_error_signature")).startswith(
                "invalid_implemented_by_argument"
            )
        )
    )
    exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
            and artifact.get("clean_diagnostic_category") is None
            and artifact.get("lean4_first_error_signature")
            == "invalid_implemented_by_argument_foo_definition_cannot_be_implemented_by_itself"
            and artifact.get("clean_first_error_signature") is None
        )
    )
    exit_status_mismatch_clean_unexpected_success_termination_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and artifact.get("lean4_first_error_signature")
            == "termination_check_failure"
        )
    )
    exit_status_mismatch_clean_unexpected_success_termination_signature_drift_files = (
        sorted(
            str(file["filename"])
            for file in files
            if (
                (artifact := frontend_run_artifact_expected_artifact(file)) is not None
                and artifact.get("comparison_status")
                == "exit_status_mismatch_first_error_signature_mismatch"
                and artifact.get("lean4_status") == "failure"
                and artifact.get("clean_status") == "success"
                and artifact.get("lean4_diagnostic_category")
                == "termination_check_failure"
                and artifact.get("clean_diagnostic_category") is None
                and artifact.get("lean4_first_error_signature")
                == "termination_check_failure"
                and artifact.get("clean_first_error_signature") is None
            )
        )
    )
    exit_status_mismatch_clean_unexpected_success_placeholder_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "success"
            and artifact.get("lean4_first_error_signature")
            == "don_t_know_how_to_synthesize_placeholder"
        )
    )
    exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_files = (
        sorted(
            str(file["filename"])
            for file in files
            if (
                (artifact := frontend_run_artifact_expected_artifact(file)) is not None
                and artifact.get("comparison_status")
                == "exit_status_mismatch_first_error_signature_mismatch"
                and artifact.get("lean4_status") == "failure"
                and artifact.get("clean_status") == "success"
                and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
                and artifact.get("clean_diagnostic_category") is None
                and artifact.get("lean4_first_error_signature")
                == "don_t_know_how_to_synthesize_placeholder"
                and artifact.get("clean_first_error_signature") is None
            )
        )
    )
    exit_status_mismatch_clean_unexpected_failure_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "success"
            and artifact.get("clean_status") == "failure"
        )
    )
    exit_status_mismatch_clean_unexpected_failure_unknown_identifier_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "success"
            and artifact.get("clean_status") == "failure"
            and artifact.get("clean_first_error_signature")
            == "unknown_ident_with_suggestions"
        )
    )
    exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "success"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") is None
            and artifact.get("clean_diagnostic_category")
            == "unknown_identifier_or_scope"
            and artifact.get("lean4_first_error_signature") is None
            and artifact.get("clean_first_error_signature")
            == "unknown_ident_with_suggestions"
        )
    )
    exit_status_mismatch_clean_unexpected_failure_too_many_arguments_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "success"
            and artifact.get("clean_status") == "failure"
            and artifact.get("clean_first_error_signature") == "too_many_arguments"
        )
    )
    exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "success"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") is None
            and artifact.get("clean_diagnostic_category") == "clean_frontend_error"
            and artifact.get("lean4_first_error_signature") is None
            and artifact.get("clean_first_error_signature") == "too_many_arguments"
        )
    )
    exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "success"
            and artifact.get("clean_status") == "failure"
            and "synthetic_sorry" in str(artifact.get("clean_first_error_signature"))
        )
    )
    exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_mismatch_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "success"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") is None
            and artifact.get("clean_diagnostic_category") == "other_frontend_error"
            and artifact.get("lean4_first_error_signature") is None
            and artifact.get("clean_first_error_signature")
            == "ex_declaration_uses_synthetic_sorry"
        )
    )
    diagnostic_only_mismatched_frontend_run_files = sorted(
        str(file["filename"])
        for file in files
        if (
            frontend_run_artifact_comparison_status(file)
            == "exit_status_match_first_error_signature_mismatch"
        )
    )
    diagnostic_only_clean_unsupported_import_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("clean_first_error_signature")
            == "unsupported_import_lean_elab_tactic"
        )
    )
    diagnostic_only_unsupported_import_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") == "user_thrown_tactic_error"
            and artifact.get("clean_diagnostic_category") == "clean_frontend_error"
            and artifact.get("lean4_first_error_signature") == "error"
            and artifact.get("clean_first_error_signature")
            == "unsupported_import_lean_elab_tactic"
        )
    )
    diagnostic_only_clean_synthetic_sorry_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and "synthetic_sorry" in str(artifact.get("clean_first_error_signature"))
        )
    )
    diagnostic_only_synthetic_sorry_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
            and artifact.get("clean_diagnostic_category") == "other_frontend_error"
            and artifact.get("lean4_first_error_signature")
            == "application_type_mismatch_the_argument"
            and "synthetic_sorry" in str(artifact.get("clean_first_error_signature"))
        )
    )
    diagnostic_only_clean_unknown_identifier_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_first_error_signature") == "unknown_identifier"
            and artifact.get("clean_first_error_signature")
            == "unknown_ident_with_suggestions"
        )
    )
    diagnostic_only_unknown_identifier_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category")
            == "unknown_identifier_or_scope"
            and artifact.get("clean_diagnostic_category")
            == "unknown_identifier_or_scope"
            and artifact.get("lean4_first_error_signature") == "unknown_identifier"
            and artifact.get("clean_first_error_signature")
            == "unknown_ident_with_suggestions"
        )
    )
    diagnostic_only_clean_unknown_fvar_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("clean_first_error_signature")
            == "unknown_fvar_type_mismatch"
        )
    )
    diagnostic_only_unknown_fvar_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") == "termination_check_failure"
            and artifact.get("clean_diagnostic_category")
            == "internal_fvar_reconstruction_blocker"
            and artifact.get("lean4_first_error_signature")
            == "termination_check_failure"
            and artifact.get("clean_first_error_signature")
            == "unknown_fvar_type_mismatch"
        )
    )
    diagnostic_only_clean_too_many_arguments_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("clean_first_error_signature") == "too_many_arguments"
        )
    )
    diagnostic_only_too_many_arguments_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category")
            == "unknown_identifier_or_scope"
            and artifact.get("clean_diagnostic_category") == "clean_frontend_error"
            and artifact.get("lean4_first_error_signature") == "unknown_constant"
            and artifact.get("clean_first_error_signature") == "too_many_arguments"
        )
    )
    diagnostic_only_invalid_implemented_by_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
            and artifact.get("clean_diagnostic_category") == "other_frontend_error"
            and artifact.get("lean4_first_error_signature")
            == "invalid_implemented_by_argument_foo_definition_cannot_be_implemented_by_itself"
            and artifact.get("clean_first_error_signature")
            == "elaboration_error_unsupported_feature_invalid_implemented_by_argument_foo_definition_cannot_be_implemented_by_itself"
        )
    )
    diagnostic_only_parser_recovery_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
            and artifact.get("clean_diagnostic_category") == "other_frontend_error"
            and artifact.get("lean4_first_error_signature")
            == "unexpected_token_expected"
            and artifact.get("clean_first_error_signature")
            == "elaboration_error_parseerror_parser_recovery_produced_raw_declaration_error_recovery_db"
        )
    )
    diagnostic_only_placeholder_signature_drift_files = sorted(
        str(file["filename"])
        for file in files
        if (
            (artifact := frontend_run_artifact_expected_artifact(file)) is not None
            and artifact.get("comparison_status")
            == "exit_status_match_first_error_signature_mismatch"
            and artifact.get("lean4_status") == "failure"
            and artifact.get("clean_status") == "failure"
            and artifact.get("lean4_diagnostic_category") == "other_frontend_error"
            and artifact.get("clean_diagnostic_category") == "other_frontend_error"
            and artifact.get("lean4_first_error_signature")
            == "don_t_know_how_to_synthesize_placeholder"
            and artifact.get("clean_first_error_signature")
            == "elaboration_error_cannotinfer"
        )
    )
    exit_status_mismatch_signature_drift_files = sorted(
        {
            *exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_success_termination_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_files,
            *exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_files,
        }
    )
    diagnostic_only_signature_drift_files = sorted(
        {
            *diagnostic_only_unsupported_import_signature_drift_files,
            *diagnostic_only_synthetic_sorry_signature_drift_files,
            *diagnostic_only_unknown_identifier_signature_drift_files,
            *diagnostic_only_unknown_fvar_signature_drift_files,
            *diagnostic_only_too_many_arguments_signature_drift_files,
            *diagnostic_only_invalid_implemented_by_signature_drift_files,
            *diagnostic_only_parser_recovery_signature_drift_files,
            *diagnostic_only_placeholder_signature_drift_files,
        }
    )
    reviewed_incomplete_or_mismatched_frontend_run_files = sorted(
        {
            *exit_status_mismatch_signature_drift_files,
            *diagnostic_only_signature_drift_files,
        }
    )
    unbucketed_incomplete_or_mismatched_frontend_run_files = sorted(
        set(incomplete_or_mismatched_frontend_run_files)
        - set(reviewed_incomplete_or_mismatched_frontend_run_files)
    )
    diagnostic_only_unsupported_import_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_unsupported_import_signature_drift_files
        )
    )
    diagnostic_only_synthetic_sorry_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_synthetic_sorry_signature_drift_files
        )
    )
    diagnostic_only_unknown_identifier_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_unknown_identifier_signature_drift_files
        )
    )
    diagnostic_only_unknown_fvar_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_unknown_fvar_signature_drift_files
        )
    )
    diagnostic_only_too_many_arguments_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_too_many_arguments_signature_drift_files
        )
    )
    diagnostic_only_invalid_implemented_by_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_invalid_implemented_by_signature_drift_files
        )
    )
    diagnostic_only_parser_recovery_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_parser_recovery_signature_drift_files
        )
    )
    diagnostic_only_placeholder_signature_drift_evidence = (
        frontend_run_artifact_signature_evidence(
            diagnostic_only_placeholder_signature_drift_files
        )
    )
    exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_success_termination_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_success_termination_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_files
    )
    exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_evidence = frontend_run_artifact_signature_evidence(
        exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_files
    )
    signature_drift_evidence_buckets = {
        "frontend_run_artifact_diagnostic_only_unsupported_import_signature_drift": (
            diagnostic_only_unsupported_import_signature_drift_files,
            diagnostic_only_unsupported_import_signature_drift_evidence,
        ),
        "frontend_run_artifact_diagnostic_only_synthetic_sorry_signature_drift": (
            diagnostic_only_synthetic_sorry_signature_drift_files,
            diagnostic_only_synthetic_sorry_signature_drift_evidence,
        ),
        "frontend_run_artifact_diagnostic_only_unknown_identifier_signature_drift": (
            diagnostic_only_unknown_identifier_signature_drift_files,
            diagnostic_only_unknown_identifier_signature_drift_evidence,
        ),
        "frontend_run_artifact_diagnostic_only_unknown_fvar_signature_drift": (
            diagnostic_only_unknown_fvar_signature_drift_files,
            diagnostic_only_unknown_fvar_signature_drift_evidence,
        ),
        "frontend_run_artifact_diagnostic_only_too_many_arguments_signature_drift": (
            diagnostic_only_too_many_arguments_signature_drift_files,
            diagnostic_only_too_many_arguments_signature_drift_evidence,
        ),
        "frontend_run_artifact_diagnostic_only_invalid_implemented_by_signature_drift": (
            diagnostic_only_invalid_implemented_by_signature_drift_files,
            diagnostic_only_invalid_implemented_by_signature_drift_evidence,
        ),
        "frontend_run_artifact_diagnostic_only_parser_recovery_signature_drift": (
            diagnostic_only_parser_recovery_signature_drift_files,
            diagnostic_only_parser_recovery_signature_drift_evidence,
        ),
        "frontend_run_artifact_diagnostic_only_placeholder_signature_drift": (
            diagnostic_only_placeholder_signature_drift_files,
            diagnostic_only_placeholder_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift": (
            exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_files,
            exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift": (
            exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_files,
            exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift": (
            exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_files,
            exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_termination_signature_drift": (
            exit_status_mismatch_clean_unexpected_success_termination_signature_drift_files,
            exit_status_mismatch_clean_unexpected_success_termination_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift": (
            exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_files,
            exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift": (
            exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_files,
            exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift": (
            exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_files,
            exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift": (
            exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_files,
            exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_evidence,
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift": (
            exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_files,
            exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_evidence,
        ),
    }
    unevidenced_signature_drift_buckets = []
    mismatched_signature_drift_evidence_buckets = []
    for key, (bucket_files, evidence) in signature_drift_evidence_buckets.items():
        evidence_files = sorted(str(record["filename"]) for record in evidence)
        if bucket_files and not evidence:
            unevidenced_signature_drift_buckets.append(
                {
                    "files_key": f"{key}_files",
                    "evidence_key": f"{key}_evidence",
                    "files": bucket_files,
                }
            )
        if bucket_files != evidence_files:
            mismatched_signature_drift_evidence_buckets.append(
                {
                    "files_key": f"{key}_files",
                    "evidence_key": f"{key}_evidence",
                    "files": bucket_files,
                    "evidence_files": evidence_files,
                }
            )
    unevidenced_signature_drift_buckets = sorted(
        unevidenced_signature_drift_buckets,
        key=lambda record: str(record["files_key"]),
    )
    mismatched_signature_drift_evidence_buckets = sorted(
        mismatched_signature_drift_evidence_buckets,
        key=lambda record: str(record["files_key"]),
    )
    launch_blocker_reasons = {
        "frontend_run_artifact_diagnostic_only_synthetic_sorry_signature_drift": (
            "clean and Lean4 both fail, but the first-error signature differs: clean reports synthetic sorry instead of Lean4's application type mismatch."
        ),
        "frontend_run_artifact_diagnostic_only_too_many_arguments_signature_drift": (
            "clean and Lean4 both fail, but the first-error signature differs: clean reports too many arguments instead of Lean4's unknown constant."
        ),
        "frontend_run_artifact_diagnostic_only_unknown_fvar_signature_drift": (
            "clean and Lean4 both fail, but the first-error signature differs: clean reports an internal free-variable reconstruction blocker instead of Lean4's termination check failure."
        ),
        "frontend_run_artifact_diagnostic_only_unknown_identifier_signature_drift": (
            "clean and Lean4 both fail, but the first-error signature differs: clean reports an unknown identifier with suggestions instead of Lean4's unknown identifier signature."
        ),
        "frontend_run_artifact_diagnostic_only_unsupported_import_signature_drift": (
            "clean and Lean4 both fail, but clean reports an unsupported import while Lean4 reaches the expected user-thrown tactic error."
        ),
        "frontend_run_artifact_diagnostic_only_invalid_implemented_by_signature_drift": (
            "clean and Lean4 both fail on invalid implemented_by self-reference, but clean reports the fail-closed unsupported-feature diagnostic instead of Lean4's native implemented_by diagnostic."
        ),
        "frontend_run_artifact_diagnostic_only_parser_recovery_signature_drift": (
            "clean and Lean4 both fail, but clean reports parser-recovery RawDecl rejection instead of Lean4's unexpected-token parse error."
        ),
        "frontend_run_artifact_diagnostic_only_placeholder_signature_drift": (
            "clean and Lean4 both fail, but clean reports CannotInfer instead of Lean4's placeholder synthesis diagnostic."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift": (
            "Lean4 succeeds, but clean fails because the declaration uses synthetic sorry."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift": (
            "Lean4 succeeds, but clean fails with a too-many-arguments frontend error."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift": (
            "Lean4 succeeds, but clean fails with an unknown identifier diagnostic."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift": (
            "Lean4 rejects dependent elimination, but clean unexpectedly succeeds."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift": (
            "Lean4 rejects implicit argument synthesis, but clean unexpectedly succeeds."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift": (
            "Lean4 rejects an invalid implemented_by self-reference, but clean unexpectedly succeeds."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift": (
            "Lean4 rejects placeholder synthesis, but clean unexpectedly succeeds."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_termination_signature_drift": (
            "Lean4 rejects termination checking, but clean unexpectedly succeeds."
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift": (
            "Lean4 reports an unexpected token parse/frontend error, but clean unexpectedly succeeds."
        ),
    }
    launch_blocker_buckets = sorted(
        (
            {
                "bucket_key": key,
                "files": bucket_files,
                "file_count": len(bucket_files),
                "blocker_reason": launch_blocker_reasons[key],
            }
            for key, (
                bucket_files,
                _evidence,
            ) in signature_drift_evidence_buckets.items()
            if bucket_files
        ),
        key=lambda record: str(record["bucket_key"]),
    )
    launch_blocker_file_count = sum(
        cast("int", record["file_count"]) for record in launch_blocker_buckets
    )

    summary = {
        "corpus_files": len(filenames),
        "phase1_gate_files": len(phase1_manifest),
        "phase1_elab_files": sum(
            1 for level in phase1_manifest.values() if level == "elab"
        ),
        "phase1_parse_only_files": sum(
            1 for level in phase1_manifest.values() if level == "parse_only"
        ),
        "excluded_from_phase1_gate_files": len(excluded_files),
        "frontend_slice_kernel_pass_files": len(slice_manifest),
        "profiled_files": len(profiles),
        "profiled_expected_failure_files": len(expected_failure_files),
        "exit_status_cross_checked_files": len(
            exit_status_cross_checked_frontend_run_files
        ),
        "diagnostic_artifact_cross_checked_files": len(
            diagnostic_artifact_cross_checked_frontend_run_files
        ),
        "cross_checked_exit_status_files": exit_status_cross_checked_frontend_run_files,
        "cross_checked_diagnostic_artifact_files": (
            diagnostic_artifact_cross_checked_frontend_run_files
        ),
        "frontend_run_artifact_exit_status_mismatched_elab_files": (
            exit_status_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_exit_status_mismatched_elab_file_count": len(
            exit_status_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_files": (
            exit_status_mismatch_clean_unexpected_success_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_file_count": len(
            exit_status_mismatch_clean_unexpected_success_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_unexpected_token_files": (
            exit_status_mismatch_clean_unexpected_success_unexpected_token_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_unexpected_token_file_count": len(
            exit_status_mismatch_clean_unexpected_success_unexpected_token_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_success_unexpected_token_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_dependent_elim_files": (
            exit_status_mismatch_clean_unexpected_success_dependent_elim_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_dependent_elim_file_count": len(
            exit_status_mismatch_clean_unexpected_success_dependent_elim_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_success_dependent_elim_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_implicit_arg_files": (
            exit_status_mismatch_clean_unexpected_success_implicit_arg_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_implicit_arg_file_count": len(
            exit_status_mismatch_clean_unexpected_success_implicit_arg_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_success_implicit_arg_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_files": (
            exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_file_count": len(
            exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_success_invalid_implemented_by_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_termination_files": (
            exit_status_mismatch_clean_unexpected_success_termination_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_termination_file_count": len(
            exit_status_mismatch_clean_unexpected_success_termination_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_termination_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_success_termination_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_termination_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_success_termination_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_termination_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_success_termination_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_placeholder_files": (
            exit_status_mismatch_clean_unexpected_success_placeholder_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_placeholder_file_count": len(
            exit_status_mismatch_clean_unexpected_success_placeholder_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_success_placeholder_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_files": (
            exit_status_mismatch_clean_unexpected_failure_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_file_count": len(
            exit_status_mismatch_clean_unexpected_failure_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_unknown_identifier_files": (
            exit_status_mismatch_clean_unexpected_failure_unknown_identifier_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_unknown_identifier_file_count": len(
            exit_status_mismatch_clean_unexpected_failure_unknown_identifier_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_failure_unknown_identifier_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_too_many_arguments_files": (
            exit_status_mismatch_clean_unexpected_failure_too_many_arguments_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_too_many_arguments_file_count": len(
            exit_status_mismatch_clean_unexpected_failure_too_many_arguments_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_failure_too_many_arguments_signature_drift_evidence
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_files": (
            exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_file_count": len(
            exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_files": (
            exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_file_count": len(
            exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_files
        ),
        "frontend_run_artifact_exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_evidence": (
            exit_status_mismatch_clean_unexpected_failure_synthetic_sorry_signature_drift_evidence
        ),
        "frontend_run_artifact_incomplete_or_mismatched_elab_files": (
            incomplete_or_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_incomplete_or_mismatched_elab_file_count": len(
            incomplete_or_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_review_bucketed_incomplete_or_mismatched_elab_files": (
            reviewed_incomplete_or_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_review_bucketed_incomplete_or_mismatched_elab_file_count": len(
            reviewed_incomplete_or_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_unbucketed_incomplete_or_mismatched_elab_files": (
            unbucketed_incomplete_or_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_unbucketed_incomplete_or_mismatched_elab_file_count": len(
            unbucketed_incomplete_or_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_signature_drift_evidence_bucket_count": len(
            signature_drift_evidence_buckets
        ),
        "frontend_run_artifact_unevidenced_signature_drift_buckets": (
            unevidenced_signature_drift_buckets
        ),
        "frontend_run_artifact_unevidenced_signature_drift_bucket_count": len(
            unevidenced_signature_drift_buckets
        ),
        "frontend_run_artifact_signature_drift_evidence_mismatched_buckets": (
            mismatched_signature_drift_evidence_buckets
        ),
        "frontend_run_artifact_signature_drift_evidence_mismatched_bucket_count": len(
            mismatched_signature_drift_evidence_buckets
        ),
        "frontend_run_artifact_launch_blocker_buckets": launch_blocker_buckets,
        "frontend_run_artifact_launch_blocker_bucket_count": len(
            launch_blocker_buckets
        ),
        "frontend_run_artifact_launch_blocker_file_count": launch_blocker_file_count,
        "frontend_run_artifact_diagnostic_only_mismatched_elab_files": (
            diagnostic_only_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_diagnostic_only_mismatched_elab_file_count": len(
            diagnostic_only_mismatched_frontend_run_files
        ),
        "frontend_run_artifact_diagnostic_only_clean_unsupported_import_files": (
            diagnostic_only_clean_unsupported_import_files
        ),
        "frontend_run_artifact_diagnostic_only_clean_unsupported_import_file_count": len(
            diagnostic_only_clean_unsupported_import_files
        ),
        "frontend_run_artifact_diagnostic_only_unsupported_import_signature_drift_files": (
            diagnostic_only_unsupported_import_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_unsupported_import_signature_drift_file_count": len(
            diagnostic_only_unsupported_import_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_unsupported_import_signature_drift_evidence": (
            diagnostic_only_unsupported_import_signature_drift_evidence
        ),
        "frontend_run_artifact_diagnostic_only_clean_synthetic_sorry_files": (
            diagnostic_only_clean_synthetic_sorry_files
        ),
        "frontend_run_artifact_diagnostic_only_clean_synthetic_sorry_file_count": len(
            diagnostic_only_clean_synthetic_sorry_files
        ),
        "frontend_run_artifact_diagnostic_only_synthetic_sorry_signature_drift_files": (
            diagnostic_only_synthetic_sorry_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_synthetic_sorry_signature_drift_file_count": len(
            diagnostic_only_synthetic_sorry_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_synthetic_sorry_signature_drift_evidence": (
            diagnostic_only_synthetic_sorry_signature_drift_evidence
        ),
        "frontend_run_artifact_diagnostic_only_clean_unknown_identifier_files": (
            diagnostic_only_clean_unknown_identifier_files
        ),
        "frontend_run_artifact_diagnostic_only_clean_unknown_identifier_file_count": len(
            diagnostic_only_clean_unknown_identifier_files
        ),
        "frontend_run_artifact_diagnostic_only_unknown_identifier_signature_drift_files": (
            diagnostic_only_unknown_identifier_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_unknown_identifier_signature_drift_file_count": len(
            diagnostic_only_unknown_identifier_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_unknown_identifier_signature_drift_evidence": (
            diagnostic_only_unknown_identifier_signature_drift_evidence
        ),
        "frontend_run_artifact_diagnostic_only_clean_unknown_fvar_files": (
            diagnostic_only_clean_unknown_fvar_files
        ),
        "frontend_run_artifact_diagnostic_only_clean_unknown_fvar_file_count": len(
            diagnostic_only_clean_unknown_fvar_files
        ),
        "frontend_run_artifact_diagnostic_only_unknown_fvar_signature_drift_files": (
            diagnostic_only_unknown_fvar_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_unknown_fvar_signature_drift_file_count": len(
            diagnostic_only_unknown_fvar_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_unknown_fvar_signature_drift_evidence": (
            diagnostic_only_unknown_fvar_signature_drift_evidence
        ),
        "frontend_run_artifact_diagnostic_only_clean_too_many_arguments_files": (
            diagnostic_only_clean_too_many_arguments_files
        ),
        "frontend_run_artifact_diagnostic_only_clean_too_many_arguments_file_count": len(
            diagnostic_only_clean_too_many_arguments_files
        ),
        "frontend_run_artifact_diagnostic_only_too_many_arguments_signature_drift_files": (
            diagnostic_only_too_many_arguments_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_too_many_arguments_signature_drift_file_count": len(
            diagnostic_only_too_many_arguments_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_too_many_arguments_signature_drift_evidence": (
            diagnostic_only_too_many_arguments_signature_drift_evidence
        ),
        "frontend_run_artifact_diagnostic_only_invalid_implemented_by_signature_drift_files": (
            diagnostic_only_invalid_implemented_by_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_invalid_implemented_by_signature_drift_file_count": len(
            diagnostic_only_invalid_implemented_by_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_invalid_implemented_by_signature_drift_evidence": (
            diagnostic_only_invalid_implemented_by_signature_drift_evidence
        ),
        "frontend_run_artifact_diagnostic_only_parser_recovery_signature_drift_files": (
            diagnostic_only_parser_recovery_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_parser_recovery_signature_drift_file_count": len(
            diagnostic_only_parser_recovery_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_parser_recovery_signature_drift_evidence": (
            diagnostic_only_parser_recovery_signature_drift_evidence
        ),
        "frontend_run_artifact_diagnostic_only_placeholder_signature_drift_files": (
            diagnostic_only_placeholder_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_placeholder_signature_drift_file_count": len(
            diagnostic_only_placeholder_signature_drift_files
        ),
        "frontend_run_artifact_diagnostic_only_placeholder_signature_drift_evidence": (
            diagnostic_only_placeholder_signature_drift_evidence
        ),
        "tactic_surface_files": status_counts["tactic"]["contains_tactic_surface"],
        "macro_notation_surface_files": status_counts["macro_notation"][
            "contains_macro_notation_surface"
        ],
        "syntax_quotation_surface_files": status_counts["syntax_quotation"][
            "contains_syntax_quotation_surface"
        ],
        "namespace_open_scoping_surface_files": status_counts["namespace_open_scoping"][
            "contains_namespace_open_scoping_surface"
        ],
        "module_import_surface_files": status_counts["module_import_resolution"][
            "contains_module_import_surface"
        ],
        "level_typeclass_surface_files": status_counts["level_typeclass_resolution"][
            "contains_level_typeclass_surface"
        ],
        "deriving_attribute_instance_surface_files": status_counts[
            "deriving_attribute_instance"
        ]["contains_deriving_attribute_instance_surface"],
        "structure_inductive_recursor_surface_files": status_counts[
            "structure_inductive_recursor"
        ]["contains_structure_inductive_recursor_surface"],
        "trust_marker_files": status_counts["trust"]["requires_trust_audit"],
        "lean4_kernel_artifact_buckets": dict(
            sorted(status_counts["lean4_kernel_artifact"].items())
        ),
        "clean_kernel_artifact_buckets": dict(
            sorted(status_counts["clean_kernel_artifact"].items())
        ),
        "kernel_artifact_schema": repo_rel(KERNEL_ARTIFACT_SCHEMA_PATH),
        "kernel_artifact_schema_version": KERNEL_ARTIFACT_SCHEMA_VERSION,
        "kernel_artifact_path_template": KERNEL_ARTIFACT_PATH_TEMPLATE,
        "lean4_kernel_artifact_valid_files": sum(
            count
            for status, count in status_counts["lean4_kernel_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_kernel_artifact_valid_files": sum(
            count
            for status, count in status_counts["clean_kernel_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_kernel_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["lean4_kernel_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "clean_kernel_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["clean_kernel_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "lean4_tactic_artifact_buckets": dict(
            sorted(status_counts["lean4_tactic_artifact"].items())
        ),
        "clean_tactic_artifact_buckets": dict(
            sorted(status_counts["clean_tactic_artifact"].items())
        ),
        "lean4_macro_artifact_buckets": dict(
            sorted(status_counts["lean4_macro_artifact"].items())
        ),
        "clean_macro_artifact_buckets": dict(
            sorted(status_counts["clean_macro_artifact"].items())
        ),
        "macro_artifact_schema": repo_rel(MACRO_ARTIFACT_SCHEMA_PATH),
        "macro_artifact_schema_version": MACRO_ARTIFACT_SCHEMA_VERSION,
        "macro_artifact_path_template": MACRO_ARTIFACT_PATH_TEMPLATE,
        "lean4_macro_artifact_valid_files": sum(
            count
            for status, count in status_counts["lean4_macro_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_macro_artifact_valid_files": sum(
            count
            for status, count in status_counts["clean_macro_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_macro_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["lean4_macro_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "clean_macro_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["clean_macro_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "lean4_syntax_quotation_artifact_buckets": dict(
            sorted(status_counts["lean4_syntax_quotation_artifact"].items())
        ),
        "clean_syntax_quotation_artifact_buckets": dict(
            sorted(status_counts["clean_syntax_quotation_artifact"].items())
        ),
        "syntax_quotation_artifact_schema": repo_rel(
            SYNTAX_QUOTATION_ARTIFACT_SCHEMA_PATH
        ),
        "syntax_quotation_artifact_schema_version": (
            SYNTAX_QUOTATION_ARTIFACT_SCHEMA_VERSION
        ),
        "syntax_quotation_artifact_path_template": (
            SYNTAX_QUOTATION_ARTIFACT_PATH_TEMPLATE
        ),
        "lean4_syntax_quotation_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "lean4_syntax_quotation_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_syntax_quotation_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "clean_syntax_quotation_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_syntax_quotation_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "lean4_syntax_quotation_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "clean_syntax_quotation_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "clean_syntax_quotation_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "lean4_namespace_open_scoping_artifact_buckets": dict(
            sorted(status_counts["lean4_namespace_open_scoping_artifact"].items())
        ),
        "clean_namespace_open_scoping_artifact_buckets": dict(
            sorted(status_counts["clean_namespace_open_scoping_artifact"].items())
        ),
        "namespace_open_scoping_artifact_schema": repo_rel(
            NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_PATH
        ),
        "namespace_open_scoping_artifact_schema_version": (
            NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_VERSION
        ),
        "namespace_open_scoping_artifact_path_template": (
            NAMESPACE_OPEN_SCOPING_ARTIFACT_PATH_TEMPLATE
        ),
        "lean4_namespace_open_scoping_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "lean4_namespace_open_scoping_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_namespace_open_scoping_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "clean_namespace_open_scoping_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_namespace_open_scoping_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "lean4_namespace_open_scoping_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "clean_namespace_open_scoping_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "clean_namespace_open_scoping_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "lean4_module_import_artifact_buckets": dict(
            sorted(status_counts["lean4_module_import_artifact"].items())
        ),
        "clean_module_import_artifact_buckets": dict(
            sorted(status_counts["clean_module_import_artifact"].items())
        ),
        "module_import_artifact_schema": repo_rel(MODULE_IMPORT_ARTIFACT_SCHEMA_PATH),
        "module_import_artifact_schema_version": (
            MODULE_IMPORT_ARTIFACT_SCHEMA_VERSION
        ),
        "module_import_artifact_path_template": (MODULE_IMPORT_ARTIFACT_PATH_TEMPLATE),
        "lean4_module_import_artifact_valid_files": sum(
            count
            for status, count in status_counts["lean4_module_import_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_module_import_artifact_valid_files": sum(
            count
            for status, count in status_counts["clean_module_import_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_module_import_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["lean4_module_import_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "clean_module_import_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["clean_module_import_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "lean4_level_typeclass_artifact_buckets": dict(
            sorted(status_counts["lean4_level_typeclass_artifact"].items())
        ),
        "clean_level_typeclass_artifact_buckets": dict(
            sorted(status_counts["clean_level_typeclass_artifact"].items())
        ),
        "level_typeclass_artifact_schema": repo_rel(
            LEVEL_TYPECLASS_ARTIFACT_SCHEMA_PATH
        ),
        "level_typeclass_artifact_schema_version": (
            LEVEL_TYPECLASS_ARTIFACT_SCHEMA_VERSION
        ),
        "level_typeclass_artifact_path_template": (
            LEVEL_TYPECLASS_ARTIFACT_PATH_TEMPLATE
        ),
        "lean4_level_typeclass_artifact_valid_files": sum(
            count
            for status, count in status_counts["lean4_level_typeclass_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_level_typeclass_artifact_valid_files": sum(
            count
            for status, count in status_counts["clean_level_typeclass_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_level_typeclass_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["lean4_level_typeclass_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "clean_level_typeclass_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["clean_level_typeclass_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "lean4_deriving_attribute_instance_artifact_buckets": dict(
            sorted(status_counts["lean4_deriving_attribute_instance_artifact"].items())
        ),
        "clean_deriving_attribute_instance_artifact_buckets": dict(
            sorted(status_counts["clean_deriving_attribute_instance_artifact"].items())
        ),
        "deriving_attribute_instance_artifact_schema": repo_rel(
            DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_PATH
        ),
        "deriving_attribute_instance_artifact_schema_version": (
            DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_VERSION
        ),
        "deriving_attribute_instance_artifact_path_template": (
            DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_PATH_TEMPLATE
        ),
        "lean4_deriving_attribute_instance_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "lean4_deriving_attribute_instance_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_deriving_attribute_instance_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "clean_deriving_attribute_instance_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_deriving_attribute_instance_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "lean4_deriving_attribute_instance_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "clean_deriving_attribute_instance_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "clean_deriving_attribute_instance_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "lean4_structure_inductive_recursor_artifact_buckets": dict(
            sorted(status_counts["lean4_structure_inductive_recursor_artifact"].items())
        ),
        "clean_structure_inductive_recursor_artifact_buckets": dict(
            sorted(status_counts["clean_structure_inductive_recursor_artifact"].items())
        ),
        "structure_inductive_recursor_artifact_schema": repo_rel(
            STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_PATH
        ),
        "structure_inductive_recursor_artifact_schema_version": (
            STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_VERSION
        ),
        "structure_inductive_recursor_artifact_path_template": (
            STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_PATH_TEMPLATE
        ),
        "lean4_structure_inductive_recursor_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "lean4_structure_inductive_recursor_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_structure_inductive_recursor_artifact_valid_files": sum(
            count
            for status, count in status_counts[
                "clean_structure_inductive_recursor_artifact"
            ].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_structure_inductive_recursor_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "lean4_structure_inductive_recursor_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "clean_structure_inductive_recursor_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts[
                "clean_structure_inductive_recursor_artifact"
            ].items()
            if "stale_or_invalid" in status
        ),
        "lean4_trust_artifact_buckets": dict(
            sorted(status_counts["lean4_trust_artifact"].items())
        ),
        "clean_trust_artifact_buckets": dict(
            sorted(status_counts["clean_trust_artifact"].items())
        ),
        "phase1_transition_buckets": dict(
            sorted(status_counts["phase1_transition"].items())
        ),
        "expected_success_accountability_buckets": dict(
            sorted(status_counts["expected_success_accountability"].items())
        ),
        "lean4_vs_clean_run_artifact_buckets": dict(
            sorted(status_counts["lean4_vs_clean_run_artifact"].items())
        ),
        "lean4_vs_clean_run_artifact_schema": repo_rel(
            LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_PATH
        ),
        "lean4_vs_clean_run_artifact_schema_version": (
            LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_VERSION
        ),
        "lean4_vs_clean_run_artifact_path_template": (
            LEAN4_VS_clean_RUN_ARTIFACT_PATH_TEMPLATE
        ),
        "lean4_vs_clean_run_artifact_valid_files": sum(
            count
            for status, count in status_counts["lean4_vs_clean_run_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_vs_clean_run_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["lean4_vs_clean_run_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "lean4_exit_status_buckets": dict(
            sorted(status_counts["lean4_exit_status"].items())
        ),
        "clean_exit_status_buckets": dict(
            sorted(status_counts["clean_exit_status"].items())
        ),
        "exit_status_artifact_schema": repo_rel(EXIT_STATUS_ARTIFACT_SCHEMA_PATH),
        "exit_status_artifact_schema_version": EXIT_STATUS_ARTIFACT_SCHEMA_VERSION,
        "exit_status_artifact_path_template": EXIT_STATUS_ARTIFACT_PATH_TEMPLATE,
        "diagnostic_artifact_schema": repo_rel(DIAGNOSTIC_ARTIFACT_SCHEMA_PATH),
        "diagnostic_artifact_schema_version": DIAGNOSTIC_ARTIFACT_SCHEMA_VERSION,
        "diagnostic_artifact_path_template": DIAGNOSTIC_ARTIFACT_PATH_TEMPLATE,
        "lean4_exit_status_artifact_valid_files": sum(
            count
            for status, count in status_counts["lean4_exit_status"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_exit_status_artifact_valid_files": sum(
            count
            for status, count in status_counts["clean_exit_status"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_exit_status_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["lean4_exit_status"].items()
            if "stale_or_invalid" in status
        ),
        "clean_exit_status_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["clean_exit_status"].items()
            if "stale_or_invalid" in status
        ),
        "lean4_diagnostic_artifact_buckets": dict(
            sorted(status_counts["lean4_diagnostic_artifact"].items())
        ),
        "clean_diagnostic_artifact_buckets": dict(
            sorted(status_counts["clean_diagnostic_artifact"].items())
        ),
        "lean4_diagnostic_artifact_valid_files": sum(
            count
            for status, count in status_counts["lean4_diagnostic_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "clean_diagnostic_artifact_valid_files": sum(
            count
            for status, count in status_counts["clean_diagnostic_artifact"].items()
            if "_valid_" in status or "_unexpected_" in status
        ),
        "lean4_diagnostic_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["lean4_diagnostic_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "clean_diagnostic_artifact_stale_or_invalid_files": sum(
            count
            for status, count in status_counts["clean_diagnostic_artifact"].items()
            if "stale_or_invalid" in status
        ),
        "profiled_expected_diagnostic_categories": dict(
            sorted(diagnostic_category_counts.items())
        ),
        "profiled_first_error_signatures": dict(
            sorted(first_error_signature_counts.items())
        ),
        "dimensions": DIMENSIONS,
        "by_dimension": {
            dimension_name: dict(sorted(counter.items()))
            for dimension_name, counter in status_counts.items()
        },
    }

    replacement_ready = None
    launch_ready = False
    launch_ready_without_replacement_ready = bool(
        launch_ready and replacement_ready is not True
    )

    return {
        "schema_version": "clean-frontend-corpus-classification-v1",
        "generated_by": repo_rel(Path(__file__).resolve()),
        "claim": (
            "Corpus-level classification evidence for frontend replacement dimensions. "
            "This artifact does not claim full Lean4 frontend parity."
        ),
        "full_frontend_parity_claimed": False,
        "overall_status": "pending_evidence",
        "replacement_ready": replacement_ready,
        "launch_ready": launch_ready,
        "launch_ready_without_replacement_ready": launch_ready_without_replacement_ready,
        "source_artifacts": [
            {"kind": "corpus_manifest", "path": repo_rel(manifest_path)},
            {"kind": "phase1_gate", "path": repo_rel(phase1_path)},
            {"kind": "kernel_slice", "path": repo_rel(slice_path)},
            {"kind": "expected_outcomes", "path": repo_rel(profiles_path)},
            {"kind": "corpus_dir", "path": repo_rel(DATA_DIR / "lean4_tests")},
            {
                "kind": "exit_status_artifact_schema",
                "path": repo_rel(EXIT_STATUS_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "diagnostic_artifact_schema",
                "path": repo_rel(DIAGNOSTIC_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "lean4_vs_clean_run_schema",
                "path": repo_rel(LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "kernel_artifact_schema",
                "path": repo_rel(KERNEL_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "macro_artifact_schema",
                "path": repo_rel(MACRO_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "syntax_quotation_artifact_schema",
                "path": repo_rel(SYNTAX_QUOTATION_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "namespace_open_scoping_artifact_schema",
                "path": repo_rel(NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "module_import_artifact_schema",
                "path": repo_rel(MODULE_IMPORT_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "level_typeclass_artifact_schema",
                "path": repo_rel(LEVEL_TYPECLASS_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "deriving_attribute_instance_artifact_schema",
                "path": repo_rel(DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "structure_inductive_recursor_artifact_schema",
                "path": repo_rel(STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_PATH),
            },
            {
                "kind": "expected_exit_status_artifacts",
                "path_template": EXIT_STATUS_ARTIFACT_PATH_TEMPLATE,
                "schema_version": EXIT_STATUS_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_diagnostic_artifacts",
                "path_template": DIAGNOSTIC_ARTIFACT_PATH_TEMPLATE,
                "schema_version": DIAGNOSTIC_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_lean4_vs_clean_run_evidence",
                "path_template": LEAN4_VS_clean_RUN_ARTIFACT_PATH_TEMPLATE,
                "schema_version": LEAN4_VS_clean_RUN_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_kernel_artifacts",
                "path_template": KERNEL_ARTIFACT_PATH_TEMPLATE,
                "schema_version": KERNEL_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_macro_artifacts",
                "path_template": MACRO_ARTIFACT_PATH_TEMPLATE,
                "schema_version": MACRO_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_syntax_quotation_artifacts",
                "path_template": SYNTAX_QUOTATION_ARTIFACT_PATH_TEMPLATE,
                "schema_version": SYNTAX_QUOTATION_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_namespace_open_scoping_artifacts",
                "path_template": NAMESPACE_OPEN_SCOPING_ARTIFACT_PATH_TEMPLATE,
                "schema_version": NAMESPACE_OPEN_SCOPING_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_module_import_artifacts",
                "path_template": MODULE_IMPORT_ARTIFACT_PATH_TEMPLATE,
                "schema_version": MODULE_IMPORT_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_level_typeclass_artifacts",
                "path_template": LEVEL_TYPECLASS_ARTIFACT_PATH_TEMPLATE,
                "schema_version": LEVEL_TYPECLASS_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_deriving_attribute_instance_artifacts",
                "path_template": DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_PATH_TEMPLATE,
                "schema_version": DERIVING_ATTRIBUTE_INSTANCE_ARTIFACT_SCHEMA_VERSION,
            },
            {
                "kind": "expected_structure_inductive_recursor_artifacts",
                "path_template": STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_PATH_TEMPLATE,
                "schema_version": STRUCTURE_INDUCTIVE_RECURSOR_ARTIFACT_SCHEMA_VERSION,
            },
        ],
        "summary": summary,
        "files": files,
    }


def normalized_json(value: object) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="output path, or '-' for stdout",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the output path does not already match generated content",
    )
    args = parser.parse_args()

    generated = normalized_json(generate())
    if str(args.output) == "-":
        sys.stdout.write(generated)
        return 0

    output_path = args.output if args.output.is_absolute() else REPO_ROOT / args.output
    if args.check:
        existing = output_path.read_text() if output_path.exists() else ""
        if existing != generated:
            print(
                f"{repo_rel(output_path)} is stale; rerun {repo_rel(Path(__file__).resolve())}",
                file=sys.stderr,
            )
            return 1
        print(f"{repo_rel(output_path)} is up to date")
        return 0

    output_path.write_text(generated)
    print(f"Generated {repo_rel(output_path)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
