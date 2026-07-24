# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Validate clean research program lock files.

The validator is intentionally lightweight and standard-library-only so it can
run in local workspaces, CI, and issue-triage scripts without installing a JSON
Schema engine. It checks the clean-owned lock shape, component entries,
artifact schema declarations, and optionally compares local git checkouts
against locked component revisions.

Examples:
    python3 scripts/research_lock.py --lock data/research_program_lock.json
    python3 scripts/research_lock.py --lock data/research_program_lock.json --json
    python3 scripts/research_lock.py --lock data/research_program_lock.json --check-local
    python3 scripts/research_lock.py --self-check
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

EXPECTED_SCHEMA_VERSION = 1
EXPECTED_MANIFEST_KIND = "research_program_lock"
DEFAULT_LOCK_PATH = Path("data/research_program_lock.json")
DEFAULT_COMPONENT_KINDS = {
    "artifact_release",
    "git_dependency",
    "git_repository",
    "json_schema",
}
GIT_COMPONENT_KINDS = {"git_repository", "git_dependency"}
SHA256_HEX_RE = re.compile(r"^[0-9a-fA-F]{64}$")
SHA256_CONTENT_ADDRESS_RE = re.compile(r"^sha256:[0-9a-fA-F]{64}$")
FULL_GIT_REVISION_RE = re.compile(r"^(?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})$")
DRAFT_SHA256_PLACEHOLDER = "replace-with-sha256-before-publication"
DEFAULT_ARTIFACT_REGISTRY_SCHEMA_ID = "clean.artifact_registry.v1"
ARTIFACT_LOCATOR_FIELDS = ("path", "uri", "url", "reference", "external_ref")


@dataclass(frozen=True)
class Finding:
    """A structural error or non-blocking warning."""

    severity: str
    path: str
    message: str

    def as_dict(self) -> dict[str, str]:
        return {
            "severity": self.severity,
            "path": self.path,
            "message": self.message,
        }


@dataclass
class ValidationResult:
    """Collected validation findings."""

    lock_path: Path
    errors: list[Finding]
    warnings: list[Finding]

    @property
    def valid(self) -> bool:
        return not self.errors

    def error(self, path: str, message: str) -> None:
        self.errors.append(Finding("error", path, message))

    def warning(self, path: str, message: str) -> None:
        self.warnings.append(Finding("warning", path, message))

    def as_dict(self) -> dict[str, Any]:
        return {
            "lock": str(self.lock_path),
            "valid": self.valid,
            "error_count": len(self.errors),
            "warning_count": len(self.warnings),
            "errors": [finding.as_dict() for finding in self.errors],
            "warnings": [finding.as_dict() for finding in self.warnings],
        }


@dataclass(frozen=True)
class ArtifactSchemaContract:
    """clean artifact contract embedded in the lock file."""

    name: str
    schema_id: str
    schema_version: int
    required_fields: tuple[str, ...]
    trust_fields: tuple[str, ...]
    quality_enum: frozenset[str] | None = None
    artifact_kinds: frozenset[str] | None = None


def load_json(path: Path) -> Any:
    """Load JSON, raising ValueError with stable user-facing text."""

    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise ValueError(f"{path}: file not found") from None
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"{path}: invalid JSON at line {exc.lineno}: {exc.msg}"
        ) from None


def is_nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def is_int_not_bool(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def list_string_field(
    obj: dict[str, Any],
    base: str,
    field: str,
    result: ValidationResult,
    *,
    required: bool,
    item_name: str,
) -> tuple[str, ...] | None:
    """Validate a schema list field containing non-empty strings."""

    if field not in obj:
        if required:
            result.error(f"{base}.{field}", f"{field} must be present")
        return None

    value = obj.get(field)
    if not isinstance(value, list):
        result.error(f"{base}.{field}", f"{field} must be a list")
        return None

    strings: list[str] = []
    valid = True
    for index, item in enumerate(value):
        if not is_nonempty_string(item):
            result.error(
                f"{base}.{field}[{index}]",
                f"{item_name} must be non-empty strings",
            )
            valid = False
        else:
            strings.append(item)

    return tuple(strings) if valid else None


def dotted_json_path(base: str, dotted_path: str) -> str:
    if not dotted_path:
        return base
    return f"{base}.{dotted_path}"


def get_dotted_path(payload: Any, dotted_path: str) -> tuple[bool, Any]:
    current = payload
    for part in dotted_path.split("."):
        if not isinstance(current, dict) or part not in current:
            return False, None
        current = current[part]
    return True, current


def is_sha256_hex(value: str) -> bool:
    return SHA256_HEX_RE.fullmatch(value) is not None


def is_content_address(value: str) -> bool:
    return SHA256_CONTENT_ADDRESS_RE.fullmatch(value) is not None


def is_full_git_revision(value: Any) -> bool:
    return isinstance(value, str) and FULL_GIT_REVISION_RE.fullmatch(value) is not None


def is_null_git_revision(value: Any) -> bool:
    return isinstance(value, str) and bool(value) and set(value) == {"0"}


def digest_looks_placeholder(value: str) -> bool:
    lowered = value.lower()
    return (
        value == DRAFT_SHA256_PLACEHOLDER
        or "replace" in lowered
        or "placeholder" in lowered
        or "pending" in lowered
        or "todo" in lowered
    )


def component_kind_enum(lock: dict[str, Any]) -> set[str]:
    """Extract known component kinds from the embedded lock schema."""

    schema = lock.get("schema")
    if not isinstance(schema, dict):
        return set(DEFAULT_COMPONENT_KINDS)

    defs = schema.get("$defs")
    if not isinstance(defs, dict):
        return set(DEFAULT_COMPONENT_KINDS)

    component = defs.get("component")
    if not isinstance(component, dict):
        return set(DEFAULT_COMPONENT_KINDS)

    properties = component.get("properties")
    if not isinstance(properties, dict):
        return set(DEFAULT_COMPONENT_KINDS)

    kind = properties.get("kind")
    if not isinstance(kind, dict):
        return set(DEFAULT_COMPONENT_KINDS)

    enum = kind.get("enum")
    if not isinstance(enum, list):
        return set(DEFAULT_COMPONENT_KINDS)

    kinds = {item for item in enum if isinstance(item, str) and item}
    return kinds or set(DEFAULT_COMPONENT_KINDS)


def validate_top_level(lock: Any, result: ValidationResult) -> bool:
    """Validate the required top-level lock shape."""

    if not isinstance(lock, dict):
        result.error("$", "lock must be a JSON object")
        return False

    if lock.get("schema_version") != EXPECTED_SCHEMA_VERSION:
        result.error("$.schema_version", "schema_version must be 1")

    if lock.get("manifest_kind") != EXPECTED_MANIFEST_KIND:
        result.error(
            "$.manifest_kind",
            "manifest_kind must be 'research_program_lock'",
        )

    for field in ("lock_id", "generated_at"):
        if not is_nonempty_string(lock.get(field)):
            result.error(f"$.{field}", f"{field} must be a non-empty string")

    components = lock.get("components")
    if not isinstance(components, list) or not components:
        result.error("$.components", "components must be a non-empty list")

    artifact_schemas = lock.get("artifact_schemas")
    if not isinstance(artifact_schemas, dict) or not artifact_schemas:
        result.error(
            "$.artifact_schemas",
            "artifact_schemas must be a non-empty object",
        )

    artifact_registry = lock.get("artifact_registry")
    if not isinstance(artifact_registry, dict):
        result.error("$.artifact_registry", "artifact_registry must be an object")

    return True


def validate_components(lock: dict[str, Any], result: ValidationResult) -> None:
    components = lock.get("components")
    if not isinstance(components, list):
        return

    known_kinds = component_kind_enum(lock)
    required_fields = ("id", "kind", "version", "revision", "source")

    for index, component in enumerate(components):
        base = f"$.components[{index}]"
        if not isinstance(component, dict):
            result.error(base, "component must be an object")
            continue

        for field in required_fields:
            if not is_nonempty_string(component.get(field)):
                result.error(f"{base}.{field}", f"{field} must be a non-empty string")

        kind = component.get("kind")
        if isinstance(kind, str) and kind not in known_kinds:
            result.error(
                f"{base}.kind",
                f"unknown component kind '{kind}' (expected one of {sorted(known_kinds)})",
            )
        if kind in GIT_COMPONENT_KINDS:
            revision = component.get("revision")
            if is_nonempty_string(revision) and (
                is_null_git_revision(revision) or not is_full_git_revision(revision)
            ):
                result.error(
                    f"{base}.revision",
                    "revision must be a full non-null 40- or 64-character hexadecimal git revision",
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


def validate_git_producer_revision(
    producer: Any,
    base: str,
    git_component_ids: set[str],
    result: ValidationResult,
) -> None:
    if not isinstance(producer, dict):
        return
    if not repo_matches_git_component(producer.get("repo"), git_component_ids):
        return

    revision = producer.get("revision")
    if not is_nonempty_string(revision):
        return
    if is_null_git_revision(revision) or not is_full_git_revision(revision):
        result.error(
            f"{base}.revision",
            "producer revision must be a full non-null 40- or 64-character hexadecimal git revision",
        )


def validate_git_producer_revisions(
    lock: dict[str, Any],
    result: ValidationResult,
) -> None:
    git_component_ids = lock_git_component_ids(lock)
    if not git_component_ids:
        return

    examples = lock.get("example")
    if isinstance(examples, dict):
        for name, payload in examples.items():
            if not isinstance(payload, dict):
                continue
            validate_git_producer_revision(
                payload.get("producer"),
                f"$.example.{name}.producer",
                git_component_ids,
                result,
            )

    registry = lock.get("artifact_registry")
    entries = registry.get("entries") if isinstance(registry, dict) else None
    if not isinstance(entries, list):
        return
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            continue
        validate_git_producer_revision(
            entry.get("producer"),
            f"$.artifact_registry.entries[{index}].producer",
            git_component_ids,
            result,
        )


def validate_artifact_schemas(
    lock: dict[str, Any],
    result: ValidationResult,
) -> dict[str, ArtifactSchemaContract]:
    artifact_schemas = lock.get("artifact_schemas")
    if not isinstance(artifact_schemas, dict):
        return {}

    contracts: dict[str, ArtifactSchemaContract] = {}
    for name, schema in artifact_schemas.items():
        base = f"$.artifact_schemas.{name}"
        if not isinstance(schema, dict):
            result.error(base, "artifact schema must be an object")
            continue

        schema_id = schema.get("schema_id")
        if not is_nonempty_string(schema_id):
            result.error(f"{base}.schema_id", "schema_id must be a non-empty string")

        schema_version = schema.get("schema_version")
        if not is_int_not_bool(schema_version):
            result.error(f"{base}.schema_version", "schema_version must be an integer")

        required_fields = list_string_field(
            schema,
            base,
            "required_fields",
            result,
            required=True,
            item_name="required field names",
        )
        trust_fields = list_string_field(
            schema,
            base,
            "trust_fields",
            result,
            required=True,
            item_name="trust field names",
        )
        quality_enum = list_string_field(
            schema,
            base,
            "quality_enum",
            result,
            required=False,
            item_name="quality enum values",
        )
        artifact_kinds = list_string_field(
            schema,
            base,
            "artifact_kinds",
            result,
            required=False,
            item_name="artifact kind enum values",
        )

        if (
            is_nonempty_string(schema_id)
            and is_int_not_bool(schema_version)
            and required_fields is not None
            and trust_fields is not None
        ):
            contracts[name] = ArtifactSchemaContract(
                name=name,
                schema_id=schema_id,
                schema_version=schema_version,
                required_fields=required_fields,
                trust_fields=trust_fields,
                quality_enum=(
                    frozenset(quality_enum) if quality_enum is not None else None
                ),
                artifact_kinds=(
                    frozenset(artifact_kinds) if artifact_kinds is not None else None
                ),
            )

    return contracts


def contract_by_schema_id(
    contracts: dict[str, ArtifactSchemaContract],
    schema_id: str,
    schema_version: Any,
) -> ArtifactSchemaContract | None:
    for contract in contracts.values():
        if contract.schema_id != schema_id:
            continue
        if schema_version is None or contract.schema_version == schema_version:
            return contract
    return None


def resolve_contract(
    contracts: dict[str, ArtifactSchemaContract],
    payload: Any,
    *,
    schema_hint: str | None,
) -> ArtifactSchemaContract | None:
    if isinstance(schema_hint, str) and schema_hint in contracts:
        return contracts[schema_hint]

    if isinstance(payload, dict):
        for field in ("schema_name", "schema_key", "artifact_schema", "schema_ref"):
            value = payload.get(field)
            if isinstance(value, str) and value in contracts:
                return contracts[value]

        schema_version = payload.get("schema_version")
        if not is_int_not_bool(schema_version):
            schema_version = None

        for field in ("schema_id", "artifact_schema_id"):
            schema_id = payload.get(field)
            if is_nonempty_string(schema_id):
                contract = contract_by_schema_id(contracts, schema_id, schema_version)
                if contract is not None:
                    return contract

        if isinstance(schema_hint, str) and schema_version is not None:
            candidate = f"{schema_hint}_v{schema_version}"
            if candidate in contracts:
                return contracts[candidate]

    return None


def default_artifact_entry_contract(
    contracts: dict[str, ArtifactSchemaContract],
) -> ArtifactSchemaContract | None:
    artifact_contracts = [
        contract
        for contract in contracts.values()
        if contract.artifact_kinds is not None
    ]
    if len(artifact_contracts) == 1:
        return artifact_contracts[0]
    return None


def validate_producer_metadata(
    producer: Any,
    base: str,
    result: ValidationResult,
    *,
    require_revision: bool = False,
) -> None:
    if not isinstance(producer, dict):
        result.error(base, "producer must be an object")
        return

    if not is_nonempty_string(producer.get("repo")):
        result.error(f"{base}.repo", "producer repo must be a non-empty string")

    if require_revision:
        if not is_nonempty_string(producer.get("revision")):
            result.error(
                f"{base}.revision",
                "producer revision must be a non-empty string",
            )
        return

    if not is_nonempty_string(producer.get("revision")):
        result.error(
            f"{base}.revision",
            "producer revision must be a non-empty string",
        )


def validate_content_address(
    entry: dict[str, Any],
    base: str,
    result: ValidationResult,
    *,
    require_content_address: bool = False,
    allow_draft_placeholders: bool,
) -> None:
    if require_content_address:
        value = entry.get("content_address")
        if "content_address" not in entry:
            result.error(f"{base}.content_address", "content_address must be present")
            return
        if not isinstance(value, dict):
            result.error(f"{base}.content_address", "content_address must be an object")
            return

        algorithm = value.get("algorithm")
        digest = value.get("digest")
        if algorithm != "sha256":
            result.error(
                f"{base}.content_address.algorithm",
                "content_address.algorithm must be sha256",
            )
        if not is_nonempty_string(digest):
            result.error(
                f"{base}.content_address.digest",
                "content_address.digest must be a non-empty string",
            )
        elif digest_looks_placeholder(digest) and not allow_draft_placeholders:
            result.error(
                f"{base}.content_address.digest",
                "content_address.digest must not be a placeholder",
            )
        elif not (
            is_sha256_hex(digest)
            or (allow_draft_placeholders and digest == DRAFT_SHA256_PLACEHOLDER)
        ):
            result.error(
                f"{base}.content_address.digest",
                "content_address.digest must be 64 hexadecimal characters",
            )
        return

    saw_address = False
    valid_address = False

    if "sha256" in entry:
        saw_address = True
        value = entry.get("sha256")
        if not is_nonempty_string(value):
            result.error(f"{base}.sha256", "sha256 must be a non-empty string")
        elif digest_looks_placeholder(value) and not allow_draft_placeholders:
            result.error(f"{base}.sha256", "sha256 must not be a placeholder")
        elif is_sha256_hex(value):
            valid_address = True
        elif allow_draft_placeholders and value == DRAFT_SHA256_PLACEHOLDER:
            valid_address = True
        else:
            result.error(f"{base}.sha256", "sha256 must be 64 hexadecimal characters")

    for field in ("content_address", "digest"):
        if field not in entry:
            continue
        saw_address = True
        value = entry.get(field)
        if field == "content_address" and isinstance(value, dict):
            algorithm = value.get("algorithm")
            digest = value.get("digest")
            if algorithm != "sha256":
                result.error(
                    f"{base}.{field}.algorithm",
                    "content_address.algorithm must be sha256",
                )
            if not is_nonempty_string(digest):
                result.error(
                    f"{base}.{field}.digest",
                    "content_address.digest must be a non-empty string",
                )
            elif digest_looks_placeholder(digest) and not allow_draft_placeholders:
                result.error(
                    f"{base}.{field}.digest",
                    "content_address.digest must not be a placeholder",
                )
            elif is_sha256_hex(digest):
                valid_address = True
            elif allow_draft_placeholders and digest == DRAFT_SHA256_PLACEHOLDER:
                valid_address = True
            else:
                result.error(
                    f"{base}.{field}.digest",
                    "content_address.digest must be 64 hexadecimal characters",
                )
        elif not is_nonempty_string(value):
            result.error(f"{base}.{field}", f"{field} must be a non-empty string")
        elif digest_looks_placeholder(value) and not allow_draft_placeholders:
            result.error(f"{base}.{field}", f"{field} must not be a placeholder")
        elif is_content_address(value):
            valid_address = True
        elif field == "digest" and is_sha256_hex(value):
            valid_address = True
        else:
            result.error(
                f"{base}.{field}",
                f"{field} must use the form 'sha256:<64 hex chars>' or a 64-character SHA-256 hex digest",
            )

    if not saw_address:
        result.error(
            f"{base}.sha256",
            "artifact registry entry must include sha256, content_address, or digest",
        )
    elif not valid_address:
        return


def validate_artifact_locator(
    entry: dict[str, Any],
    base: str,
    result: ValidationResult,
) -> None:
    storage = entry.get("storage")
    if isinstance(storage, dict):
        storage_type = storage.get("type")
        if storage_type not in {"git_path", "external_uri"}:
            result.error(
                f"{base}.storage.type",
                "storage.type must be git_path or external_uri",
            )
            return
        if storage_type == "git_path":
            if not is_nonempty_string(storage.get("path")):
                result.error(f"{base}.storage.path", "git_path storage requires a path")
            return
        if not any(
            is_nonempty_string(storage.get(field))
            for field in ("uri", "url", "reference", "external_ref")
        ):
            result.error(
                f"{base}.storage",
                "external_uri storage requires uri, url, reference, or external_ref",
            )
        return
    if "storage" in entry:
        result.error(f"{base}.storage", "storage must be an object")
        return

    locator_fields = [field for field in ARTIFACT_LOCATOR_FIELDS if field in entry]
    if not locator_fields:
        result.error(
            f"{base}.path",
            "artifact registry entry must include path, uri, url, reference, or external_ref",
        )
        return

    for field in locator_fields:
        if not is_nonempty_string(entry.get(field)):
            result.error(f"{base}.{field}", f"{field} must be a non-empty string")


def validate_artifact_links(
    entry: dict[str, Any],
    base: str,
    result: ValidationResult,
    *,
    require_links: bool,
) -> None:
    links = entry.get("links")
    if links is None:
        if require_links:
            result.error(f"{base}.links", "links metadata must be present")
        return
    if not isinstance(links, dict):
        result.error(f"{base}.links", "links must be an object")
        return

    if not is_nonempty_string(links.get("dashboard_anchor")):
        result.error(
            f"{base}.links.dashboard_anchor",
            "links.dashboard_anchor must be a non-empty string",
        )

    issues = links.get("issues")
    if issues is not None:
        if not isinstance(issues, list):
            result.error(f"{base}.links.issues", "links.issues must be a list")
            return
        for index, issue in enumerate(issues):
            if not is_int_not_bool(issue) or issue <= 0:
                result.error(
                    f"{base}.links.issues[{index}]",
                    "links.issues entries must be positive integers",
                )


def entry_sha256_digest(entry: dict[str, Any]) -> str | None:
    value = entry.get("sha256")
    if isinstance(value, str) and is_sha256_hex(value):
        return value.lower()

    value = entry.get("digest")
    if isinstance(value, str):
        if is_sha256_hex(value):
            return value.lower()
        if is_content_address(value):
            return value.split(":", 1)[1].lower()

    value = entry.get("content_address")
    if isinstance(value, str) and is_content_address(value):
        return value.split(":", 1)[1].lower()
    if isinstance(value, dict):
        digest = value.get("digest")
        if isinstance(digest, str) and is_sha256_hex(digest):
            return digest.lower()
    return None


def entry_git_path(entry: dict[str, Any]) -> str | None:
    storage = entry.get("storage")
    if isinstance(storage, dict) and storage.get("type") == "git_path":
        path = storage.get("path")
        return path if is_nonempty_string(path) else None
    path = entry.get("path")
    return path if is_nonempty_string(path) else None


def resolve_artifact_path(raw_path: str, lock_path: Path) -> Path:
    path = Path(raw_path).expanduser()
    if path.is_absolute():
        return path
    cwd_path = Path.cwd() / path
    if cwd_path.exists():
        return cwd_path
    return lock_path.parent / path


def sha256_file(path: Path) -> tuple[str | None, str | None]:
    if not path.exists():
        return None, f"artifact path does not exist: {path}"
    if not path.is_file():
        return None, f"artifact path is not a file: {path}"

    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as exc:
        return None, f"could not hash artifact: {exc}"
    return digest.hexdigest(), None


def validate_local_artifact_hash(
    entry: dict[str, Any],
    base: str,
    result: ValidationResult,
) -> None:
    raw_path = entry_git_path(entry)
    digest = entry_sha256_digest(entry)
    if raw_path is None or digest is None:
        return

    actual, error = sha256_file(resolve_artifact_path(raw_path, result.lock_path))
    if error is not None:
        result.error(f"{base}.storage.path", error)
    elif actual != digest:
        result.error(
            f"{base}.content_address",
            f"SHA-256 mismatch for {raw_path}: expected {digest}, got {actual}",
        )


def validate_artifact_kind(
    entry: dict[str, Any],
    base: str,
    result: ValidationResult,
    contract: ArtifactSchemaContract | None,
) -> None:
    kind = entry.get("kind")
    known_kinds = contract.artifact_kinds if contract is not None else None

    if known_kinds is not None:
        if not is_nonempty_string(kind):
            result.error(f"{base}.kind", "kind must be a non-empty string")
        elif kind not in known_kinds:
            result.error(
                f"{base}.kind",
                f"unknown artifact kind '{kind}' (expected one of {sorted(known_kinds)})",
            )
    elif "kind" in entry and not is_nonempty_string(kind):
        result.error(f"{base}.kind", "kind must be a non-empty string")


def validate_artifact_registry_entry(
    entry: Any,
    base: str,
    result: ValidationResult,
    *,
    contract: ArtifactSchemaContract | None,
    known_schema_names: set[str] | None = None,
    inherited_artifact_id: Any = None,
    inherited_producer: Any = None,
    inferred_artifact_id: str | None = None,
    require_entry_artifact_id: bool,
    require_registry_fields: bool = False,
    allow_draft_placeholders: bool,
) -> None:
    if not isinstance(entry, dict):
        result.error(base, "artifact registry entry must be an object")
        return

    artifact_id = entry.get("artifact_id", inherited_artifact_id)
    if artifact_id is None and inferred_artifact_id is not None:
        artifact_id = inferred_artifact_id

    if require_entry_artifact_id and not is_nonempty_string(artifact_id):
        result.error(f"{base}.artifact_id", "artifact_id must be a non-empty string")
    elif "artifact_id" in entry and not is_nonempty_string(entry.get("artifact_id")):
        result.error(f"{base}.artifact_id", "artifact_id must be a non-empty string")

    schema_ref = entry.get("schema_ref")
    if require_registry_fields and not is_nonempty_string(schema_ref):
        result.error(f"{base}.schema_ref", "schema_ref must be a non-empty string")
    elif (
        is_nonempty_string(schema_ref)
        and known_schema_names is not None
        and known_schema_names
        and schema_ref not in known_schema_names
    ):
        result.error(
            f"{base}.schema_ref", f"unknown artifact schema ref '{schema_ref}'"
        )

    if "producer" in entry:
        validate_producer_metadata(
            entry.get("producer"),
            f"{base}.producer",
            result,
            require_revision=require_registry_fields,
        )
    elif inherited_producer is None:
        result.error(f"{base}.producer", "producer metadata must be present")

    if require_registry_fields and "storage" not in entry:
        result.error(f"{base}.storage", "storage metadata must be present")

    validate_content_address(
        entry,
        base,
        result,
        require_content_address=require_registry_fields,
        allow_draft_placeholders=allow_draft_placeholders,
    )
    validate_artifact_locator(entry, base, result)
    validate_artifact_links(
        entry,
        base,
        result,
        require_links=require_registry_fields,
    )
    validate_local_artifact_hash(entry, base, result)
    validate_artifact_kind(entry, base, result, contract)


def validate_artifact_entries(
    manifest: dict[str, Any],
    base: str,
    result: ValidationResult,
    *,
    contract: ArtifactSchemaContract | None,
    allow_draft_placeholders: bool,
) -> None:
    if "artifacts" not in manifest:
        return

    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, list):
        result.error(f"{base}.artifacts", "artifacts must be a list")
        return

    for index, entry in enumerate(artifacts):
        validate_artifact_registry_entry(
            entry,
            f"{base}.artifacts[{index}]",
            result,
            contract=contract,
            known_schema_names=None,
            inherited_artifact_id=manifest.get("artifact_id"),
            inherited_producer=manifest.get("producer"),
            require_entry_artifact_id=False,
            require_registry_fields=False,
            allow_draft_placeholders=allow_draft_placeholders,
        )


def validate_artifact_payload_against_contract(
    payload: Any,
    base: str,
    result: ValidationResult,
    *,
    contract: ArtifactSchemaContract,
    allow_draft_placeholders: bool,
) -> None:
    if not isinstance(payload, dict):
        result.error(base, "artifact payload must be an object")
        return

    for field in contract.required_fields:
        present, _ = get_dotted_path(payload, field)
        if not present:
            result.error(
                dotted_json_path(base, field),
                f"required field '{field}' declared by {contract.name} is missing",
            )

    for field in contract.trust_fields:
        present, _ = get_dotted_path(payload, field)
        if not present:
            result.error(
                dotted_json_path(base, field),
                f"trust field '{field}' declared by {contract.name} is missing",
            )

    present, schema_version = get_dotted_path(payload, "schema_version")
    if present:
        if not is_int_not_bool(schema_version):
            result.error(f"{base}.schema_version", "schema_version must be an integer")
        elif schema_version != contract.schema_version:
            result.error(
                f"{base}.schema_version",
                f"schema_version must match {contract.name} ({contract.schema_version})",
            )

    for field in ("schema_id", "artifact_schema_id"):
        present, schema_id = get_dotted_path(payload, field)
        if present and schema_id != contract.schema_id:
            result.error(
                dotted_json_path(base, field),
                f"{field} must match {contract.schema_id}",
            )

    present, producer = get_dotted_path(payload, "producer")
    if present:
        validate_producer_metadata(producer, f"{base}.producer", result)

    if contract.quality_enum is not None:
        present, quality = get_dotted_path(payload, "proof.quality")
        if not present:
            result.error(
                f"{base}.proof.quality",
                "proof.quality must be present when quality_enum is declared",
            )
        elif not is_nonempty_string(quality):
            result.error(
                f"{base}.proof.quality", "proof.quality must be a non-empty string"
            )
        elif quality not in contract.quality_enum:
            result.error(
                f"{base}.proof.quality",
                f"unknown proof quality '{quality}' (expected one of {sorted(contract.quality_enum)})",
            )

    validate_artifact_entries(
        payload,
        base,
        result,
        contract=contract,
        allow_draft_placeholders=allow_draft_placeholders,
    )


def validate_examples(
    lock: dict[str, Any],
    contracts: dict[str, ArtifactSchemaContract],
    result: ValidationResult,
) -> None:
    examples = lock.get("example")
    if examples is None:
        return
    if not isinstance(examples, dict):
        result.error("$.example", "example must be an object")
        return

    allow_draft_placeholders = lock.get("status") == "scaffold"
    for name, payload in examples.items():
        base = f"$.example.{name}"
        contract = resolve_contract(contracts, payload, schema_hint=name)
        if contract is None:
            result.error(base, "no matching artifact schema contract found for example")
            continue

        validate_artifact_payload_against_contract(
            payload,
            base,
            result,
            contract=contract,
            allow_draft_placeholders=allow_draft_placeholders,
        )


def registry_entries(
    registry: Any,
    base: str,
    result: ValidationResult,
) -> list[tuple[Any, str, str | None, str | None]]:
    if isinstance(registry, list):
        return [
            (entry, f"{base}[{index}]", None, None)
            for index, entry in enumerate(registry)
        ]

    if not isinstance(registry, dict):
        result.error(base, "artifact_registry must be an object or list")
        return []

    if "entries" in registry:
        entries = registry.get("entries")
        if not isinstance(entries, list):
            result.error(f"{base}.entries", "artifact_registry.entries must be a list")
            return []
        return [
            (entry, f"{base}.entries[{index}]", None, None)
            for index, entry in enumerate(entries)
        ]

    collected: list[tuple[Any, str, str | None, str | None]] = []
    for key, value in registry.items():
        path = f"{base}.{key}"
        if isinstance(value, list):
            for index, entry in enumerate(value):
                collected.append((entry, f"{path}[{index}]", key, None))
        else:
            collected.append((value, path, None, key))
    return collected


def validate_artifact_registry(
    lock: dict[str, Any],
    contracts: dict[str, ArtifactSchemaContract],
    result: ValidationResult,
) -> None:
    registry = lock.get("artifact_registry")
    if registry is None:
        return
    if not isinstance(registry, dict):
        return
    if isinstance(registry, dict):
        schema_id = registry.get("schema_id")
        if schema_id != DEFAULT_ARTIFACT_REGISTRY_SCHEMA_ID:
            result.error(
                "$.artifact_registry.schema_id",
                f"schema_id must be {DEFAULT_ARTIFACT_REGISTRY_SCHEMA_ID}",
            )
        schema_version = registry.get("schema_version")
        if schema_version != 1:
            result.error(
                "$.artifact_registry.schema_version",
                "schema_version must be 1",
            )
        if "entries" not in registry:
            result.error("$.artifact_registry.entries", "entries must be present")
            return

    allow_draft_placeholders = lock.get("status") == "scaffold"
    default_contract = default_artifact_entry_contract(contracts)
    artifact_schemas = lock.get("artifact_schemas")
    known_schema_names = (
        set(artifact_schemas) if isinstance(artifact_schemas, dict) else set()
    )
    seen_artifact_ids: set[str] = set()
    for entry, path, schema_hint, inferred_artifact_id in registry_entries(
        registry,
        "$.artifact_registry",
        result,
    ):
        artifact_id = None
        if isinstance(entry, dict):
            artifact_id = entry.get("artifact_id", inferred_artifact_id)
        elif inferred_artifact_id is not None:
            artifact_id = inferred_artifact_id
        if is_nonempty_string(artifact_id):
            if artifact_id in seen_artifact_ids:
                result.error(path, f"duplicate artifact_id '{artifact_id}'")
            else:
                seen_artifact_ids.add(artifact_id)
        contract = resolve_contract(contracts, entry, schema_hint=schema_hint)
        if contract is None:
            contract = default_contract
        validate_artifact_registry_entry(
            entry,
            path,
            result,
            contract=contract,
            known_schema_names=known_schema_names,
            inferred_artifact_id=inferred_artifact_id,
            require_entry_artifact_id=True,
            require_registry_fields=True,
            allow_draft_placeholders=allow_draft_placeholders,
        )


def workspace_path(component: dict[str, Any], lock_path: Path) -> Path | None:
    workspace = component.get("workspace")
    if workspace is None:
        observed_checkout = component.get("observed_checkout")
        if isinstance(observed_checkout, dict):
            workspace = observed_checkout.get("workspace")
    if workspace is None:
        return None
    if not is_nonempty_string(workspace):
        return None

    path = Path(workspace).expanduser()
    if not path.is_absolute():
        path = lock_path.parent / path
    return path


def git_head_revision(workspace: Path) -> tuple[str | None, str | None]:
    """Return `(revision, error_message)` for a workspace git checkout."""

    if not workspace.exists():
        return None, f"workspace path does not exist: {workspace}"
    if not workspace.is_dir():
        return None, f"workspace path is not a directory: {workspace}"

    try:
        proc = subprocess.run(
            ["git", "-C", str(workspace), "rev-parse", "HEAD"],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return None, f"could not inspect git revision: {exc}"

    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        return (
            None,
            f"could not inspect git revision: {detail or 'git rev-parse failed'}",
        )

    revision = proc.stdout.strip()
    if not revision:
        return None, "git rev-parse returned an empty revision"
    return revision, None


def check_local_revisions(lock: dict[str, Any], result: ValidationResult) -> None:
    components = lock.get("components")
    if not isinstance(components, list):
        return

    for index, component in enumerate(components):
        base = f"$.components[{index}]"
        if not isinstance(component, dict):
            continue

        workspace = workspace_path(component, result.lock_path)
        if workspace is None:
            continue

        expected = component.get("revision")
        if not is_nonempty_string(expected):
            continue

        actual, error = git_head_revision(workspace)
        if error is not None:
            result.warning(f"{base}.workspace", error)
            continue

        if actual != expected:
            component_id = component.get("id", f"component[{index}]")
            result.warning(
                f"{base}.revision",
                f"local revision mismatch for {component_id}: expected {expected}, got {actual}",
            )


def validate_lock_payload(
    lock: Any,
    lock_path: Path,
    *,
    check_local: bool = False,
) -> ValidationResult:
    """Validate an already-loaded lock payload."""

    result = ValidationResult(lock_path=lock_path, errors=[], warnings=[])
    if not validate_top_level(lock, result):
        return result

    if isinstance(lock, dict):
        validate_components(lock, result)
        contracts = validate_artifact_schemas(lock, result)
        validate_examples(lock, contracts, result)
        validate_artifact_registry(lock, contracts, result)
        validate_git_producer_revisions(lock, result)
        if check_local:
            check_local_revisions(lock, result)

    return result


def validate_lock_file(
    lock_path: Path, *, check_local: bool = False
) -> ValidationResult:
    result = ValidationResult(lock_path=lock_path, errors=[], warnings=[])
    try:
        payload = load_json(lock_path)
    except ValueError as exc:
        result.error("$", str(exc))
        return result
    return validate_lock_payload(payload, lock_path, check_local=check_local)


def render_text(result: ValidationResult) -> str:
    lines = [
        f"research lock: {result.lock_path}",
        f"valid: {str(result.valid).lower()}",
        f"errors: {len(result.errors)}",
        f"warnings: {len(result.warnings)}",
    ]
    lines.extend(
        f"{finding.severity}: {finding.path}: {finding.message}"
        for finding in result.errors + result.warnings
    )
    return "\n".join(lines)


def print_result(result: ValidationResult, *, json_output: bool) -> None:
    if json_output:
        print(json.dumps(result.as_dict(), indent=2, sort_keys=True))
    else:
        print(render_text(result))


def self_check_payload() -> dict[str, Any]:
    return {
        "schema_version": 1,
        "manifest_kind": "research_program_lock",
        "lock_id": "self-check-lock",
        "generated_at": "2026-04-23T00:00:00Z",
        "status": "scaffold",
        "schema": {
            "$defs": {
                "component": {
                    "properties": {
                        "kind": {
                            "enum": [
                                "git_repository",
                                "git_dependency",
                                "artifact_release",
                                "json_schema",
                            ]
                        }
                    }
                }
            }
        },
        "components": [
            {
                "id": "clean",
                "kind": "git_repository",
                "version": "self-check",
                "revision": "1111111111111111111111111111111111111111",
                "source": "local:self-check",
            }
        ],
        "artifact_schemas": {
            "proof_artifact_manifest_v1": {
                "schema_id": "clean.proof_artifact_manifest.v1",
                "schema_version": 1,
                "required_fields": [
                    "schema_version",
                    "artifact_id",
                    "lock_id",
                    "producer",
                    "proof",
                    "artifacts",
                ],
                "trust_fields": [
                    "proof.quality",
                    "proof.kernel_checked",
                    "proof.sorry_count",
                    "proof.trusted_ay_count",
                    "proof.axiom_closure",
                    "proof.external_certificates",
                ],
                "quality_enum": ["constructive", "unchecked"],
                "artifact_kinds": ["source_manifest"],
            }
        },
        "example": {
            "proof_artifact_manifest": {
                "schema_version": 1,
                "artifact_id": "self-check-artifact",
                "lock_id": "self-check-lock",
                "producer": {
                    "repo": "clean",
                    "revision": "1111111111111111111111111111111111111111",
                },
                "proof": {
                    "quality": "constructive",
                    "kernel_checked": True,
                    "sorry_count": 0,
                    "trusted_ay_count": 0,
                    "axiom_closure": [],
                    "external_certificates": [],
                },
                "artifacts": [
                    {
                        "kind": "source_manifest",
                        "uri": "artifact://self-check/source-manifest",
                        "sha256": (
                            "0000000000000000000000000000000000000000000000000000000000000000"
                        ),
                    }
                ],
            }
        },
        "artifact_registry": {
            "schema_id": "clean.artifact_registry.v1",
            "schema_version": 1,
            "entries": [
                {
                    "artifact_id": "self-check-artifact",
                    "kind": "source_manifest",
                    "schema_ref": "proof_artifact_manifest_v1",
                    "content_address": {
                        "algorithm": "sha256",
                        "digest": "0000000000000000000000000000000000000000000000000000000000000000",
                    },
                    "producer": {
                        "repo": "clean",
                        "revision": "1111111111111111111111111111111111111111",
                    },
                    "storage": {
                        "type": "external_uri",
                        "uri": "artifact://self-check/source-manifest",
                    },
                    "links": {
                        "issues": [3690],
                        "dashboard_anchor": "artifact:self-check-artifact",
                    },
                }
            ],
        },
    }


def run_self_check(json_output: bool) -> int:
    with tempfile.TemporaryDirectory() as td:
        lock_path = Path(td) / "research_program_lock.json"
        result = validate_lock_payload(self_check_payload(), lock_path)

    if json_output:
        print(json.dumps(result.as_dict(), indent=2, sort_keys=True))
    elif result.valid:
        print("research_lock self-check: ok")
    else:
        print(render_text(result), file=sys.stderr)

    return 0 if result.valid else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lock",
        type=Path,
        default=DEFAULT_LOCK_PATH,
        help=f"Path to research lock JSON (default: {DEFAULT_LOCK_PATH})",
    )
    parser.add_argument(
        "--json", action="store_true", help="Emit machine-readable JSON"
    )
    parser.add_argument(
        "--check-local",
        action="store_true",
        help="Warn when workspace checkouts do not match locked revisions",
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="Run an internal validator self-check and exit",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    if args.self_check:
        return run_self_check(args.json)

    result = validate_lock_file(args.lock, check_local=args.check_local)
    print_result(result, json_output=args.json)
    return 0 if result.valid else 1


if __name__ == "__main__":
    raise SystemExit(main())
