#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Dry-run and validation helper for tactic generated-count artifacts.

This helper intentionally does not run Lean 4 or Lean 5. In dry-run mode it
parses a generated-count corpus and emits the complete runner-artifact JSON
shape with fail-closed status. In check mode it validates a real artifact
against the registry contract, selected manifest, and source corpus checksum.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:  # Prefer PyYAML when it is provisioned.
    import yaml  # type: ignore[import-untyped]

    _YAML_PARSE_ERRORS: tuple[type[BaseException], ...] = (yaml.YAMLError,)
except ModuleNotFoundError:  # pragma: no cover - exercised only without PyYAML
    # The Rust guard
    # `crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs` shells out
    # to this runner via `python3 ... --dry-run` and asserts the process
    # succeeds. PyYAML is not always provisioned in that test environment, so we
    # fall back to a dependency-free loader for the constrained, committed YAML
    # subset used by the tactic-parity registry and count corpora. This keeps
    # the runner fail-closed and environment-independent without weakening any
    # contract; PyYAML stays the preferred path above.
    yaml = None  # type: ignore[assignment]
    _YAML_PARSE_ERRORS = ()

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_REGISTRY = REPO_ROOT / "evals" / "registry" / "tactic-parity.yaml"
CONTRACT_VERSION = "clean-tactic-generated-count-runner-artifact-v1"
CONTRACT_SCHEMA_VERSION = "clean-tactic-generated-count-runner-contract-schema-v1"
SOURCE_CORPUS_VERSION = "clean-tactic-generated-count-source-corpus-v1"
FAIL_CLOSED_STATUS = "fail-closed-missing-lean4-runner-artifact"
DRY_RUN_RUN_ID = "dry-run-no-lean4-runner"
RUNNER_REPO_PATH = "scripts/tactic_parity/generated_count_runner.py"
REQUIRED_ARTIFACT_FIELDS = [
    "schema_version",
    "tactic_lane",
    "run_id",
    "cases_total",
    "lean4_successes",
    "clean_successes",
    "matched_successes",
    "source_corpus_path",
    "source_corpus_sha256",
    "runner_path",
    "runner_command",
]
FORBIDDEN_ARTIFACT_FIELDS = {
    "engine": "generated-count artifacts must compare Lean4 and clean counts",
    "tactic": "use tactic_lane to bind evidence to a generated-count manifest",
}


@dataclass(frozen=True)
class LaneManifest:
    tactic_lane: str
    source_corpus_path: str
    runner_path: str
    runner_command: str
    runner_artifact_contract: str
    missing_runner_status: str


@dataclass(frozen=True)
class SourceCorpus:
    tactic_lane: str
    path: Path
    repo_path: str
    sha256: str
    case_ids: list[str]

    @property
    def cases_total(self) -> int:
        return len(self.case_ids)


def repo_rel(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


_BLOCK_SCALAR_INDICATORS = {">", ">-", ">+", "|", "|-", "|+"}


def _strip_lines(text: str) -> list[tuple[int, str]]:
    """Return (indent, content) for each significant line, dropping blanks and
    whole-line ``#`` comments. Inline ``#`` is intentionally not stripped so
    quoted scalars such as ``"#3701"`` survive."""
    nodes: list[tuple[int, str]] = []
    for raw in text.splitlines():
        without_indent = raw.lstrip(" ")
        content = without_indent.rstrip()
        if not content or content.startswith("#"):
            continue
        nodes.append((len(raw) - len(without_indent), content))
    return nodes


def _split_key(content: str) -> tuple[str, str]:
    if content.endswith(":"):
        return content[:-1].strip(), ""
    marker = content.find(": ")
    if marker == -1:
        return content.strip(), ""
    return content[:marker].strip(), content[marker + 2 :].strip()


def _parse_scalar(token: str) -> Any:
    token = token.strip()
    if len(token) >= 2 and token[0] == token[-1] and token[0] in "\"'":
        return token[1:-1]
    if token in ("true", "True"):
        return True
    if token in ("false", "False"):
        return False
    if token in ("null", "~", ""):
        return None
    if token.lstrip("-").isdigit():
        return int(token)
    return token


def _looks_like_mapping(content: str) -> bool:
    return content.endswith(":") or ": " in content


def _consume_block_scalar(
    nodes: list[tuple[int, str]], index: int, parent_indent: int
) -> tuple[str, int]:
    parts: list[str] = []
    while index < len(nodes) and nodes[index][0] > parent_indent:
        parts.append(nodes[index][1])
        index += 1
    return " ".join(parts), index


def _parse_node(nodes: list[tuple[int, str]], index: int) -> tuple[Any, int]:
    if nodes[index][1].startswith("- ") or nodes[index][1] == "-":
        return _parse_sequence(nodes, index, nodes[index][0])
    return _parse_mapping(nodes, index, nodes[index][0])


def _parse_mapping(
    nodes: list[tuple[int, str]], index: int, indent: int
) -> tuple[dict[str, Any], int]:
    result: dict[str, Any] = {}
    while (
        index < len(nodes)
        and nodes[index][0] == indent
        and not (nodes[index][1].startswith("- ") or nodes[index][1] == "-")
    ):
        key, rest = _split_key(nodes[index][1])
        index += 1
        if rest in _BLOCK_SCALAR_INDICATORS:
            value, index = _consume_block_scalar(nodes, index, indent)
        elif rest == "":
            if index < len(nodes) and nodes[index][0] > indent:
                value, index = _parse_node(nodes, index)
            else:
                value = None
        else:
            value = _parse_scalar(rest)
        result[key] = value
    return result, index


def _parse_sequence(
    nodes: list[tuple[int, str]], index: int, indent: int
) -> tuple[list[Any], int]:
    items: list[Any] = []
    while (
        index < len(nodes)
        and nodes[index][0] == indent
        and (nodes[index][1].startswith("- ") or nodes[index][1] == "-")
    ):
        content = nodes[index][1]
        inline = "" if content == "-" else content[2:]
        inline_indent = indent + (len(content) - len(inline))
        sub: list[tuple[int, str]] = []
        if inline:
            sub.append((inline_indent, inline))
        index += 1
        while index < len(nodes) and nodes[index][0] > indent:
            sub.append(nodes[index])
            index += 1
        if not sub:
            items.append(None)
        elif len(sub) == 1 and not _looks_like_mapping(sub[0][1]):
            items.append(_parse_scalar(sub[0][1]))
        else:
            value, _ = _parse_node(sub, 0)
            items.append(value)
    return items, index


def _minimal_yaml_load(text: str) -> Any:
    """Parse the constrained YAML subset used by the committed tactic-parity
    registry and count corpora when PyYAML is unavailable. Supports block
    mappings, block sequences, plain/quoted scalars, folded block scalars,
    booleans, integers, and whole-line comments."""
    nodes = _strip_lines(text)
    if not nodes:
        return None
    value, _ = _parse_node(nodes, 0)
    return value


def load_yaml(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    if yaml is not None:
        payload = yaml.safe_load(text)
    else:
        payload = _minimal_yaml_load(text)
    if not isinstance(payload, dict):
        raise ValueError(f"{repo_rel(path)} must contain a YAML object")
    return payload


def load_lane_manifest(registry_path: Path, tactic_lane: str) -> LaneManifest:
    registry = load_yaml(registry_path)
    inputs = registry.get("inputs")
    if not isinstance(inputs, dict):
        raise ValueError("tactic parity registry is missing inputs")

    contract = inputs.get("generated_count_runner_artifact_contract")
    if not isinstance(contract, dict):
        raise ValueError("registry is missing generated_count_runner_artifact_contract")
    if contract.get("version") != CONTRACT_VERSION:
        raise ValueError("generated-count runner artifact contract version mismatch")
    if contract.get("missing_or_mismatched_artifact_status") != FAIL_CLOSED_STATUS:
        raise ValueError("generated-count runner artifact contract must fail closed")

    manifests = inputs.get("generated_count_manifests")
    if not isinstance(manifests, list):
        raise ValueError("registry is missing generated_count_manifests")

    for raw_manifest in manifests:
        if not isinstance(raw_manifest, dict):
            raise ValueError("generated_count_manifests entries must be YAML objects")
        if raw_manifest.get("tactic_lane") != tactic_lane:
            continue
        if raw_manifest.get("generated") is not False:
            raise ValueError(f"{tactic_lane} manifest must remain generated: false")
        runner_path = require_str(
            raw_manifest, "runner_path", f"{tactic_lane} manifest"
        )
        runner_command = require_str(
            raw_manifest, "runner_command", f"{tactic_lane} manifest"
        )
        if runner_path != RUNNER_REPO_PATH:
            raise ValueError(
                f"{tactic_lane} manifest runner_path must be {RUNNER_REPO_PATH!r}"
            )
        expected_command = f"python3 {runner_path} --lane {tactic_lane} --dry-run"
        if runner_command != expected_command:
            raise ValueError(
                f"{tactic_lane} manifest runner_command must be {expected_command!r}"
            )
        if not (REPO_ROOT / runner_path).is_file():
            raise ValueError(
                f"{tactic_lane} manifest runner_path does not exist: {runner_path}"
            )
        return LaneManifest(
            tactic_lane=tactic_lane,
            source_corpus_path=require_str(
                raw_manifest, "source_corpus_path", f"{tactic_lane} manifest"
            ),
            runner_path=runner_path,
            runner_command=runner_command,
            runner_artifact_contract=require_str(
                raw_manifest, "runner_artifact_contract", f"{tactic_lane} manifest"
            ),
            missing_runner_status=require_str(
                raw_manifest, "missing_runner_status", f"{tactic_lane} manifest"
            ),
        )

    raise ValueError(f"generated-count manifest is missing tactic lane {tactic_lane!r}")


def require_str(payload: dict[str, Any], field: str, context: str) -> str:
    value = payload.get(field)
    if not isinstance(value, str) or not value:
        raise ValueError(f"{context} must define non-empty string field {field!r}")
    return value


def require_int(payload: dict[str, Any], field: str, context: str) -> int:
    value = payload.get(field)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{context} must define non-negative integer field {field!r}")
    return value


def load_source_corpus(manifest: LaneManifest) -> SourceCorpus:
    corpus_path = REPO_ROOT / manifest.source_corpus_path
    corpus = load_yaml(corpus_path)
    if corpus.get("schema_version") != SOURCE_CORPUS_VERSION:
        raise ValueError(f"{manifest.source_corpus_path} has wrong schema_version")
    if corpus.get("tactic_lane") != manifest.tactic_lane:
        raise ValueError(
            f"{manifest.source_corpus_path} tactic_lane does not match manifest"
        )
    if corpus.get("generated") is not False:
        raise ValueError(f"{manifest.source_corpus_path} must remain generated: false")

    raw_cases = corpus.get("cases")
    if not isinstance(raw_cases, list) or not raw_cases:
        raise ValueError(
            f"{manifest.source_corpus_path} must contain at least one case"
        )

    case_ids: list[str] = []
    seen_case_ids: set[str] = set()
    for index, raw_case in enumerate(raw_cases):
        context = f"{manifest.source_corpus_path} cases[{index}]"
        if not isinstance(raw_case, dict):
            raise ValueError(f"{context} must be a YAML object")
        case_id = require_str(raw_case, "id", context)
        if case_id in seen_case_ids:
            raise ValueError(
                f"{manifest.source_corpus_path} has duplicate case id {case_id!r}"
            )
        seen_case_ids.add(case_id)
        for field in ("lean4_tactic", "clean_tactic", "expected_bucket"):
            require_str(raw_case, field, context)
        case_ids.append(case_id)

    corpus_bytes = corpus_path.read_bytes()
    return SourceCorpus(
        tactic_lane=manifest.tactic_lane,
        path=corpus_path,
        repo_path=manifest.source_corpus_path,
        sha256=hashlib.sha256(corpus_bytes).hexdigest(),
        case_ids=case_ids,
    )


def dry_run_artifact(manifest: LaneManifest, corpus: SourceCorpus) -> dict[str, Any]:
    if manifest.runner_artifact_contract != CONTRACT_VERSION:
        raise ValueError("manifest points at the wrong runner artifact contract")
    if manifest.missing_runner_status != FAIL_CLOSED_STATUS:
        raise ValueError("manifest missing_runner_status must fail closed")

    return {
        "schema_version": CONTRACT_VERSION,
        "tactic_lane": manifest.tactic_lane,
        "run_id": DRY_RUN_RUN_ID,
        "cases_total": corpus.cases_total,
        "lean4_successes": None,
        "clean_successes": None,
        "matched_successes": None,
        "source_corpus_path": corpus.repo_path,
        "source_corpus_sha256": corpus.sha256,
        "runner_path": manifest.runner_path,
        "runner_command": manifest.runner_command,
        "artifact_status": FAIL_CLOSED_STATUS,
        "dry_run": True,
        "case_ids": corpus.case_ids,
    }


def artifact_contract() -> dict[str, Any]:
    return {
        "schema_version": CONTRACT_SCHEMA_VERSION,
        "artifact_contract_version": CONTRACT_VERSION,
        "artifact_format": "json",
        "required_fields": REQUIRED_ARTIFACT_FIELDS,
        "integer_count_fields": [
            "cases_total",
            "lean4_successes",
            "clean_successes",
            "matched_successes",
        ],
        "dry_run_nullable_fields": [
            "lean4_successes",
            "clean_successes",
            "matched_successes",
        ],
        "optional_fields": [
            "artifact_status",
            "dry_run",
            "case_ids",
        ],
        "forbidden_fields": sorted(FORBIDDEN_ARTIFACT_FIELDS),
        "missing_or_mismatched_artifact_status": FAIL_CLOSED_STATUS,
        "print_contract_produces_evidence": False,
        "dry_run_produces_evidence": False,
        "readiness_effect": "none",
    }


def validate_artifact(
    artifact: dict[str, Any],
    manifest: LaneManifest,
    corpus: SourceCorpus,
    *,
    allow_dry_run: bool = False,
) -> list[str]:
    errors: list[str] = []
    if artifact.get("schema_version") == CONTRACT_SCHEMA_VERSION:
        errors.append("--print-contract output is not a generated-count artifact")
        return errors

    for field, reason in sorted(FORBIDDEN_ARTIFACT_FIELDS.items()):
        if field in artifact:
            errors.append(f"forbidden artifact field {field!r}: {reason}")

    errors.extend(
        f"missing required field {field!r}"
        for field in REQUIRED_ARTIFACT_FIELDS
        if field not in artifact
    )

    if artifact.get("schema_version") != CONTRACT_VERSION:
        errors.append("schema_version does not match generated-count runner contract")
    if artifact.get("tactic_lane") != manifest.tactic_lane:
        errors.append("tactic_lane does not match generated-count manifest")
    if artifact.get("source_corpus_path") != corpus.repo_path:
        errors.append("source_corpus_path does not match generated-count manifest")
    if artifact.get("source_corpus_sha256") != corpus.sha256:
        errors.append("source_corpus_sha256 does not match source corpus contents")
    runner_path = artifact.get("runner_path")
    if not isinstance(runner_path, str) or not runner_path:
        errors.append("runner_path must be a non-empty string")
    elif runner_path != manifest.runner_path:
        errors.append("runner_path does not match generated-count manifest")
    runner_command = artifact.get("runner_command")
    if not isinstance(runner_command, str) or not runner_command:
        errors.append("runner_command must be a non-empty string")
    elif runner_command != manifest.runner_command:
        errors.append("runner_command does not match generated-count manifest")
    if artifact.get("cases_total") != corpus.cases_total:
        errors.append("cases_total does not match source corpus case count")
    if "case_ids" in artifact and artifact.get("case_ids") != corpus.case_ids:
        errors.append("case_ids does not match source corpus order")

    run_id = artifact.get("run_id")
    if not isinstance(run_id, str) or not run_id:
        errors.append("run_id must be a non-empty string")

    is_dry_run = artifact.get("dry_run") is True
    if is_dry_run and not allow_dry_run:
        errors.append("dry-run skeleton is not a real generated-count artifact")
    if is_dry_run:
        if artifact.get("artifact_status") != FAIL_CLOSED_STATUS:
            errors.append("dry-run skeleton must keep fail-closed artifact_status")
        errors.extend(
            f"dry-run skeleton field {field!r} must be null"
            for field in ("lean4_successes", "clean_successes", "matched_successes")
            if artifact.get(field) is not None
        )
        case_ids = artifact.get("case_ids")
        if case_ids != corpus.case_ids:
            errors.append("dry-run skeleton case_ids must match source corpus order")
        return errors

    counts: dict[str, int] = {}
    for field in ("lean4_successes", "clean_successes", "matched_successes"):
        try:
            counts[field] = require_int(artifact, field, "generated-count artifact")
        except ValueError as err:
            errors.append(str(err))
    if len(counts) != 3:
        return errors

    cases_total = corpus.cases_total
    for field, value in counts.items():
        if value > cases_total:
            errors.append(f"{field} must not exceed cases_total")
    if counts["matched_successes"] > min(
        counts["lean4_successes"], counts["clean_successes"]
    ):
        errors.append("matched_successes must not exceed either engine success count")
    return errors


def load_json_object(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return payload


def write_json_object_atomic(
    path: Path, payload: dict[str, Any], *, pretty: bool = False
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    indent = 2 if pretty else None
    data = json.dumps(payload, indent=indent, sort_keys=True)
    data += "\n"

    fd, temp_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temp_path = Path(temp_name)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_path, path)
    except BaseException:
        try:
            temp_path.unlink()
        except FileNotFoundError:
            pass
        raise


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Emit or validate tactic generated-count runner artifacts."
    )
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument("--lane", help="generated-count tactic lane to load")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--print-contract",
        action="store_true",
        help="emit the runner artifact contract JSON to stdout without evidence",
    )
    mode.add_argument(
        "--dry-run",
        action="store_true",
        help="emit a fail-closed skeleton JSON artifact to stdout",
    )
    mode.add_argument(
        "--write-dry-run",
        type=Path,
        help="write a fail-closed skeleton JSON artifact to the given path",
    )
    mode.add_argument(
        "--check-artifact",
        type=Path,
        help="validate an existing JSON artifact against the registry contract",
    )
    parser.add_argument(
        "--allow-dry-run",
        action="store_true",
        help="allow --check-artifact to validate a dry-run skeleton instead of real counts",
    )
    parser.add_argument(
        "--pretty", action="store_true", help="pretty-print JSON output"
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        indent = 2 if args.pretty else None
        if args.print_contract:
            print(json.dumps(artifact_contract(), indent=indent, sort_keys=True))
            return 0
        if args.lane is None:
            parser.error("--lane is required unless --print-contract is used")

        manifest = load_lane_manifest(args.registry, args.lane)
        corpus = load_source_corpus(manifest)
        if args.dry_run:
            print(
                json.dumps(
                    dry_run_artifact(manifest, corpus), indent=indent, sort_keys=True
                )
            )
            return 0
        if args.write_dry_run is not None:
            write_json_object_atomic(
                args.write_dry_run,
                dry_run_artifact(manifest, corpus),
                pretty=args.pretty,
            )
            return 0

        artifact_path: Path = args.check_artifact
        if not artifact_path.exists():
            print(
                f"{FAIL_CLOSED_STATUS}: artifact does not exist: {artifact_path}",
                file=sys.stderr,
            )
            return 2
        artifact = load_json_object(artifact_path)
        errors = validate_artifact(
            artifact, manifest, corpus, allow_dry_run=args.allow_dry_run
        )
        if errors:
            for error in errors:
                print(f"generated-count artifact invalid: {error}", file=sys.stderr)
            return 1
        return 0
    except (OSError, ValueError, json.JSONDecodeError, *_YAML_PARSE_ERRORS) as err:
        print(f"generated-count runner error: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
