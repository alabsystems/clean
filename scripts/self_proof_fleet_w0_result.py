# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Read an explicitly pinned W0 gate result for build export."""

import json
from pathlib import Path
import re

from kcheck_coverage_export import Refused, no_number, once
from self_proof_fleet_w0 import OBJECT_ID, W0BuildError, digest, export_w0_build

SHA256 = re.compile(r"[0-9a-f]{64}")
SOURCE_FIELDS = ("source_commit", "source_tree", "board_sha256", "coverage_sha256", "executable_sha256")
RECORD_FIELDS = {
    *SOURCE_FIELDS, "schema", "source_checkout", "executable", "cargo_artifact",
    "version", "qualification_sha256", "cargo_log_sha256",
}
RUNNER = "scripts/run_w0_scoreboard_gate.sh"
# Retained-binary qualification recorded in evidence-ev2-w0-gate-result-2026-11-18.
HISTORICAL_QUALIFICATION = {
    RUNNER: "9da3c051a804e7097cf28b9994a09d4d7262a0ebfecdbd0466fa2736bf64a2b5",
    "scripts/cargo_test_nonvacuous.sh": "341f2d9f9a67b8b90c41092dbfbe43a994c2752d62e993ad118289602901b43a",
    "scripts/kcheck_coverage_export.py": "98cd261f65827d3fe707e96e9f7442b388a46f78175d2cb96742e4ec4fda0a9f",
    "scripts/self_proof_fleet_w0.py": "7dd042201dd0f8ccfc73aeeea255d6dedacee0f83377153a2e1aa6780dd1ded0",
}


def _read_json(raw, label):
    try:
        return json.loads(raw, object_pairs_hook=once, parse_constant=no_number)
    except (ValueError, Refused) as error:
        raise W0BuildError(f"invalid {label} ({error})") from error


def _require_qualification(qualification):
    if (not isinstance(qualification, dict) or qualification.keys() != HISTORICAL_QUALIFICATION.keys()
            or not all(isinstance(value, str) and SHA256.fullmatch(value) for value in qualification.values())):
        raise W0BuildError("invalid W0 gate result qualification hashes")
    if qualification == HISTORICAL_QUALIFICATION:
        return
    registry = Path(__file__).resolve().parents[1] / "data/gate_registry.json"
    rows = _read_json(registry.read_bytes(), "gate registry")["rows"]
    pins = [row["demonstrated"] for row in rows if row["id"] == "run_w0_scoreboard_gate" and row["path"] == RUNNER]
    if len(pins) == 1:
        pin = pins[0]
        replay, inputs = pin["replayed"], pin["inputs"]
        if (qualification == {RUNNER: pin["script_sha256"], **inputs}
                and replay["script_sha256"] == pin["script_sha256"]
                and replay["inputs_sha256"] == digest(json.dumps(sorted(inputs.items())).encode())):
            return
    raise W0BuildError("W0 gate result does not match a qualified script set")


def _record_path(value):
    if not isinstance(value, str) or any(char in value for char in "\0\r\n"):
        raise W0BuildError("invalid W0 gate result path")
    path = Path(value)
    if not path.is_absolute() or str(path.resolve(strict=True)) != value:
        raise W0BuildError("W0 gate result path differs from its recorded location")
    return path


def _require_artifact(record, root, executable):
    row = record["cargo_artifact"]
    crate = root / "crates/clean"
    target, profile = row["target"], row["profile"]
    image, outputs = row["executable"], row["filenames"]
    if (row["reason"] != "compiler-artifact" or profile["test"] is not False
            or target["name"] != "clean" or target["kind"] != ["bin"] or target["crate_types"] != ["bin"]
            or target["src_path"] != str(crate / "src/bin/clean.rs")
            or row["manifest_path"] != str(crate / "Cargo.toml")
            or row["package_id"].split("#", 1)[0] != f"path+{crate.as_uri()}"
            or not isinstance(image, str) or not Path(image).is_absolute()
            or not isinstance(outputs, list) or image not in outputs or Path(image).is_symlink()
            or Path(image).resolve(strict=True) != executable or executable.parts[-2:] != ("debug", "clean")
            or row["trust_executable_sha256"] != record["executable_sha256"]):
        raise W0BuildError("W0 gate result does not select the normal Clean Cargo artifact")


def export_w0_gate_result(path, sha256, output_parent):
    """Validate a gate result and export the exact build it qualified."""
    path = Path(path)
    if not SHA256.fullmatch(sha256) or not path.is_file():
        raise W0BuildError("W0 gate result requires a regular file and independently recorded SHA-256")
    raw = path.read_bytes()
    if digest(raw) != sha256:
        raise W0BuildError("W0 gate result differs from its supplied SHA-256")
    record = _read_json(raw, "W0 gate result")
    if not isinstance(record, dict) or record.keys() != RECORD_FIELDS or record["schema"] != "clean.w0_gate_result.v1":
        raise W0BuildError("unsupported W0 gate result schema or fields")
    inputs = {field: record[field] for field in SOURCE_FIELDS}
    commit, version = record["source_commit"], record["version"]
    for field in (*SOURCE_FIELDS, "cargo_log_sha256"):
        pattern = OBJECT_ID if field in ("source_commit", "source_tree") else SHA256
        if not isinstance(record[field], str) or not pattern.fullmatch(record[field]):
            raise W0BuildError(f"invalid W0 gate result {field}")
    if not isinstance(version, str) or not re.fullmatch(rf"clean [^\s+]+\+g{commit}", version):
        raise W0BuildError("W0 gate result version must name its producing commit")
    _require_qualification(record["qualification_sha256"])
    root, executable = _record_path(record["source_checkout"]), _record_path(record["executable"])
    try:
        _require_artifact(record, root, executable)
    except (AttributeError, KeyError, TypeError) as error:
        raise W0BuildError("invalid W0 gate result Cargo artifact") from error
    return export_w0_build(root, executable, record["executable_sha256"], output_parent,
                           expected_inputs=inputs, expected_version=version)
