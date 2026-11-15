"""Finite, unambiguous schema-v1 vendor metadata; no source-tree attestation."""

import contextlib
import io
import json
import math
from pathlib import Path
import sys
import tempfile

GENERATOR = "scripts/gen_vendor_manifest.py"
SUMMARY_FIELDS = ("total_crates", "registry_crates", "git_crates", "total_size_bytes")
ROW_STRINGS = ("name", "version", "dir", "source_kind", "source", "checksum", "checksum_kind")


def _pairs(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError(f"duplicate JSON member {key!r}")
        result[key] = value
    return result


def _constant(value):
    raise ValueError(f"non-finite JSON constant {value}")


def _float(value):
    number = float(value)
    if not math.isfinite(number):
        raise ValueError(f"non-finite JSON number {value}")
    return number


def _counter(value, label):
    if type(value) is not int or value < 0:
        raise ValueError(f"SHAPE: {label} must be a nonnegative integer")


def read_manifest(path):
    data = json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=_pairs,
                      parse_constant=_constant, parse_float=_float)
    if not isinstance(data, dict):
        raise ValueError("SHAPE: manifest must be an object")
    if type(data.get("schema_version")) is not int or data["schema_version"] != 1:
        raise ValueError("SCHEMA: schema_version must be integer 1")
    if data.get("generator") != GENERATOR:
        raise ValueError(f"SCHEMA: generator must be {GENERATOR!r}")
    rows = data.get("crates")
    if not isinstance(rows, list):
        raise ValueError("SHAPE: crates must be an array")
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"SHAPE: crate row {index} must be an object")
        for field in ROW_STRINGS:
            if not isinstance(row.get(field), str) or not row[field]:
                raise ValueError(f"SHAPE: crate row {index}.{field} must be a nonempty string")
        for field in ("size_bytes", "file_count"):
            _counter(row.get(field), f"crate row {index}.{field}")
    summary = data.get("summary")
    if not isinstance(summary, dict):
        raise ValueError("SHAPE: summary must be an object")
    for field in SUMMARY_FIELDS:
        _counter(summary.get(field), f"summary.{field}")
    if ("total_size_mb" in summary
            and type(summary["total_size_mb"]) not in (int, float)):
        raise ValueError("SHAPE: summary.total_size_mb must be a finite number")
    return data


def summary_problems(manifest):
    """Check internal consistency only; measured byte counts still need the tree."""
    rows, summary = manifest["crates"], manifest["summary"]
    expected = {
        "total_crates": len(rows),
        "registry_crates": sum(row["source_kind"] == "registry" for row in rows),
        "git_crates": sum(row["source_kind"] == "git" for row in rows),
        "total_size_bytes": sum(row["size_bytes"] for row in rows),
    }
    if "total_size_mb" in summary:
        try:
            expected["total_size_mb"] = round(expected["total_size_bytes"] / (1024 * 1024), 1)
        except OverflowError:
            return ["SUMMARY: total_size_mb cannot represent the byte total"]
    try:
        return [f"SUMMARY: {field} {summary[field]!r} != {want} derived from rows"
                for field, want in expected.items() if summary[field] != want]
    except ValueError:
        return ["SUMMARY: inconsistent counters exceed integer display limit"]


def selftest_manifest(rows, lock_sha):
    rows = [dict(row, size_bytes=0, file_count=0) for row in rows]
    return {"schema_version": 1, "generator": GENERATOR, "cargo_lock_sha256": lock_sha,
            "crates": rows, "summary": {"total_crates": len(rows),
            "registry_crates": len(rows), "git_crates": 0, "total_size_bytes": 0,
            "total_size_mb": 0.0}}


def check_self_test(check, rows, lock_sha, lock_path):
    """Exercise the public checker, including finite positive and malformed controls."""
    base = selftest_manifest(rows, lock_sha)
    raw = json.dumps(base)
    cases = [
        ("finite metadata", raw[:-1] + ', "metadata": 1.25}', None),
        ("array root", "[]", "SHAPE:"),
        ("unknown schema", raw.replace('"schema_version": 1', '"schema_version": 999'), "SCHEMA:"),
        ("boolean schema", raw.replace('"schema_version": 1', '"schema_version": true'), "SCHEMA:"),
        ("foreign generator", raw.replace(GENERATOR, "other.py"), "SCHEMA:"),
        ("duplicate member", '{"schema_version": 1, ' + raw[1:], "duplicate JSON member"),
    ]
    large = json.loads(raw)
    del large["summary"]["total_size_mb"]
    digits = sys.get_int_max_str_digits() or 4300
    oversized = json.dumps(large).replace('"size_bytes": 0', '"size_bytes": ' + '9' * digits)
    cases.append(("oversized sum display", oversized, "SUMMARY:"))
    for literal in ("NaN", "Infinity", "-Infinity", "1e999", "-1e999"):
        cases.append((literal, raw[:-1] + ', "metadata": ' + literal + '}', "non-finite"))
    for label, edit, reason in (
        ("floating count", lambda data: data["summary"].update(total_crates=float(len(rows))), "SHAPE:"),
        ("wrong source count", lambda data: data["summary"].update(registry_crates=0), "SUMMARY:"),
        ("wrong size sum", lambda data: data["summary"].update(total_size_bytes=1), "SUMMARY:"),
        ("wrong MB display", lambda data: data["summary"].update(total_size_mb=0.1), "SUMMARY:"),
        ("boolean row count", lambda data: data["crates"][0].update(file_count=True), "SHAPE:"),
        ("non-object row", lambda data: data["crates"].__setitem__(0, []), "SHAPE:"),
    ):
        data = json.loads(raw)
        edit(data)
        cases.append((label, json.dumps(data), reason))
    failures = []
    with tempfile.TemporaryDirectory(prefix="vendor-format-") as temporary:
        path = Path(temporary) / "manifest.json"
        for label, text, reason in cases:
            path.write_text(text, encoding="utf-8")
            errors = io.StringIO()
            with contextlib.redirect_stderr(errors):
                status = check(str(path), str(lock_path))
            ok = (status == 0 and not errors.getvalue()) if reason is None else (
                status == 1 and reason in errors.getvalue())
            print(f"  self-test ARM {'ok' if ok else 'FAILED'}: manifest format {label} -> exit {status}")
            if not ok:
                failures.append("manifest-format:" + label)
    return failures
