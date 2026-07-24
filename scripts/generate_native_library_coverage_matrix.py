#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import argparse
import json
import re
from collections.abc import Iterable
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
GENERATOR_PATH = "scripts/generate_native_library_coverage_matrix.py"
NATIVE_REDUCER_SOURCE_GLOB = "crates/clean-kernel/src/env/native_reducers*.rs"
INIT_REDUCER_SOURCES = {
    "crates/clean-kernel/src/env/native_reducers.rs",
    "crates/clean-kernel/src/env/native_reducers_init.rs",
}
MATHLIB_COMPATIBILITY_EVIDENCE = [
    "reports/2026-04-13-mathlib-smoke-test.md",
    "reports/2026-04-14-mathlib-verify-progress.md",
    "reports/2026-04-14-mathlib-verify-200.json",
    "crates/clean-olean/tests/verify_mathlib_tests.rs",
    "scripts/verify_mathlib.sh",
]
OLD_MATRIX_BLOCKER = (
    "No complete generated Init, Std, or core-Mathlib API coverage matrix exists yet."
)
SCOPED_MATRIX_BLOCKER = (
    "Generated API coverage matrix is scoped to registered native reducer names "
    "and compatibility-only Mathlib evidence; it is not a complete Init, Std, "
    "or core-Mathlib API enumeration."
)


STATIC_NAME_RE = re.compile(
    r"static\s+([A-Z][A-Z0-9_]*)\s*:\s*LazyLock<Name>\s*="
    r"\s*LazyLock::new\(\|\|\s*Name::from_string\(\"([^\"]+)\"\)\s*\);",
    re.DOTALL,
)
MACRO_NAME_RE = re.compile(
    r"name!\(\s*(?:pub\(crate\)\s+)?([A-Z][A-Z0-9_]*)\s*=\s*\"([^\"]+)\"\s*\);"
)
DIRECT_REGISTRATION_RE = re.compile(
    r"register_native_reducer\(\s*names::([A-Z][A-Z0-9_]*)\.clone\(\)",
    re.DOTALL,
)
REGISTER_ALL_NAME_RE = re.compile(r"names::([A-Z][A-Z0-9_]*)\s*=>")
MACRO_NAME_REF_RE = re.compile(r"names::([A-Z][A-Z0-9_]*)")


def native_reducer_sources(repo_root: Path = REPO_ROOT) -> list[Path]:
    return sorted(
        path
        for path in repo_root.glob(NATIVE_REDUCER_SOURCE_GLOB)
        if not path.name.endswith("_tests.rs")
    )


def _rel(path: Path, repo_root: Path) -> str:
    return path.relative_to(repo_root).as_posix()


def _macro_invocation_bodies(text: str, macro_name: str) -> Iterable[str]:
    marker = f"{macro_name}!("
    search_from = 0
    while True:
        start = text.find(marker, search_from)
        if start == -1:
            return

        body_start = start + len(marker)
        depth = 1
        index = body_start
        while index < len(text) and depth:
            char = text[index]
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            index += 1

        if depth == 0:
            yield text[body_start : index - 1]
            search_from = index
        else:
            return


def _name_constants(sources: list[Path]) -> dict[str, set[str]]:
    constants: dict[str, set[str]] = {}

    for source in sources:
        text = source.read_text(encoding="utf-8")
        for ident, lean_name in STATIC_NAME_RE.findall(text):
            constants.setdefault(ident, set()).add(lean_name)
        for ident, lean_name in MACRO_NAME_RE.findall(text):
            constants.setdefault(ident, set()).add(lean_name)

    return constants


def _registered_name_ids(text: str) -> set[str]:
    ids = set(DIRECT_REGISTRATION_RE.findall(text))

    for body in _macro_invocation_bodies(text, "register_all"):
        ids.update(REGISTER_ALL_NAME_RE.findall(body))

    for macro_name in ("register_uint_width", "register_sint_width"):
        for body in _macro_invocation_bodies(text, macro_name):
            ids.update(MACRO_NAME_REF_RE.findall(body))

    return ids


def _registered_apis_by_source(repo_root: Path) -> dict[str, set[str]]:
    sources = native_reducer_sources(repo_root)
    constants = _name_constants(sources)
    by_source: dict[str, set[str]] = {}

    for source in sources:
        rel_source = _rel(source, repo_root)
        text = source.read_text(encoding="utf-8")
        registered_ids = _registered_name_ids(text)
        unresolved = sorted(ident for ident in registered_ids if ident not in constants)
        if unresolved:
            raise ValueError(
                f"{rel_source} has registered native reducer names without "
                f"Name::from_string constants: {unresolved}"
            )
        ambiguous = {
            ident: sorted(constants[ident])
            for ident in registered_ids
            if len(constants[ident]) != 1
        }
        if ambiguous:
            raise ValueError(
                f"{rel_source} has ambiguous registered native reducer names: {ambiguous}"
            )
        by_source[rel_source] = {
            next(iter(constants[ident])) for ident in registered_ids
        }

    return by_source


def _source_visible_name_census(
    sources: list[Path], registered_apis: list[str]
) -> dict:
    all_source_names = sorted(
        {
            lean_name
            for names in _name_constants(sources).values()
            for lean_name in names
        }
    )
    registered = set(registered_apis)
    support_only_names = sorted(
        lean_name for lean_name in all_source_names if lean_name not in registered
    )

    return {
        "basis": "Lean Name constants in native reducer implementation sources",
        "complete_lean_api_census": False,
        "source_visible_name_count": len(all_source_names),
        "registered_native_api_count": len(registered_apis),
        "support_only_name_count": len(support_only_names),
        "support_only_names": support_only_names,
        "blockers": [
            "This census only accounts for Lean names mentioned by native reducer implementation sources.",
            "Support-only names are constructors, instances, proof constructors, or type names used by reducers; they are not counted as native API replacements.",
            "Lean 4 Init, Std, and core-Mathlib declarations not mentioned in native reducer sources remain outside this census.",
        ],
    }


def _apis_for_sources(
    by_source: dict[str, set[str]], selected_sources: Iterable[str]
) -> list[str]:
    selected = set(selected_sources)
    apis: set[str] = set()
    for source, source_apis in by_source.items():
        if source in selected:
            apis.update(source_apis)
    return sorted(apis)


def _matrix_row(
    *,
    row_id: str,
    api_scope: str,
    status: str,
    coverage_basis: str,
    source_files: list[str],
    registered_apis: list[str],
    blockers: list[str],
) -> dict:
    return {
        "id": row_id,
        "api_scope": api_scope,
        "status": status,
        "coverage_basis": coverage_basis,
        "source_files": source_files,
        "native_api_count": len(registered_apis),
        "registered_apis": registered_apis,
        "blockers": blockers,
    }


def build_matrix(repo_root: Path = REPO_ROOT) -> dict:
    sources = native_reducer_sources(repo_root)
    by_source = _registered_apis_by_source(repo_root)
    source_files = sorted(by_source)
    init_sources = [source for source in source_files if source in INIT_REDUCER_SOURCES]
    std_sources = [
        source for source in source_files if source not in INIT_REDUCER_SOURCES
    ]
    init_apis = _apis_for_sources(by_source, init_sources)
    std_apis = _apis_for_sources(by_source, std_sources)
    unique_apis = sorted(set(init_apis) | set(std_apis))
    source_name_census = _source_visible_name_census(sources, unique_apis)

    return {
        "generator": GENERATOR_PATH,
        "coverage_kind": "scoped_registered_native_reducer_matrix",
        "complete_api_enumeration": False,
        "scope_note": (
            "This generated matrix covers clean native reducer registration names "
            "only. It is evidence for scoped Init/Std replacement work, not a "
            "complete Lean 4 Init, Std, or core-Mathlib API census."
        ),
        "source_globs": [NATIVE_REDUCER_SOURCE_GLOB],
        "source_files": source_files,
        "totals": {
            "matrix_row_count": 3,
            "unique_registered_native_api_count": len(unique_apis),
            "init_native_api_count": len(init_apis),
            "std_native_api_count": len(std_apis),
            "core_mathlib_native_api_count": 0,
            "source_visible_name_count": source_name_census[
                "source_visible_name_count"
            ],
            "support_only_source_name_count": source_name_census[
                "support_only_name_count"
            ],
        },
        "source_name_census": source_name_census,
        "matrix_rows": [
            _matrix_row(
                row_id="init-native-reducers",
                api_scope="Init",
                status="in_progress",
                coverage_basis="registered native reducer names",
                source_files=init_sources,
                registered_apis=init_apis,
                blockers=[
                    "Reducer registrations are scoped native evidence, not complete Init API replacement.",
                    "Some negative Decidable proof payloads still use sorryAx.",
                ],
            ),
            _matrix_row(
                row_id="std-native-reducers",
                api_scope="Std/high-use primitives",
                status="in_progress",
                coverage_basis="registered native reducer names",
                source_files=std_sources,
                registered_apis=std_apis,
                blockers=[
                    "Primitive reducer registrations are not complete Std API replacement.",
                    "Reducer evidence does not cover all Std declarations or theorem APIs.",
                ],
            ),
            {
                "id": "mathlib-olean-compatibility",
                "api_scope": "core-Mathlib",
                "status": "compatibility_only",
                "coverage_basis": ".olean load/type-check compatibility evidence only",
                "source_files": [],
                "native_api_count": 0,
                "registered_apis": [],
                "compatibility_evidence": MATHLIB_COMPATIBILITY_EVIDENCE,
                "blockers": [
                    "No native core-Mathlib API replacement source is represented in this matrix.",
                    "Mathlib evidence remains .olean compatibility-only.",
                ],
            },
        ],
    }


def _with_matrix_after_focused_validation(report: dict, matrix: dict) -> dict:
    updated = {}
    inserted = False
    for key, value in report.items():
        if key == "api_coverage_matrix":
            continue
        updated[key] = value
        if key == "focused_validation":
            updated["api_coverage_matrix"] = matrix
            inserted = True

    if not inserted:
        updated["api_coverage_matrix"] = matrix

    return updated


def update_report(report_path: Path, repo_root: Path = REPO_ROOT) -> None:
    report = json.loads(report_path.read_text(encoding="utf-8"))
    report = _with_matrix_after_focused_validation(report, build_matrix(repo_root))
    blockers = report.get("overall_blockers", [])
    report["overall_blockers"] = [
        SCOPED_MATRIX_BLOCKER if blocker == OLD_MATRIX_BLOCKER else blocker
        for blocker in blockers
    ]
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate the scoped native-library API coverage matrix."
    )
    parser.add_argument(
        "--update-report",
        type=Path,
        help="Update a native-library replacement report JSON in place.",
    )
    args = parser.parse_args()

    if args.update_report:
        update_report(args.update_report)
        return

    print(json.dumps(build_matrix(), indent=2))


if __name__ == "__main__":
    main()
