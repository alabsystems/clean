#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Fail closed if Clean crosses Trust or floats its TrustIr contract pin."""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # Python 3.10 and older.
    import tomli as tomllib


ROOT = Path(__file__).resolve().parent.parent
ROOT_MANIFEST = ROOT / "Cargo.toml"
AUTOFORM_MANIFEST = ROOT / "crates/clean-autoform/Cargo.toml"
AUTOFORM_SOURCE = ROOT / "crates/clean-autoform/src"
CONTRACT_NAME = "trust-ir-contract"
CONTRACT_REPOSITORY = "https://github.com/alabsystems/trust-ir.git"
ANY_CONTRACT_DECLARATION = re.compile(
    rf"(?m)^[ \t]*{re.escape(CONTRACT_NAME)}[ \t]*="
)
EXACT_REVISION = re.compile(r"[0-9a-f]{40}")
FORBIDDEN_DEPENDENCIES = ("trust-types", "trust-verifier-api")
FORBIDDEN_CRATE_NAMES = ("trust_types", "trust_verifier_api")
PATH_DECLARATION = re.compile(r"\bpath\s*=\s*[\"']([^\"']+)[\"']")
EXCLUDED_MANIFEST_DIRS = {".git", "target"}


class BoundaryViolation(ValueError):
    """A manifest crosses the Clean -> Trust workspace boundary."""


def fail(message: str) -> None:
    raise SystemExit(f"Clean dependency-boundary check failed: {message}")


def workspace_manifest_paths() -> list[Path]:
    manifests: list[Path] = []
    for directory, child_dirs, files in os.walk(ROOT):
        child_dirs[:] = sorted(
            child for child in child_dirs if child not in EXCLUDED_MANIFEST_DIRS
        )
        if "Cargo.toml" in files:
            manifests.append(Path(directory) / "Cargo.toml")
    return sorted(manifests)


def path_points_into_trust(manifest: Path, declared_path: str, root: Path) -> bool:
    candidate = (manifest.parent / declared_path).resolve()
    trust_root = (root.parent / "trust").resolve()
    try:
        candidate.relative_to(trust_root)
    except ValueError:
        return False
    return True


def check_manifest_boundaries(manifests: dict[Path, str], root: Path) -> None:
    for manifest, text in manifests.items():
        relative = manifest.relative_to(root)
        for dependency in FORBIDDEN_DEPENDENCIES:
            declaration = re.compile(rf"(?m)^\s*{re.escape(dependency)}\s*=")
            package_alias = re.compile(
                rf"\bpackage\s*=\s*[\"']{re.escape(dependency)}[\"']"
            )
            dependency_table = re.compile(
                rf"(?m)^\s*\[[^\]\n]*dependencies\s*\.\s*"
                rf"[\"']?{re.escape(dependency)}[\"']?\s*\]\s*$"
            )
            if (
                declaration.search(text)
                or package_alias.search(text)
                or dependency_table.search(text)
            ):
                raise BoundaryViolation(
                    f"{relative} declares forbidden Trust dependency {dependency}"
                )

        for match in PATH_DECLARATION.finditer(text):
            declared_path = match.group(1)
            if path_points_into_trust(manifest, declared_path, root):
                raise BoundaryViolation(
                    f"{relative} path dependency points into the Trust workspace: "
                    f"{declared_path}"
                )


def check_contract_declaration(root_manifest: str, autoform_present: bool) -> None:
    """Require one immutable canonical contract pin when clean-autoform exists."""

    declaration_count = len(ANY_CONTRACT_DECLARATION.findall(root_manifest))

    if not autoform_present:
        if declaration_count:
            raise BoundaryViolation(
                "bootstrap projection retained TrustIr after removing clean-autoform"
            )
        return

    if declaration_count != 1:
        raise BoundaryViolation(
            "workspace must declare trust-ir-contract exactly once"
        )
    try:
        parsed = tomllib.loads(root_manifest)
        contract = parsed["workspace"]["dependencies"][CONTRACT_NAME]
    except (KeyError, TypeError, tomllib.TOMLDecodeError) as error:
        raise BoundaryViolation(
            "workspace trust-ir-contract declaration is not valid TOML"
        ) from error
    if (
        not isinstance(contract, dict)
        or set(contract) != {"git", "rev"}
        or contract.get("git") != CONTRACT_REPOSITORY
        or not isinstance(contract.get("rev"), str)
        or EXACT_REVISION.fullmatch(contract["rev"]) is None
    ):
        raise BoundaryViolation(
            "workspace trust-ir-contract must contain only the canonical "
            f"{CONTRACT_REPOSITORY} URL and an exact lowercase 40-hex rev"
        )


def regression_self_test() -> None:
    fixture_root = Path("/clean-boundary-self-test/clean")
    nested_manifest = fixture_root / "crates/nested/Cargo.toml"
    root_manifest = fixture_root / "Cargo.toml"

    fixtures = (
        (
            {
                root_manifest: "[workspace]\n",
                nested_manifest: (
                    "[dependencies]\n"
                    "verification-bridge = "
                    '{ path = "../../../trust/crates/trust-types" }\n'
                ),
            },
            "nested Trust path",
        ),
        (
            {
                root_manifest: "[workspace]\n",
                nested_manifest: (
                    "[dependencies]\n"
                    'solver = { package = "trust-types", version = "1" }\n'
                ),
            },
            "package alias",
        ),
        (
            {
                root_manifest: "[workspace]\n",
                nested_manifest: (
                    "[target.'cfg(unix)'.dependencies.trust-verifier-api]\n"
                    'version = "1"\n'
                ),
            },
            "dependency table",
        ),
    )

    for manifests, description in fixtures:
        try:
            check_manifest_boundaries(manifests, fixture_root)
        except BoundaryViolation as error:
            if "crates/nested/Cargo.toml" not in str(error):
                raise AssertionError(
                    f"{description} regression reported the wrong file"
                )
        else:
            raise AssertionError(f"{description} regression was not rejected")

    exact_revision = "1" * 40
    canonical = (
        "[workspace.dependencies]\n"
        f'{CONTRACT_NAME} = {{ git = "{CONTRACT_REPOSITORY}", '
        f'rev = "{exact_revision}" }}\n'
    )
    check_contract_declaration(canonical, autoform_present=True)
    check_contract_declaration(
        "[workspace.dependencies]\n"
        f"{CONTRACT_NAME} = {{\n"
        f'  rev = "{exact_revision}",\n'
        f'  git = "{CONTRACT_REPOSITORY}",\n'
        "}\n",
        autoform_present=True,
    )
    check_contract_declaration("[workspace.dependencies]\n", autoform_present=False)

    invalid_contracts = (
        (
            canonical.replace(CONTRACT_REPOSITORY, "https://example.invalid/trust-ir.git"),
            True,
            "non-canonical contract repository",
        ),
        (
            canonical.replace(
                f'rev = "{exact_revision}"', 'branch = "main"'
            ),
            True,
            "floating contract branch",
        ),
        (
            canonical.replace(exact_revision, exact_revision[:12]),
            True,
            "abbreviated contract revision",
        ),
        (
            canonical.replace(
                f'rev = "{exact_revision}"',
                f'rev = "{exact_revision}", features = ["serde"]',
            ),
            True,
            "extra contract dependency field",
        ),
        (canonical + canonical, True, "duplicate contract declaration"),
        ("[workspace.dependencies]\n", True, "missing contract declaration"),
        (canonical, False, "contract retained in bootstrap projection"),
    )
    for manifest, autoform_present, description in invalid_contracts:
        try:
            check_contract_declaration(manifest, autoform_present)
        except BoundaryViolation:
            pass
        else:
            raise AssertionError(f"{description} regression was not rejected")


def main() -> int:
    regression_self_test()

    manifest_paths = workspace_manifest_paths()
    manifests = {manifest: manifest.read_text() for manifest in manifest_paths}
    root_manifest = ROOT_MANIFEST.read_text()
    autoform_manifest = (
        AUTOFORM_MANIFEST.read_text() if AUTOFORM_MANIFEST.is_file() else ""
    )

    try:
        check_contract_declaration(root_manifest, bool(autoform_manifest))
    except BoundaryViolation as error:
        fail(str(error))

    try:
        check_manifest_boundaries(manifests, ROOT)
    except BoundaryViolation as error:
        fail(str(error))

    if autoform_manifest and not re.search(
        r"(?m)^trust-ir-contract\s*=\s*\{\s*workspace\s*=\s*true\s*\}$",
        autoform_manifest,
    ):
        fail("clean-autoform must consume trust-ir-contract from the workspace")

    for source in AUTOFORM_SOURCE.rglob("*.rs") if autoform_manifest else ():
        text = source.read_text()
        for crate_name in FORBIDDEN_CRATE_NAMES:
            if crate_name in text:
                fail(f"{source.relative_to(ROOT)} still imports or links {crate_name}")

    # This exact command exposed the old Clean -> Trust -> Clean workspace
    # recursion. Keep it in the regression so a future path back-edge cannot be
    # dismissed as a downstream-layout problem.
    result = subprocess.run(
        [
            "cargo",
            "metadata",
            "--locked",
            "--no-deps",
            "--format-version",
            "1",
        ],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stderr)
        fail("locked root metadata did not close")

    print("Clean dependency boundary is closed through trust-ir-contract")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
