#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Fail closed if Clean crosses a workspace boundary or splits first-party pins."""

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
ROOT_LOCK = ROOT / "Cargo.lock"
CLI_RUNNER_LOCK = ROOT / "cli-runner/Cargo.lock"
AUTOFORM_MANIFEST = ROOT / "crates/clean-autoform/Cargo.toml"
AUTOFORM_SOURCE = ROOT / "crates/clean-autoform/src"
CRYSTAL_A2_MANIFEST = ROOT / "scripts/crystal_a2_project/Cargo.toml"
CRYSTAL_A2_LOCK = ROOT / "scripts/crystal_a2_project/Cargo.lock"
CRYSTAL_A2_PACKAGE = "a2mint-project"
CONTRACT_NAME = "trust-ir-contract"
CONTRACT_REPOSITORY = "https://github.com/alabsystems/trust-ir.git"
ANY_CONTRACT_DECLARATION = re.compile(
    rf"(?m)^[ \t]*{re.escape(CONTRACT_NAME)}[ \t]*="
)
EXACT_REVISION = re.compile(r"[0-9a-f]{40}")
TRUST_IR_LOCK_SOURCE = re.compile(
    r"^git\+https://github\.com/alabsystems/trust-ir\.git"
    r"\?rev=([0-9a-f]{40})#([0-9a-f]{40})$"
)
AY_DEPENDENCY_NAMES = (
    "ay",
    "ay-dpll",
    "ay-core",
    "ay-lean-bridge",
    "ay-proof",
    "ay-frontend",
    "ay-translate",
)
AY_REPOSITORY = "https://github.com/alabsystems/ay.git"
TY_DEPENDENCY_NAME = "tla-core"
TY_REPOSITORY = "https://github.com/alabsystems/ty.git"
AY_LOCK_SOURCE = re.compile(
    rf"^git\+{re.escape(AY_REPOSITORY)}\?rev=([0-9a-f]{{40}})#([0-9a-f]{{40}})$"
)
TY_LOCK_SOURCE = re.compile(
    rf"^git\+{re.escape(TY_REPOSITORY)}\?rev=([0-9a-f]{{40}})#([0-9a-f]{{40}})$"
)
FORBIDDEN_DEPENDENCIES = ("trust-types", "trust-verifier-api")
FORBIDDEN_CRATE_NAMES = ("trust_types", "trust_verifier_api")
PATH_DECLARATION = re.compile(r"\bpath\s*=\s*[\"']([^\"']+)[\"']")
# `.claude/` is gitignored agent scratch: `.claude/worktrees/` holds detached
# worktrees AND full checkouts of OTHER repositories (trust, ay, trust-ir,
# trust-cg). Walking into it made this gate's verdict depend on which sibling
# lanes happened to be running -- a Trust checkout legitimately declares
# `trust-types`, so the boundary check failed on a manifest that is not Clean's
# and is not even tracked here. Measured 2026-08-20.
EXCLUDED_MANIFEST_DIRS = {".git", ".claude", "target"}


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


def tracked_lock_paths() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "*Cargo.lock"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    )
    return sorted(ROOT / name for name in result.stdout.decode().split("\0") if name)


def path_points_into_trust(manifest: Path, declared_path: str, root: Path) -> bool:
    candidate = (manifest.parent / declared_path).resolve()
    trust_root = (root.parent / "trust").resolve()
    try:
        candidate.relative_to(trust_root)
    except ValueError:
        return False
    return True


def path_escapes_workspace(manifest: Path, declared_path: str, root: Path) -> bool:
    candidate = (manifest.parent / declared_path).resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError:
        return True
    return False


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

        # A committed path outside this repository makes Cargo.lock depend on
        # mutable sibling state. Inspect declaration lines rather than comments
        # (several manifests document rejected external paths in comments).
        for line in text.splitlines():
            if line.lstrip().startswith("#"):
                continue
            for match in PATH_DECLARATION.finditer(line):
                declared_path = match.group(1)
                if path_points_into_trust(manifest, declared_path, root):
                    raise BoundaryViolation(
                        f"{relative} path dependency points into the Trust workspace: "
                        f"{declared_path}"
                    )
                if path_escapes_workspace(manifest, declared_path, root):
                    raise BoundaryViolation(
                        f"{relative} path dependency escapes the Clean workspace: "
                        f"{declared_path}"
                    )


def check_contract_declaration(
    root_manifest: str, autoform_present: bool
) -> str | None:
    """Require one immutable canonical contract pin when clean-autoform exists."""

    declaration_count = len(ANY_CONTRACT_DECLARATION.findall(root_manifest))

    if not autoform_present:
        if declaration_count:
            raise BoundaryViolation(
                "bootstrap projection retained TrustIr after removing clean-autoform"
            )
        return None

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
    return contract["rev"]


def check_contract_lock_revision(
    root_manifest: str, autoform_present: bool, lock_revision: str | None
) -> None:
    """Bind the normal workspace contract to its lock without breaking bootstrap."""

    if not autoform_present:
        return
    try:
        contract_revision = tomllib.loads(root_manifest)["workspace"]["dependencies"][
            CONTRACT_NAME
        ]["rev"]
    except (KeyError, TypeError, tomllib.TOMLDecodeError) as error:
        raise BoundaryViolation(
            "workspace trust-ir-contract revision is not valid TOML"
        ) from error
    if lock_revision != contract_revision:
        raise BoundaryViolation(
            "Cargo.lock TrustIR revision does not match trust-ir-contract: "
            f"lock={lock_revision}, contract={contract_revision}"
        )


def check_first_party_manifest_pins(root_manifest: str) -> tuple[str, str, str]:
    """Return the one AY version/revision and Ty revision required by the root."""

    try:
        dependencies = tomllib.loads(root_manifest)["workspace"]["dependencies"]
    except (KeyError, TypeError, tomllib.TOMLDecodeError) as error:
        raise BoundaryViolation(
            "root workspace dependencies table is not valid TOML"
        ) from error
    if not isinstance(dependencies, dict):
        raise BoundaryViolation("root workspace dependencies table is not a table")

    ay_versions: set[str] = set()
    ay_revisions: set[str] = set()
    for name in AY_DEPENDENCY_NAMES:
        dependency = dependencies.get(name)
        if not isinstance(dependency, dict):
            raise BoundaryViolation(f"workspace AY dependency {name} is absent")
        version = dependency.get("version")
        revision = dependency.get("rev")
        if (
            dependency.get("git") != AY_REPOSITORY
            or not isinstance(version, str)
            or not version
            or not isinstance(revision, str)
            or EXACT_REVISION.fullmatch(revision) is None
        ):
            raise BoundaryViolation(
                f"workspace AY dependency {name} needs the canonical Git URL, "
                "a version, and an exact lowercase 40-hex rev"
            )
        ay_versions.add(version)
        ay_revisions.add(revision)
    if len(ay_versions) != 1 or len(ay_revisions) != 1:
        raise BoundaryViolation(
            "workspace AY dependencies split versions or revisions: "
            f"versions={sorted(ay_versions)}, revisions={sorted(ay_revisions)}"
        )

    ty_dependency = dependencies.get(TY_DEPENDENCY_NAME)
    if not isinstance(ty_dependency, dict):
        raise BoundaryViolation(
            f"workspace Ty dependency {TY_DEPENDENCY_NAME} is absent"
        )
    ty_revision = ty_dependency.get("rev")
    if (
        ty_dependency.get("git") != TY_REPOSITORY
        or not isinstance(ty_revision, str)
        or EXACT_REVISION.fullmatch(ty_revision) is None
    ):
        raise BoundaryViolation(
            f"workspace Ty dependency {TY_DEPENDENCY_NAME} needs the canonical "
            "Git URL and an exact lowercase 40-hex rev"
        )

    return next(iter(ay_versions)), next(iter(ay_revisions)), ty_revision


def check_first_party_lock_inventory(
    lock_texts: dict[str, str],
    required_contexts: set[str],
    ay_version: str,
    ay_revision: str,
    ty_revision: str,
) -> str:
    """Bind AY and Ty in every tracked lock to the root manifest's epoch."""

    missing = required_contexts.difference(lock_texts)
    if missing:
        raise BoundaryViolation(
            "required first-party locks are not tracked: " + ", ".join(sorted(missing))
        )

    tla_core_versions: dict[str, str] = {}
    for context, lock_text in sorted(lock_texts.items()):
        try:
            packages = tomllib.loads(lock_text).get("package")
        except tomllib.TOMLDecodeError as error:
            raise BoundaryViolation(f"{context} is not valid TOML") from error
        if not isinstance(packages, list):
            raise BoundaryViolation(f"{context} has no package inventory")

        ay_packages: list[dict] = []
        ty_packages: list[dict] = []
        for package in packages:
            if not isinstance(package, dict):
                continue
            source = package.get("source")
            if not isinstance(source, str):
                continue
            if source.startswith(f"git+{AY_REPOSITORY}"):
                match = AY_LOCK_SOURCE.fullmatch(source)
                if match is None or match.group(1) != match.group(2):
                    raise BoundaryViolation(
                        f"{context} package {package.get('name', '<unknown>')} "
                        "does not use one resolved canonical AY revision"
                    )
                if match.group(1) != ay_revision:
                    raise BoundaryViolation(
                        f"{context} AY revision {match.group(1)} does not match "
                        f"workspace revision {ay_revision}"
                    )
                ay_packages.append(package)
            elif source.startswith(f"git+{TY_REPOSITORY}"):
                match = TY_LOCK_SOURCE.fullmatch(source)
                if match is None or match.group(1) != match.group(2):
                    raise BoundaryViolation(
                        f"{context} package {package.get('name', '<unknown>')} "
                        "does not use one resolved canonical Ty revision"
                    )
                if match.group(1) != ty_revision:
                    raise BoundaryViolation(
                        f"{context} Ty revision {match.group(1)} does not match "
                        f"workspace revision {ty_revision}"
                    )
                ty_packages.append(package)

        if context in required_contexts and not ay_packages:
            raise BoundaryViolation(f"{context} has no AY package source")
        ay_lock_versions: set[str] = set()
        for package in ay_packages:
            version = package.get("version")
            if not isinstance(version, str) or not version:
                raise BoundaryViolation(
                    f"{context} AY package {package.get('name', '<unknown>')} "
                    "has no lockfile version"
                )
            ay_lock_versions.add(version)
        if ay_packages and ay_lock_versions != {ay_version}:
            raise BoundaryViolation(
                f"{context} AY versions {sorted(ay_lock_versions)} do not match "
                f"workspace version {ay_version}"
            )

        direct_ty = [
            package
            for package in ty_packages
            if package.get("name") == TY_DEPENDENCY_NAME
        ]
        if len(direct_ty) > 1:
            raise BoundaryViolation(
                f"{context} contains multiple Git-pinned {TY_DEPENDENCY_NAME} packages"
            )
        if context in required_contexts and len(direct_ty) != 1:
            raise BoundaryViolation(
                f"{context} must contain exactly one Git-pinned {TY_DEPENDENCY_NAME}"
            )
        if direct_ty:
            version = direct_ty[0].get("version")
            if not isinstance(version, str) or not version:
                raise BoundaryViolation(
                    f"{context} {TY_DEPENDENCY_NAME} has no lockfile version"
                )
            tla_core_versions[context] = version

    versions = set(tla_core_versions.values())
    if len(versions) != 1:
        detail = ", ".join(
            f"{context}={version}"
            for context, version in sorted(tla_core_versions.items())
        )
        raise BoundaryViolation(
            f"tracked locks split {TY_DEPENDENCY_NAME} versions: {detail}"
        )
    return next(iter(versions))


def check_trust_ir_lock_source(lock_text: str, context: str, required: bool) -> str | None:
    """Require one exact TrustIR Git universe within a Cargo lock graph."""

    try:
        lock = tomllib.loads(lock_text)
    except tomllib.TOMLDecodeError as error:
        raise BoundaryViolation(f"{context} is not valid TOML") from error
    packages = lock.get("package")
    if not isinstance(packages, list):
        raise BoundaryViolation(f"{context} has no package inventory")
    trust_ir_packages = [
        package
        for package in packages
        if isinstance(package, dict)
        and isinstance(package.get("name"), str)
        and (
            package["name"] == "trust-ir"
            or package["name"].startswith("trust-ir-")
        )
    ]
    if not trust_ir_packages:
        if required:
            raise BoundaryViolation(f"{context} has no TrustIR package source")
        return None

    revisions: set[str] = set()
    for package in trust_ir_packages:
        source = package.get("source")
        match = TRUST_IR_LOCK_SOURCE.fullmatch(source) if isinstance(source, str) else None
        if match is None:
            raise BoundaryViolation(
                f"{context} package {package['name']} does not use the canonical "
                "exact TrustIR Git source"
            )
        query, resolved = match.groups()
        if query != resolved:
            raise BoundaryViolation(
                f"{context} package {package['name']} resolves {resolved} "
                f"but requests {query}"
            )
        revisions.add(query)
    if len(revisions) != 1:
        raise BoundaryViolation(
            f"{context} resolves multiple TrustIR Git revisions: "
            + ", ".join(sorted(revisions))
        )
    return next(iter(revisions))


def check_trust_ir_lock_inventory(
    lock_texts: dict[str, str], required_context: str | None
) -> str | None:
    """Require one TrustIR revision across every tracked lock graph."""

    if required_context is not None and required_context not in lock_texts:
        raise BoundaryViolation(f"required lock {required_context} is not tracked")
    resolved: dict[str, str] = {}
    for context, lock_text in sorted(lock_texts.items()):
        revision = check_trust_ir_lock_source(
            lock_text,
            context,
            context == required_context,
        )
        if revision is not None:
            resolved[context] = revision
    revisions = set(resolved.values())
    if len(revisions) > 1:
        detail = ", ".join(
            f"{context}={revision}" for context, revision in sorted(resolved.items())
        )
        raise BoundaryViolation(
            f"tracked lockfiles resolve multiple TrustIR Git revisions: {detail}"
        )
    if required_context is not None:
        return resolved.get(required_context)
    return next(iter(revisions), None)


def check_crystal_a2_producer(
    manifest_text: str,
    lock_text: str | None,
    contract_revision: str,
) -> None:
    """Bind the out-of-workspace proof-artifact producer to Clean's authority."""

    try:
        manifest = tomllib.loads(manifest_text)
    except tomllib.TOMLDecodeError as error:
        raise BoundaryViolation(
            f"{CRYSTAL_A2_MANIFEST.relative_to(ROOT)} is not valid TOML"
        ) from error
    if manifest.get("workspace") != {}:
        raise BoundaryViolation(
            f"{CRYSTAL_A2_MANIFEST.relative_to(ROOT)} must remain an empty standalone "
            "workspace"
        )
    allowed_top_level = {"workspace", "package", "dependencies", "bin"}
    if set(manifest) != allowed_top_level:
        raise BoundaryViolation(
            f"{CRYSTAL_A2_MANIFEST.relative_to(ROOT)} must contain only its standalone "
            "workspace, package, dependencies, and binary tables"
        )
    package = manifest.get("package")
    if (
        not isinstance(package, dict)
        or package.get("name") != CRYSTAL_A2_PACKAGE
        or package.get("publish") is not False
    ):
        raise BoundaryViolation(
            f"{CRYSTAL_A2_MANIFEST.relative_to(ROOT)} must declare the exact unpublished "
            f"{CRYSTAL_A2_PACKAGE} package"
        )
    dependencies = manifest.get("dependencies")
    if not isinstance(dependencies, dict) or set(dependencies) != {"trust-ir", "sha2"}:
        raise BoundaryViolation(
            "crystal A2 producer must have exactly one TrustIR reader and sha2; "
            "aliases or additional dependency tables could escalate reader features"
        )
    trust_ir = dependencies.get("trust-ir")
    required_fields = {"git", "rev", "default-features", "features"}
    if not isinstance(trust_ir, dict) or set(trust_ir) != required_fields:
        raise BoundaryViolation(
            "crystal A2 producer trust-ir dependency must contain only the exact "
            "Git authority, feature floor, and revision"
        )
    features = trust_ir.get("features")
    if (
        trust_ir.get("git") != CONTRACT_REPOSITORY
        or trust_ir.get("rev") != contract_revision
        or trust_ir.get("default-features") is not False
        or not isinstance(features, list)
        or len(features) != 2
        or set(features) != {"binary", "fmt"}
    ):
        raise BoundaryViolation(
            "crystal A2 producer trust-ir dependency must match trust-ir-contract "
            f"{contract_revision} with exactly binary+fmt and default features off"
        )
    if lock_text is None:
        raise BoundaryViolation(
            f"{CRYSTAL_A2_LOCK.relative_to(ROOT)} must be tracked for locked reproduction"
        )
    lock_revision = check_trust_ir_lock_source(
        lock_text,
        str(CRYSTAL_A2_LOCK.relative_to(ROOT)),
        True,
    )
    if lock_revision != contract_revision:
        raise BoundaryViolation(
            f"{CRYSTAL_A2_LOCK.relative_to(ROOT)} TrustIR revision {lock_revision} "
            f"does not match trust-ir-contract {contract_revision}"
        )
    try:
        packages = tomllib.loads(lock_text).get("package")
    except tomllib.TOMLDecodeError as error:
        raise BoundaryViolation(
            f"{CRYSTAL_A2_LOCK.relative_to(ROOT)} is not valid TOML"
        ) from error
    roots = (
        [
            package
            for package in packages
            if isinstance(package, dict)
            and package.get("name") == CRYSTAL_A2_PACKAGE
            and package.get("source") is None
        ]
        if isinstance(packages, list)
        else []
    )
    if len(roots) != 1:
        raise BoundaryViolation(
            f"{CRYSTAL_A2_LOCK.relative_to(ROOT)} must contain one local "
            f"{CRYSTAL_A2_PACKAGE} root package"
        )


def check_crystal_a2_locked_metadata() -> None:
    """Require Cargo itself to accept the standalone graph without relocking."""

    command = (
        "cargo",
        "metadata",
        "--locked",
        "--no-deps",
        "--manifest-path",
        str(CRYSTAL_A2_MANIFEST.relative_to(ROOT)),
        "--format-version",
        "1",
    )
    try:
        result = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        raise BoundaryViolation(
            "cannot run locked Crystal A2 Cargo metadata: " + str(error)
        ) from error
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        if len(detail) > 1_000:
            detail = detail[-1_000:]
        suffix = f": {detail}" if detail else ""
        raise BoundaryViolation(
            "Crystal A2 Cargo.lock is not current under cargo metadata --locked"
            + suffix
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
        (
            {
                root_manifest: "[workspace]\n",
                nested_manifest: (
                    "[patch.\"https://github.com/alabsystems/ty.git\"]\n"
                    'tla-core = { path = "../../../ty/crates/tla-core" }\n'
                ),
            },
            "mutable sibling path",
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
    # Same pin, keys in the opposite order: the checker must not depend on
    # `git` preceding `rev`.
    #
    # This fixture used to spell that as a MULTI-LINE inline table. TOML 1.0
    # forbids newlines inside an inline table, so no conforming parser accepts
    # it -- `tomllib.loads` raised TOMLDecodeError, `check_contract_declaration`
    # converted that into BoundaryViolation, and this self-test failed on every
    # Python with a working `tomllib`. On Python 3.9 (this machine's `/usr/bin/
    # python3`) the script instead died at import for lack of `tomllib`, so the
    # failure was masked and local_gate.sh's FIRST leg had been dead since
    # 3477dc787. Cargo would reject the multi-line spelling in a real manifest
    # too, so nothing of value is lost by testing the valid one.
    check_contract_declaration(
        "[workspace.dependencies]\n"
        f'{CONTRACT_NAME} = {{ rev = "{exact_revision}", '
        f'git = "{CONTRACT_REPOSITORY}" }}\n',
        autoform_present=True,
    )
    check_contract_declaration("[workspace.dependencies]\n", autoform_present=False)
    check_contract_lock_revision(canonical, True, exact_revision)
    check_contract_lock_revision("[workspace.dependencies]\n", False, None)
    try:
        check_contract_lock_revision(canonical, True, "2" * 40)
    except BoundaryViolation:
        pass
    else:
        raise AssertionError("contract/lock revision mismatch was not rejected")

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

    def lock_source(revision: str, resolved: str | None = None) -> str:
        resolved = revision if resolved is None else resolved
        return (
            "git+https://github.com/alabsystems/trust-ir.git"
            f"?rev={revision}#{resolved}"
        )

    def lock_fixture(rows: tuple[tuple[str, str | None], ...]) -> str:
        blocks = ['version = 4\n']
        for name, source in rows:
            block = f'[[package]]\nname = "{name}"\nversion = "0.4.0"\n'
            if source is not None:
                block += f'source = "{source}"\n'
            blocks.append(block)
        return "\n".join(blocks)

    revision_a = "a" * 40
    revision_b = "b" * 40
    coherent_lock = lock_fixture(
        (
            ("trust-ir", lock_source(revision_a)),
            ("trust-ir-contract", lock_source(revision_a)),
        )
    )
    unrelated_lock = lock_fixture((("serde", "registry+https://example.invalid/index"),))
    assert check_trust_ir_lock_source(coherent_lock, "fixture.lock", True) == revision_a
    assert check_trust_ir_lock_source(unrelated_lock, "optional.lock", False) is None
    assert (
        check_trust_ir_lock_inventory(
            {
                "Cargo.lock": coherent_lock,
                "nested/Cargo.lock": lock_fixture(
                    (("trust-ir", lock_source(revision_a)),)
                ),
                "unrelated/Cargo.lock": unrelated_lock,
            },
            "Cargo.lock",
        )
        == revision_a
    )

    producer_manifest = (
        "[workspace]\n\n"
        "[package]\n"
        f'name = "{CRYSTAL_A2_PACKAGE}"\n'
        'version = "0.1.0"\n'
        "publish = false\n\n"
        "[dependencies]\n"
        f'trust-ir = {{ git = "{CONTRACT_REPOSITORY}", rev = "{revision_a}", '
        'default-features = false, features = ["binary", "fmt"] }\n'
        'sha2 = { version = "0.10", default-features = false }\n\n'
        "[[bin]]\n"
        'name = "a2project"\n'
        'path = "src/main.rs"\n'
    )
    producer_lock = lock_fixture(
        (
            (CRYSTAL_A2_PACKAGE, None),
            ("trust-ir", lock_source(revision_a)),
        )
    )
    check_crystal_a2_producer(producer_manifest, producer_lock, revision_a)
    invalid_producers = (
        (
            producer_manifest.replace(
                f'git = "{CONTRACT_REPOSITORY}", rev = "{revision_a}"',
                'path = "../../../trust/first-party/trust-ir/crates/trust-ir"',
            ),
            producer_lock,
            "mutable sibling path",
        ),
        (producer_manifest, None, "missing standalone lock"),
        (
            producer_manifest,
            producer_lock.replace(revision_a, revision_b),
            "lock/manifest authority split",
        ),
        (
            producer_manifest.replace('["binary", "fmt"]', '["binary"]'),
            producer_lock,
            "reader feature drift",
        ),
        (
            producer_manifest.replace(
                "[dependencies]\n",
                "[dependencies]\n"
                f'trust-ir-full = {{ package = "trust-ir", git = "{CONTRACT_REPOSITORY}", '
                f'rev = "{revision_a}", features = ["compiler"] }}\n',
            ),
            producer_lock,
            "feature-escalating TrustIR alias",
        ),
    )
    for manifest_text, lock_text, description in invalid_producers:
        try:
            check_crystal_a2_producer(manifest_text, lock_text, revision_a)
        except BoundaryViolation:
            pass
        else:
            raise AssertionError(f"{description} regression was not rejected")

    invalid_locks = (
        (
            lock_fixture(
                (
                    ("trust-ir", lock_source(revision_a)),
                    ("trust-ir-contract", lock_source(revision_b)),
                )
            ),
            True,
            "split TrustIR revisions",
        ),
        (
            lock_fixture((("trust-ir", lock_source(revision_a, revision_b)),)),
            True,
            "query/resolved mismatch",
        ),
        (lock_fixture((("trust-ir", None),)), True, "path TrustIR source"),
        (unrelated_lock, True, "missing required TrustIR source"),
    )
    for lock_text, required, description in invalid_locks:
        try:
            check_trust_ir_lock_source(lock_text, "fixture.lock", required)
        except BoundaryViolation:
            pass
        else:
            raise AssertionError(f"{description} regression was not rejected")

    try:
        check_trust_ir_lock_inventory(
            {
                "Cargo.lock": coherent_lock,
                "nested/Cargo.lock": lock_fixture(
                    (("trust-ir", lock_source(revision_b)),)
                ),
            },
            "Cargo.lock",
        )
    except BoundaryViolation:
        pass
    else:
        raise AssertionError("cross-lock TrustIR split regression was not rejected")

    revision_c = "c" * 40
    first_party_manifest = "[workspace.dependencies]\n" + "".join(
        f'{name} = {{ package = "{name}", version = "0.13.0", '
        f'git = "{AY_REPOSITORY}", rev = "{revision_a}" }}\n'
        for name in AY_DEPENDENCY_NAMES
    ) + (
        f'{TY_DEPENDENCY_NAME} = {{ git = "{TY_REPOSITORY}", '
        f'rev = "{revision_b}" }}\n'
    )
    assert check_first_party_manifest_pins(first_party_manifest) == (
        "0.13.0",
        revision_a,
        revision_b,
    )
    invalid_first_party_manifests = (
        (
            first_party_manifest.replace('version = "0.13.0"', 'version = "0.12.0"', 1),
            "split AY versions",
        ),
        (
            first_party_manifest.replace(revision_a, revision_c, 1),
            "split AY revisions",
        ),
        (
            first_party_manifest.replace(AY_REPOSITORY, "https://example.invalid/ay.git", 1),
            "non-canonical AY repository",
        ),
        (
            first_party_manifest.replace(revision_b, revision_b[:12]),
            "abbreviated Ty revision",
        ),
    )
    for manifest, description in invalid_first_party_manifests:
        try:
            check_first_party_manifest_pins(manifest)
        except BoundaryViolation:
            pass
        else:
            raise AssertionError(f"{description} regression was not rejected")

    def first_party_source(repository: str, revision: str) -> str:
        return f"git+{repository}?rev={revision}#{revision}"

    def first_party_lock_fixture(
        ay_version: str = "0.13.0",
        ay_revision: str = revision_a,
        ty_version: str = "0.13.0",
        ty_revision: str = revision_b,
    ) -> str:
        return "\n".join(
            (
                "version = 4\n",
                "[[package]]\n"
                'name = "ay"\n'
                f'version = "{ay_version}"\n'
                f'source = "{first_party_source(AY_REPOSITORY, ay_revision)}"\n',
                "[[package]]\n"
                f'name = "{TY_DEPENDENCY_NAME}"\n'
                f'version = "{ty_version}"\n'
                f'source = "{first_party_source(TY_REPOSITORY, ty_revision)}"\n',
            )
        )

    required_locks = {"Cargo.lock", "cli-runner/Cargo.lock"}
    coherent_first_party_locks = {
        "Cargo.lock": first_party_lock_fixture(),
        "cli-runner/Cargo.lock": first_party_lock_fixture(),
        "unrelated/Cargo.lock": unrelated_lock,
    }
    assert (
        check_first_party_lock_inventory(
            coherent_first_party_locks,
            required_locks,
            "0.13.0",
            revision_a,
            revision_b,
        )
        == "0.13.0"
    )
    invalid_first_party_locks = (
        (
            {
                **coherent_first_party_locks,
                "cli-runner/Cargo.lock": first_party_lock_fixture(
                    ay_revision=revision_c
                ),
            },
            "stale standalone AY revision",
        ),
        (
            {
                **coherent_first_party_locks,
                "cli-runner/Cargo.lock": first_party_lock_fixture(
                    ay_version="0.12.0"
                ),
            },
            "stale standalone AY version",
        ),
        (
            {
                **coherent_first_party_locks,
                "cli-runner/Cargo.lock": first_party_lock_fixture(
                    ty_revision=revision_c
                ),
            },
            "stale standalone Ty revision",
        ),
        (
            {
                **coherent_first_party_locks,
                "cli-runner/Cargo.lock": first_party_lock_fixture(
                    ty_version="0.12.0"
                ),
            },
            "split standalone tla-core version",
        ),
        (
            {"Cargo.lock": first_party_lock_fixture()},
            "missing standalone first-party lock",
        ),
    )
    for lock_texts, description in invalid_first_party_locks:
        try:
            check_first_party_lock_inventory(
                lock_texts,
                required_locks,
                "0.13.0",
                revision_a,
                revision_b,
            )
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
        contract_revision = check_contract_declaration(
            root_manifest, bool(autoform_manifest)
        )
        ay_version, ay_revision, ty_revision = check_first_party_manifest_pins(
            root_manifest
        )
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

    try:
        lock_paths = tracked_lock_paths()
        if ROOT_LOCK not in lock_paths:
            raise BoundaryViolation("Cargo.lock is not tracked")
        lock_texts = {
            str(lock_path.relative_to(ROOT)): lock_path.read_text()
            for lock_path in lock_paths
        }
        trust_ir_revision = check_trust_ir_lock_inventory(
            lock_texts,
            str(ROOT_LOCK.relative_to(ROOT)) if autoform_manifest else None,
        )
        check_contract_lock_revision(
            root_manifest,
            bool(autoform_manifest),
            trust_ir_revision,
        )
        if contract_revision is None:
            raise BoundaryViolation(
                "crystal A2 producer requires the workspace trust-ir-contract authority"
            )
        check_crystal_a2_producer(
            CRYSTAL_A2_MANIFEST.read_text(),
            lock_texts.get(str(CRYSTAL_A2_LOCK.relative_to(ROOT))),
            contract_revision,
        )
        check_crystal_a2_locked_metadata()
        tla_core_version = check_first_party_lock_inventory(
            lock_texts,
            {
                str(ROOT_LOCK.relative_to(ROOT)),
                str(CLI_RUNNER_LOCK.relative_to(ROOT)),
            },
            ay_version,
            ay_revision,
            ty_revision,
        )
    except (
        OSError,
        KeyError,
        TypeError,
        subprocess.CalledProcessError,
        BoundaryViolation,
    ) as error:
        fail(str(error))

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

    print(
        "Clean dependency boundary is closed through trust-ir-contract; "
        f"one TrustIR lock source={trust_ir_revision or 'absent'}; "
        f"AY {ay_version}@{ay_revision}; "
        f"{TY_DEPENDENCY_NAME} {tla_core_version}@{ty_revision}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
