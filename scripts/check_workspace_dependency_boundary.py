#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Fail closed if Clean crosses a workspace boundary or splits first-party pins."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # Python 3.10 and older.
    import tomli as tomllib

# The WS6.5 leg table: every trust-ir / trust-cg declaration by file, the two
# lockfiles each is recorded in, and the coherence test that binds them. Lives
# beside this gate so scripts/bump-trust-ir-pin.sh and this leg judge one
# shape; imported by path so the gate runs from any working directory.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import trust_ir_pin_legs  # noqa: E402
import check_ay_updates as ay_pins  # noqa: E402
import dev_ir_aliases  # noqa: E402
import ay_exec_policy_owner as exec_policy  # noqa: E402
from resource_transport import resource_fds  # noqa: E402


ROOT = Path(__file__).resolve().parent.parent
ROOT_MANIFEST = ROOT / "Cargo.toml"
ROOT_LOCK = ROOT / "Cargo.lock"
CLI_RUNNER_LOCK = ROOT / "cli-runner/Cargo.lock"
BENCH_RUNNER_LOCK = ROOT / "bench-runner/Cargo.lock"
REALTELEM_HARNESS_LOCK = ROOT / "realtelem-harness/Cargo.lock"
TELEMETRY_HARNESS_LOCK = ROOT / "telemetry-harness/Cargo.lock"
REQUIRED_TY_LOCKS = (ROOT_LOCK, CLI_RUNNER_LOCK)
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
AY_ROOT_LOCK_PACKAGE_NAMES = frozenset(
    {
        "ay",
        "ay-allsat",
        "ay-arrays",
        "ay-bv",
        "ay-chc",
        "ay-core",
        "ay-count",
        "ay-diff-logic",
        "ay-dispatch",
        "ay-dpll",
        "ay-drat-check",
        "ay-dt",
        "ay-euf",
        "ay-fp",
        "ay-frontend",
        "ay-intsat",
        "ay-jit",
        "ay-lean-bridge",
        "ay-lia",
        "ay-lra",
        "ay-map",
        "ay-milp",
        "ay-model-check",
        "ay-multiset",
        "ay-nia",
        "ay-nonlinear-common",
        "ay-nra",
        "ay-pb-core",
        "ay-prefetch",
        "ay-proof",
        "ay-proof-common",
        "ay-sat",
        "ay-sat-congruence-core",
        "ay-seq",
        "ay-set",
        "ay-strings",
        "ay-sys",
        "ay-translate",
    }
)
AY_STANDALONE_LOCK_PACKAGE_NAMES = AY_ROOT_LOCK_PACKAGE_NAMES - {"ay-lean-bridge"}
REQUIRED_AY_LOCK_INVENTORIES = {
    ROOT_LOCK: AY_ROOT_LOCK_PACKAGE_NAMES,
    CLI_RUNNER_LOCK: AY_STANDALONE_LOCK_PACKAGE_NAMES,
    BENCH_RUNNER_LOCK: AY_STANDALONE_LOCK_PACKAGE_NAMES,
    REALTELEM_HARNESS_LOCK: AY_STANDALONE_LOCK_PACKAGE_NAMES,
    TELEMETRY_HARNESS_LOCK: AY_STANDALONE_LOCK_PACKAGE_NAMES,
}
AY_REPOSITORY = "https://github.com/alabsystems/ay.git"
TY_DEPENDENCY_NAME = "tla-core"
TY_REPOSITORY = "https://github.com/alabsystems/ty.git"
# An AY move lands only with clean-auto -- the one workspace crate with a
# direct AY dependency -- TESTED at the new revision. This is the one
# statement of the qualifying command; the record names the revision it was
# run at, and the dep-boundary leg refuses a tree whose AY pin the record does
# not name.
#
# The command is every clean-auto LIBRARY test under both AY features, with no
# test-name filter. `ay-bv-blast` is in it because no workspace member enables
# it: no workspace build, check or clippy compiles the modules that consume
# ay_proof's bit-blast exporter, the exporter AY's tree-sized-cap root fix
# rewrote. Only local_gate.sh's full-mode leg `ay-bv-blast-gated` runs them, on
# whatever tree it is given and bound to no AY move; this command is a superset
# of that leg's selection. There is no filter because a filter is how the first
# spelling (`-- bridge::ay_backend`, round 9b) left out `crate::proved_gate`, a
# direct consumer of the exporter and the anti-vacuity controls of the PROVED
# gate. NOT reached by this command, so NOT qualified by the record:
# clean-auto's integration tests, and clean-elab's `ay-smt` smt tactic (it
# reaches AY only through clean-auto's bridge). The round 9b review ran both
# by hand at AY 630842a8 and their tests passed; nothing binds them to an AY
# move.
AY_CONSUMER_QUALIFICATION = ROOT / "data/ay_consumer_qualification.json"
AY_CONSUMER_QUALIFICATION_SCHEMA = "clean.ay-consumer-qualification/v1"
AY_CONSUMER_QUALIFICATION_COMMAND = (
    "targo --unverified test --locked -p clean-auto "
    "--features carcara-verify,ay-bv-blast --lib"
)
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


FRONTEND = ROOT / "scripts/rust_frontend.sh"


def resolve_targo() -> str:
    """The targo this gate runs, from `scripts/rust_frontend.sh --targo`.

    Never `targo` from PATH: `~/.cargo/bin/targo` is a rustup symlink, targo
    refuses to run as one, and until 2026-09-29 this leg was RED on every tree
    for a pusher whose PATH put `~/.cargo/bin` first and GREEN for one whose
    PATH did not. The frontend holds the one rule (an explicit `$TARGO`, else
    `$(rustc +trust --print sysroot)/bin/targo`); a refusal is a failure here."""
    try:
        result = subprocess.run(
            ["bash", str(FRONTEND), "--targo"],
            cwd=ROOT,
            capture_output=True,
            check=False,
            pass_fds=resource_fds(os.environ),
        )
    except (OSError, RuntimeError) as error:
        raise BoundaryViolation(
            f"cannot run {FRONTEND.relative_to(ROOT)} --targo: {error}"
        ) from error
    targo = os.fsdecode(result.stdout).removesuffix("\n")
    if result.returncode != 0 or not targo.strip():
        raise BoundaryViolation(
            f"no targo to run: {FRONTEND.relative_to(ROOT)} --targo exited "
            f"{result.returncode}: {' '.join(os.fsdecode(result.stderr).split())}"
        )
    return targo


def workspace_manifest_paths(root: Path = ROOT) -> list[Path]:
    root = root.resolve()
    tracked = subprocess.run(
        ["git", "ls-files", "-z", "--", "Cargo.toml", "*/Cargo.toml"],
        cwd=root, capture_output=True, check=True,
    )
    manifests = {
        (root / os.fsdecode(name)).resolve()
        for name in tracked.stdout.split(b"\0") if name
    }
    for directory, child_dirs, files in os.walk(root):
        child_dirs[:] = sorted(
            child for child in child_dirs if child not in EXCLUDED_MANIFEST_DIRS
            # macOS build-output relocation: target -> target.noindex. Exclude
            # only this ROOT directory, not arbitrary *.noindex source trees.
            and not (Path(directory) == root and child == "target.noindex")
        )
        if "Cargo.toml" in files:
            manifests.add((Path(directory) / "Cargo.toml").resolve())

    # A directory exclusion must never hide tracked or declared source. Include
    # explicit/glob workspace members and then close over in-repo path edges,
    # including Cargo's automatically included path-dependency members.
    workspace = tomllib.loads((root / "Cargo.toml").read_text()).get("workspace", {})
    members = workspace.get("members", [])
    if not isinstance(members, list) or any(not isinstance(m, str) for m in members):
        raise BoundaryViolation("workspace members must be a list of path patterns")
    for member in members:
        directories = list(root.glob(member))
        if not directories:
            raise BoundaryViolation(f"workspace member pattern matches nothing: {member}")
        for directory in directories:
            manifest = (directory / "Cargo.toml").resolve()
            if not manifest.is_relative_to(root):
                raise BoundaryViolation(f"workspace member escapes Clean: {member}")
            if not manifest.is_file():
                raise BoundaryViolation(f"workspace member has no Cargo.toml: {member}")
            manifests.add(manifest)
    pending = list(manifests)
    while pending:
        manifest = pending.pop()
        if not manifest.is_relative_to(root):
            raise BoundaryViolation(f"tracked manifest escapes Clean: {manifest}")
        for line in manifest.read_text().splitlines():
            if line.lstrip().startswith("#"):
                continue
            for match in PATH_DECLARATION.finditer(line):
                dependency = (manifest.parent / match.group(1) / "Cargo.toml").resolve()
                # External paths are refused by check_manifest_boundaries; do
                # not walk other repositories. File-valued bin/lib paths are
                # not package manifests. Canonical identities stop alias cycles.
                if (
                    dependency.is_relative_to(root)
                    and dependency.is_file()
                    and dependency not in manifests
                ):
                    manifests.add(dependency)
                    pending.append(dependency)
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
    # Clean may itself be a Trust submodule, with ../trust pointing to the
    # enclosing workspace. Ownership by the actual Clean root is more specific
    # than that ancestor. Resolve first so an outward symlink still refuses.
    if candidate.is_relative_to(root.resolve()):
        return False
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
    required_ay_inventories: dict[str, frozenset[str]],
    required_ty_contexts: set[str],
    ay_version: str,
    ay_revision: str,
    ty_revision: str,
) -> str:
    """Bind AY and Ty in every tracked lock to the root manifest's epoch.

    Every standalone consumer resolves AY without ay-lean-bridge; the root
    resolves the complete AY graph. The root and CLI consumer also resolve Ty,
    unlike the standalone clean-auto harnesses. Require each authority-bearing
    lock's exact AY package roster while still rejecting stale first-party
    sources in every tracked lock.
    """

    missing = (set(required_ay_inventories) | required_ty_contexts).difference(
        lock_texts
    )
    if missing:
        raise BoundaryViolation(
            "required first-party locks are not tracked: " + ", ".join(sorted(missing))
        )

    tla_core_versions: dict[str, str] = {}
    ay_graph_generations: set[bool] = set()
    for context, lock_text in sorted(lock_texts.items()):
        try:
            packages = tomllib.loads(lock_text).get("package")
        except tomllib.TOMLDecodeError as error:
            raise BoundaryViolation(f"{context} is not valid TOML") from error
        if not isinstance(packages, list):
            raise BoundaryViolation(f"{context} has no package inventory")
        try:
            vendor = exec_policy.locked_identity(packages, ay_revision, ay_version)
        except exec_policy.OwnerError as error:
            raise BoundaryViolation(f"{context}: {error}") from error

        ay_packages: list[dict] = []
        ty_packages: list[dict] = []
        for package in packages:
            if not isinstance(package, dict):
                continue
            name = package.get("name")
            source = package.get("source")
            is_ay_package = isinstance(name, str) and (
                name == "ay" or name.startswith("ay-")
            )
            is_ay_source = isinstance(source, str) and source.startswith(
                f"git+{AY_REPOSITORY}"
            )
            if is_ay_package != is_ay_source:
                if is_ay_source and exec_policy.identity(package) == vendor:
                    continue
                raise BoundaryViolation(
                    f"{context} package {name or '<unknown>'} does not use the "
                    "canonical AY Git source"
                )
            if is_ay_source:
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
            elif isinstance(source, str) and source.startswith(
                f"git+{TY_REPOSITORY}"
            ):
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

        expected_ay_names = required_ay_inventories.get(context)
        if expected_ay_names is not None:
            legacy_ay_names = expected_ay_names
            try:
                expected_ay_names = ay_pins.ay_lock_package_names(packages, expected_ay_names)
            except ay_pins.PinEvidenceError as error:
                raise BoundaryViolation(f"{context}: {error}") from error
            if "ay-dpll" in legacy_ay_names:
                ay_graph_generations.add("ay-cdclt" in expected_ay_names)
            ay_names = [str(package["name"]) for package in ay_packages]
            actual_ay_names = set(ay_names)
            duplicate_ay_names = sorted(
                name for name in actual_ay_names if ay_names.count(name) > 1
            )
            if (
                actual_ay_names != expected_ay_names
                or len(actual_ay_names) != len(ay_names)
            ):
                raise BoundaryViolation(
                    f"{context} AY package inventory does not match the audited "
                    f"graph: missing={sorted(expected_ay_names - actual_ay_names)}, "
                    f"unexpected={sorted(actual_ay_names - expected_ay_names)}, "
                    f"duplicates={duplicate_ay_names}"
                )
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
        if context in required_ty_contexts and len(direct_ty) != 1:
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
    if len(ay_graph_generations) > 1:
        raise BoundaryViolation("tracked locks split the reviewed AY package inventory generations")
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


def check_ay_consumer_qualification(record_text: str | None, ay_revision: str) -> None:
    """The AY the tree pins must be the AY its consumer qualification names.

    The record is evidence the pusher wrote (the counts the command printed),
    not a re-run: this leg cannot run a ten-minute test on every push. What it
    refuses is an AY move that lands with no qualification at the new
    revision, or with a failing or empty one, or with one run by a command
    other than `AY_CONSUMER_QUALIFICATION_COMMAND`."""
    where = str(AY_CONSUMER_QUALIFICATION.relative_to(ROOT))
    how = (
        f"run `{AY_CONSUMER_QUALIFICATION_COMMAND}` at the pinned AY (under "
        "`scripts/heavy_gate.sh run 12`) and record its counts in " + where
    )
    if record_text is None:
        raise BoundaryViolation(f"AY consumer qualification: {where} is missing; {how}")
    try:
        record = json.loads(record_text)
    except json.JSONDecodeError as error:
        raise BoundaryViolation(
            f"AY consumer qualification: {where} is not JSON: {error}"
        ) from error
    if not isinstance(record, dict) or record.get("schema") != AY_CONSUMER_QUALIFICATION_SCHEMA:
        raise BoundaryViolation(
            f"AY consumer qualification: {where} is not a "
            f"{AY_CONSUMER_QUALIFICATION_SCHEMA} record"
        )
    if record.get("ay_rev") != ay_revision:
        raise BoundaryViolation(
            f"AY consumer qualification: the tree pins AY {ay_revision} but {where} "
            f"qualifies {record.get('ay_rev')!r}; {how}"
        )
    if record.get("command") != AY_CONSUMER_QUALIFICATION_COMMAND:
        raise BoundaryViolation(
            f"AY consumer qualification: {where} was measured by "
            f"{record.get('command')!r}, not by the qualifying command; {how}"
        )
    counts = [record.get(key) for key in ("passed", "failed", "ignored")]
    if not all(type(count) is int and count >= 0 for count in counts):
        raise BoundaryViolation(
            f"AY consumer qualification: {where} needs integer passed/failed/ignored counts"
        )
    passed, failed, _ = counts
    if failed != 0 or passed == 0:
        raise BoundaryViolation(
            f"AY consumer qualification: {where} records passed={passed} failed={failed} "
            f"at AY {ay_revision}; an AY move lands only on a green, non-empty run"
        )


# Cargo's refusal when `--locked` meets a lock that would have to change. Only
# used to skip the network retry below: a verdict never rests on the wording,
# because any non-zero exit that the retry does not clear is a refusal.
LOCK_WOULD_CHANGE = "--locked was passed"


def git_pinned_lock_paths(lock_texts: dict[str, str]) -> list[str]:
    """The tracked locks that record a pinned Git source.

    Those are exactly the locks a pin transaction rewrites
    (`scripts/bump_ay_pin.py`: the root lock and the four AY-bearing satellite
    locks; `scripts/bump-trust-ir-pin.sh`: the root lock and the Crystal A2
    lock). Derived from the lock CONTENT, never from a list, so a satellite
    workspace that starts pinning a Git source is covered the day it does."""
    selected = []
    for relative, text in lock_texts.items():
        try:
            packages = tomllib.loads(text).get("package")
        except tomllib.TOMLDecodeError as error:
            raise BoundaryViolation(f"{relative} is not valid TOML") from error
        if not isinstance(packages, list):
            raise BoundaryViolation(f"{relative} has no [[package]] inventory")
        if any(
            isinstance(package, dict)
            and isinstance(package.get("source"), str)
            and package["source"].startswith("git+")
            for package in packages
        ):
            selected.append(relative)
    return sorted(selected)


def check_git_pinned_locks_resolve(
    lock_texts: dict[str, str], targo: str | None = None
) -> None:
    """Every Git-pinned lock must resolve under `targo metadata --locked`.

    With dependency RESOLUTION: `--no-deps` never resolves the graph, so
    `metadata --locked --no-deps` exits 0 on a stale lock (measured
    2026-09-30 on cli-runner/Cargo.lock, which had lacked `clean-lake`'s
    `blake3` edge since 5d756fadf; the Crystal A2 check this replaces ran that
    vacuous spelling). A stale satellite lock is not harmless: every
    `scripts/bump_ay_pin.py` run refused while that one lock was stale, so no
    AY pin could move for four days and nothing on the push path said why.

    Each lock is asked OFFLINE first, all at once. A lock Cargo refuses to
    keep is RED at once; any other offline failure (the local cache cannot
    decide) is asked again with the network allowed, still `--locked`, and
    that answer is the verdict. `targo` defaults to `resolve_targo()`; the
    self-test passes a stand-in."""

    targo = targo or resolve_targo()
    selected = git_pinned_lock_paths(lock_texts)
    if not selected:
        raise BoundaryViolation("no tracked lock records a pinned Git source")

    def command(relative: str, offline: bool) -> list[str]:
        manifest = str(Path(relative).with_name("Cargo.toml"))
        return [
            targo,
            "metadata",
            "--locked",
            *(["--offline"] if offline else []),
            "--format-version",
            "1",
            "--manifest-path",
            manifest,
        ]

    def summary(stderr: str) -> str:
        # Cargo's LAST error line is the refusal; earlier ones can be noise from
        # scanning a Git checkout's fixtures.
        lines = [line for line in stderr.splitlines() if line.startswith("error")]
        return (lines[-1] if lines else stderr.strip())[-600:]

    try:
        running = {
            relative: subprocess.Popen(
                command(relative, offline=True),
                cwd=ROOT,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                text=True,
                pass_fds=resource_fds(os.environ),
            )
            for relative in selected
        }
    except OSError as error:
        raise BoundaryViolation(f"cannot run targo metadata --locked: {error}") from error
    stale = []
    for relative, child in running.items():
        _, stderr = child.communicate()
        if child.returncode == 0:
            continue
        if LOCK_WOULD_CHANGE not in stderr:
            try:
                online = subprocess.run(
                    command(relative, offline=False),
                    cwd=ROOT,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                    text=True,
                    check=False,
                    pass_fds=resource_fds(os.environ),
                )
            except (OSError, RuntimeError) as error:
                raise BoundaryViolation(
                    f"cannot run targo metadata --locked: {error}"
                ) from error
            if online.returncode == 0:
                continue
            stderr = online.stderr
        stale.append(f"{relative}: {summary(stderr)}")
    if stale:
        raise BoundaryViolation(
            "a Git-pinned lock does not resolve under targo metadata --locked "
            "(regenerate it with `targo metadata --offline --format-version 1 "
            "--manifest-path <its Cargo.toml>`, review the diff, commit it):\n  "
            + "\n  ".join(stale)
        )


def ay_consumer_qualification_self_test() -> None:
    """Arms: the pinned AY unqualified, a failing run, an empty run, a record
    measured by another command (a filtered one included), a missing record
    and a non-record are each refused; the one well-formed green record at the
    pinned AY is accepted. First, the command itself must select every
    clean-auto library test under both AY features."""
    words = AY_CONSUMER_QUALIFICATION_COMMAND.split()

    def value_of(flag: str) -> str | None:
        at = words.index(flag) if words.count(flag) == 1 else len(words)
        return words[at + 1] if at + 1 < len(words) else None

    selects_all = (
        "--" not in words
        and "--lib" in words
        and value_of("-p") == "clean-auto"
        and {"ay-bv-blast", "carcara-verify"}
        <= set((value_of("--features") or "").split(","))
    )
    if not selects_all:
        raise AssertionError(
            "AY_CONSUMER_QUALIFICATION_COMMAND must run every clean-auto --lib test under "
            "ay-bv-blast and carcara-verify, with no test-name filter: the filtered first "
            "spelling (-- bridge::ay_backend) never ran crate::proved_gate"
        )
    revision = "a" * 40
    good = {
        "schema": AY_CONSUMER_QUALIFICATION_SCHEMA,
        "ay_rev": revision,
        "command": AY_CONSUMER_QUALIFICATION_COMMAND,
        "passed": 3,
        "failed": 0,
        "ignored": 0,
    }
    check_ay_consumer_qualification(json.dumps(good), revision)
    arms = (
        ({**good, "ay_rev": "b" * 40}, "a move that left the qualification behind"),
        ({**good, "failed": 1}, "a failing run"),
        ({**good, "passed": 0}, "an empty run"),
        ({**good, "passed": True}, "a non-integer count"),
        ({**good, "command": AY_CONSUMER_QUALIFICATION_COMMAND.replace(",ay-bv-blast", "")},
         "a run without the bit-blast lane"),
        ({**good, "schema": "clean.other/v1"}, "a foreign record"),
        ({**good, "command": AY_CONSUMER_QUALIFICATION_COMMAND + " -- bridge::ay_backend"},
         "a run filtered to bridge::ay_backend, which leaves out crate::proved_gate"),
    )
    for record, description in arms:
        try:
            check_ay_consumer_qualification(json.dumps(record), revision)
        except BoundaryViolation:
            continue
        raise AssertionError(f"AY consumer qualification accepted {description}")
    for text, description in ((None, "a missing record"), ("[", "a non-JSON record")):
        try:
            check_ay_consumer_qualification(text, revision)
        except BoundaryViolation:
            continue
        raise AssertionError(f"AY consumer qualification accepted {description}")


def git_pinned_lock_self_test() -> None:
    """The lock-resolution leg's verdicts, against a stand-in targo.

    Arms: a lock Cargo refuses to keep is RED and is never retried online; an
    offline cache miss is retried online and GREEN when that resolves, RED
    when it does not; a lock with no Git source is never asked; and a tree
    with no Git-pinned lock is refused rather than passed vacuously."""
    git_lock = (
        'version = 4\n[[package]]\nname = "a"\nversion = "0.1.0"\n'
        'source = "git+https://example.invalid/a.git?rev=0#0"\n'
    )
    registry_lock = (
        'version = 4\n[[package]]\nname = "b"\nversion = "0.1.0"\n'
        'source = "registry+https://github.com/rust-lang/crates.io-index"\n'
    )
    with tempfile.TemporaryDirectory(prefix="clean-boundary-locks-") as temp:
        log = Path(temp) / "calls.log"
        stand_in = Path(temp) / "targo"
        stand_in.write_text(
            "#!/bin/sh\n"
            f'echo "$*" >> "{log}"\n'
            'case "$*" in\n'
            '  *stale/Cargo.toml*) echo "error: cannot update the lock file x '
            f'because {LOCK_WOULD_CHANGE} to prevent this" >&2; exit 101;;\n'
            '  *--offline*) echo "error: failed to download a" >&2; exit 101;;\n'
            '  *unreachable/Cargo.toml*) echo "error: failed to fetch a" >&2; exit 101;;\n'
            "esac\n"
            "exit 0\n"
        )
        stand_in.chmod(0o755)

        def verdict(locks: dict[str, str]) -> str | None:
            log.write_text("")
            try:
                check_git_pinned_locks_resolve(locks, str(stand_in))
            except BoundaryViolation as error:
                return str(error)
            return None

        assert verdict({"cached/Cargo.lock": git_lock, "plain/Cargo.lock": registry_lock}) is None, (
            "an offline cache miss that resolves online was refused"
        )
        calls = log.read_text()
        assert "cached/Cargo.toml" in calls and "plain/Cargo.toml" not in calls, (
            "the leg asked a lock with no Git source, or skipped a Git-pinned one"
        )
        refused = verdict({"cached/Cargo.lock": git_lock, "stale/Cargo.lock": git_lock})
        assert refused is not None and "stale/Cargo.lock" in refused, (
            "a lock Cargo refuses to keep under --locked was accepted"
        )
        assert "cached/Cargo.lock" not in refused, "a resolving lock was named stale"
        retried = [line for line in log.read_text().splitlines() if "stale/" in line]
        assert len(retried) == 1 and "--offline" in retried[0], (
            "a lock Cargo refused offline was asked again online"
        )
        refused = verdict({"unreachable/Cargo.lock": git_lock})
        assert refused is not None and "unreachable/Cargo.lock" in refused, (
            "a lock neither the offline cache nor the network resolves was accepted"
        )
        assert verdict({"plain/Cargo.lock": registry_lock}) is not None, (
            "a tree with no Git-pinned lock passed a leg that asked nothing"
        )


def manifest_discovery_self_test() -> None:
    """Exercise real discovery, Git tracking and aliases, not supplied maps."""
    with tempfile.TemporaryDirectory(prefix="clean-boundary-discovery-") as temp:
        root = Path(temp).resolve()
        subprocess.run(["git", "init", "-q", str(root)], check=True)

        def write(relative: str, text: str) -> Path:
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            return path

        forbidden = '[dependencies]\ntrust-types = "1"\n'
        write("Cargo.toml", "[workspace]\nmembers = []\n")
        write(".gitignore", "/target.noindex/\n/ignored-source/\n")
        generated = write("target.noindex/generated/Cargo.toml", forbidden)
        ordinary = write("crates/target.noindex/Cargo.toml", forbidden)
        ignored_source = write("ignored-source/Cargo.toml", forbidden)
        (root / "target").symlink_to("target.noindex", target_is_directory=True)
        found = workspace_manifest_paths(root)
        assert generated not in found, "unreferenced generated output was scanned"
        assert ordinary in found, "nested .noindex source was hidden"
        assert ignored_source in found, "Git ignore rules hid ordinary source"

        tracked = write("target.noindex/tracked/Cargo.toml", forbidden)
        subprocess.run(["git", "add", "-f", "--", str(tracked)], cwd=root, check=True)
        assert tracked in workspace_manifest_paths(root), "tracked output-path manifest was hidden"

        literal = write("target.noindex/member/Cargo.toml", forbidden)
        globbed = write("target.noindex/glob-one/Cargo.toml", forbidden)
        aliased = write("target.noindex/aliased/Cargo.toml", forbidden)
        (root / "member-alias").symlink_to("target.noindex/aliased", target_is_directory=True)
        write(
            "Cargo.toml",
            '[workspace]\nmembers = ["target.noindex/member", '
            '"target.noindex/glob-*", "member-alias"]\n',
        )
        dependency = write("target.noindex/dependency/Cargo.toml", forbidden)
        transitive = write("target.noindex/transitive/Cargo.toml", forbidden)
        write("crates/source/Cargo.toml", '[dependencies]\nbridge = { path = "../../target/dependency" }\n')
        dependency.write_text(forbidden + 'next = { path = "../transitive" }\n')
        transitive.write_text(forbidden + 'back = { path = "../dependency" }\n')
        found = workspace_manifest_paths(root)
        protected = [ordinary, ignored_source, tracked, literal, globbed, aliased, dependency, transitive]
        assert generated not in found, "generated output exclusion was lost"
        assert all(path in found for path in protected), "declared/path source was hidden"
        for manifest in protected:
            try:
                check_manifest_boundaries({manifest: manifest.read_text()}, root)
            except BoundaryViolation as error:
                assert "forbidden Trust dependency trust-types" in str(error)
            else:
                raise AssertionError(f"discovered forbidden manifest was accepted: {manifest}")
        write("Cargo.toml", '[workspace]\nmembers = ["missing-member"]\n')
        try:
            workspace_manifest_paths(root)
        except BoundaryViolation:
            pass
        else:
            raise AssertionError("unresolved declared member was silently omitted")


def pin_coherence_self_test(revision_a: str, revision_b: str) -> None:
    """The WS6.5 coherence test can fail, in both directions it was written for.

    Negative twin: the 2026-09-17 tree (3e87b95ba) -- every manifest leg and
    the root lock at the new trust-ir revision, the crystal A2 lock still at
    the old one. Mutation control: ONE hand-edited manifest leg. Each is
    refused NAMING the leg; the same fixtures with the mutation reverted pass.
    The full battery is scripts/test_bump_trust_ir_pin.py; these two arms make
    the hook leg itself demonstrably falsifiable.
    """
    url = trust_ir_pin_legs.TRUST_IR_URL
    cg_url = trust_ir_pin_legs.TRUST_CG_URL
    cg_rev = "d" * 40

    def declaration(key: str, dep_url: str, rev: str) -> str:
        return f'{key} = {{ git = "{dep_url}", rev = "{rev}" }}\n'

    def package(name: str, source: str | None) -> str:
        row = f'[[package]]\nname = "{name}"\nversion = "0.1.0"\n'
        if source is not None:
            row += f'source = "{source}"\n'
        return row + "\n"

    def git_source(dep_url: str, rev: str) -> str:
        return f"git+{dep_url}?rev={rev}#{rev}"

    def tree(ir: str, crystal_lock: str) -> tuple[dict[str, str], dict[str, str]]:
        manifests = {}
        for relative, keys in trust_ir_pin_legs.TRUST_IR_LEGS.items():
            manifests[relative] = "[dependencies]\n" + "".join(
                declaration(key, url, ir) for key in keys
            )
        for relative, keys in trust_ir_pin_legs.TRUST_CG_LEGS.items():
            manifests[relative] = manifests.get(relative, "[dependencies]\n") + "".join(
                declaration(key, cg_url, cg_rev) for key in keys
            )
        locks = {
            "Cargo.lock": "version = 4\n\n"
            + "".join(package(name, None) for name in trust_ir_pin_legs.PATCHED_CLEAN_CRATES)
            + package("trust-ir", git_source(url, ir))
            + package("trust-cg-ir", git_source(cg_url, cg_rev)),
            "scripts/crystal_a2_project/Cargo.lock": "version = 4\n\n"
            + package("trust-ir", git_source(url, crystal_lock)),
        }
        return manifests, locks

    manifests, locks = tree(revision_a, revision_a)
    assert trust_ir_pin_legs.check_pin_coherence(manifests, locks) == {
        "trust-ir": revision_a,
        "trust-cg": cg_rev,
    }

    # Negative twin: crystal lock left behind.
    manifests, locks = tree(revision_a, revision_b)
    try:
        trust_ir_pin_legs.check_pin_coherence(manifests, locks)
    except trust_ir_pin_legs.PinCoherenceError as error:
        assert "scripts/crystal_a2_project/Cargo.lock resolves trust-ir " + revision_b in str(error), error
    else:
        raise AssertionError("crystal-lock-left-behind regression was not rejected")

    # Mutation control: one hand-edited manifest leg.
    manifests, locks = tree(revision_a, revision_a)
    manifests["crates/clean-reflect/Cargo.toml"] = manifests[
        "crates/clean-reflect/Cargo.toml"
    ].replace(revision_a, revision_b)
    try:
        trust_ir_pin_legs.check_pin_coherence(manifests, locks)
    except trust_ir_pin_legs.PinCoherenceError as error:
        assert "trust-ir pin is split across manifest legs" in str(error), error
        assert f"crates/clean-reflect/Cargo.toml:trust-ir={revision_b[:12]}" in str(error), error
    else:
        raise AssertionError("hand-edited manifest leg regression was not rejected")

    # A comment that restates a pin is refused -- on one line, wrapped across
    # two, or with the id in capitals; comments that name neither, or name the
    # two in separate comment blocks, are not.
    for note in (
        "# Now: trust-cg f7476fd5 pins trust-ir 4f09dab8, every edge sits there.\n",
        "# every TrustIR edge in this workspace sits at\n# 4f09dab8 with it.\n",
        "# trust-ir is pinned at 4F09DAB8 today\n",
    ):
        manifests, _ = tree(revision_a, revision_a)
        manifests["crates/clean-auto/Cargo.toml"] = note + manifests["crates/clean-auto/Cargo.toml"]
        assert trust_ir_pin_legs.restated_pins(manifests) == [
            "crates/clean-auto/Cargo.toml:1: " + " ".join(note.split("\n")).strip()
        ], trust_ir_pin_legs.restated_pins(manifests)
    manifests, _ = tree(revision_a, revision_a)
    manifests["crates/clean-auto/Cargo.toml"] = (
        "# the redirect was removed on 2026-08-12 (93550c617)\n"
        "\n"
        "# keep the TrustIR edge at the revision this TrustCG pin selects\n"
        + manifests["crates/clean-auto/Cargo.toml"]
    )
    assert trust_ir_pin_legs.restated_pins(manifests) == []


def nested_workspace_paths_self_test() -> None:
    """Own paths remain local under the real ancestor Trust symlink layout."""
    with tempfile.TemporaryDirectory(prefix="clean-nested-boundary-") as temp:
        outer = Path(temp).resolve()
        trust = outer / "trust"
        root = trust / "first-party/clean"
        local = root / "crates/clean"
        local.mkdir(parents=True)
        (root.parent / "trust").symlink_to("..", target_is_directory=True)
        (root / "local-alias").symlink_to("crates/clean", target_is_directory=True)
        manifest = root / "Cargo.toml"
        for path in ("crates/clean", "local-alias"):
            check_manifest_boundaries(
                {manifest: f'[dependencies]\nlocal = {{ path = "{path}" }}\n'}, root
            )

        foreign = trust / "crates/trust-types"
        foreign.mkdir(parents=True)
        (root / "external-alias").symlink_to(foreign, target_is_directory=True)
        near = root.with_name("clean-other")
        near.mkdir()
        outside = outer / "outside"
        outside.mkdir()
        for target, message in (
            (foreign, "points into the Trust workspace"),
            (root / "external-alias", "points into the Trust workspace"),
            (near, "points into the Trust workspace"),
            (outside, "escapes the Clean workspace"),
        ):
            path = os.path.relpath(target, root)
            try:
                check_manifest_boundaries(
                    {manifest: f'[dependencies]\nbridge = {{ path = "{path}" }}\n'}, root
                )
            except BoundaryViolation as error:
                assert message in str(error), error
            else:
                raise AssertionError(f"escaped dependency was accepted: {path}")


def regression_self_test() -> None:
    nested_workspace_paths_self_test()
    manifest_discovery_self_test()
    git_pinned_lock_self_test()
    ay_consumer_qualification_self_test()
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

    pin_coherence_self_test(revision_a, revision_b)

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
        ay_names: tuple[str, ...] = ("ay", "ay-sat"),
        ty_version: str = "0.13.0",
        ty_revision: str = revision_b,
    ) -> str:
        ay_packages = [
            (
                "[[package]]\n"
                f'name = "{name}"\n'
                f'version = "{ay_version}"\n'
                f'source = "{first_party_source(AY_REPOSITORY, ay_revision)}"\n'
            )
            for name in ay_names
        ]
        return "\n".join(
            [
                "version = 4\n",
                *ay_packages,
                "[[package]]\n"
                f'name = "{TY_DEPENDENCY_NAME}"\n'
                f'version = "{ty_version}"\n'
                f'source = "{first_party_source(TY_REPOSITORY, ty_revision)}"\n',
            ]
        )

    required_ay_inventories = {
        context: frozenset({"ay", "ay-sat"})
        for context in (
            "Cargo.lock",
            "cli-runner/Cargo.lock",
            "bench-runner/Cargo.lock",
            "realtelem-harness/Cargo.lock",
            "telemetry-harness/Cargo.lock",
        )
    }
    required_ty_locks = {"Cargo.lock", "cli-runner/Cargo.lock"}
    coherent_first_party_locks = {
        "Cargo.lock": first_party_lock_fixture(),
        "cli-runner/Cargo.lock": first_party_lock_fixture(),
        "bench-runner/Cargo.lock": first_party_lock_fixture(),
        "realtelem-harness/Cargo.lock": first_party_lock_fixture(),
        "telemetry-harness/Cargo.lock": first_party_lock_fixture(),
        "unrelated/Cargo.lock": unrelated_lock,
    }
    assert (
        check_first_party_lock_inventory(
            coherent_first_party_locks,
            required_ay_inventories,
            required_ty_locks,
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
                "bench-runner/Cargo.lock": unrelated_lock,
            },
            "standalone clean-auto consumer without AY",
        ),
        (
            {
                **coherent_first_party_locks,
                "bench-runner/Cargo.lock": (
                    "version = 4\n\n"
                    "[[package]]\n"
                    'name = "ay"\n'
                    'version = "0.13.0"\n'
                ),
            },
            "standalone clean-auto consumer with path-sourced AY",
        ),
        (
            {
                **coherent_first_party_locks,
                "bench-runner/Cargo.lock": first_party_lock_fixture(
                    ay_names=("ay",)
                ),
            },
            "incomplete standalone AY package inventory",
        ),
        (
            {
                **coherent_first_party_locks,
                "bench-runner/Cargo.lock": first_party_lock_fixture(
                    ay_names=("ay", "ay-unexpected")
                ),
            },
            "substituted standalone AY package inventory",
        ),
        (
            {
                **coherent_first_party_locks,
                "bench-runner/Cargo.lock": first_party_lock_fixture(
                    ay_names=("ay", "ay-sat", "ay-sat")
                ),
            },
            "duplicate standalone AY package inventory",
        ),
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
            {
                context: lock
                for context, lock in coherent_first_party_locks.items()
                if context != "telemetry-harness/Cargo.lock"
            },
            "missing standalone first-party lock",
        ),
    )
    for lock_texts, description in invalid_first_party_locks:
        try:
            check_first_party_lock_inventory(
                lock_texts,
                required_ay_inventories,
                required_ty_locks,
                "0.13.0",
                revision_a,
                revision_b,
            )
        except BoundaryViolation:
            pass
        else:
            raise AssertionError(f"{description} regression was not rejected")


def workspace_metadata(targo: str) -> subprocess.CompletedProcess:
    """Run the existing locked root metadata boundary with caller transport."""
    return subprocess.run(
        [
            targo,
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
        pass_fds=resource_fds(os.environ),
    )


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
        check_ay_consumer_qualification(
            AY_CONSUMER_QUALIFICATION.read_text()
            if AY_CONSUMER_QUALIFICATION.is_file()
            else None,
            ay_revision,
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
        coherence_locks = dev_ir_aliases.production_locks(
            ROOT,
            {str(path.relative_to(ROOT)): text for path, text in manifests.items()},
            lock_texts,
        )
        trust_ir_revision = check_trust_ir_lock_inventory(
            coherence_locks,
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
        check_git_pinned_locks_resolve(lock_texts)
        # WS6.5: one trust-ir.git?rev= across every manifest leg AND both
        # lockfiles, one trust-cg.git?rev= across clean-auto and the root lock,
        # and trust-ir's clean.git pin resolved into this workspace. Refusals
        # name the leg. scripts/bump-trust-ir-pin.sh is the only sanctioned
        # writer of these legs.
        try:
            pin_revisions = trust_ir_pin_legs.check_pin_coherence(
                trust_ir_pin_legs.read_tracked(ROOT, "*Cargo.toml"), coherence_locks
            )
        except (
            trust_ir_pin_legs.PinShapeError,
            trust_ir_pin_legs.PinCoherenceError,
        ) as error:
            raise BoundaryViolation(
                "trust-ir/trust-cg pin legs are incoherent (move them only with "
                f"scripts/bump-trust-ir-pin.sh): {error}"
            ) from error
        restated = trust_ir_pin_legs.restated_pins(
            trust_ir_pin_legs.read_tracked(ROOT, "*Cargo.toml")
        )
        if restated:
            raise BoundaryViolation(
                "a manifest comment restates a trust-ir/trust-cg pin; the `rev` field "
                "is the only statement of it, and the one the bump moves:\n  "
                + "\n  ".join(restated)
            )
        if pin_revisions["trust-ir"] != trust_ir_revision:
            raise BoundaryViolation(
                f"manifest trust-ir legs declare {pin_revisions['trust-ir']} but the "
                f"tracked locks resolve {trust_ir_revision}"
            )
        tla_core_version = check_first_party_lock_inventory(
            lock_texts,
            {
                str(path.relative_to(ROOT)): inventory
                for path, inventory in REQUIRED_AY_LOCK_INVENTORIES.items()
            },
            {str(path.relative_to(ROOT)) for path in REQUIRED_TY_LOCKS},
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
        dev_ir_aliases.DevAliasError,
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
    try:
        targo = resolve_targo()
    except BoundaryViolation as error:
        fail(str(error))
    result = workspace_metadata(targo)
    if result.returncode != 0:
        sys.stderr.write(result.stderr)
        fail("locked root metadata did not close")

    print(
        "Clean dependency boundary is closed through trust-ir-contract; "
        f"one production TrustIR lock source={trust_ir_revision or 'absent'}; "
        f"trust-cg {pin_revisions['trust-cg']}; "
        f"AY {ay_version}@{ay_revision}; "
        f"{TY_DEPENDENCY_NAME} {tla_core_version}@{ty_revision}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
