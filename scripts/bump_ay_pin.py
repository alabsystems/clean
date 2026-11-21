#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Move Clean's existing AY cohort in one rollback-protected transaction.

Usage: python3 scripts/bump_ay_pin.py <40-hex-AY-revision> --targo /path/to/targo \
           [--ay-version 0.28.0] [--admit-registry-package nix@0.29.0] \
           [--admit-registry-package cfg_aliases@0.2.1] \
           [--admit-registry-package wait-timeout@0.2.1]

The explicit immutable revision is the target, never AY's current remote main.
Only Cargo.toml and the five existing AY-bearing locks are writable. Package
versions stay fixed unless the explicit reviewed 0.27.0 -> 0.28.0 migration or
a forward patch move within 0.28 is selected. Registry additions require explicit named checksum-bound source
admission. Other non-AY resolution, features, predecessor pins and patches stay fixed.
The reviewed ay-cdclt addition requires ay-dpll's immutable mandatory edge.
Cargo generates locks; this script never rewrites lock source strings.
Metadata does not compile or qualify AY/Clean. Consumer qualification, artifact
authentication, publication receipts and Git operations remain separate.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import tomllib

import check_ay_updates as pins
import check_workspace_dependency_boundary as boundary
import ay_exec_policy_owner as exec_policy
import ay_registry_source_owner as registry_owner
from ay_package_version import is_ay_028_patch, stable_version
from resource_transport import resource_fds


AY_URL = pins.AY_REPO_URL
# Versions never follow a tip. Forward patch moves require explicit selection
# and the same immutable source, graph and consumer checks as revision moves.
AY_VERSION = "0.27.0"
AY_VERSION_MIGRATION = (AY_VERSION, "0.28.0")
MANIFEST = "Cargo.toml"
LOCKS = (
    "Cargo.lock",
    "cli-runner/Cargo.lock",
    "bench-runner/Cargo.lock",
    "realtelem-harness/Cargo.lock",
    "telemetry-harness/Cargo.lock",
)
OWNED = (MANIFEST, *LOCKS)
ROSTERS = {
    path: boundary.AY_ROOT_LOCK_PACKAGE_NAMES if path == "Cargo.lock"
    else boundary.AY_STANDALONE_LOCK_PACKAGE_NAMES
    for path in LOCKS
}
REVIEWED_PACKAGES = ROSTERS["Cargo.lock"] | {"ay-cdclt"}
GUARDS = ("scripts/check_ay_updates.py", "scripts/check_workspace_dependency_boundary.py",
          "scripts/ay_exec_policy_owner.py", "scripts/ay_registry_source_owner.py",
          "scripts/ay_package_version.py")
SHA = re.compile(r"[0-9a-f]{40}\Z")
REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"


class Refusal(Exception):
    """Unsupported or failed transaction; not a compiler/proof verdict."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refusal(message)


def exact_sha(value: str) -> str:
    require(isinstance(value, str) and SHA.fullmatch(value) is not None,
            "revision must be exactly 40 lowercase hexadecimal characters")
    return value


def source(revision: str) -> str:
    return f"git+{AY_URL}?rev={revision}#{revision}"


def family(name: object) -> bool:
    return isinstance(name, str) and (name == "ay" or name.startswith("ay-"))


def document(data: bytes, label: str) -> dict:
    try:
        return tomllib.loads(data.decode("utf-8"))
    except (UnicodeError, tomllib.TOMLDecodeError) as error:
        raise Refusal(f"{label}: invalid TOML: {error}") from error


def safe_file(root: Path, relative: str) -> Path:
    path = root
    require(not Path(relative).is_absolute() and ".." not in Path(relative).parts,
            f"unsafe controlled path: {relative}")
    for component in Path(relative).parts:
        path /= component
        require(not path.is_symlink(), f"symlink in controlled path: {relative}")
    require(path.is_file(), f"missing regular file: {relative}")
    info = path.stat()
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
            f"controlled file is not singly linked: {relative}")
    return path


@dataclass(frozen=True)
class Snapshot:
    data: bytes
    mode: int


def snapshot(root: Path, paths=OWNED) -> dict[str, Snapshot]:
    return {relative: Snapshot(path.read_bytes(), stat.S_IMODE(path.stat().st_mode))
            for relative in paths for path in [safe_file(root, relative)]}


def unchanged(root: Path, expected: dict[str, Snapshot]) -> None:
    require(snapshot(root, expected) == expected, "transaction input bytes or modes changed")


def install(root: Path, relative: str, data: bytes, mode: int, *, recovery=False) -> None:
    if recovery:
        path = root
        for component in Path(relative).parts[:-1]:
            path /= component
            require(not path.is_symlink() and path.is_dir(), f"unsafe recovery parent: {relative}")
        path /= Path(relative).name
        require(not path.is_dir() or path.is_symlink(), f"recovery target is a directory: {relative}")
    else:
        path = safe_file(root, relative)
    descriptor, temporary = tempfile.mkstemp(prefix=".ay-pin-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as output:
            output.write(data)
            output.flush()
            os.fchmod(output.fileno(), mode)
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def restore(root: Path, before: dict[str, Snapshot]) -> None:
    errors = []
    for relative, saved in before.items():
        try:
            install(root, relative, saved.data, saved.mode, recovery=True)
        except BaseException as error:
            errors.append(f"{relative}: {type(error).__name__}: {error}")
    require(not errors, "ROLLBACK INCOMPLETE: " + "; ".join(errors))
    unchanged(root, before)


class Commands:
    """Same explicit frontend/child-stop discipline as the compiler pin transaction."""

    def __init__(self, root: Path, targo: Path, ay_checkout_cache: Path | None = None):
        self.root, self.targo = root, targo
        self.ay_checkout_cache = ay_checkout_cache
        self.git = shutil.which("git")
        require(self.git is not None, "Git is required")

    def run(self, argv, *, cwd, git=False, allowed=(0,)) -> str:
        environment = dict(os.environ)
        if git:
            for key in list(environment):
                if key.startswith("GIT_CONFIG") or key in {
                    "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                    "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                    "GIT_NAMESPACE", "GIT_REPLACE_REF_BASE",
                }:
                    del environment[key]
            environment["GIT_NO_REPLACE_OBJECTS"] = "1"
            environment["GIT_TERMINAL_PROMPT"] = "0"
        child = subprocess.Popen(argv, cwd=cwd, env=environment, text=True,
                                 stdout=subprocess.PIPE, start_new_session=True,
                                 pass_fds=resource_fds(environment))
        try:
            output, _ = child.communicate()
        except BaseException:
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait(timeout=5)
            raise
        require(child.returncode in allowed, f"command failed ({child.returncode}): {' '.join(argv)}")
        return output or ""

    def git_run(self, args, *, cwd=None, allowed=(0,)) -> str:
        return self.run([self.git, *args], cwd=cwd or self.root, git=True, allowed=allowed)

    def agh_run(self, args, *, cwd) -> str:
        agh = shutil.which("agh")
        require(agh is not None, "Agh is required for immutable AY source reads")
        return self.run([agh, *args], cwd=cwd, git=True)

    def frontend(self, args) -> str:
        # Metadata is a noncompiling subcommand: no --unverified flag or Cargo fallback.
        return self.run([str(self.targo), *args], cwd=self.root)


def clean_owned(commands: Commands) -> None:
    commands.git_run(["ls-files", "--error-unmatch", "--", *OWNED])
    status = commands.git_run(["status", "--porcelain=v1", "--untracked-files=all", "--", *OWNED])
    require(not status, "owned AY pin files are dirty; resolve them before retrying")


def protected_inputs(commands: Commands) -> dict[str, Snapshot]:
    paths = commands.git_run(["ls-files", "-z", "--", "*Cargo.toml", "*Cargo.lock", *GUARDS]).split("\0")
    names = {path for path in paths if path}
    mandatory = set(OWNED) | set(GUARDS) | {str(PurePosixPath(lock).with_name(MANIFEST)) for lock in LOCKS}
    require(mandatory <= names, "tracked transaction input inventory is incomplete")
    inputs = snapshot(commands.root, sorted(names - set(OWNED)))
    for relative, saved in inputs.items():
        if relative.endswith("Cargo.lock"):
            require(not any(family(row["name"]) or row.get("source", "").startswith("git+" + AY_URL)
                            for row in packages(saved.data, relative)),
                    f"unsupported AY-bearing lock outside six-file transaction: {relative}")
    return inputs


@contextmanager
def exclusive(commands: Commands):
    raw = commands.git_run(["rev-parse", "--git-path", "ay-pin-transaction.lock"]).strip()
    require(bool(raw), "Git did not resolve the transaction lock path")
    path = Path(raw)
    if not path.is_absolute():
        path = commands.root / path
    require(all(not parent.is_symlink() for parent in path.parents), "symlink in lock parent")
    # Clean requires the same portable atomic-mkdir discipline as heavy_gate.
    # A stale directory is a refusal, never authority to remove another holder.
    try:
        path.mkdir(mode=0o700)
    except FileExistsError as error:
        raise Refusal("another AY pin transaction owns this checkout (or a stale lock needs review)") from error
    held = path.stat()
    try:
        yield
    finally:
        require(all(not parent.is_symlink() for parent in path.parents), "transaction lock parent changed")
        now = path.lstat()
        require(stat.S_ISDIR(now.st_mode) and (held.st_dev, held.st_ino) == (now.st_dev, now.st_ino),
                "transaction lock identity changed; preserve it for review")
        path.rmdir()


class Authority:
    """Exact remote commit in a private object store; no sibling HEAD authority."""

    def __init__(self, commands: Commands, directory: Path, revision: str):
        self.commands, self.directory, self.revision = commands, directory, exact_sha(revision)
        self._documents = {}
        directory.mkdir()
        commands.git_run(["init", "--bare", "--quiet"], cwd=directory)
        rewrites = commands.git_run(["config", "--get-regexp", r"^url\..*\.insteadof$"],
                                    cwd=directory, allowed=(0, 1))
        for line in rewrites.splitlines():
            fields = line.split(None, 1)
            require(len(fields) == 2 and not AY_URL.startswith(fields[1]),
                    "Git URL rewrite would substitute AY remote authority")
        commands.git_run(["remote", "add", "origin", AY_URL], cwd=directory)
        fetch = ["repo", "fetch", "alabsystems/ay", str(directory),
                 "--ref", revision, "--into", "refs/agh/pin-authority", "--checkout-closure"]
        cache = getattr(commands, "ay_checkout_cache", None)
        if cache is not None:
            fetch.extend(["--checkout-cache", str(cache)])
        commands.agh_run(fetch, cwd=directory)
        actual = commands.git_run(["rev-parse", "--verify", "refs/agh/pin-authority^{commit}"],
                                  cwd=directory).strip()
        require(actual == revision, "AY remote resolved a different commit")

    def read(self, relative: str) -> dict:
        doc = self.read_optional(relative)
        require(doc is not None, f"missing immutable manifest: {relative}")
        return doc

    def read_optional(self, relative: str) -> dict | None:
        # Only an empty exact ls-tree result means absent. A malformed object,
        # symlink, directory, Git failure, or invalid TOML must remain a refusal.
        require(isinstance(relative, str) and bool(relative)
                and re.fullmatch(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*", relative) is not None
                and not any(part in (".", "..") for part in relative.split("/")),
                "unsafe immutable object path")
        if relative in self._documents:
            return self._documents[relative]
        tree = self.commands.git_run(["ls-tree", "-z", self.revision, "--", relative], cwd=self.directory)
        entries = [entry for entry in tree.split("\0") if entry]
        if not entries:
            self._documents[relative] = None
            return None
        require(len(entries) == 1, f"missing/ambiguous immutable manifest: {relative}")
        header, separator, path = entries[0].partition("\t")
        fields = header.split()
        require(separator and path == relative and len(fields) == 3
                and fields[0] in ("100644", "100755") and fields[1] == "blob"
                and SHA.fullmatch(fields[2]) is not None,
                f"immutable manifest is not a regular blob: {relative}")
        raw = self.commands.git_run(["show", f"{self.revision}:{relative}"], cwd=self.directory)
        doc = document(raw.encode(), f"{self.revision}:{relative}")
        self._documents[relative] = doc
        return doc


@dataclass(frozen=True)
class Current:
    revision: str
    version: str
    ty_revision: str


def packages(data: bytes, label: str) -> list[dict]:
    rows = document(data, label).get("package")
    require(isinstance(rows, list) and bool(rows) and all(isinstance(row, dict) for row in rows),
            f"{label}: missing package inventory")
    identities = [(row.get("name"), row.get("version"), row.get("source")) for row in rows]
    require(all(isinstance(name, str) and isinstance(version, str)
                and (identity is None or isinstance(identity, str)) for name, version, identity in identities),
            f"{label}: invalid package identity")
    require(len(set(identities)) == len(identities), f"{label}: duplicate package identity")
    return rows


def current(root: Path, files: dict[str, Snapshot]) -> Current:
    # The existing validators own the seven declarations and reviewed inventories.
    unchanged(root, files)
    try:
        evidence = pins.read_pin_evidence(root)
        version, revision, ty_revision = boundary.check_first_party_manifest_pins(files[MANIFEST].data.decode())
        boundary.check_first_party_lock_inventory(
            {path: files[path].data.decode() for path in LOCKS}, ROSTERS,
            {"Cargo.lock", "cli-runner/Cargo.lock"}, version, revision, ty_revision)
    except (pins.PinEvidenceError, boundary.BoundaryViolation, UnicodeError) as error:
        raise Refusal(str(error)) from error
    exact_sha(revision)
    require(evidence.ay_dependency_rev == revision, "AY validators disagree")
    require(version == AY_VERSION or is_ay_028_patch(version),
            "AY package-version migration requires separate review")
    doc = document(files[MANIFEST].data, MANIFEST)
    for url, table in doc.get("patch", {}).items():
        require(not pins._is_ay_git_url(url) and not any(
            pins._dependency_mentions_ay(name, dep) for name, dep in table.items()),
            "root patch redirects AY authority")
    for name, dep in doc.get("replace", {}).items():
        require(not pins._dependency_mentions_ay(name.split(":", 1)[0], dep),
                "root replacement redirects AY authority")
    for name in pins.AY_MANIFEST_KEYS:
        require(not {"branch", "tag", "path"}.intersection(doc["workspace"]["dependencies"][name]),
                f"{name}: mutable/mixed AY selectors")
    for path in LOCKS:
        packages(files[path].data, path)
    return Current(revision, version, ty_revision)


@dataclass(frozen=True)
class Target:
    revision: str
    version: str
    declarations: dict[str, dict[str, list[dict]]]
    required: dict[str, set[str]]
    package_names: frozenset[str] = ROSTERS["Cargo.lock"]
    exec_policy: bool = False
    registry_owners: dict[tuple[str, str], registry_owner.Owner] | None = None


def unused_vendor_declaration(authority: Authority, excludes: list[str], package_name: str,
                              resolved: str, optional: bool) -> str:
    """Validate an unselected excluded vendor; never admit its effective graph.

    AY declares its CLI-only VeriPB package even with CLI features off. The
    immutable declaration is readable authority, while validate_graph and
    validate_metadata still refuse any foreign AY-source package activation.
    """
    require(optional and not family(package_name),
            f"unreviewed required vendor dependency: {package_name}")
    require(resolved in excludes and resolved.startswith("vendor/")
            and all(part not in ("", ".", "..") for part in resolved.split("/")),
            f"vendor dependency is not an explicit excluded root: {package_name}")
    require(authority.read_optional(resolved + "/Targo.toml") is None,
            f"alternate vendor Targo authority: {package_name}")
    doc = authority.read(resolved + "/Cargo.toml")
    package = doc.get("package")
    require(isinstance(package, dict) and package.get("name") == package_name
            and "workspace" not in package and isinstance(doc.get("workspace"), dict),
            f"vendor package has no matching explicit workspace owner: {package_name}")
    version = package.get("version")
    require(isinstance(version, str)
            and re.fullmatch(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)", version) is not None,
            f"vendor package needs an explicit stable version: {package_name}")
    return version


def selected_version(state: Current, requested: str | None) -> str:
    version = state.version if requested is None else requested
    previous, selected = stable_version(state.version), stable_version(version)
    require(state.version == AY_VERSION or is_ay_028_patch(state.version),
            "unsupported current AY package version")
    patch_forward = (is_ay_028_patch(state.version) and is_ay_028_patch(version)
                     and selected >= previous)
    require(version == state.version or (state.version, version) == AY_VERSION_MIGRATION
            or patch_forward,
            "unsupported AY package-version migration")
    require(version == AY_VERSION or is_ay_028_patch(version), "unsupported AY target package version")
    return version


def target(commands: Commands, directory: Path, state: Current, revision: str,
           version: str | None = None, admit_registry: tuple[str, ...] = ()) -> Target:
    version = selected_version(state, version)
    authority = Authority(commands, directory / "ay", revision)
    workspace = authority.read(MANIFEST).get("workspace", {})
    require(isinstance(workspace, dict) and isinstance(workspace.get("package"), dict)
            and workspace["package"].get("version") == version,
            "target AY package version differs; select its reviewed --ay-version explicitly")
    members = workspace.get("members")
    excludes = workspace.get("exclude", [])
    literal = lambda path: isinstance(path, str) and re.fullmatch(
        r"[A-Za-z0-9_-]+(?:/[A-Za-z0-9_-]+)*", path) is not None
    require(isinstance(members, list) and bool(members) and all(literal(path) for path in members)
            and len(set(members)) == len(members),
            "target AY workspace requires unique literal member paths")
    require(isinstance(excludes, list) and all(literal(path) for path in excludes)
            and len(set(excludes)) == len(excludes),
            "target AY workspace requires unique literal exclusion paths")
    checked_directories = set()

    def check_directory(directory: str) -> None:
        if directory in checked_directories:
            return
        alternate = posixpath.join(directory, "Targo.toml")
        require(authority.read_optional(alternate) is None,
                f"alternate immutable Targo manifest is unsupported: {alternate}")
        checked_directories.add(directory)

    check_directory("")
    catalog = {}
    for member in members:
        require(not any(member == path or member.startswith(path + "/") for path in excludes),
                f"target AY workspace member is excluded: {member}")
        check_directory(member)
        relative = member + "/Cargo.toml"
        doc = authority.read(relative)
        package = doc.get("package")
        require(isinstance(package, dict) and "workspace" not in doc and "workspace" not in package,
                f"{relative}: member-owned or explicit package.workspace is unsupported")
        name = package.get("name")
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None
                and name not in catalog, "ambiguous target package catalog")
        # Root membership does not override nearer implicit ownership. Refuse
        # intervening workspaces and owner redirects rather than guessing how
        # their inherited versions/dependencies would be resolved by Targo.
        parent = posixpath.dirname(member)
        while parent:
            check_directory(parent)
            ancestor_path = posixpath.join(parent, MANIFEST)
            ancestor = authority.read_optional(ancestor_path)
            if ancestor is not None:
                owner = ancestor.get("package", ancestor.get("project", {}))
                require("workspace" not in ancestor and isinstance(owner, dict)
                        and "workspace" not in owner,
                        f"{relative}: intermediate manifest changes workspace ownership: {ancestor_path}")
            parent = posixpath.dirname(parent)
        catalog[name] = (relative, doc)
    declarations, required = {}, {}
    has_exec_policy = False
    selected = ROSTERS["Cargo.lock"] | ({"ay-cdclt"} if "ay-cdclt" in catalog else set())
    if "ay-cdclt" in catalog:
        require(catalog["ay-cdclt"][0] == "crates/ay-cdclt/Cargo.toml",
                "target ay-cdclt is not the reviewed workspace package")
    for name in selected:
        require(name in catalog, f"target AY does not define admitted package {name}")
        relative, doc = catalog[name]
        package_version = doc["package"].get("version")
        require(package_version in (version, {"workspace": True}), f"target {name} version differs")
        declarations[name], required[name] = {}, set()
        containers = [doc, *doc.get("target", {}).values()]
        for container in containers:
            for section in ("dependencies", "build-dependencies"):
                for alias, raw in container.get(section, {}).items():
                    raw = {"version": raw} if isinstance(raw, str) else raw
                    require(isinstance(raw, dict), f"{name}: malformed dependency {alias}")
                    optional = raw.get("optional", False)
                    require(isinstance(optional, bool), f"{name}: malformed optional dependency")
                    inherited = raw.get("workspace") is True
                    dep = workspace.get("dependencies", {}).get(alias) if inherited else raw
                    dep = {"version": dep} if isinstance(dep, str) else dep
                    require(isinstance(dep, dict), f"{name}: unresolved workspace dependency {alias}")
                    package_name = dep.get("package", alias)
                    require(isinstance(package_name, str), f"{name}: malformed dependency package")
                    if "path" in dep:
                        if not family(package_name):
                            require(not {"git", "rev", "tag", "branch"}.intersection(dep),
                                    f"{name}: mixed vendor path dependency authority")
                            path = dep["path"]
                            require(isinstance(path, str) and not PurePosixPath(path).is_absolute()
                                    and "\\" not in path, f"{name}: invalid vendor dependency path")
                            resolved = posixpath.normpath(posixpath.join(
                                "" if inherited else posixpath.dirname(relative), path))
                            if package_name == exec_policy.NAME:
                                require(name == "ay-sys" and alias == exec_policy.NAME
                                        and container is doc.get("target", {}).get('cfg(target_os = "macos")')
                                        and section == "dependencies",
                                        "exec-policy needs the actual ay-sys macOS dependency")
                                try:
                                    vendor_version = exec_policy.immutable_version(
                                        authority, excludes, package_name, resolved, optional)
                                except exec_policy.OwnerError as error:
                                    raise Refusal(str(error)) from error
                                has_exec_policy = True
                                required[name].add(package_name)
                            else:
                                vendor_version = unused_vendor_declaration(
                                    authority, excludes, package_name, resolved, optional)
                            declarations[name].setdefault(package_name, []).append(
                                {"git": AY_URL, "rev": revision, "version": vendor_version})
                            continue
                        # AY's CLI-only optional packages are declared even when
                        # Clean never resolves them. Validate their immutable
                        # ownership without admitting them to the lock roster;
                        # validate_graph still rejects any such activation.
                        require(package_name in catalog and family(package_name)
                                and (package_name in REVIEWED_PACKAGES or optional),
                                f"{name}: path dependency escapes AY package authority: {package_name}")
                        require(not {"git", "rev", "tag", "branch"}.intersection(dep),
                                f"{name}: mixed path dependency authority")
                        path = dep["path"]
                        require(isinstance(path, str) and not PurePosixPath(path).is_absolute()
                                and "\\" not in path, f"{name}: invalid dependency path")
                        resolved = posixpath.normpath(posixpath.join("" if inherited else posixpath.dirname(relative), path))
                        require(resolved + "/Cargo.toml" == catalog[package_name][0],
                                f"{name}: wrong path for AY package {package_name}")
                        require(catalog[package_name][1]["package"].get("version")
                                in (version, {"workspace": True}),
                                f"target {package_name} version differs")
                        dep = {"git": AY_URL, "rev": revision, "version": version}
                    elif family(package_name):
                        raise Refusal(f"{name}: AY dependency is not an owning-workspace path")
                    elif "git" in dep:
                        require(not {"path", "branch", "tag"}.intersection(dep), f"{name}: mutable Git dependency")
                        exact_sha(dep.get("rev", ""))
                    else:
                        require(not {"registry", "registry-index", "rev", "branch", "tag"}.intersection(dep)
                                and isinstance(dep.get("version"), str), f"{name}: unsupported registry authority")
                    declarations[name].setdefault(package_name, []).append(dep)
                    # Platform-specific and optional edges may be absent; they never authorize an unlisted edge.
                    if container is doc and not optional:
                        required[name].add(package_name)
    active = "ay-cdclt" in required["ay-dpll"]
    require(not active or "ay-cdclt" in declarations,
            "target ay-dpll requires missing ay-cdclt")
    names = ROSTERS["Cargo.lock"] | ({"ay-cdclt"} if active else set())
    require(not has_exec_policy or is_ay_028_patch(version),
            "independent exec-policy source owner requires the reviewed AY 0.28 patch line")
    registry_owners = None
    if admit_registry:
        try:
            registry_owners = registry_owner.from_ay(authority, admit_registry,
                Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo"))))
        except registry_owner.OwnerError as error:
            raise Refusal(str(error)) from error
    return Target(revision, version, declarations, required, names, has_exec_policy, registry_owners)


def rewritten(files: dict[str, Snapshot], state: Current, revision: str,
              version: str | None = None) -> dict[str, bytes]:
    exact_sha(revision)
    version = selected_version(state, version)
    text = files[MANIFEST].data.decode()
    for name in pins.AY_MANIFEST_KEYS:
        matches = list(re.finditer(rf'(?m)^{re.escape(name)}\s*=\s*\{{[^\n}}]*\}}[^\n]*$', text))
        require(len(matches) == 1, f"{name}: expected one inline declaration")
        match = matches[0]
        replacement, count = re.subn(rf'\brev\s*=\s*"{state.revision}"', f'rev = "{revision}"', match[0])
        require(count == 1, f"{name}: ambiguous revision")
        replacement, count = re.subn(rf'\bversion\s*=\s*"{re.escape(state.version)}"',
                                    f'version = "{version}"', replacement)
        require(count == 1, f"{name}: ambiguous version")
        text = text[:match.start()] + replacement + text[match.end():]
    expected = document(files[MANIFEST].data, MANIFEST)
    for name in pins.AY_MANIFEST_KEYS:
        expected["workspace"]["dependencies"][name]["rev"] = revision
        expected["workspace"]["dependencies"][name]["version"] = version
    require(document(text.encode(), MANIFEST) == expected, "rewrite changed non-AY manifest authority")
    return {MANIFEST: text.encode()}


def package_index(rows: list[dict]) -> dict[str, list[dict]]:
    result = {}
    for row in rows:
        result.setdefault(row["name"], []).append(row)
    return result


def resolve_edge(raw: str, rows: dict[str, list[dict]], label: str) -> dict:
    require(isinstance(raw, str), f"{label}: non-string dependency")
    match = re.fullmatch(r"([^ ()]+)(?: ([^ ()]+))?(?: \(([^()]+)\))?", raw)
    require(match is not None, f"{label}: malformed dependency identity")

    def source_matches(resolved):
        requested = match[3]
        if requested is None or resolved == requested:
            return True
        # Cargo's dependency disambiguator omits the precise Git fragment;
        # the selected package row retains it. Resolve that spelling to one
        # FULL row identity, never erase the commit from graph comparisons.
        # Explicit fragments, registry sources and differing rev queries do
        # not receive this abbreviation rule. Multiple matches still refuse.
        if not isinstance(resolved, str) or not requested.startswith("git+") or "#" in requested:
            return False
        base, separator, precise = resolved.rpartition("#")
        return base == requested and bool(separator) and re.fullmatch(r"[0-9a-f]{40}", precise) is not None

    selected = [row for row in rows.get(match[1], [])
                if (match[2] is None or row["version"] == match[2])
                and source_matches(row.get("source"))]
    require(len(selected) == 1, f"{label}: unresolved/ambiguous dependency {raw}")
    return selected[0]


def matches_version(requirement: str, version: str) -> bool:
    # Reuses TY's bounded stable-numeric caret/exact admission, not a second
    # general Cargo resolver. Unsupported ranges/prereleases fail closed.
    numeric = r"(0|[1-9][0-9]*)(?:\.(0|[1-9][0-9]*))?(?:\.(0|[1-9][0-9]*))?"
    requested = re.fullmatch(r"([=^]?)" + numeric, requirement) if isinstance(requirement, str) else None
    selected = re.fullmatch(numeric, version) if isinstance(version, str) else None
    require(requested is not None and selected is not None
            and all(part is not None for part in selected.groups()),
            f"unsupported version requirement/identity: {requirement!r} / {version!r}")
    parts = tuple(int(part) for part in requested.groups()[1:] if part is not None)
    lower = parts + (0,) * (3 - len(parts))
    actual = tuple(int(part) for part in selected.groups())
    if requested[1] == "=":
        require(len(parts) == 3, "partial exact version requirement is unsupported")
        return actual == lower
    pivot = next((index for index, value in enumerate(parts) if value), len(parts) - 1)
    upper = lower[:pivot] + (lower[pivot] + 1,) + (0,) * (2 - pivot)
    return lower <= actual < upper


def validate_graph(before: bytes, after: bytes, label: str, state: Current,
                   revision: str, authority: Target) -> bool:
    old_rows, new_rows = packages(before, label), packages(after, label)
    require(authority.revision == revision
            and selected_version(state, authority.version) == authority.version,
            "wrong target authority")
    target_names = authority.package_names - ({"ay-lean-bridge"} if label != "Cargo.lock" else set())
    require(authority.package_names in (ROSTERS["Cargo.lock"], REVIEWED_PACKAGES),
            "unreviewed target AY package inventory")
    try:
        old_vendor = exec_policy.locked_identity(old_rows, state.revision, state.version)
        new_vendor = exec_policy.locked_identity(new_rows, revision, authority.version)
    except exec_policy.OwnerError as error:
        raise Refusal(f"{label}: {error}") from error
    require(bool(new_vendor) == authority.exec_policy and (old_vendor is None or new_vendor is not None),
            f"{label}: independent exec-policy owner disagrees with immutable required edge")
    for rows, expected, version, names in ((old_rows, state.revision, state.version, None),
                                           (new_rows, revision, authority.version, target_names)):
        if names is None:
            try:
                names = pins.ay_lock_package_names(rows, ROSTERS[label])
            except pins.PinEvidenceError as error:
                raise Refusal(f"{label}: {error}") from error
        ay = [row for row in rows if family(row["name"])]
        require(len(ay) == len(names) and {row["name"] for row in ay} == names,
                f"{label}: AY roster changed or split")
        require(all(row.get("source") == source(expected) and row["version"] == version for row in ay),
                f"{label}: AY source/version differs")
        vendor = old_vendor if rows is old_rows else new_vendor
        require(all(family(row["name"]) or exec_policy.identity(row) == vendor
                    or not row.get("source", "").startswith("git+" + AY_URL)
                    for row in rows), f"{label}: foreign package under AY authority")

    old_index, new_index = package_index(old_rows), package_index(new_rows)
    try:
        gained_registry = registry_owner.validate_gain(old_rows, new_rows, authority.registry_owners,
            lambda raw: resolve_edge(raw, new_index, label), matches_version)
    except registry_owner.OwnerError as error:
        raise Refusal(f"{label}: {error}") from error

    def identity(row, remap):
        original = row.get("source", "")
        if remap and exec_policy.identity(row) == old_vendor:
            return exec_policy.NAME, exec_policy.VERSION, source(revision)
        if remap and family(row["name"]) and original == source(state.revision):
            return row["name"], authority.version, source(revision)
        return row["name"], row["version"], original

    def external(rows, index, remap):
        result = []
        for row in rows:
            vendor = old_vendor if rows is old_rows else new_vendor
            if family(row["name"]) or exec_policy.identity(row) == vendor:
                continue
            if rows is new_rows and registry_owner.identity(row) in gained_registry:
                continue
            saved = {key: value for key, value in row.items() if key != "dependencies"}
            edges = row.get("dependencies", [])
            require(isinstance(edges, list), f"{label}: malformed external dependencies")
            selected = [identity(resolve_edge(edge, index, label), remap) for edge in edges]
            require(len(set(selected)) == len(selected), f"{label}: duplicate external dependency identity")
            saved["dependencies"] = sorted(selected)
            result.append(saved)
        return sorted(result,
                      key=lambda row: (row["name"], row["version"], row.get("source", "")))

    old_external = external(old_rows, old_index, True)
    new_external = external(new_rows, new_index, False)
    if old_external != new_external:
        removed = [row for row in old_external if row not in new_external]
        added = [row for row in new_external if row not in old_external]
        raise Refusal(f"{label}: non-AY resolution changed; "
                      f"removed={json.dumps(removed, sort_keys=True)}; "
                      f"added={json.dumps(added, sort_keys=True)}")
    old_meta, new_meta = document(before, label), document(after, label)
    old_meta.pop("package")
    new_meta.pop("package")
    require(old_meta == new_meta, f"{label}: lock metadata changed")
    for row in new_rows:
        if not family(row["name"]):
            continue
        name = row["name"]
        require(set(row) <= {"name", "version", "source", "dependencies"}, f"{label}: unexpected AY package metadata")
        edges = row.get("dependencies", [])
        require(isinstance(edges, list) and all(isinstance(edge, str) for edge in edges)
                and len(set(edges)) == len(edges), f"{label}: malformed/duplicate AY edges")
        selected = [resolve_edge(edge, new_index, label) for edge in edges]
        require(len({identity(edge, False) for edge in selected}) == len(selected), f"{label}: duplicate selected AY edge")
        require(authority.required[name] <= {edge["name"] for edge in selected}, f"{name}: missing required target dependency")
        for edge in selected:
            declarations = authority.declarations[name].get(edge["name"], [])
            require(bool(declarations), f"{name}: dependency absent from immutable target: {edge['name']}")
            # Lock rows do not identify the selected alias/platform condition.
            # Every same-package declaration must admit it; do not borrow a
            # weaker optional alias to excuse a conflicting requirement.
            for dep in declarations:
                require(edge.get("source") == (f"git+{dep['git']}?rev={dep['rev']}#{dep['rev']}"
                                                if "git" in dep else REGISTRY),
                        f"{name}: dependency source differs from immutable target: {edge['name']}")
                if "version" in dep:
                    require(matches_version(dep["version"], edge["version"]),
                            f"{name}: dependency version violates immutable target: {edge['name']}")
    return gained_registry


def validate_metadata(raw: str, lock: bytes, label: str, revision: str) -> None:
    try:
        metadata = json.loads(raw)
    except (ValueError, TypeError) as error:
        raise Refusal(f"{label}: malformed frontend metadata") from error
    rows = metadata.get("packages") if isinstance(metadata, dict) else None
    require(isinstance(rows, list) and all(isinstance(row, dict) for row in rows), f"{label}: missing effective graph")
    locked = packages(lock, label)
    ay_versions = {row["version"] for row in locked if family(row["name"])}
    require(len(ay_versions) == 1, f"{label}: missing or split AY versions")
    try:
        vendor = exec_policy.locked_identity(locked, revision, next(iter(ay_versions)))
    except exec_policy.OwnerError as error:
        raise Refusal(f"{label}: {error}") from error
    require(all(family(row.get("name")) or exec_policy.identity(row) == vendor
                or not str(row.get("source", "")).startswith("git+" + AY_URL)
                for row in rows), f"{label}: foreign effective package under AY source")
    ay = [row for row in rows if family(row.get("name")) or exec_policy.identity(row) == vendor]
    expected = {(row["name"], row["version"], row["source"]) for row in locked
                if family(row["name"]) or exec_policy.identity(row) == vendor}
    actual = [(row.get("name"), row.get("version"), row.get("source")) for row in ay]
    require(all(all(isinstance(value, str) for value in identity) for identity in actual),
            f"{label}: malformed effective AY identity")
    require(len(actual) == len(expected) and set(actual) == expected
            and all(identity[2] == source(revision) for identity in actual), f"{label}: effective AY graph overrides selected lock")


def transaction(root: Path, revision: str, commands: Commands,
                version: str | None = None, admit_registry: tuple[str, ...] = ()) -> None:
    exact_sha(revision)
    with exclusive(commands):
        clean_owned(commands)
        before = snapshot(root)
        inputs = protected_inputs(commands)
        state = current(root, before)
        version = selected_version(state, version)
        with tempfile.TemporaryDirectory(prefix="clean-ay-authority-") as temporary:
            authority = target(commands, Path(temporary), state, revision, version, admit_registry)
        require((authority.revision, authority.version) == (revision, version),
                "immutable target does not match selected revision/version")
        staged = rewritten(before, state, revision, version)
        clean_owned(commands)
        unchanged(root, before)
        unchanged(root, inputs)
        backup = Path(tempfile.mkdtemp(prefix="clean-ay-recovery-"))
        retain_backup = False
        try:
            for relative, saved in before.items():
                path = backup / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("wb") as output:
                    output.write(saved.data)
                    output.flush()
                    os.fchmod(output.fileno(), saved.mode)
                    os.fsync(output.fileno())
            install(root, MANIFEST, staged[MANIFEST], before[MANIFEST].mode)
            # Even a same-revision request checks the immutable target and all five
            # effective locked graphs; it is not an unconditional early success.
            for lock in LOCKS:
                manifest = str(root / Path(lock).with_name(MANIFEST))
                args = ["metadata", "--format-version", "1", "--manifest-path", manifest]
                if revision == state.revision and version == state.version:
                    args.append("--locked")
                commands.frontend(args)
                if authority.registry_owners:
                    original_rows = packages(before[lock].data, lock)
                    proposed = packages(safe_file(root, lock).read_bytes(), lock)
                    try:
                        constraints = registry_owner.resolution_constraints(original_rows, proposed,
                            authority.registry_owners, matches_version)
                    except registry_owner.OwnerError as error:
                        raise Refusal(str(error)) from error
                    for name, previous, wanted in constraints:
                        commands.frontend(["update", "--manifest-path", manifest, "-p",
                                           name + "@" + previous, "--precise", wanted])
            after = snapshot(root)
            require(after[MANIFEST].data == staged[MANIFEST], "resolver changed staged manifest")
            require(all(after[path].mode == before[path].mode for path in OWNED), "resolver changed owned modes")
            selected = current(root, after)
            require(selected == Current(revision, version, state.ty_revision), "installed authority differs")
            gained_registry = set()
            for lock in LOCKS:
                gained_registry |= validate_graph(before[lock].data, after[lock].data, lock,
                                                   state, revision, authority)
                raw = commands.frontend(["metadata", "--locked", "--format-version", "1", "--manifest-path",
                                         str(root / Path(lock).with_name(MANIFEST))])
                validate_metadata(raw, after[lock].data, lock, revision)
            require(set(admit_registry) <= {name + "@" + version for name, version, _ in gained_registry},
                    "named registry admission gains its package in no lock")
            unchanged(root, after)
            unchanged(root, inputs)
        except BaseException as error:
            try:
                restore(root, before)
            except BaseException as recovery:
                retain_backup = True
                raise Refusal(f"{recovery}; original-byte recovery files: {backup}; original failure: {error}") from error
            print("AY transaction failed; restored all six original files and modes.", file=sys.stderr)
            raise
        finally:
            if not retain_backup:
                shutil.rmtree(backup)
    print(f"AY graph selected at {version}@{revision}; six files coherent; Git index untouched. "
          "No compiler, proof, consumer qualification or publication receipt was produced.")
    if revision != state.revision:
        # The move lands only with its consumers tested at the new revision; the
        # dep-boundary leg holds that rule, and states the command once.
        print(f"Before this lands: `{boundary.AY_CONSUMER_QUALIFICATION_COMMAND}` "
              f"(under build-slot and a measured scripts/heavy_gate.sh reservation), recorded for AY {revision} in "
              f"{boundary.AY_CONSUMER_QUALIFICATION.relative_to(boundary.ROOT)}; "
              "the dep-boundary leg refuses the move until then.")


def selected_targo(raw: str) -> Path:
    path = Path(raw)
    executable = "targo.exe" if os.name == "nt" else "targo"
    require(path.is_absolute() and os.path.normcase(path.name) == executable,
            f"--targo must be an absolute path named {executable}")
    require(path.is_file() and os.access(path, os.X_OK), "selected Targo is not executable")
    resolved = path.resolve()
    require(os.path.normcase(resolved.name) == executable, "selected Targo resolves to a different executable name")
    return resolved


def interrupted(signum, _frame):
    raise InterruptedError(f"AY pin transaction interrupted by signal {signum}")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("revision", help="explicit immutable AY commit; never follows remote main")
    parser.add_argument("--targo", required=True, help="explicit operational frontend; caller authenticates it")
    parser.add_argument("--ay-version",
                        help="explicit stable forward patch version (or reviewed 0.27.0 -> 0.28.0); omitted preserves current")
    parser.add_argument("--ay-checkout-cache", type=Path,
                        help="optional existing absolute Git object DATA hint; native source authentication is unchanged")
    parser.add_argument("--admit-registry-package", action="append", default=[],
                        choices=[registry_owner.SELECTION, registry_owner.REUSED_SELECTION,
                                 registry_owner.WAIT_SELECTION],
                        help="explicit checksum-bound registry node required by AY's system edges")
    args = parser.parse_args(argv)
    previous = signal.signal(signal.SIGTERM, interrupted)
    try:
        root = Path(__file__).resolve().parent.parent
        if args.ay_checkout_cache is not None:
            require(args.ay_checkout_cache.is_absolute() and args.ay_checkout_cache.is_dir(),
                    "AY checkout cache must be an existing absolute directory")
        transaction(root, exact_sha(args.revision), Commands(root, selected_targo(args.targo), args.ay_checkout_cache),
                    args.ay_version, tuple(args.admit_registry_package))
        return 0
    except (Refusal, OSError, KeyboardInterrupt) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 1
    finally:
        signal.signal(signal.SIGTERM, previous)


if __name__ == "__main__":
    raise SystemExit(main())
