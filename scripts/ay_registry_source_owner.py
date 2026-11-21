# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Explicit registry source admission for AY's actual system dependencies.

The selected AY object owns the request and registry checksums. Actual archive
bytes own the dependency declarations. Only named nix 0.29.0, its
cfg_aliases 0.2.1 build dependency and wait-timeout 0.2.1 may enter.
This is source-graph validation, not a compiler, proof or resource authority.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import io
from pathlib import Path, PurePosixPath
import re
import tarfile
from ay_package_version import is_ay_028_patch
try:
    import tomllib
except ModuleNotFoundError:
    from pip._vendor import tomli as tomllib

NAME = "nix"
VERSION = "0.29.0"
SELECTION = NAME + "@" + VERSION
REUSED_NAME = "cfg_aliases"
REUSED_VERSION = "0.2.1"
REUSED_SELECTION = REUSED_NAME + "@" + REUSED_VERSION
WAIT_NAME = "wait-timeout"
WAIT_VERSION = "0.2.1"
WAIT_SELECTION = WAIT_NAME + "@" + WAIT_VERSION
REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"


class OwnerError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise OwnerError("AY registry source owner: " + message)


@dataclass(frozen=True)
class Owner:
    ay_revision: str
    name: str
    version: str
    checksum: str
    declarations: dict[str, list[dict]]
    required: frozenset[str]


def from_ay(authority, selected, cargo_home):
    require(len(set(selected)) == len(selected)
            and bool(set(selected) & {SELECTION, WAIT_SELECTION})
            and set(selected) <= {SELECTION, REUSED_SELECTION, WAIT_SELECTION}
            and (REUSED_SELECTION not in selected or SELECTION in selected),
            "requires named system dependency admissions; cfg_aliases requires nix")
    workspace = authority.read("Cargo.toml").get("workspace", {})
    version = workspace.get("package", {}).get("version")
    require(is_ay_028_patch(version)
            and "crates/ay-sys" in workspace.get("members", []),
            "requires the actual AY 0.28 workspace member")
    system = authority.read("crates/ay-sys/Cargo.toml")
    require(system.get("package", {}).get("name") == "ay-sys"
            and system["package"].get("version") in (version, {"workspace": True}),
            "requires the actual ay-sys member")
    if SELECTION in selected:
        dep = workspace.get("dependencies", {}).get(NAME)
        require(isinstance(dep, dict) and set(dep) == {"version", "default-features", "features"}
                and dep["version"] == "0.29" and dep["default-features"] is False
                and dep["features"] == ["process", "signal", "term"],
                "unexpected immutable AY workspace nix dependency")
        require(system.get("target", {}).get("cfg(unix)", {}).get("dependencies", {}).get(NAME)
                    == {"workspace": True}, "requires the actual ay-sys Unix nix dependency")
    if WAIT_SELECTION in selected:
        require(workspace.get("dependencies", {}).get(WAIT_NAME) == WAIT_VERSION
                and system.get("dependencies", {}).get(WAIT_NAME) == {"workspace": True},
                "requires the actual ay-sys primary wait-timeout dependency")
    result = {}
    for selection in selected:
        name, version = selection.split("@")
        result[name, version] = _read_source(authority, cargo_home, name, version)
    return result


def _read_source(authority, cargo_home, name, version):
    locked = authority.read("Cargo.lock").get("package", [])
    rows = [row for row in locked if row.get("name") == name and row.get("version") == version
            and row.get("source") == REGISTRY]
    require(len(rows) == 1 and isinstance(rows[0].get("checksum"), str)
            and re.fullmatch(r"[0-9a-f]{64}", rows[0]["checksum"]) is not None,
            "missing immutable selected AY registry checksum")
    checksum = rows[0]["checksum"]
    archives = list((Path(cargo_home) / "registry/cache").glob(f"index.crates.io-*/{name}-{version}.crate"))
    require(len(archives) == 1 and archives[0].is_file() and not archives[0].is_symlink(),
            "requires one actual canonical registry source archive")
    with archives[0].open("rb") as source:
        data = source.read(4 * 1024 * 1024 + 1)
    require(len(data) <= 4 * 1024 * 1024 and hashlib.sha256(data).hexdigest() == checksum,
            "registry archive disagrees with immutable AY checksum")
    manifest = None
    count, total = 0, 0
    with tarfile.open(fileobj=io.BytesIO(data), mode="r|gz") as archive:
        for member in archive:
            path = PurePosixPath(member.name)
            count += 1
            total += member.size
            require(count <= 1024 and total <= 16 * 1024 * 1024
                    and bool(path.parts) and not path.is_absolute() and ".." not in path.parts
                    and path.parts[0] == f"{name}-{version}" and (member.isdir() or member.isreg()),
                    "unsupported registry source archive member")
            if member.name == f"{name}-{version}/Cargo.toml":
                require(manifest is None and member.isreg() and member.size <= 128 * 1024,
                        "missing or ambiguous registry manifest")
                manifest = tomllib.loads(archive.extractfile(member).read().decode())
    require(isinstance(manifest, dict) and manifest.get("package", {}).get("name") == name
            and manifest["package"].get("version") == version, "wrong actual registry package")
    declarations, required = {}, set()
    for index, container in enumerate([manifest, *manifest.get("target", {}).values()]):
        for section in ("dependencies", "build-dependencies"):
            for alias, raw in container.get(section, {}).items():
                raw = {"version": raw} if isinstance(raw, str) else raw
                require(isinstance(raw, dict) and isinstance(raw.get("version"), str)
                        and not {"git", "path", "registry", "registry-index", "workspace"}.intersection(raw),
                        "unsupported registry package dependency authority")
                dependency_name = raw.get("package", alias)
                require(isinstance(dependency_name, str) and isinstance(raw.get("optional", False), bool),
                        "malformed registry dependency")
                declarations.setdefault(dependency_name, []).append(raw)
                if index == 0 and not raw.get("optional", False):
                    required.add(dependency_name)
    if name == WAIT_NAME:
        require(manifest.get("target", {}).get("cfg(unix)", {}).get("dependencies")
                    == {"libc": {"version": "0.2.56"}}
                and set(declarations) == {"libc"},
                "unsupported actual wait-timeout dependency closure")
        required.add("libc")
    return Owner(authority.revision, name, version, checksum, declarations, frozenset(required))


def identity(row):
    return row.get("name"), row.get("version"), row.get("source")


def resolution_constraints(old_rows, new_rows, owners, matches_version):
    """Constrain only newly introduced nodes; preserve every prior owner."""
    result = []
    old_ids = {identity(row) for row in old_rows}
    for name, wanted in owners:
        if (name, wanted, REGISTRY) in old_ids:
            continue
        if name == REUSED_NAME and any(row["name"] == name for row in old_rows):
            continue
        candidates = [row for row in new_rows if row["name"] == name
                      and row.get("source") == REGISTRY and identity(row) not in old_ids]
        require(len(candidates) <= 1, "ambiguous newly introduced registry node")
        if candidates and candidates[0]["version"] != wanted:
            version = candidates[0]["version"]
            requirements = (["0.29"] if name == NAME else [WAIT_VERSION] if name == WAIT_NAME else
                [decl["version"] for decl in owners[NAME, VERSION].declarations.get(name, [])])
            require(bool(requirements) and all(matches_version(item, version) for item in requirements),
                    "proposed registry node violates the actual requesting dependency")
            result.append((name, version, wanted))
    return result


def validate_gain(old_rows, new_rows, owners, resolve, matches_version):
    allowed = {(NAME, VERSION, REGISTRY), (REUSED_NAME, REUSED_VERSION, REGISTRY),
               (WAIT_NAME, WAIT_VERSION, REGISTRY)}
    old_identities = {identity(previous) for previous in old_rows}
    gained = {identity(row): row for row in new_rows
              if identity(row) in allowed and identity(row) not in old_identities}
    for key, row in gained.items():
        owner = (owners or {}).get(key[:2])
        require(owner is not None, "new registry node requires explicit source admission")
        require(set(row) <= {"name", "version", "source", "checksum", "dependencies"}
                and row.get("checksum") == owner.checksum,
                "selected registry row differs from actual source archive")
        edges = row.get("dependencies", [])
        require(isinstance(edges, list), "malformed registry dependency array")
        selected = [resolve(edge) for edge in edges]
        require(len({identity(edge) for edge in selected}) == len(selected), "duplicate registry dependency")
        require(owner.required <= {edge["name"] for edge in selected}, "missing actual registry dependency")
        for edge in selected:
            require((identity(edge) in old_identities or identity(edge) in gained)
                    and edge.get("source") == REGISTRY,
                    "new registry node may use only existing or explicitly admitted registry identities")
            declarations = owner.declarations.get(edge["name"], [])
            require(bool(declarations) and all(matches_version(dep["version"], edge["version"])
                                             for dep in declarations),
                    "registry edge disagrees with the actual checksum-bound manifest")
        if owner.name in (NAME, WAIT_NAME):
            actual_owner = [p for p in new_rows if p["name"] == "ay-sys"
                            and any(resolve(edge) is row for edge in p.get("dependencies", []))]
            source = f"git+https://github.com/alabsystems/ay.git?rev={owner.ay_revision}#{owner.ay_revision}"
            require(len(actual_owner) == 1 and is_ay_028_patch(actual_owner[0].get("version"))
                    and actual_owner[0].get("source") == source,
                    "new registry node needs the actual selected ay-sys edge")
        else:
            nix = gained.get((NAME, VERSION, REGISTRY))
            require(nix is not None and any(resolve(edge) is row for edge in nix.get("dependencies", [])),
                    "new cfg_aliases node requires the actually gained nix build edge")
    return set(gained)
