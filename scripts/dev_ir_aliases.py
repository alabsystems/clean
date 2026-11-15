#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Validate explicit dev-only IR aliases before projecting production pins.

The declaration is not a waiver for a revision: Cargo's resolved graph must
show that every excluded package is unreachable through normal/build edges
from every workspace member, and reachable through a declared dev alias.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
from pathlib import Path

from resource_transport import resource_fds

try:
    import tomllib
except ModuleNotFoundError:
    import tomli as tomllib

IR_URL = "https://github.com/alabsystems/trust-ir.git"
SOURCE = re.compile(r"git\+" + re.escape(IR_URL) + r"\?rev=([0-9a-f]{40})#([0-9a-f]{40})$")


class DevAliasError(ValueError):
    pass


def ir_name(name: str) -> bool:
    return isinstance(name, str) and (name == "trust-ir" or name.startswith("trust-ir-"))


def dependency_tables(doc: dict):
    for kind in ("dependencies", "build-dependencies", "dev-dependencies"):
        yield kind, doc.get(kind, {})
    for target in doc.get("target", {}).values():
        for kind in ("dependencies", "build-dependencies", "dev-dependencies"):
            yield kind, target.get(kind, {})


def declared_aliases(manifests: dict[str, str]) -> dict[str, tuple[str, str]]:
    try:
        root = tomllib.loads(manifests.get("Cargo.toml", ""))
    except tomllib.TOMLDecodeError as error:
        raise DevAliasError(f"root manifest is not valid TOML: {error}") from error
    ws = root.get("workspace", {})
    try:
        names = ws.get("metadata", {}).get("clean", {}).get("dev-only-ir-aliases", [])
    except AttributeError as error:
        raise DevAliasError("workspace.metadata.clean must be a table") from error
    if not isinstance(names, list) or any(not isinstance(x, str) for x in names) or len(set(names)) != len(names):
        raise DevAliasError("dev-only-ir-aliases must be a list of distinct dependency aliases")
    if not names:
        return {}
    if len({name.replace("-", "_") for name in names}) != len(names):
        raise DevAliasError("dev-only IR aliases must have distinct Cargo crate names")
    aliases = {}
    for name in names:
        dep = ws.get("dependencies", {}).get(name)
        if not isinstance(dep, dict) or dep.get("git") != IR_URL or not ir_name(dep.get("package", "")):
            raise DevAliasError(f"dev alias {name} must name an exact shared IR package")
        rev = dep.get("rev", "")
        if not isinstance(rev, str) or re.fullmatch(r"[0-9a-f]{40}", rev) is None:
            raise DevAliasError(f"dev alias {name} must have an exact IR revision")
        if any(key in dep for key in ("path", "branch", "tag")):
            raise DevAliasError(f"dev alias {name} has an ambiguous source")
        aliases[name] = (dep["package"], rev)
    consumed = set()
    for path, text in manifests.items():
        try:
            doc = tomllib.loads(text)
        except tomllib.TOMLDecodeError as error:
            raise DevAliasError(f"{path}: invalid manifest: {error}") from error
        for kind, table in dependency_tables(doc):
            for alias in aliases.keys() & table.keys():
                dep = table[alias]
                if kind != "dev-dependencies" or not isinstance(dep, dict) or dep.get("workspace") is not True:
                    raise DevAliasError(f"{path}: {alias} must be a workspace dev-dependency")
                if any(key in dep for key in ("git", "rev", "path", "package", "branch", "tag")):
                    raise DevAliasError(f"{path}: {alias} overrides the declared dev-only source")
                consumed.add(alias)
    if aliases.keys() - consumed:
        raise DevAliasError("unconsumed dev-only IR aliases: " + ", ".join(sorted(aliases.keys() - consumed)))
    return aliases


def _revision(source: str | None) -> str:
    match = SOURCE.fullmatch(source or "")
    if match is None or match[1] != match[2]:
        raise DevAliasError(f"IR source is not an exact canonical Git revision: {source!r}")
    return match[1]


def excluded_packages(manifests: dict[str, str], metadata: dict) -> set[tuple[str, str, str]]:
    aliases = declared_aliases(manifests)
    packages = {p["id"]: p for p in metadata["packages"]}
    nodes = {n["id"]: n for n in metadata["resolve"]["nodes"]}
    members = set(metadata["workspace_members"])
    if not members or not members <= packages.keys() or not members <= nodes.keys():
        raise DevAliasError("resolved workspace membership is incomplete")

    def edges(node: str):
        for edge in nodes[node]["deps"]:
            if edge["pkg"] not in packages or edge["pkg"] not in nodes or not edge.get("dep_kinds"):
                raise DevAliasError("resolved dependency edge is incomplete")
            yield edge

    def runtime_closure(roots):
        seen, pending = set(), list(roots)
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            pending.extend(edge["pkg"] for edge in edges(current)
                           if any(kind.get("kind") != "dev" for kind in edge["dep_kinds"]))
        return seen

    production = runtime_closure(members)
    production_revs = {_revision(packages[p].get("source")) for p in production if ir_name(packages[p]["name"])}
    if len(production_revs) != 1:
        raise DevAliasError("production dependency graph splits IR revisions: " + ", ".join(sorted(production_revs)))
    production_rev = next(iter(production_revs))
    permitted, seen_aliases = set(), set()
    for member in members:
        try:
            relative = Path(packages[member]["manifest_path"]).relative_to(metadata["workspace_root"]).as_posix()
            member_doc = tomllib.loads(manifests[relative])
        except (KeyError, ValueError) as error:
            raise DevAliasError("resolved workspace member has no inspected manifest") from error
        declared_here = {alias for kind, table in dependency_tables(member_doc)
                         if kind == "dev-dependencies" for alias in aliases if alias in table}
        for edge in edges(member):
            if not any(kind.get("kind") == "dev" for kind in edge["dep_kinds"]):
                continue
            # Cargo normalizes extern crate names, including renamed aliases.
            alias = next((name for name in aliases if name.replace("-", "_") == edge["name"]), None)
            closure = runtime_closure([edge["pkg"]])
            foreign = {p for p in closure if ir_name(packages[p]["name"])
                       and _revision(packages[p].get("source")) != production_rev}
            if alias is None:
                if foreign:
                    raise DevAliasError(f"undeclared dev edge {edge['name']} reaches a second IR revision")
                continue
            if alias not in declared_here:
                raise DevAliasError(f"resolved dev alias {alias} is not declared by {relative}")
            package, rev = aliases[alias]
            head = packages[edge["pkg"]]
            if head["name"] != package or _revision(head.get("source")) != rev:
                raise DevAliasError(f"dev alias {alias} resolves to a different package or revision")
            if any(kind.get("kind") != "dev" for kind in edge["dep_kinds"]):
                raise DevAliasError(f"dev alias {alias} also has a runtime/build edge")
            if any(_revision(packages[p].get("source")) != rev for p in foreign):
                raise DevAliasError(f"dev alias {alias} has an incoherent IR dependency closure")
            permitted.update(foreign)
            seen_aliases.add(alias)
    if aliases.keys() != seen_aliases:
        raise DevAliasError("declared dev aliases are missing from the resolved graph")
    foreign_all = {p for p in packages if ir_name(packages[p]["name"])
                   and _revision(packages[p].get("source")) != production_rev}
    if foreign_all != permitted or foreign_all & production:
        raise DevAliasError("second IR revision is undeclared or reachable in production")
    return {(packages[p]["name"], packages[p]["version"], packages[p]["source"]) for p in permitted}


def project_lock(text: str, excluded: set[tuple[str, str, str]]) -> str:
    parts = re.split(r"(?m)(?=^\[\[package\]\]\s*$)", text)
    out, found = [], set()
    for part in parts:
        rows = tomllib.loads(part).get("package", [])
        key = None
        if rows:
            row = rows[0]
            key = (row["name"], row["version"], row.get("source"))
        if key in excluded:
            found.add(key)
        else:
            out.append(part)
    if found != excluded:
        raise DevAliasError("resolved dev-only IR packages disagree with the root lock")
    return "".join(out)


def production_locks(root: Path, manifests: dict[str, str], locks: dict[str, str], targo: str | None = None) -> dict[str, str]:
    """Return a validation-only projection; never rewrite any manifest or lock."""
    if not declared_aliases(manifests):
        return locks
    if targo is None:
        result = subprocess.run(["bash", str(root / "scripts/rust_frontend.sh"), "--targo"],
                                cwd=root, capture_output=True, check=False,
                                pass_fds=resource_fds(os.environ))
        if result.returncode or not os.fsdecode(result.stdout).strip():
            raise DevAliasError("cannot select Targo for dev-alias dependency resolution")
        targo = os.fsdecode(result.stdout).removesuffix("\n")
    result = subprocess.run([targo, "metadata", "--locked", "--all-features", "--format-version", "1"],
                            cwd=root, capture_output=True, text=True, check=False,
                            pass_fds=resource_fds(os.environ))
    if result.returncode:
        raise DevAliasError("cannot resolve dev-alias dependency graph: " + result.stderr[-1200:])
    try:
        excluded = excluded_packages(manifests, json.loads(result.stdout))
        projected = dict(locks)
        projected["Cargo.lock"] = project_lock(locks["Cargo.lock"], excluded)
        return projected
    except (KeyError, TypeError, json.JSONDecodeError) as error:
        raise DevAliasError(f"malformed resolved dev-alias dependency graph: {error}") from error
