#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Read canonical compiler metadata through fresh native Agh authority.

This authenticates source bytes, not compilation, proof or publication grades.
The pin owner separately checks manifest co-ownership before installing anything.
"""
from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess

SHA = re.compile(r"[0-9a-f]{40}\Z")
REPOSITORIES = ("alabsystems/trust-ir", "alabsystems/trust-cg")
MAIN = "refs/agh/fetched-main"


class Refusal(Exception):
    pass


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise Refusal(reason)


def git_environment() -> dict[str, str]:
    environment = dict(os.environ)
    for key in list(environment):
        if key.startswith("GIT_CONFIG") or key in {
            "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
            "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_NAMESPACE", "GIT_REPLACE_REF_BASE", "GIT_GRAFT_FILE",
            "GIT_SHALLOW_FILE", "GIT_TEMPLATE_DIR", "GIT_DEFAULT_HASH",
            "GIT_DEFAULT_REF_FORMAT",
        }:
            del environment[key]
    # Removing a config override restores defaults. Suppress them explicitly;
    # NO_REPLACE does not disable legacy graft files.
    environment.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                       GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1",
                       GIT_TERMINAL_PROMPT="0", GIT_OPTIONAL_LOCKS="0")
    return environment


class Authority:
    def __init__(self, directory: Path, repository: str, revision: str,
                 *, execute=subprocess.run):
        require(repository in REPOSITORIES, "unknown canonical repository")
        require(isinstance(revision, str) and SHA.fullmatch(revision) is not None,
                "revision must be exactly forty lowercase hex characters")
        self.git, self.agh = shutil.which("git"), shutil.which("agh")
        require(self.git is not None and self.agh is not None,
                "native Agh and Git are required; no direct network fallback")
        self.directory, self.repository, self.revision = directory, repository, revision
        self.execute = execute
        directory.mkdir(mode=0o700)
        self.run([self.git, "init", "--bare", "--quiet", "--template=", "--object-format=sha1"])
        self.run([self.agh, "repo", "fetch-main", repository, str(directory), "--blobless"])
        actual = self.run([self.git, "rev-parse", "--verify", revision + "^{commit}"])
        require(actual.decode("ascii").strip() == revision, "different selected commit")
        self.run([self.git, "merge-base", "--is-ancestor", revision, MAIN])

    def run(self, arguments: list[str]) -> bytes:
        result = self.execute(arguments, cwd=self.directory, env=git_environment(),
                              stdout=subprocess.PIPE, check=False)
        require(result.returncode == 0, f"authority command refused ({result.returncode}): {arguments[1]}")
        require(isinstance(result.stdout, bytes), "authority transport must preserve raw bytes")
        return result.stdout

    def entry(self, path: str) -> str | None:
        require(path in {"Cargo.toml", "Targo.toml"}, "unsupported authority manifest path")
        raw = self.run([self.git, "ls-tree", "-z", self.revision, "--", path])
        entries = [entry for entry in raw.split(b"\0") if entry]
        if not entries:
            return None
        require(len(entries) == 1, "ambiguous authority manifest")
        header, separator, name = entries[0].partition(b"\t")
        fields = header.split()
        require(separator and name == path.encode("ascii") and len(fields) == 3
                and fields[0] in {b"100644", b"100755"} and fields[1] == b"blob"
                and re.fullmatch(rb"[0-9a-f]{40}", fields[2]) is not None,
                "authority manifest is not an exact regular blob")
        return fields[2].decode("ascii")

    def manifest(self) -> bytes:
        require(self.entry("Targo.toml") is None, "unsupported Targo manifest precedence")
        oid = self.entry("Cargo.toml")
        require(oid is not None, "missing authority Cargo.toml")
        data = self.run([self.agh, "cat", f"{self.repository}@{self.revision}:Cargo.toml"])
        require(len(data) <= 32 * 1024 * 1024, "authority manifest exceeds byte limit")
        header = b"blob " + str(len(data)).encode("ascii") + b"\0"
        require(hashlib.sha1(header + data).hexdigest() == oid,
                "authority bytes differ from the authenticated Git blob")
        return data


def prepare(directory: Path, manifest: Path, ir: str, cg: str) -> None:
    require(not manifest.exists() and not manifest.is_symlink(), "manifest output already exists")
    for revision in (ir, cg):
        require(isinstance(revision, str) and SHA.fullmatch(revision) is not None,
                "revision must be exactly forty lowercase hex characters")
    directory.mkdir(mode=0o700)
    Authority(directory / "trust-ir", REPOSITORIES[0], ir)
    backend = Authority(directory / "trust-cg", REPOSITORIES[1], cg)
    data = backend.manifest()
    with manifest.open("xb") as output:
        output.write(data)
    for repository, revision in zip(REPOSITORIES, (ir, cg)):
        print(f"native Agh main contains {repository}@{revision}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--trust-ir", required=True)
    parser.add_argument("--trust-cg", required=True)
    args = parser.parse_args()
    try:
        prepare(args.directory, args.manifest, args.trust_ir, args.trust_cg)
    except (Refusal, OSError, UnicodeError) as error:
        parser.exit(1, f"REFUSED: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
