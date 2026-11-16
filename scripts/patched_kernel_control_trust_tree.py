#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The scratch Trust tree of P3's Trust leg (`scripts/patched_kernel_control_trust.py`): each
`first-party/*` gitlink filled from a complete local repository that holds the pinned
commit, never a partial clone, with nothing fetched (`GIT_NO_LAZY_FETCH=1`), and the
copy-on-write clone the mutant tree is made from."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import patched_kernel_control as p3  # noqa: E402

ROOT = p3.ROOT
CLEAN_GITLINK = "first-party/clean"
NO_FETCH = {**os.environ, "GIT_NO_LAZY_FETCH": "1"}


def fail(message: str) -> None:
    print(f"patched_kernel_control_trust: {message}", file=sys.stderr)
    raise SystemExit(1)


def run(*args: str) -> str:
    out = subprocess.run(list(args), capture_output=True, text=True, env=NO_FETCH)
    if out.returncode != 0:
        fail(f"`{' '.join(args)}` exited {out.returncode}: {out.stderr.strip()}")
    return out.stdout


def is_partial_clone(repo: Path) -> bool:
    probe = subprocess.run(["git", "-C", str(repo), "config", "--get-regexp", r"^remote\..*\.(promisor|partialclonefilter)$"],
                           capture_output=True, text=True, env=NO_FETCH)
    return bool(probe.stdout.strip())


def has_commit(repo: Path, sha: str) -> bool:
    if not (repo / ".git").exists() or is_partial_clone(repo):
        return False
    probe = subprocess.run(["git", "-C", str(repo), "cat-file", "-e", f"{sha}^{{commit}}"], capture_output=True, env=NO_FETCH)
    return probe.returncode == 0


def gitlinks(trust: Path, sha: str) -> dict[str, str]:
    links = {}
    for line in run("git", "-C", str(trust), "ls-tree", sha, "first-party/").splitlines():
        meta, path = line.split("\t", 1)
        mode, kind, commit = meta.split()
        if mode == "160000" and kind == "commit":
            links[path] = commit
    if CLEAN_GITLINK not in links:
        fail(f"Trust {sha} has no {CLEAN_GITLINK} gitlink")
    return links


def source_for(path: str, commit: str, trust: Path, named: dict[str, list[Path]] | None = None) -> tuple[Path, bool]:
    """A complete local repository holding `commit`, and whether `--gitlink-source`
    named it. The usual places come first; a named repository is held to the
    same rules (not a partial clone, the commit present). Nothing is fetched."""
    name = path.removeprefix("first-party/")
    usual = list(dict.fromkeys(repo.resolve() for repo in ([ROOT] if path == CLEAN_GITLINK else []) + [trust / path, ROOT.parent / name, trust.parent / name]))
    chosen = (named or {}).get(path, [])
    extra = [repo for repo in chosen if repo not in usual]
    for repo in usual + extra:
        if has_commit(repo, commit):
            # Marked whenever it was named, even where a usual place is the same directory.
            return repo, repo in chosen
    fail(f"no complete local repository holds {path} at {commit} (looked in {', '.join(map(str, usual + extra))}; partial clones are skipped)")
    raise AssertionError


def named_sources(specs: list[str]) -> dict[str, list[Path]]:
    """`--gitlink-source first-party/<name>=DIR`, repeatable."""
    named: dict[str, list[Path]] = {}
    for spec in specs:
        path, sep, directory = spec.partition("=")
        if not sep or not path.startswith("first-party/") or not directory:
            fail(f"--gitlink-source wants first-party/<name>=DIR, not {spec!r}")
        named.setdefault(path, []).append(Path(directory).resolve())
    return named


def shown_path(repo: Path, trust: Path) -> str:
    """Where a source came from, without a machine-specific prefix."""
    if repo == ROOT:
        return "this repository"
    return os.path.relpath(repo, trust.parent)


def extract(repo: Path, commit: str, dest: Path) -> None:
    """`commit` of `repo` into `dest`, every file stamped now (`tar -m`)."""
    dest.mkdir(parents=True, exist_ok=True)
    pack = subprocess.Popen(["git", "-C", str(repo), "archive", "--format=tar", commit], stdout=subprocess.PIPE, env=NO_FETCH)
    unpack = subprocess.Popen(["tar", "-x", "-m", "-f", "-", "-C", str(dest)], stdin=pack.stdout)
    assert pack.stdout is not None
    pack.stdout.close()  # tar holds the read end; git sees EPIPE if tar dies
    if unpack.wait() != 0 or pack.wait() != 0:
        fail(f"extracting {repo} at {commit} into {dest} failed")


def clone_tree(src: Path, dest: Path) -> None:
    # APFS clone where available (copy-on-write: no data copied, writes stay
    # private to the clone); a plain copy elsewhere.
    if subprocess.run(["cp", "-c", "-R", str(src), str(dest)], capture_output=True).returncode != 0:
        shutil.rmtree(dest, ignore_errors=True)
        shutil.copytree(src, dest, symlinks=True)


# Trust's own pins disagree in `crates/trust-spec-temporal` (measured 2026-11-15 at Trust
# acd139f735 and 52c2d5c509): its ty pin e937bfca has tla-core's appended
# `Expr::BuiltinSet`, the workspace redirects clean-tla's tla-core edge onto that ty, and
# its Clean pin e64e4b790's clean-tla has no arm for it (E0004 at both matches below), so
# the workspace does not compile. Clean's own fix, commit 7253ee4957 ("read BuiltinSet as a
# leaf", as `NumericSet` is read), is an ancestor of e64e4b790 that the preservation merge
# above it did not carry. The scratch tree gets exactly those two arms; nothing else in
# Clean moves, and the runner refuses the day either pin makes them wrong.
TY_GITLINK = "first-party/ty"
TLA_SHIM_FILE = "crates/clean-tla/src/core_ast/tuple_pattern.rs"
TLA_SHIM_FROM = "7253ee4957501344412bf48db7e753d52f0765ff"
TLA_SHIM_ANCHORS = ["        | Expr::NumericSet(_) => expr.node.clone(),\n", "        | Expr::NumericSet(_) => {}\n"]
TY_AST = "crates/tla-core/src/ast.rs"
TY_VARIANT = "    BuiltinSet(crate::BuiltinValueSet),\n"


def shim_clean_tla(tree: Path) -> dict[str, str]:
    """Give `tree`'s clean-tla the two `Expr::BuiltinSet` arms of Clean's 7253ee4957, refusing
    when Trust's Clean pin already has them or its ty pin lacks the variant."""
    target = tree / CLEAN_GITLINK / TLA_SHIM_FILE
    text = target.read_text()
    if "BuiltinSet" in text:
        fail(f"Trust's Clean pin already names `Expr::BuiltinSet` in {TLA_SHIM_FILE}: the clean-tla shim is obsolete; remove it")
    ty_ast = tree / TY_GITLINK / TY_AST
    if not ty_ast.is_file() or ty_ast.read_text().count(TY_VARIANT) != 1:
        fail(f"Trust's ty pin does not declare `Expr::BuiltinSet` once in {TY_AST}: the clean-tla shim would not compile; remove it")
    original = p3.sha256(target)
    for anchor in TLA_SHIM_ANCHORS:
        if text.count(anchor) != 1:
            fail(f"the clean-tla shim's anchor {anchor.strip()!r} occurs {text.count(anchor)} times in {TLA_SHIM_FILE}")
        text = text.replace(anchor, anchor.replace(" => ", "\n        | Expr::BuiltinSet(_) => ", 1))
    target.write_text(text)
    return {"file": f"{CLEAN_GITLINK}/{TLA_SHIM_FILE}", "from_commit": TLA_SHIM_FROM,
            "original_sha256": original, "patched_sha256": p3.sha256(target),
            "why": "Trust's ty pin declares tla-core's Expr::BuiltinSet, which its Clean pin's clean-tla does not match; "
                   "trust-spec-temporal (which shares one tla-core between them) does not compile without these two arms"}
