#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The leg table behind Clean's trust-ir / trust-cg pin: shape, coherence, rewrite.

WS6.5 of the two-language completion roadmap. A trust-ir pin move in this
repository is NOT an edit, it is a transaction over eight manifest declarations
in six files, three trust-cg declarations that co-own the same trust-ir
revision, and TWO lockfiles -- the root `Cargo.lock` and the standalone
`scripts/crystal_a2_project/Cargo.lock`, which no `--workspace` command ever
touches. `3e87b95ba` moved every manifest leg and the root lock and left the
crystal lock at the previous revision; `48ce23658` had to repair it. This
module is the machine-readable leg table, so that omission is impossible
rather than merely detectable:

  * `census`  -- every declaration, per file, against the declared shape. A
                 declaration in a file the table does not name, a missing one,
                 or one the anchored parser cannot read is a `!!` row and a
                 refusal: the rewrite would otherwise silently miss it.
  * `check`   -- the coherence test: exactly ONE `trust-ir.git?rev=` value
                 across all manifests AND both lockfiles, exactly one
                 `trust-cg.git?rev=` value across the manifests and the root
                 lock, and exactly one `clean-kernel` row in the root lock with
                 no Git source (trust-ir's own clean.git pin must resolve into
                 THIS workspace through the root `[patch]`; a version mismatch
                 drops that patch with a warning and pulls a second kernel).
                 `scripts/check_workspace_dependency_boundary.py` runs it on
                 every push.
  * `stage`   -- the anchored rewrite of every leg into a staging directory.
                 Nothing in the working tree is touched; the driver installs.
  * `trust-cg-authority` -- reads the IMMUTABLE target trust-cg commit's
                 manifest and requires that it pins exactly the trust-ir
                 revision being adopted. A trust-cg that pins another rev puts
                 a second trust-ir graph in the root lock (two `0.x.0`
                 packages from different sources are different crates), which
                 is the 2026-09-14 failure the clean-auto manifest note records.

The driver is `scripts/bump-trust-ir-pin.sh`. The core functions read bytes
they are handed and write only into an explicit staging directory. The check
command additionally resolves explicitly declared dev-only aliases so their
test graph cannot hide a production pin split.
Its exit status distinguishes a proven coherence failure (3) from a shape,
policy or tooling failure that did not establish a split (2). An unexpected
Python failure (1) must never be mistaken for a proven split by the driver.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
import dev_ir_aliases

try:
    import tomllib
except ModuleNotFoundError:  # Python 3.10 and older.
    import tomli as tomllib  # type: ignore[no-redef]


TRUST_IR_URL = "https://github.com/alabsystems/trust-ir.git"
TRUST_CG_URL = "https://github.com/alabsystems/trust-cg.git"
URLS = {"trust-ir": TRUST_IR_URL, "trust-cg": TRUST_CG_URL}

# The leg table. Every `git = "<trust-ir.git>"` / `git = "<trust-cg.git>"`
# declaration in a TRACKED Cargo.toml must be one of these rows, in this order
# within its file, and every row must be present. A new consumer crate, a
# renamed dependency key, or a declaration that moves to another file is a
# shape change: update this table and the assertions in
# scripts/test_bump_trust_ir_pin.py together, then re-run.
TRUST_IR_LEGS: dict[str, tuple[str, ...]] = {
    "Cargo.toml": ("trust-ir-contract", "trust-ir-semr"),
    "crates/clean-auto/Cargo.toml": ("trust-ir",),
    "crates/clean-compiler/Cargo.toml": ("trust-ir", "trust-ir-build", "trust-ir-conformance"),
    "crates/clean-reflect/Cargo.toml": ("trust-ir",),
    "crates/clean-verify/Cargo.toml": ("trust-ir",),
    "scripts/crystal_a2_project/Cargo.toml": ("trust-ir",),
}
TRUST_CG_LEGS: dict[str, tuple[str, ...]] = {
    "crates/clean-auto/Cargo.toml": ("trust-cg-lower", "trust-cg-ir", "trust-cg-opt"),
}
LEGS = {"trust-ir": TRUST_IR_LEGS, "trust-cg": TRUST_CG_LEGS}

# The lockfiles each pin is recorded in. The crystal lock is the leg that was
# missed: it belongs to a standalone `[workspace]` and is invisible to every
# `--workspace` command in this repository.
TRUST_IR_LOCKS = ("Cargo.lock", "scripts/crystal_a2_project/Cargo.lock")
TRUST_CG_LOCKS = ("Cargo.lock",)
LOCKS = {"trust-ir": TRUST_IR_LOCKS, "trust-cg": TRUST_CG_LOCKS}
ROOT_LOCK = "Cargo.lock"
# The clean.git crates trust-ir pins and the root `[patch]` redirects into this
# workspace. Each must appear exactly once in the root lock, with no source.
PATCHED_CLEAN_CRATES = ("clean-kernel", "clean-mathverse", "clean-olean")

SHA = re.compile(r"[0-9a-f]{40}")
DECLARATION = re.compile(r"^\s*([A-Za-z0-9_.-]+)\s*=\s*\{(.*)\}\s*(?:#.*)?$")
GIT_FIELD = re.compile(r'(?:^|[\s,{])git\s*=\s*"([^"]*)"')
REV_FIELD = re.compile(r'(?:^|[\s,{])rev\s*=\s*"([^"]*)"')
# Every spelling of the repository, not only the exact URL: Cargo canonicalises
# a GitHub source (it strips `.git`, ignores case in the host and path), so
# `git = "https://github.com/alabsystems/trust-ir"` or the ssh form
# `git@github.com:alabsystems/trust-ir.git` IS a trust-ir dependency that
# resolves and lands in the lock -- with a source string the exact-URL lock
# check refuses, but only AFTER a refresh, naming the lock rather than the leg.
# A census keyed on the exact URL alone would neither count nor rewrite it.
# Any non-comment line that mentions the repository in a spelling other than
# the exact declaration form is therefore a `!!` row.
MENTION = {
    dep: re.compile(rf"alabsystems/{re.escape(dep)}(?:\.git)?(?![A-Za-z0-9_-])", re.IGNORECASE)
    for dep in URLS
}


# A restated pin: a manifest COMMENT naming trust-ir / trust-cg beside a commit
# id. The declaration's `rev = "…"` is the only statement of a pin that
# scripts/bump-trust-ir-pin.sh moves, so a comment quoting one is stale on the
# next bump -- crates/clean-auto/Cargo.toml's note did it twice ("every TrustIR
# edge sits at 7b9146ba", deleted, then "…sits at 4f09dab8", stale within a day).
# "Beside" is the comment BLOCK -- consecutive commented lines -- because a
# note wraps: "…sits at\n# 4f09dab8" split the name and the id across two
# lines, and a per-line rule passed it. A commit id here is 7-40 hex in either
# case holding a digit AND a letter, so a word ("deadbeef") or a date
# ("20260923") is not one, and neither spelling of `4F09DAB8` escapes.
PIN_NAME = re.compile(r"trust[-_ ]?(?:ir|cg)", re.IGNORECASE)
COMMIT_ID = re.compile(
    r"(?<![0-9A-Za-z])(?=[0-9a-f]*[a-f])(?=[0-9a-f]*[0-9])[0-9a-f]{7,40}(?![0-9A-Za-z])",
    re.IGNORECASE,
)


class PinShapeError(ValueError):
    """A leg no longer matches its declared shape (a `!!` row)."""


class PinCoherenceError(ValueError):
    """The legs parse but do not agree on one revision."""


def exact_sha(value: str, label: str) -> str:
    if not isinstance(value, str) or SHA.fullmatch(value) is None:
        raise PinShapeError(f"{label}: expected a 40-hex lowercase commit, got {value!r}")
    return value


def tracked(root: Path, pattern: str) -> list[str]:
    """Tracked paths matching a git pathspec, relative to root, sorted."""
    out = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", pattern],
        capture_output=True, text=True, check=True,
    ).stdout
    return sorted(path for path in out.split("\0") if path)


def read_tracked(root: Path, pattern: str) -> dict[str, str]:
    return {relative: (root / relative).read_text() for relative in tracked(root, pattern)}


def declarations(text: str, dep: str, label: str) -> list[tuple[int, str, str]]:
    """Every `(line, key, rev)` declaration of `dep`'s Git URL in one manifest.

    Anchored on the LINE: an inline table is the only shape this repository
    uses for these pins, and a multi-line `[dependencies.x]` table carrying the
    URL is refused rather than half-read. Comment lines are skipped -- they
    quote the URL to explain the pin, never to declare it. Any other spelling
    of the repository (`MENTION`: no `.git`, ssh, a case variant) is a
    declaration Cargo would resolve and the rewrite would miss, so it is
    refused here, naming the line, rather than found later by the lock check.
    """
    url = URLS[dep]
    mention = MENTION[dep]
    found = []
    for number, line in enumerate(text.splitlines(), 1):
        if mention.search(line) is None:
            continue
        if line.lstrip().startswith("#"):
            continue
        match = DECLARATION.match(line)
        git = GIT_FIELD.search(match[2]) if match else None
        if match is None or git is None:
            raise PinShapeError(
                f"{label}:{number}: {dep} Git URL outside an inline dependency "
                "declaration (multi-line tables and patches are unsupported)"
            )
        if git[1] != url:
            raise PinShapeError(
                f"{label}:{number}: {match[1]} declares {dep} through {git[1]!r}, not the "
                f"exact {url}; Cargo unifies the spellings, the leg table does not"
            )
        if mention.search(match[2].replace(url, "")) is not None:
            raise PinShapeError(
                f"{label}:{number}: {match[1]} mentions {dep} twice in one declaration"
            )
        rev = REV_FIELD.search(match[2])
        if rev is None:
            raise PinShapeError(f"{label}:{number}: {match[1]} declares {url} without rev")
        found.append((number, match[1], exact_sha(rev[1], f"{label}:{number}: {match[1]} rev")))
    return found


def census(manifests: dict[str, str], dep: str) -> dict[str, list[tuple[int, str, str]]]:
    """Per-file declarations of `dep`, verified against the leg table.

    `manifests` maps every TRACKED Cargo.toml (relative path -> text). Files
    outside the table must declare nothing; files in the table must declare
    exactly the listed production keys in order. Explicit dev-only aliases
    are separately classified by manifest kind and resolved reachability.
    Anything else is a `!!` refusal.
    """
    table = LEGS[dep]
    try:
        dev_aliases = dev_ir_aliases.declared_aliases(manifests) if dep == "trust-ir" else {}
    except dev_ir_aliases.DevAliasError as error:
        raise PinShapeError(str(error)) from error
    rows: dict[str, list[tuple[int, str, str]]] = {}
    problems = []
    for relative in sorted(set(manifests) | set(table)):
        text = manifests.get(relative)
        if text is None:
            problems.append(f"!! {relative}: leg file is not tracked")
            continue
        try:
            found = declarations(text, dep, relative)
            if relative == "Cargo.toml":
                for alias in dev_aliases:
                    if sum(row[1] == alias for row in found) != 1:
                        raise PinShapeError(f"{relative}: dev alias {alias} must have exactly one Git declaration")
                # A maintained alias retains its dev-only reachability checks,
                # but its immutable revision is part of the ordinary cohort.
                # In particular SemR regressions must not silently stay on a
                # second historical IR while production pins advance.
                found = [row for row in found
                         if row[1] not in dev_aliases or row[1] in table.get(relative, ())]
        except PinShapeError as error:
            problems.append(f"!! {error}")
            continue
        expected = table.get(relative, ())
        keys = tuple(key for _, key, _ in found)
        if keys != expected:
            problems.append(
                f"!! {relative}: {dep} declarations {list(keys)} differ from the "
                f"leg table {list(expected)}"
            )
            continue
        if found:
            rows[relative] = found
    if problems:
        raise PinShapeError("\n".join(problems))
    return rows


def revisions(rows: dict[str, list[tuple[int, str, str]]]) -> dict[str, str]:
    """`file:key -> rev` for every declaration."""
    return {f"{relative}:{key}": rev for relative, found in rows.items() for _, key, rev in found}


def manifest_revision(manifests: dict[str, str], dep: str) -> str:
    """The ONE revision every manifest leg of `dep` declares, else a refusal."""
    rows = census(manifests, dep)
    by_leg = revisions(rows)
    distinct = sorted(set(by_leg.values()))
    if len(distinct) != 1:
        detail = ", ".join(f"{leg}={rev[:12]}" for leg, rev in sorted(by_leg.items()))
        raise PinCoherenceError(f"{dep} pin is split across manifest legs: {detail}")
    return distinct[0]


def lock_packages(text: str, label: str) -> list[dict]:
    try:
        lock = tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        raise PinShapeError(f"{label} is not valid TOML: {error}") from error
    packages = lock.get("package")
    if not isinstance(packages, list) or not all(isinstance(row, dict) for row in packages):
        raise PinShapeError(f"{label} has no package inventory")
    return packages


def lock_revision(text: str, label: str, dep: str) -> str:
    """The one exact `dep` Git source every `dep` package row in a lock records."""
    url = URLS[dep]
    prefix = f"{dep}-"
    revs = set()
    rows = [
        row for row in lock_packages(text, label)
        if isinstance(row.get("name"), str) and (row["name"] == dep or row["name"].startswith(prefix))
    ]
    if not rows:
        raise PinCoherenceError(f"{label} records no {dep} package")
    for row in rows:
        source = row.get("source")
        match = re.fullmatch(rf"git\+{re.escape(url)}\?rev=([0-9a-f]{{40}})#([0-9a-f]{{40}})", source or "")
        if match is None:
            raise PinCoherenceError(
                f"{label} package {row['name']} does not use the exact {dep} Git source: {source!r}"
            )
        if match[1] != match[2]:
            raise PinCoherenceError(f"{label} package {row['name']} requests {match[1]} but resolves {match[2]}")
        revs.add(match[1])
    if len(revs) != 1:
        raise PinCoherenceError(f"{label} resolves multiple {dep} Git revisions: " + ", ".join(sorted(revs)))
    return next(iter(revs))


def check_patched_clean_crates(text: str, label: str = ROOT_LOCK) -> None:
    """trust-ir's clean.git pin must land in THIS workspace, never a second copy."""
    packages = lock_packages(text, label)
    for name in PATCHED_CLEAN_CRATES:
        rows = [row for row in packages if row.get("name") == name]
        if len(rows) != 1 or rows[0].get("source") is not None:
            sources = [row.get("source") for row in rows]
            raise PinCoherenceError(
                f"{label} carries {len(rows)} {name} row(s) {sources}; trust-ir's clean.git "
                "pin must resolve into this workspace through the root [patch] (exactly one "
                "row, no source) -- a version mismatch drops the patch and pulls a second copy"
            )


def check_pin_coherence(manifests: dict[str, str], locks: dict[str, str]) -> dict[str, str]:
    """The WS6.5 coherence test. Returns `{"trust-ir": rev, "trust-cg": rev}`.

    `manifests`: every tracked Cargo.toml; `locks`: every tracked Cargo.lock.
    Raises PinShapeError (a `!!` leg) or PinCoherenceError (a split), each
    naming the leg.
    """
    result = {}
    for dep in ("trust-ir", "trust-cg"):
        declared = manifest_revision(manifests, dep)
        for relative in LOCKS[dep]:
            text = locks.get(relative)
            if text is None:
                raise PinShapeError(f"{relative}: lock is not tracked")
            locked = lock_revision(text, relative, dep)
            if locked != declared:
                raise PinCoherenceError(
                    f"{relative} resolves {dep} {locked} but every manifest leg declares "
                    f"{declared}; refresh that lock in the same transaction"
                )
        result[dep] = declared
    root = locks.get(ROOT_LOCK)
    if root is None:
        raise PinShapeError(f"{ROOT_LOCK}: lock is not tracked")
    check_patched_clean_crates(root)
    return result


def restated_pins(manifests: dict[str, str]) -> list[str]:
    """`file:line: comment` for every manifest comment block that restates a pin.

    A block is a run of consecutive lines that each carry a comment, so a note
    wrapped across lines is read whole; a trailing comment after a declaration
    counts too, and the declaration part of the line (before `#`) is the pin
    itself and is not read here. The line is the block's first.
    """
    found = []
    for relative, text in sorted(manifests.items()):
        block: list[tuple[int, str, str]] = []
        for number, line in enumerate(text.splitlines() + [""], 1):
            _, hash_, comment = line.partition("#")
            if hash_:
                block.append((number, line.strip(), comment))
                continue
            said = " ".join(c for _, _, c in block)
            if block and PIN_NAME.search(said) and COMMIT_ID.search(said):
                found.append(f"{relative}:{block[0][0]}: " + " ".join(l for _, l, _ in block))
            block = []
    return found


def rewritten(text: str, dep: str, label: str, to: str) -> str:
    """Every leg line of `dep` in one manifest with its rev moved to `to`."""
    exact_sha(to, "target revision")
    lines = text.splitlines(keepends=True)
    for number, key, rev in declarations(text, dep, label):
        line = lines[number - 1]
        new, count = re.subn(rf'\brev\s*=\s*"{rev}"', f'rev = "{to}"', line)
        if count != 1:
            raise PinShapeError(f"{label}:{number}: {key}: ambiguous rev field")
        lines[number - 1] = new
    return "".join(lines)


def stage(manifests: dict[str, str], targets: dict[str, str], stage_dir: Path) -> list[str]:
    """Write every changed leg file under `stage_dir`; return the changed paths.

    Both censuses run first (shape errors refuse before a byte is staged), and
    the staged text is re-censused so a rewrite that changed the shape cannot
    be installed. Nothing outside `stage_dir` is written.
    """
    staged: dict[str, str] = {}
    for dep, to in targets.items():
        rows = census(manifests, dep)
        for relative in rows:
            current = staged.get(relative, manifests[relative])
            new = rewritten(current, dep, relative, to)
            if new != manifests[relative]:
                staged[relative] = new
    after = dict(manifests)
    after.update(staged)
    for dep, to in targets.items():
        if manifest_revision(after, dep) != to:
            raise PinShapeError(f"staged {dep} legs do not all read {to}")
    for relative, text in sorted(staged.items()):
        path = stage_dir / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    return sorted(staged)


def trust_cg_pins(manifest_text: str, label: str) -> set[str]:
    """Every trust-ir.git revision the target trust-cg manifest declares.

    Parsed as TOML, from every dependency table (workspace, package, dev,
    build, target-specific). A `[patch]` of the trust-ir URL is refused: a
    trust-cg that redirects trust-ir does not build at its own pin.
    """
    try:
        doc = tomllib.loads(manifest_text)
    except tomllib.TOMLDecodeError as error:
        raise PinShapeError(f"{label}: invalid TOML: {error}") from error
    for patched in doc.get("patch", {}):
        if TRUST_IR_URL.startswith(patched.rstrip("/")) or patched.startswith(TRUST_IR_URL):
            raise PinShapeError(f"{label}: [patch] redirects {TRUST_IR_URL}; the pin is not what builds")
    tables = []
    workspace = doc.get("workspace", {})
    if isinstance(workspace, dict):
        tables.append(workspace.get("dependencies", {}))
    containers = [doc, *(doc.get("target", {}).values() if isinstance(doc.get("target"), dict) else [])]
    for container in containers:
        if not isinstance(container, dict):
            continue
        for section in ("dependencies", "dev-dependencies", "build-dependencies"):
            tables.append(container.get(section, {}))
    found = set()
    for table in tables:
        if not isinstance(table, dict):
            continue
        for key, dep in table.items():
            if isinstance(dep, dict) and dep.get("git") == TRUST_IR_URL:
                rev = dep.get("rev")
                if not isinstance(rev, str) or SHA.fullmatch(rev) is None:
                    raise PinShapeError(f"{label}: {key} pins {TRUST_IR_URL} without an exact rev")
                if {"branch", "tag", "path"} & set(dep):
                    raise PinShapeError(f"{label}: {key} carries a mutable/mixed trust-ir selector")
                found.add(rev)
    if not found:
        raise PinShapeError(f"{label}: no trust-ir.git declaration found; not a trust-cg manifest?")
    return found


def check_trust_cg_authority(manifest_text: str, label: str, trust_ir_rev: str) -> None:
    pins = trust_cg_pins(manifest_text, label)
    if pins != {trust_ir_rev}:
        raise PinCoherenceError(
            f"{label} pins trust-ir {sorted(pins)}, not the coordinated {trust_ir_rev}; a "
            "trust-cg that co-owns a different trust-ir puts a second trust-ir graph in Cargo.lock"
        )


# ---------------------------------------------------------------- command line

def cmd_census(root: Path) -> int:
    manifests = read_tracked(root, "*Cargo.toml")
    code = 0
    for dep in ("trust-ir", "trust-cg"):
        try:
            rows = census(manifests, dep)
        except PinShapeError as error:
            print(str(error))
            code = max(code, 2)
            continue
        revs = revisions(rows)
        distinct = sorted(set(revs.values()))
        for leg, rev in sorted(revs.items()):
            mark = "  " if len(distinct) == 1 else "<>"
            print(f"{mark} {dep:8} {rev}  {leg}")
        if len(distinct) != 1:
            print(f"<> {dep} is SPLIT across {len(distinct)} revisions")
            code = max(code, 1)
    return code


def cmd_current(root: Path, dep: str) -> int:
    try:
        print(manifest_revision(read_tracked(root, "*Cargo.toml"), dep))
    except (PinShapeError, PinCoherenceError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 1
    return 0


def cmd_check(root: Path) -> int:
    try:
        manifests = read_tracked(root, "*Cargo.toml")
        locks = dev_ir_aliases.production_locks(root, manifests, read_tracked(root, "*Cargo.lock"))
        result = check_pin_coherence(manifests, locks)
    except PinCoherenceError as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 3
    except (PinShapeError, dev_ir_aliases.DevAliasError, subprocess.CalledProcessError, OSError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 2
    restated = restated_pins(read_tracked(root, "*Cargo.toml"))
    if restated:
        print("REFUSED: a manifest comment restates a trust-ir/trust-cg pin (the `rev` "
              "field is the only statement of it):\n  " + "\n  ".join(restated), file=sys.stderr)
        return 2
    print(f"trust-ir pin coherent at {result['trust-ir']}; trust-cg pin coherent at {result['trust-cg']}; "
          f"one {', one '.join(PATCHED_CLEAN_CRATES)} row in {ROOT_LOCK}")
    return 0


def cmd_legs(root: Path) -> int:
    files = sorted(set(TRUST_IR_LEGS) | set(TRUST_CG_LEGS) | set(TRUST_IR_LOCKS) | set(TRUST_CG_LOCKS))
    for relative in files:
        print(relative)
    return 0


def cmd_stage(root: Path, trust_ir_to: str, trust_cg_to: str, stage_dir: Path) -> int:
    try:
        targets = {
            "trust-ir": exact_sha(trust_ir_to, "--trust-ir-to"),
            "trust-cg": exact_sha(trust_cg_to, "--trust-cg-to"),
        }
        staged = stage(read_tracked(root, "*Cargo.toml"), targets, stage_dir)
    except (PinShapeError, PinCoherenceError, subprocess.CalledProcessError, OSError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 1
    for relative in staged:
        print(relative)
    return 0


def cmd_trust_cg_authority(manifest: Path, trust_ir_rev: str) -> int:
    try:
        check_trust_cg_authority(manifest.read_text(), str(manifest), exact_sha(trust_ir_rev, "--trust-ir"))
    except (PinShapeError, PinCoherenceError, OSError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 1
    print(f"trust-cg authority pins trust-ir {trust_ir_rev}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    root_default = Path(__file__).resolve().parent.parent
    for name in ("census", "check", "legs", "current", "stage"):
        p = sub.add_parser(name)
        p.add_argument("--root", type=Path, default=root_default)
        if name == "current":
            p.add_argument("--dep", choices=("trust-ir", "trust-cg"), required=True)
        if name == "stage":
            p.add_argument("--trust-ir-to", required=True)
            p.add_argument("--trust-cg-to", required=True)
            p.add_argument("--stage-dir", type=Path, required=True)
    p = sub.add_parser("trust-cg-authority")
    p.add_argument("--manifest", type=Path, required=True)
    p.add_argument("--trust-ir", required=True)
    args = parser.parse_args(argv)
    if args.command == "census":
        return cmd_census(args.root)
    if args.command == "check":
        return cmd_check(args.root)
    if args.command == "legs":
        return cmd_legs(args.root)
    if args.command == "current":
        return cmd_current(args.root, args.dep)
    if args.command == "stage":
        return cmd_stage(args.root, args.trust_ir_to, args.trust_cg_to, args.stage_dir)
    return cmd_trust_cg_authority(args.manifest, args.trust_ir)


if __name__ == "__main__":
    raise SystemExit(main())
