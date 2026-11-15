#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# Emit data/vendor_manifest.json: a provenance + tamper-evidence manifest for
# the `cargo vendor` source tree (paragon axis 1: "every third-party dependency
# vendored AND verified"). The verified half lives here — every vendored crate
# is pinned by name+version and its source checksum, so a re-vendor can be
# diffed against this manifest to detect any drift in third-party source.
#
# For crates.io crates the checksum is the registry sha256 (from each crate's
# .cargo-checksum.json "package" field), which we cross-check against
# Cargo.lock's own `checksum =` field — the two MUST agree or we abort. For the
# git-sourced crate (carcara) there is no registry sha256, so we pin it by its
# git source URL+rev (from Cargo.lock) plus a deterministic tree hash derived
# from its per-file checksums (cargo's own .cargo-checksum.json "files" map),
# giving tamper-evidence over its vendored bytes too.
#
# Usage: python3 scripts/gen_vendor_manifest.py [vendor_dir] [out_json]
#   defaults: vendor/  data/vendor_manifest.json
#
# THIRD-PARTY-ONLY STAGING (2026-10-07):
#   python3 scripts/gen_vendor_manifest.py --stage-third-party [vendor_dir] [--download]
#   python3 scripts/gen_vendor_manifest.py [vendor_dir]
#
# `cargo vendor` cannot produce the tree this manifest describes: it refuses
# this lock outright ("found duplicate version of package indexmap v2.14.0
# vendored from two sources" -- crates-io and the first-party ty.git, which
# carries its own indexmap/num-integer/num-traits/sha2 copies), and when it
# could run it copied first-party AY/ty/trust-ir/trust-cg sources into vendor/,
# which this generator refuses by design. The staging mode builds exactly the
# THIRD-PARTY half: every crates.io package Cargo.lock names, unpacked the way
# cargo's own registry vendoring unpacks it (see `stage_third_party`), and
# nothing else. First-party git sources stay subrepos and are never staged.

import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import urllib.request
from pathlib import Path, PurePosixPath

import vendor_manifest_format

ANSWERS_PINNED_INPUTS = True

INTERNAL_GIT_SOURCE_MARKERS = (
    "github.com/alabsystems/",
    "github.com/alabsystems/ay",
    "github.com/alabsystems/ny",
)


CRATES_IO_SOURCE = "registry+https://github.com/rust-lang/crates.io-index"
CRATES_IO_DOWNLOAD = "https://static.crates.io/crates/{name}/{name}-{version}.crate"
# What cargo writes into every vendored crate's `.cargo-checksum.json`
# (src/cargo/ops/vendor.rs), so a staged tree is the tree `cargo vendor` writes.
CARGO_CHECKSUM_COMMENT = (
    "This file only protects against accidental modifications. "
    "It is not a security mechanism and does not protect against malicious changes."
)


def parse_cargo_lock(lock_path):
    """Return every `[[package]]` of Cargo.lock, in order, losslessly.

    A LIST of {'name', 'version', 'checksum': str|None, 'source': str|None},
    never a map keyed by (name, version). Until 2026-10-07 this returned that
    map, and the key is not unique: this lock carries indexmap 2.14.0,
    num-integer 0.1.46, num-traits 0.2.19 and sha2 0.10.9 TWICE -- once from
    crates.io and once from the first-party ty.git -- so the later git row
    overwrote the crates.io row, the package count read 4 short, and a staging
    pass over the map silently dropped four third-party crates. Measured, not
    hypothetical: the first staging run here staged 385 of 389.
    """
    with open(lock_path, encoding="utf-8") as f:
        text = f.read()
    entries = []
    # Cargo.lock is a sequence of [[package]] TOML tables.
    for block in text.split("[[package]]"):
        name = re.search(r'^name = "([^"]+)"', block, re.MULTILINE)
        ver = re.search(r'^version = "([^"]+)"', block, re.MULTILINE)
        if not name or not ver:
            continue
        checksum = re.search(r'^checksum = "([^"]+)"', block, re.MULTILINE)
        source = re.search(r'^source = "([^"]+)"', block, re.MULTILINE)
        entries.append({
            "name": name.group(1),
            "version": ver.group(1),
            "checksum": checksum.group(1) if checksum else None,
            "source": source.group(1) if source else None,
        })
    return entries


def lock_entry_for(entries, name, version, registry):
    """The ONE lock row a vendored `<name>-<version>/` directory came from.

    `registry` says how it was vendored (a "package" checksum means a registry
    crate). Same name+version from two sources is legal in a lock, so the
    lookup is by source kind too, and an ambiguous match is refused rather than
    resolved by whichever row happened to come last.
    """
    rows = [
        e for e in entries
        if e["name"] == name and e["version"] == version
        and bool(e["source"] and e["source"].startswith("registry+")) == registry
    ]
    if len(rows) > 1:
        raise StageRefused(f"{name} {version}: {len(rows)} lock rows of the same source kind")
    return rows[0] if rows else {}


def tree_hash_from_files_map(files_map):
    """Deterministic sha256 over a crate's per-file sha256 map.

    cargo writes a `.cargo-checksum.json` "files" map ({relpath: sha256}) for
    every vendored crate and re-checks it on `--offline` build, so hashing that
    map gives a stable content fingerprint for crates (git-sourced) that carry
    no single registry package checksum.
    """
    h = hashlib.sha256()
    for path in sorted(files_map):
        h.update(path.encode("utf-8"))
        h.update(b"\0")
        h.update(files_map[path].encode("utf-8"))
        h.update(b"\0")
    return h.hexdigest()


def split_name_version(dirname):
    r"""`zeroize-1.9.0` -> ('zeroize', '1.9.0'); handles hyphenated names.

    The `.*` is NON-GREEDY, and that is the whole correctness argument. Semver
    BUILD METADATA may contain hyphens (`toml-0.9.12+spec-1.1.0`,
    `wasip2-1.0.4+wasi-0.2.12`, `wasi-0.11.0+wasi-snapshot-preview1`), so a
    greedy split takes the LAST hyphen and yields ('toml-0.9.12+spec', '1.1.0')
    -- a name that identifies no package. Measured 2026-09-14: that mangled 8 of
    385 rows in data/vendor_manifest.json, every Cargo.lock lookup for them
    missed, and the checksum cross-check was therefore SKIPPED while the row
    still recorded `checksum_kind: "sha256-registry"` -- a label the manifest's
    own note defines as "verified equal to Cargo.lock's `checksum =` field".

    Non-greedy takes the FIRST split point whose suffix is a whole semver, which
    is the right one: a name ending in a number cannot be mistaken for a version
    because `foo-1-2.0.0` fails `\d+\.\d+\.\d+` at `1-2.0.0` and the scan
    moves on. `$` anchors the suffix, so the match is still the full tail.
    """
    m = re.match(r"^(.*?)-(\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.+-]+)?)$", dirname)
    if not m:
        return None, None
    return m.group(1), m.group(2)


SPLIT_CASES = (
    # (dirname, name, version) -- the first four are the shapes that were wrong.
    ("toml-0.9.12+spec-1.1.0", "toml", "0.9.12+spec-1.1.0"),
    ("wasip2-1.0.4+wasi-0.2.12", "wasip2", "1.0.4+wasi-0.2.12"),
    ("wasi-0.11.0+wasi-snapshot-preview1", "wasi", "0.11.0+wasi-snapshot-preview1"),
    ("toml_datetime-0.7.5+spec-1.1.0", "toml_datetime", "0.7.5+spec-1.1.0"),
    ("zeroize-1.9.0", "zeroize", "1.9.0"),
    ("proc-macro2-1.0.86", "proc-macro2", "1.0.86"),
    ("rustc-demangle-0.1.24", "rustc-demangle", "0.1.24"),
    ("serde_json-1.0.140", "serde_json", "1.0.140"),
    ("foo-1-2.0.0", "foo-1", "2.0.0"),
    ("pre-release-1.2.3-rc.1", "pre-release", "1.2.3-rc.1"),
    ("no-version-here", None, None),
)


def self_test():
    """Arms for the split, and for the label that must not outrun its check."""
    failures = []
    for dirname, want_name, want_version in SPLIT_CASES:
        got = split_name_version(dirname)
        ok = got == (want_name, want_version)
        print(f"  self-test ARM {'ok' if ok else 'FAILED'}: {dirname} -> {got}"
              + ("" if ok else f" (want {(want_name, want_version)})"))
        if not ok:
            failures.append(dirname)

    # The label is a CLAIM about Cargo.lock, so it may only be used when the
    # lookup actually landed. Both directions, because a label that is never
    # applied is as useless as one that is always applied.
    for lock_checksum, want in ((None, "sha256-vendor-unverified"), ("abc", "sha256-registry")):
        got = registry_checksum_kind(lock_checksum)
        ok = got == want
        print(f"  self-test ARM {'ok' if ok else 'FAILED'}: lock_checksum={lock_checksum!r}"
              f" -> {got}" + ("" if ok else f" (want {want})"))
        if not ok:
            failures.append(f"label:{lock_checksum}")

    # The check against a synthetic two-package lock, stderr held. A manifest
    # with NO rows, one with a locked crate's row REMOVED (R165's 342-of-389
    # shape), one with a row's checksum changed, and one with an extra row must
    # each be refused; the full regenerated set must pass -- both directions.
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        lock = Path(tmp, "Cargo.lock")
        lock.write_text(
            "".join(f'[[package]]\nname = "{n}"\nversion = "{v}"\n'
                    f'source = "{CRATES_IO_SOURCE}"\nchecksum = "{c}"\n\n'
                    for n, v, c in (("zeroize", "1.9.0", "abc"), ("adler2", "2.0.1", "def")))
            + '[[package]]\nname = "clean"\nversion = "0.9.0"\n')
        sha = hashlib.sha256(lock.read_bytes()).hexdigest()
        full = sorted(lock_derived_rows(str(lock)).values(), key=lambda r: r["dir"])
        cases = (
            ("no rows", [], "EMPTY:"),
            ("one locked row removed", full[1:], "MISSING: 1 of"),
            ("a checksum changed", [dict(full[0], checksum="0" * 3)] + full[1:], "DIFFERS: 1 "),
            ("an extra row", full + [dict(full[0], name="extra", dir="extra-1.9.0")], "EXTRA: 1 "),
            ("a row duplicated", full + full[:1], "DUPLICATE: 1 "),
            ("the full regenerated set", full, None),
        )
        # want: None = must pass; else the refusal line that must be the reason.
        for arm, rows, want in cases:
            manifest = Path(tmp, "m.json")
            manifest.write_text(json.dumps(vendor_manifest_format.selftest_manifest(rows, sha)))
            held, sys.stderr = sys.stderr, io.StringIO()
            try:
                got = check_committed(str(manifest), str(lock))
                said = sys.stderr.getvalue()
            finally:
                sys.stderr = held
            ok = got == 0 and not said if want is None else got == 1 and want in said
            print(f"  self-test ARM {'ok' if ok else 'FAILED'}: check, {arm} "
                  f"({len(rows)} row(s) over a 2-crate lock) -> exit {got}"
                  + ("" if ok else f" (want {want or 'a pass'}; stderr {said!r})"))
            if not ok:
                failures.append(f"check:{arm}")

        failures.extend(vendor_manifest_format.check_self_test(check_committed, full, sha, lock))

    failures.extend(stage_self_test())

    if failures:
        print(f"self-test: {len(failures)} arm(s) FAILED: {', '.join(map(str, failures))}",
              file=sys.stderr)
        return 1
    print("self-test: all arms green")
    return 0


def count_lock_packages(lock_path="Cargo.lock"):
    """How many `[[package]]` tables the lock carries; 0 when it cannot be read."""
    try:
        return len(parse_cargo_lock(lock_path))
    except OSError:
        return 0


def lock_has_packages(lock_path="Cargo.lock"):
    return count_lock_packages(lock_path) > 0


def registry_checksum_kind(lock_checksum):
    """What the row may CLAIM about a crates.io checksum.

    `sha256-registry` is defined by this manifest's own note as "verified equal
    to Cargo.lock's `checksum =` field at generation time". When the Cargo.lock
    lookup misses there is nothing to have been equal to, so the row must not
    say it did -- before 2026-09-14 it said it anyway for every row the name
    split had mangled.
    """
    return "sha256-registry" if lock_checksum else "sha256-vendor-unverified"


def is_internal_source(name, source):
    """Internal first-party repositories must remain subrepos, never vendor data."""
    if name == "ay" or (name and name.startswith("ay-")):
        return True
    if name == "ny" or (name and name.startswith("ny-")):
        return True
    return bool(source) and any(marker in source for marker in INTERNAL_GIT_SOURCE_MARKERS)


def unrecognized_vendor_entries(vendor_dir):
    """Return top-level entries that a release archive must never carry."""
    problems = []
    for entry in sorted(os.listdir(vendor_dir)):
        path = os.path.join(vendor_dir, entry)
        if entry == ".vendor_manifest.json":
            if os.path.islink(path) or not os.path.isfile(path):
                problems.append(f"{entry}: embedded manifest is not a regular file")
            continue
        if os.path.islink(path):
            problems.append(f"{entry}: symbolic links are not allowed")
            continue
        if not os.path.isdir(path):
            problems.append(f"{entry}: unexpected top-level file")
            continue
        if not os.path.isfile(os.path.join(path, ".cargo-checksum.json")):
            problems.append(f"{entry}: missing .cargo-checksum.json")
            continue
        name, version = split_name_version(entry)
        if name is None or version is None:
            problems.append(f"{entry}: directory name is not crate-name-version")
    return problems


class StageRefused(Exception):
    """A staging precondition failed; nothing about the tree may be trusted."""


def third_party_packages(lock):
    """The packages a third-party-only tree must hold, from a parsed Cargo.lock.

    Returns sorted [(name, version, checksum)] for every crates.io package.
    First-party git sources (AY, ty, trust-ir, trust-cg) are subrepos and are
    skipped by design; path packages are in-tree. Anything else -- a git source
    that is NOT first-party, another registry, a registry row with no checksum --
    is a package this flow cannot stage faithfully, so it REFUSES rather than
    minting a manifest that silently omits it.
    """
    packages, refused = [], []
    for entry in sorted(lock, key=lambda e: (e["name"], e["version"], e["source"] or "")):
        name, version, source = entry["name"], entry["version"], entry.get("source")
        if source is None or source.startswith("path+"):
            continue
        if is_internal_source(name, source):
            continue
        if source != CRATES_IO_SOURCE:
            refused.append(f"{name} {version}: source {source} is neither crates.io nor first-party")
            continue
        if not entry.get("checksum"):
            refused.append(f"{name} {version}: crates.io package with no `checksum =` in Cargo.lock")
            continue
        packages.append((name, version, entry["checksum"]))
    if refused:
        raise StageRefused("cannot stage these packages faithfully:\n  " + "\n  ".join(refused))
    return packages


def cargo_registry_cache_dirs():
    """cargo's downloaded-.crate caches for crates.io, under $CARGO_HOME."""
    home = Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo")
    cache = home / "registry" / "cache"
    if not cache.is_dir():
        return []
    return sorted(p for p in cache.iterdir() if p.is_dir() and p.name.startswith("index.crates.io-"))


def fetch_crate(name, version, checksum, cache_dirs, download):
    """The .crate bytes whose sha256 IS Cargo.lock's checksum, or a refusal.

    This comparison is the verification cargo itself performs on every
    download, and it is what makes `package` in .cargo-checksum.json a claim
    rather than a copy. A cached file that disagrees with the lock is refused,
    never silently replaced by a download.
    """
    fname = f"{name}-{version}.crate"
    for cache in cache_dirs:
        path = cache / fname
        if path.is_file():
            data = path.read_bytes()
            got = hashlib.sha256(data).hexdigest()
            if got != checksum:
                raise StageRefused(
                    f"{path}: sha256 {got} != Cargo.lock checksum {checksum} -- a corrupt or "
                    "substituted cache entry; refusing it rather than downloading over it"
                )
            return data
    if not download:
        raise StageRefused(
            f"{fname} is not in cargo's registry cache ({', '.join(map(str, cache_dirs)) or 'none'}); "
            "re-run with --download, or `targo fetch --locked` first"
        )
    url = CRATES_IO_DOWNLOAD.format(name=name, version=version)
    with urllib.request.urlopen(url, timeout=60) as response:  # noqa: S310 -- fixed https host
        data = response.read()
    got = hashlib.sha256(data).hexdigest()
    if got != checksum:
        raise StageRefused(f"{url}: sha256 {got} != Cargo.lock checksum {checksum}")
    return data


def vendor_includes(relative):
    """cargo's `vendor_this` filter (src/cargo/ops/vendor.rs), on a crate-relative path."""
    if ".git" in relative.parts:
        return False
    if relative.name in (".gitattributes", ".gitignore"):
        return False
    return relative.as_posix() != ".cargo-ok"


def unpack_crate(data, name, version, vendor_dir):
    """Unpack one .crate into vendor_dir/<name>-<version>/ exactly as cargo vendors it.

    Mirrors cargo's registry `unpack` + `vendor_this`: every entry must sit under
    the `<name>-<version>/` prefix and be a regular file or a directory (cargo
    bails on anything else, so this refuses too); a `.cargo-ok` anywhere is
    skipped, as are `.git` trees, `.gitattributes` and `.gitignore`. Returns the
    per-file sha256 map cargo records under "files".
    """
    prefix = f"{name}-{version}"
    dst = Path(vendor_dir) / prefix
    if dst.exists():
        raise StageRefused(f"{dst} already exists; stage into an empty directory")
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tar:
        members = tar.getmembers()
        for member in members:
            entry = PurePosixPath(member.name)
            if entry.is_absolute() or ".." in entry.parts or not entry.parts or entry.parts[0] != prefix:
                raise StageRefused(f"{prefix}.crate: entry {member.name!r} is not under {prefix}/")
            if not (member.isdir() or member.type in (tarfile.REGTYPE, tarfile.AREGTYPE)):
                raise StageRefused(f"{prefix}.crate: entry {member.name!r} has invalid type {member.type!r}")
        for member in members:
            entry = PurePosixPath(member.name)
            relative = PurePosixPath(*entry.parts[1:])
            if entry.name == ".cargo-ok" or not vendor_includes(relative):
                continue
            target = dst.joinpath(*relative.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            source = tar.extractfile(member)
            target.write_bytes(source.read() if source else b"")
    dst.mkdir(parents=True, exist_ok=True)
    files = {}
    for root, _dirs, filenames in os.walk(dst):
        for fn in filenames:
            path = Path(root) / fn
            files[path.relative_to(dst).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return files


def stage_third_party(vendor_dir, lock_path="Cargo.lock", cache_dirs=None, download=False):
    """Write the third-party-only vendor tree for `lock_path` into an EMPTY vendor_dir.

    One `<name>-<version>/` per crates.io package (cargo's --versioned-dirs
    layout), each with the `.cargo-checksum.json` cargo writes: "package" is
    the lock checksum the .crate was just verified against, "files" the
    per-file sha256 map. Returns the number of crates staged.
    """
    vendor = Path(vendor_dir)
    if vendor.exists() and any(vendor.iterdir()):
        raise StageRefused(f"{vendor} is not empty; stage into a fresh directory")
    packages = third_party_packages(parse_cargo_lock(lock_path))
    if not packages:
        raise StageRefused(f"{lock_path} names no crates.io packages to stage")
    caches = cargo_registry_cache_dirs() if cache_dirs is None else cache_dirs
    vendor.mkdir(parents=True, exist_ok=True)
    for name, version, checksum in packages:
        data = fetch_crate(name, version, checksum, caches, download)
        files = unpack_crate(data, name, version, vendor)
        record = {"$comment": CARGO_CHECKSUM_COMMENT, "files": files, "package": checksum}
        Path(vendor, f"{name}-{version}", ".cargo-checksum.json").write_text(
            json.dumps(record, separators=(",", ":"), sort_keys=True)
        )
    return len(packages)


def _synthetic_crate(name, version, entries):
    """A gzipped tar of (path, bytes|None for a dir|'symlink') for the self-test."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as tar:
        for path, payload in entries:
            info = tarfile.TarInfo(path)
            if payload is None:
                info.type = tarfile.DIRTYPE
                tar.addfile(info)
            elif payload == "symlink":
                info.type = tarfile.SYMTYPE
                info.linkname = "Cargo.toml"
                tar.addfile(info)
            else:
                info.size = len(payload)
                tar.addfile(info, io.BytesIO(payload))
    return buf.getvalue()


def stage_self_test():
    """Arms for the staging flow; returns a list of failed arm names."""
    import tempfile

    failures = []
    good = _synthetic_crate("demo", "1.0.0", [
        ("demo-1.0.0", None),
        ("demo-1.0.0/Cargo.toml", b"[package]\nname = \"demo\"\n"),
        ("demo-1.0.0/src/lib.rs", b"pub fn f() {}\n"),
        ("demo-1.0.0/.cargo_vcs_info.json", b"{}\n"),
        ("demo-1.0.0/.gitignore", b"target\n"),
        ("demo-1.0.0/.cargo-ok", b"ok"),
        ("demo-1.0.0/.git/HEAD", b"ref: refs/heads/main\n"),
    ])
    good_sum = hashlib.sha256(good).hexdigest()
    lock_text = (
        '[[package]]\nname = "demo"\nversion = "1.0.0"\n'
        f'source = "{CRATES_IO_SOURCE}"\nchecksum = "{{sum}}"\n\n'
        '[[package]]\nname = "tla-core"\nversion = "0.15.0"\n'
        'source = "git+https://github.com/alabsystems/ty.git?rev=1#1"\n\n'
        # The SAME name+version again from a first-party git source, AFTER the
        # crates.io row: the order that made a (name, version)-keyed parse drop
        # the crates.io crate (indexmap 2.14.0 & three more, measured 2026-10-07).
        '[[package]]\nname = "demo"\nversion = "1.0.0"\n'
        'source = "git+https://github.com/alabsystems/ty.git?rev=1#1"\n'
    )

    def run(arm, crate, lock_sum, want_refusal, check=None):
        # want_refusal: None = must stage and pass `check`; else a fragment the
        # refusal must carry, so an arm refused for an UNRELATED reason fails.
        lock_sum = lock_sum or hashlib.sha256(crate).hexdigest()
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp, "cache")
            cache.mkdir()
            Path(cache, "demo-1.0.0.crate").write_bytes(crate)
            lock = Path(tmp, "Cargo.lock")
            lock.write_text(lock_text.replace("{sum}", lock_sum))
            try:
                staged = stage_third_party(Path(tmp, "vendor"), str(lock), [cache], download=False)
                refusal = None
            except StageRefused as exc:
                staged, refusal = 0, str(exc)
            if want_refusal is None:
                ok = refusal is None and check(Path(tmp, "vendor"), staged)
            else:
                ok = refusal is not None and want_refusal in refusal
            print(f"  self-test ARM {'ok' if ok else 'FAILED'}: stage {arm}"
                  + ("" if ok else f" (refusal={refusal!r})"))
            if not ok:
                failures.append(f"stage:{arm}")

    def staged_like_cargo(vendor, staged):
        record = json.loads(Path(vendor, "demo-1.0.0", ".cargo-checksum.json").read_text())
        want_files = {
            "Cargo.toml": hashlib.sha256(b"[package]\nname = \"demo\"\n").hexdigest(),
            "src/lib.rs": hashlib.sha256(b"pub fn f() {}\n").hexdigest(),
            ".cargo_vcs_info.json": hashlib.sha256(b"{}\n").hexdigest(),
        }
        return (staged == 1 and record.get("package") == good_sum
                and record.get("files") == want_files
                and sorted(p.name for p in vendor.iterdir()) == ["demo-1.0.0"])

    # The first-party ty.git rows in the lock are skipped, not staged and not
    # refused -- including the one that shares the crates.io crate's name+version.
    run("stages the crates.io crate as cargo vendors it, first-party twin skipped",
        good, good_sum, want_refusal=None, check=staged_like_cargo)
    run("refuses a .crate whose sha256 is not the lock checksum", good, "0" * 64,
        want_refusal="!= Cargo.lock checksum")
    run("refuses an entry outside the <name>-<version>/ prefix",
        _synthetic_crate("demo", "1.0.0", [("demo-1.0.0/Cargo.toml", b"x"), ("other-1.0.0/x", b"y")]),
        None, want_refusal="is not under demo-1.0.0/")
    run("refuses a symlink entry, as cargo's unpack does",
        _synthetic_crate("demo", "1.0.0", [("demo-1.0.0/Cargo.toml", b"x"), ("demo-1.0.0/link", "symlink")]),
        None, want_refusal="has invalid type")
    return failures


# The fields of a manifest row that Cargo.lock alone determines. `size_bytes`
# and `file_count` are measured on the vendored bytes and need the (gitignored)
# tree; every other field is a function of one lock row, so `--check`
# regenerates them from the lock in full and compares.
LOCK_DERIVED_FIELDS = ("name", "version", "dir", "source_kind", "source", "checksum", "checksum_kind")


def lock_derived_rows(lock_path="Cargo.lock"):
    """Every manifest row Cargo.lock requires, lock-derived fields only, keyed by (name, version).

    One row per crates.io package of the lock (`third_party_packages`), exactly as
    the generator writes it for a faithfully staged tree. Raises StageRefused for a
    lock this flow cannot describe (a non-first-party git source, a registry row
    without a checksum), and for two crates.io rows of one name+version.
    """
    rows = {}
    for name, version, checksum in third_party_packages(parse_cargo_lock(lock_path)):
        key = (name, version)
        if key in rows:
            raise StageRefused(f"{name} {version}: two crates.io rows in {lock_path}")
        rows[key] = {
            "name": name,
            "version": version,
            "dir": f"{name}-{version}",
            "source_kind": "registry",
            "source": CRATES_IO_SOURCE,
            "checksum": checksum,
            "checksum_kind": registry_checksum_kind(checksum),
        }
    return rows


def rows_against_lock(rows, expected, limit=12):
    """Problems of `rows` against `lock_derived_rows`: missing, extra, duplicate, differing.

    R165 (2026-10-27): a staging run stopped at a crate missing from cargo's
    registry cache, the generator wrote a 342-row manifest from the partial tree,
    and `--check` accepted it, because it held each row to the lock's checksum but
    never held the row SET to the lock's crates.io set. A manifest that omits a
    locked crate vouches for a vendor tree that cannot build this lock offline.
    """
    problems = []
    seen = {}
    duplicates = []
    for row in rows:
        key = (row.get("name"), row.get("version"))
        if key in seen:
            duplicates.append(key)
        seen[key] = row

    def listed(label, keys, why):
        if keys:
            problems.append(f"{label}: {len(keys)} {why}:")
            problems.extend(f"    {n} {v}" for n, v in sorted(keys, key=str)[:limit])
            if len(keys) > limit:
                problems.append(f"    … and {len(keys) - limit} more")

    listed("MISSING", [k for k in expected if k not in seen],
           f"of the lock's {len(expected)} crates.io packages have no row (the manifest "
           f"carries {len(rows)}; a partial vendor tree, or a stale manifest)")
    listed("EXTRA", [k for k in seen if k not in expected],
           "rows name no crates.io package of the lock")
    listed("DUPLICATE", duplicates, "name+version pairs carry more than one row")
    differing = []
    for key, want in expected.items():
        got = seen.get(key)
        if got is None:
            continue
        for field in LOCK_DERIVED_FIELDS:
            if got.get(field) != want[field]:
                differing.append(f"    {key[0]} {key[1]}: {field} {got.get(field)!r} != "
                                 f"regenerated {want[field]!r}")
    if differing:
        problems.append(f"DIFFERS: {len(differing)} row field(s) disagree with the row "
                        "regenerated from the lock:")
        problems.extend(differing[:limit])
        if len(differing) > limit:
            problems.append(f"    … and {len(differing) - limit} more")
    return problems


def check_committed(manifest_path="data/vendor_manifest.json", lock_path="Cargo.lock"):
    """Two claims the committed manifest makes that can be checked with NO vendor tree.

    Both inputs are committed, so this runs on any box — which matters, because
    `vendor/` is gitignored and released as an archive, so the generator itself
    cannot run here at all.

    (a) STALENESS. The manifest pins `cargo_lock_sha256`, the digest of the
        Cargo.lock it was generated against. If the live lock differs, every
        "verified equal to Cargo.lock at generation time" claim is about a lock
        that is no longer this repository's.

    (b) A CLAIM THAT WAS NEVER TRUE. `checksum_kind: "sha256-registry"` is
        defined by the manifest's own note as "verified equal to Cargo.lock's
        `checksum =` field at generation time". A row whose NAME could not be a
        crate name — a `+` can only appear in semver BUILD METADATA, never in a
        package name — is one the generator's greedy name/version split mangled
        (`toml-0.9.12+spec-1.1.0` -> name `toml-0.9.12+spec`, version `1.1.0`).
        Its Cargo.lock lookup missed by construction, so the comparison never
        ran, and the row recorded the label anyway. That is independent of (a):
        it was false the day it was written.

    (b) is deliberately NOT "does not resolve in the current lock". 42 rows fail
        that, and 34 of them are ordinary crates whose versions the lock has
        simply moved past since 2026-07-01 — drift, which (a) already reports
        in one line. Conflating the two would let a real never-verified claim
        hide inside a routine staleness list.
    """
    try:
        manifest = vendor_manifest_format.read_manifest(manifest_path)
    except (OSError, ValueError, RecursionError) as exc:
        sys.stderr.write(f"VENDOR_MANIFEST=fail cannot read {manifest_path}: {exc}\n")
        return 1
    problems = []

    pinned = manifest.get("cargo_lock_sha256")
    try:
        live = hashlib.sha256(Path(lock_path).read_bytes()).hexdigest()
    except OSError as exc:
        sys.stderr.write(f"VENDOR_MANIFEST=fail cannot read {lock_path}: {exc}\n")
        return 1
    if pinned != live:
        problems.append(
            f"STALE: the manifest pins cargo_lock_sha256 {str(pinned)[:16]}… and "
            f"{lock_path} now hashes {live[:16]}…, so every "
            "\"verified equal to Cargo.lock at generation time\" claim in it is about a "
            f"lock this repository no longer has (generated_at {manifest.get('generated_at')})"
        )

    rows = manifest["crates"]
    # (c) A MANIFEST OVER NOTHING. Measured 2026-09-15: `cargo vendor` failed
    #     (a cross-source duplicate, below), left an EMPTY vendor/, and the
    #     generator wrote a 0-row manifest pinning the live lock -- which this
    #     check then accepted, because both of its claims were vacuously true.
    #     A lock with packages and a manifest with no rows is not a verified
    #     vendor tree; it is the absence of one.
    if not rows and lock_has_packages(lock_path):
        problems.append(
            f"EMPTY: the manifest carries no rows while {lock_path} names "
            f"{count_lock_packages(lock_path)} packages -- a manifest generated over "
            "an empty or missing vendor/ tree verifies nothing"
        )
    impossible = [r for r in rows if "+" in str(r.get("name", ""))]
    if impossible:
        problems.append(
            f"NEVER VERIFIED: {len(impossible)} of {len(rows)} rows carry a `name` that "
            "cannot be a crate name (a `+` belongs to semver build metadata), so the "
            "name/version split mangled them, their Cargo.lock lookup missed by "
            "construction, and the checksum comparison never ran — while the row still "
            "records checksum_kind "
            + ", ".join(sorted({repr(r.get("checksum_kind")) for r in impossible}))
            + ":"
        )
        problems.extend(f"    {r.get('name')!r} {r.get('version')!r}" for r in impossible)

    # (d) THE WHOLE SET. Regenerate every lock-derived field of every row from
    #     the lock and compare: a row missing, extra, duplicated or differing is
    #     refused (R167; the 342-of-389 manifest R165 found passed (a)-(c)).
    try:
        expected = lock_derived_rows(lock_path)
    except StageRefused as exc:
        problems.append(f"UNDESCRIBABLE LOCK: {exc}")
    else:
        problems.extend(rows_against_lock(rows, expected))
        problems.extend(vendor_manifest_format.summary_problems(manifest))

    if problems:
        sys.stderr.write("VENDOR_MANIFEST=fail\n")
        for line in problems:
            sys.stderr.write(f"  {line}\n")
        sys.stderr.write(
            "  Regenerate from a third-party-only staged tree (vendor/ is gitignored):\n"
            "    python3 scripts/gen_vendor_manifest.py --stage-third-party vendor --download\n"
            "    python3 scripts/gen_vendor_manifest.py vendor\n"
        )
        return 1
    print(
        f"VENDOR_MANIFEST=ok {len(rows)} rows; cargo_lock_sha256 matches the live lock, "
        f"the rows are exactly the {len(rows)} regenerated from its crates.io packages, "
        "and no row claims a checksum it could not have compared"
    )
    return 0


def main():
    if sys.argv[1:] == ["--pinned-inputs"]:
        from script_import_inputs import first_party_imports

        print("\n".join(first_party_imports(Path(__file__))))
        return 0
    if "--self-test" in sys.argv[1:]:
        return self_test()
    if "--check" in sys.argv[1:]:
        rest = [a for a in sys.argv[1:] if a != "--check"]
        return check_committed(*rest[:2])
    if "--stage-third-party" in sys.argv[1:]:
        rest = [a for a in sys.argv[1:] if a not in ("--stage-third-party", "--download")]
        target = rest[0] if rest else "vendor"
        try:
            count = stage_third_party(target, download="--download" in sys.argv[1:])
        except StageRefused as exc:
            sys.stderr.write(f"FATAL: third-party staging refused: {exc}\n")
            return 1
        print(f"staged {count} crates.io crates into {target}/ (first-party git sources are "
              "subrepos and were not staged); now run: python3 scripts/gen_vendor_manifest.py "
              f"{target}")
        return 0
    vendor_dir = sys.argv[1] if len(sys.argv) > 1 else "vendor"
    out_json = sys.argv[2] if len(sys.argv) > 2 else "data/vendor_manifest.json"

    lock = parse_cargo_lock("Cargo.lock")

    unrecognized = unrecognized_vendor_entries(vendor_dir)
    if unrecognized:
        sys.stderr.write(
            "FATAL: vendor tree contains unrecognized top-level entries that "
            "would enter the release archive:\n  "
            + "\n  ".join(unrecognized)
            + "\n"
        )
        sys.exit(1)

    crates = []
    total_bytes = 0
    registry_count = 0
    git_count = 0
    mismatches = []
    internal_sources = []

    for dirname in sorted(os.listdir(vendor_dir)):
        crate_dir = os.path.join(vendor_dir, dirname)
        if not os.path.isdir(crate_dir):
            continue
        checksum_path = os.path.join(crate_dir, ".cargo-checksum.json")
        with open(checksum_path, encoding="utf-8") as f:
            cc = json.load(f)

        name, version = split_name_version(dirname)
        pkg_checksum = cc.get("package")
        files_map = cc.get("files", {})

        # Measure the vendored crate directory size (source bytes on disk).
        size = 0
        for root, _dirs, filenames in os.walk(crate_dir):
            for fn in filenames:
                try:
                    size += os.path.getsize(os.path.join(root, fn))
                except OSError:
                    pass
        total_bytes += size

        try:
            lock_entry = lock_entry_for(lock, name, version, bool(pkg_checksum)) if name else {}
        except StageRefused as exc:
            sys.stderr.write(f"FATAL: {exc}\n")
            sys.exit(1)
        lock_checksum = lock_entry.get("checksum")
        lock_source = lock_entry.get("source")

        if is_internal_source(name, lock_source):
            internal_sources.append(f"{name} {version} ({lock_source or 'unknown source'})")
            continue

        if pkg_checksum:
            # crates.io crate: registry sha256 must equal Cargo.lock's checksum.
            source_kind = "registry"
            registry_count += 1
            checksum = pkg_checksum
            checksum_kind = registry_checksum_kind(lock_checksum)
            if lock_checksum and lock_checksum != pkg_checksum:
                mismatches.append(
                    f"{name} {version}: vendor {pkg_checksum} != lock {lock_checksum}"
                )
        else:
            # git/path crate (carcara): pin by git source + a tree hash over the
            # per-file checksum map so the vendored bytes are still tamper-evident.
            source_kind = "git"
            git_count += 1
            checksum = tree_hash_from_files_map(files_map)
            checksum_kind = "sha256-filetree"

        crates.append(
            {
                "name": name,
                "version": version,
                "dir": dirname,
                "source_kind": source_kind,
                "source": lock_source,
                "checksum": checksum,
                "checksum_kind": checksum_kind,
                "size_bytes": size,
                "file_count": len(files_map),
            }
        )

    if internal_sources:
        sys.stderr.write(
            "FATAL: internal first-party repositories must use subrepos and must "
            "not be included in vendor artifacts:\n  "
            + "\n  ".join(internal_sources)
            + "\n"
        )
        sys.exit(1)

    if not crates and lock_has_packages("Cargo.lock"):
        # The empty-tree vacuity `check_committed` refuses, refused at the
        # source: a `cargo vendor` that failed part-way (measured 2026-09-15:
        # `found duplicate version of package indexmap v2.14.0 vendored from two
        # sources`, crates-io and the first-party ty.git) leaves a directory
        # with nothing in it, and a manifest minted over it would pin the live
        # lock while vouching for zero crates.
        sys.stderr.write(
            f"FATAL: {vendor_dir}/ holds no crate directories while Cargo.lock names "
            f"{count_lock_packages('Cargo.lock')} packages; refusing to write a manifest "
            "over an empty vendor tree\n"
        )
        sys.exit(1)

    # The partial-tree manifest R165 found, refused at the source: a staging run
    # that stopped part-way leaves a tree missing locked crates, and a manifest
    # minted over it pins the live lock while vouching for a subset of it.
    try:
        incomplete = rows_against_lock(crates, lock_derived_rows("Cargo.lock"))
    except StageRefused as exc:
        incomplete = [f"UNDESCRIBABLE LOCK: {exc}"]
    if incomplete:
        sys.stderr.write(
            f"FATAL: {vendor_dir}/ is not the third-party tree Cargo.lock requires; "
            "refusing to write a manifest over it (re-stage into an empty directory with "
            "--stage-third-party, adding --download if cargo's cache lacks a crate):\n  "
            + "\n  ".join(incomplete)
            + "\n"
        )
        sys.exit(1)

    if mismatches:
        sys.stderr.write(
            "FATAL: vendored checksum disagrees with Cargo.lock for:\n  "
            + "\n  ".join(mismatches)
            + "\n"
        )
        sys.exit(1)

    # Record the resolved Cargo.lock digest so the manifest is bound to a
    # specific dependency resolution — a lock change invalidates this manifest.
    with open("Cargo.lock", "rb") as f:
        lock_sha256 = hashlib.sha256(f.read()).hexdigest()

    try:
        generated_at = (
            subprocess.check_output(["date", "-u", "+%Y-%m-%dT%H:%M:%SZ"])
            .decode()
            .strip()
        )
    except Exception:
        generated_at = "unknown"

    manifest = {
        "note": (
            "Provenance + tamper-evidence manifest for the `cargo vendor` source "
            "tree (paragon axis 1: 'every third-party dependency vendored AND "
            "verified'). Each vendored crate is pinned by name+version+checksum. "
            "For crates.io crates the checksum is the registry sha256 (verified "
            "equal to Cargo.lock's `checksum =` field at generation time); for the "
            "git-sourced crate it is a deterministic sha256 over cargo's per-file "
            "checksum map. Restage external sources and re-run "
            "scripts/gen_vendor_manifest.py, then diff against this file to detect "
            "any third-party source drift. Internal AY/NY repositories are "
            "first-party subrepos and are rejected by this generator. "
            "The vendor/ tree itself is GITIGNORED and released as an artifact "
            "(vendor-sources-v*.tar.zst), mirroring the .mathverse shard release "
            "convention — see docs and scripts/package_vendor.sh."
        ),
        "schema_version": 1,
        "generated_at": generated_at,
        "generator": "scripts/gen_vendor_manifest.py",
        "cargo_lock_sha256": lock_sha256,
        "summary": {
            "total_crates": len(crates),
            "registry_crates": registry_count,
            "git_crates": git_count,
            "total_size_bytes": total_bytes,
            "total_size_mb": round(total_bytes / 1_048_576, 1),
        },
        "crates": crates,
    }

    os.makedirs(os.path.dirname(out_json), exist_ok=True)
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=False)
        f.write("\n")

    print(
        f"Wrote {out_json}: {len(crates)} crates "
        f"({registry_count} registry + {git_count} git), "
        f"{manifest['summary']['total_size_mb']} MB"
    )


if __name__ == "__main__":
    # `main()` alone DISCARDED the return value, so --check could never fail the
    # process however loudly it complained: measured 2026-09-14, the check
    # printed 42 unbacked rows and exited 0. Read the exit code, always.
    raise SystemExit(main())
