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

import hashlib
import json
import os
import re
import subprocess
import sys

INTERNAL_GIT_SOURCE_MARKERS = (
    "github.com/alabsystems/",
    "github.com/alabsystems/ay",
    "github.com/alabsystems/ny",
)


def parse_cargo_lock(lock_path):
    """Return {(name, version): {'checksum': str|None, 'source': str|None}}."""
    with open(lock_path, encoding="utf-8") as f:
        text = f.read()
    entries = {}
    # Cargo.lock is a sequence of [[package]] TOML tables.
    for block in text.split("[[package]]"):
        name = re.search(r'^name = "([^"]+)"', block, re.MULTILINE)
        ver = re.search(r'^version = "([^"]+)"', block, re.MULTILINE)
        if not name or not ver:
            continue
        checksum = re.search(r'^checksum = "([^"]+)"', block, re.MULTILINE)
        source = re.search(r'^source = "([^"]+)"', block, re.MULTILINE)
        entries[(name.group(1), ver.group(1))] = {
            "checksum": checksum.group(1) if checksum else None,
            "source": source.group(1) if source else None,
        }
    return entries


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
    """`zeroize-1.9.0` -> ('zeroize', '1.9.0'); handles hyphenated names."""
    m = re.match(r"^(.*)-(\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.+-]+)?)$", dirname)
    if not m:
        return None, None
    return m.group(1), m.group(2)


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


def main():
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

        lock_entry = lock.get((name, version), {}) if name else {}
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
            checksum_kind = "sha256-registry"
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
    main()
