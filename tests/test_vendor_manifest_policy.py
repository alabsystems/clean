# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "gen_vendor_manifest.py"
SPEC = importlib.util.spec_from_file_location("clean_gen_vendor_manifest", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
generator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = generator
SPEC.loader.exec_module(generator)


def test_internal_ay_and_ny_are_never_vendor_sources() -> None:
    assert generator.is_internal_source(
        "ay-sat",
        "git+https://github.com/alabsystems/ay.git?rev=abc#abc",
    )
    assert generator.is_internal_source(
        "ny-core",
        "git+https://github.com/alabsystems/ny.git?rev=abc#abc",
    )
    assert generator.is_internal_source(
        "renamed-internal",
        "git+ssh://git@github.com/alabsystems/internal.git?rev=abc#abc",
    )


def test_external_git_sources_remain_vendor_eligible() -> None:
    assert not generator.is_internal_source(
        "carcara",
        "git+https://github.com/ufmg-smite/carcara?rev=abc#abc",
    )


def test_unrecognized_vendor_entries_fail_closed(tmp_path: Path) -> None:
    (tmp_path / "internal-copy").mkdir()
    (tmp_path / "loose-internal.txt").write_text("must never be archived\n")

    problems = generator.unrecognized_vendor_entries(tmp_path)

    assert problems == [
        "internal-copy: missing .cargo-checksum.json",
        "loose-internal.txt: unexpected top-level file",
    ]


MANIFEST = ROOT / "data" / "vendor_manifest.json"
LOCK = ROOT / "Cargo.lock"


def test_committed_manifest_is_the_full_set_regenerated_from_the_lock() -> None:
    """Control: the real manifest passes, and covers every crates.io package."""
    assert generator.check_committed(str(MANIFEST), str(LOCK)) == 0
    rows = json.loads(MANIFEST.read_text())["crates"]
    assert len(rows) == len(generator.lock_derived_rows(str(LOCK)))


def test_manifest_missing_one_locked_crate_is_refused(tmp_path: Path, capsys) -> None:
    """R165's 342-of-389 manifest, reduced to one removed row: refused for MISSING."""
    manifest = json.loads(MANIFEST.read_text())
    removed = manifest["crates"].pop(len(manifest["crates"]) // 2)
    mutant = tmp_path / "vendor_manifest.json"
    mutant.write_text(json.dumps(manifest))

    assert generator.check_committed(str(mutant), str(LOCK)) == 1
    said = capsys.readouterr().err
    assert "MISSING: 1 of" in said
    assert f"{removed['name']} {removed['version']}" in said


def test_lock_changed_without_regenerating_is_refused(tmp_path: Path, capsys) -> None:
    """86588a484's shape: a lock edit that moves no crates.io package still reds."""
    lock = tmp_path / "Cargo.lock"
    lock.write_bytes(LOCK.read_bytes() + b"\n")

    assert generator.check_committed(str(MANIFEST), str(lock)) == 1
    assert "STALE:" in capsys.readouterr().err
