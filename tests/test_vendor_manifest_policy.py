# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import importlib.util
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
