#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the static Rust source-inventory synchronizer."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("sync_readme_metrics.py")
SPEC = importlib.util.spec_from_file_location("sync_readme_metrics", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {MODULE_PATH}")
sync_readme_metrics = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = sync_readme_metrics
SPEC.loader.exec_module(sync_readme_metrics)


class SourceInventoryTests(unittest.TestCase):
    """Exercise archive operation and fail-closed source reads."""

    def test_archive_snapshot_without_git_metadata_is_inventoried(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "crates" / "demo" / "src" / "lib.rs"
            source.parent.mkdir(parents=True)
            source.write_text("#[test]\nfn archive_test() {}\n", encoding="utf-8")

            layout = sync_readme_metrics.build_layout(root)
            files = sync_readme_metrics.tracked_rust_files(layout)

            self.assertEqual(files, [source.resolve()])
            self.assertEqual(sync_readme_metrics.count_loc(files), 2)
            self.assertEqual(sync_readme_metrics.count_test_attributes(files), 1)

    def test_missing_tracked_source_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            missing = Path(directory) / "missing.rs"
            with self.assertRaises(FileNotFoundError):
                sync_readme_metrics.count_loc([missing])
            with self.assertRaises(FileNotFoundError):
                sync_readme_metrics.count_test_attributes([missing])


if __name__ == "__main__":
    unittest.main()
