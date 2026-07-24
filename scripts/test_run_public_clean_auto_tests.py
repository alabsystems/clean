#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Unit tests for the public clean-auto release shard planner."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("run_public_clean_auto_tests.py")
SPEC = importlib.util.spec_from_file_location("public_clean_auto", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class InventoryTests(unittest.TestCase):
    def test_parses_terse_inventory_and_summary(self) -> None:
        output = "a::one: test\na::two: test\n\n2 tests, 0 benchmarks\n"
        self.assertEqual(
            MODULE.parse_inventory(output, "fixture"),
            ["a::one", "a::two"],
        )

    def test_accepts_native_terse_inventory_without_summary(self) -> None:
        self.assertEqual(
            MODULE.parse_inventory("a::one: test\n", "fixture"), ["a::one"]
        )

    def test_rejects_unknown_output(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "unexpected"):
            MODULE.parse_inventory(
                "a::one: benchmark\n1 test, 1 benchmark\n", "fixture"
            )


class PartitionTests(unittest.TestCase):
    def test_partition_is_bounded_disjoint_and_complete(self) -> None:
        names = [
            "alpha::small::one",
            "alpha::small::two",
            "alpha::large::one",
            "alpha::large::two",
            "alpha::large::three",
            "beta::one",
        ]
        shards = MODULE.partition_inventory(names, 2)
        covered = [name for shard in shards for name in shard.expected]
        self.assertCountEqual(covered, names)
        self.assertEqual(len(covered), len(set(covered)))
        self.assertLessEqual(max(len(shard.expected) for shard in shards), 2)

    def test_substring_collision_falls_back_to_narrower_shards(self) -> None:
        names = ["left::shared::one", "prefix::left::shared::two"]
        shards = MODULE.partition_inventory(names, 1)
        self.assertEqual(
            {name for shard in shards for name in shard.expected}, set(names)
        )
        for shard in shards:
            selected = {name for name in names if shard.selector in name}
            if shard.mode == "filter":
                self.assertEqual(selected, set(shard.expected))

    def test_exact_command_places_harness_arguments_after_separator(self) -> None:
        shard = MODULE.Shard("exact", "a::one", ("a::one",))
        self.assertEqual(
            MODULE.cargo_command(shard, "--list", "--format", "terse")[-6:],
            ["--", "a::one", "--exact", "--list", "--format", "terse"],
        )


if __name__ == "__main__":
    unittest.main()
