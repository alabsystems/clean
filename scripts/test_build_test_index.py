# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Regression tests for scripts.build_test_index."""

from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_test_index import build_index, cache_path_for, main


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _make_workspace(root: Path) -> Path:
    _write(
        root / "Cargo.toml",
        """
[workspace]
members = ["crates/alpha", "crates/beta"]
""".strip()
        + "\n",
    )
    _write(
        root / "crates/alpha/Cargo.toml",
        """
[package]
name = "alpha"
version = "0.1.0"
edition = "2021"
""".strip()
        + "\n",
    )
    _write(
        root / "crates/alpha/src/lib.rs",
        """
#[cfg(test)]
mod nested {
    #[test]
    fn alpha_test() {}
}

#[test]
fn root_test() {}
""".strip()
        + "\n",
    )
    _write(
        root / "crates/beta/Cargo.toml",
        """
[package]
name = "beta"
version = "0.1.0"
edition = "2021"
""".strip()
        + "\n",
    )
    _write(
        root / "crates/beta/tests/integration.rs",
        """
mod basic;

#[test]
fn beta_integration() {}
""".strip()
        + "\n",
    )
    _write(
        root / "crates/beta/tests/integration/basic.rs",
        """
#[test]
fn beta_nested_integration() {}
""".strip()
        + "\n",
    )
    _write(
        root / "crates/beta/tests/tree_case/main.rs",
        """
mod nested;
""".strip()
        + "\n",
    )
    _write(
        root / "crates/beta/tests/tree_case/nested.rs",
        """
#[test]
fn beta_tree_test() {}
""".strip()
        + "\n",
    )
    return root


def _make_bin_workspace(root: Path) -> Path:
    _write(
        root / "Cargo.toml",
        """
[workspace]
members = ["crates/gamma"]
""".strip()
        + "\n",
    )
    _write(
        root / "crates/gamma/Cargo.toml",
        """
[package]
name = "gamma"
version = "0.1.0"
edition = "2021"
""".strip()
        + "\n",
    )
    _write(
        root / "crates/gamma/src/main.rs",
        """
#[test]
fn root_bin_test() {}
""".strip()
        + "\n",
    )
    _write(
        root / "crates/gamma/src/bin/tool.rs",
        """
mod nested {
    #[test]
    fn tool_nested_test() {}
}
""".strip()
        + "\n",
    )
    _write(
        root / "crates/gamma/src/bin/worker/main.rs",
        """
#[test]
fn worker_main_test() {}
""".strip()
        + "\n",
    )
    _write(
        root / "crates/gamma/src/bin/worker/helper.rs",
        """
#[test]
fn worker_helper_test() {}
""".strip()
        + "\n",
    )
    return root


class BuildTestIndexTests(unittest.TestCase):
    def test_build_writes_default_cache_path(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "build",
                        "--workspace-root",
                        str(workspace),
                    ]
                )
            self.assertEqual(rc, 0)

            cache_path = cache_path_for(workspace)
            self.assertTrue(cache_path.exists())
            payload = json.loads(cache_path.read_text(encoding="utf-8"))
            self.assertEqual(payload["total_crates"], 2)
            self.assertEqual(payload["total_tests"], 5)
            self.assertIn("Written to", stdout.getvalue())

    def test_build_can_write_deterministic_generated_at(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "build",
                        "--workspace-root",
                        str(workspace),
                        "--deterministic",
                    ]
                )
            self.assertEqual(rc, 0)

            payload = json.loads(cache_path_for(workspace).read_text(encoding="utf-8"))

        self.assertEqual(payload["generated_at"], "1970-01-01T00:00:00Z")
        self.assertIn("Written to", stdout.getvalue())

    def test_build_generated_at_override_wins_over_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "build",
                        "--workspace-root",
                        str(workspace),
                        "--deterministic",
                        "--generated-at",
                        "2026-04-26T00:00:00Z",
                    ]
                )
            self.assertEqual(rc, 0)

            payload = json.loads(cache_path_for(workspace).read_text(encoding="utf-8"))

        self.assertEqual(payload["generated_at"], "2026-04-26T00:00:00Z")

    def test_build_index_is_stable_with_fixed_generated_at(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            first = build_index(workspace, generated_at="fixed")
            second = build_index(workspace, generated_at="fixed")

        self.assertEqual(first, second)
        self.assertEqual(
            [
                (test["package"], test["module"], test["name"], test["file"])
                for test in first["tests"]
            ],
            sorted(
                (test["package"], test["module"], test["name"], test["file"])
                for test in first["tests"]
            ),
        )

    def test_query_returns_copy_pasteable_cargo_command(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "query",
                        "alpha_test",
                        "--workspace-root",
                        str(workspace),
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(
                stdout.getvalue().strip(),
                "cargo test --locked --message-format=short -j 1 -p alpha --lib -- nested::alpha_test",
            )

    def test_query_supports_integration_tests(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "query",
                        "beta_integration",
                        "--workspace-root",
                        str(workspace),
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(
                stdout.getvalue().strip(),
                "cargo test --locked --message-format=short -j 1 -p beta --test integration -- beta_integration",
            )

    def test_query_supports_nested_integration_tree_targets(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "query",
                        "beta_tree_test",
                        "--workspace-root",
                        str(workspace),
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(
                stdout.getvalue().strip(),
                "cargo test --locked --message-format=short -j 1 -p beta --test tree_case -- nested::beta_tree_test",
            )

    def test_query_supports_nested_modules_under_flat_integration_harness(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_workspace(Path(td))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "query",
                        "beta_nested_integration",
                        "--workspace-root",
                        str(workspace),
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(
                stdout.getvalue().strip(),
                "cargo test --locked --message-format=short -j 1 -p beta --test integration -- basic::beta_nested_integration",
            )

    def test_query_supports_binary_targets(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_bin_workspace(Path(td))

            for pattern, expected in [
                (
                    "root_bin_test",
                    "cargo test --locked --message-format=short -j 1 -p gamma --bin gamma -- root_bin_test",
                ),
                (
                    "tool_nested_test",
                    "cargo test --locked --message-format=short -j 1 -p gamma --bin tool -- nested::tool_nested_test",
                ),
                (
                    "worker_main_test",
                    "cargo test --locked --message-format=short -j 1 -p gamma --bin worker -- worker_main_test",
                ),
                (
                    "worker_helper_test",
                    "cargo test --locked --message-format=short -j 1 -p gamma --bin worker -- helper::worker_helper_test",
                ),
            ]:
                stdout = io.StringIO()
                with contextlib.redirect_stdout(stdout):
                    rc = main(
                        [
                            "query",
                            pattern,
                            "--workspace-root",
                            str(workspace),
                        ]
                    )
                self.assertEqual(rc, 0)
                self.assertEqual(stdout.getvalue().strip(), expected)

            payload = json.loads(cache_path_for(workspace).read_text(encoding="utf-8"))
            self.assertEqual(payload["schema_version"], 3)
            self.assertEqual(payload["total_tests"], 4)

    def test_query_rebuilds_stale_cache_version(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            workspace = _make_bin_workspace(Path(td))
            cache_path = cache_path_for(workspace)
            cache_path.parent.mkdir(parents=True, exist_ok=True)
            cache_path.write_text(
                json.dumps(
                    {
                        "schema_version": 2,
                        "tests": [
                            {
                                "name": "stale",
                                "module": "stale",
                                "file": "stale.rs",
                                "line": 1,
                                "cargo_cmd": "cargo test --locked --message-format=short -j 1 -p gamma -- stale",
                                "package": "gamma",
                                "kind": "lib",
                            }
                        ],
                    },
                    indent=2,
                )
                + "\n",
                encoding="utf-8",
            )

            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "query",
                        "worker_main_test",
                        "--workspace-root",
                        str(workspace),
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(
                stdout.getvalue().strip(),
                "cargo test --locked --message-format=short -j 1 -p gamma --bin worker -- worker_main_test",
            )

            payload = json.loads(cache_path.read_text(encoding="utf-8"))
            self.assertEqual(payload["schema_version"], 3)
            self.assertEqual(payload["total_tests"], 4)

    def test_fixtures_do_not_reintroduce_unbounded_cargo_examples(self) -> None:
        source = Path(__file__).read_text(encoding="utf-8")

        self.assertNotIn("cargo test" + " -p gamma -- stale", source)


if __name__ == "__main__":
    unittest.main()
