# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Regression tests for scripts.dead_code_audit.

The synthetic workspace exercises the first-pass scanner requirements:

  * top-level `pub` items are collected
  * pub items inside `impl` blocks and `pub use` re-exports are ignored
  * cross-crate references are estimated with file:line evidence
  * ignore rules suppress intentional API surface
  * `--fail-on-candidates` produces CI-friendly non-zero exit codes
"""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.dead_code_audit import load_ignore_rules, main, scan_workspace


def _write(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def _make_workspace(root: Path, *, include_non_code_mentions: bool = False) -> tuple[Path, Path, Path]:
    _write(
        root / "Cargo.toml",
        """
[workspace]
members = ["crates/a", "crates/b"]
""".strip()
        + "\n",
    )

    crate_a = root / "crates" / "a"
    crate_b = root / "crates" / "b"

    _write(
        crate_a / "Cargo.toml",
        """
[package]
name = "a"
version = "0.1.0"
edition = "2021"
""".strip()
        + "\n",
    )
    _write(
        crate_b / "Cargo.toml",
        """
[package]
name = "b"
version = "0.1.0"
edition = "2021"
""".strip()
        + "\n",
    )

    _write(
        crate_a / "src" / "lib.rs",
        """
pub fn used_cross_crate() {}

pub fn dead_candidate() {}

pub fn mention_only_in_non_code() {}

pub struct PublicType;

impl PublicType {
    pub fn associated_dead(&self) {}
}

pub use self::used_cross_crate as exported_used_cross_crate;

#[cfg(test)]
mod tests {
    pub fn test_helper() {}
}

#[cfg(test)]
pub fn top_level_test_helper() {}
""".strip()
        + "\n",
    )

    crate_b_body = """
use a::used_cross_crate;

pub fn call_used() {
    used_cross_crate();
}
""".strip()
    if include_non_code_mentions:
        crate_b_body = """
use a::used_cross_crate;

const _STRING_ONLY: &str = "mention_only_in_non_code";
const _RAW_STRING_ONLY: &str = r#"mention_only_in_non_code"#;

/*
mention_only_in_non_code
*/

pub fn call_used() {
    used_cross_crate();
}
""".strip()

    _write(
        crate_b / "src" / "lib.rs",
        crate_b_body + "\n",
    )

    return root, crate_a, crate_b


class DeadCodeAuditTests(unittest.TestCase):
    def test_scan_workspace_finds_dead_candidates_and_skips_false_positives(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root, crate_a, _crate_b = _make_workspace(Path(td))
            result = scan_workspace(root, crate_filter="a")

            names = {item.name for item in result.all_items}
            self.assertIn("used_cross_crate", names)
            self.assertIn("dead_candidate", names)
            self.assertIn("PublicType", names)
            self.assertIn("associated_dead", names)
            self.assertNotIn("exported_used_cross_crate", names)
            self.assertNotIn("test_helper", names)
            self.assertNotIn("top_level_test_helper", names)

            dead = {item.name for item in result.dead_items}
            self.assertIn("dead_candidate", dead)
            self.assertIn("mention_only_in_non_code", dead)
            self.assertIn("PublicType", dead)
            self.assertIn("associated_dead", dead)
            self.assertNotIn("used_cross_crate", dead)

            used = next(item for item in result.all_items if item.name == "used_cross_crate")
            self.assertEqual(used.cross_crate_crates, 1)
            self.assertEqual(used.cross_crate_files, 1)
            self.assertGreaterEqual(used.cross_crate_sites, 1)
            self.assertEqual(used.reference_crates, ["b"])
            self.assertTrue(any(ref.file_path.endswith("crates/b/src/lib.rs") for ref in used.references))

            dead_item = next(item for item in result.dead_items if item.name == "dead_candidate")
            self.assertEqual(dead_item.cross_crate_crates, 0)

    def test_ignore_file_suppresses_named_item(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root, crate_a, _crate_b = _make_workspace(Path(td))
            ignore_file = root / "data" / "dead_code_ignore.toml"
            _write(
                ignore_file,
                f"""
[[ignore]]
crate = "a"
file = "{(crate_a / 'src' / 'lib.rs').relative_to(root)}"
line = 3
""".strip()
                + "\n",
            )

            rules = load_ignore_rules(ignore_file)
            result = scan_workspace(root, crate_filter="a", ignore_rules=rules)
            self.assertEqual(len(result.ignored_items), 1)
            self.assertEqual(
                {item.name for item in result.dead_items},
                {"mention_only_in_non_code", "PublicType", "associated_dead"},
            )
            self.assertNotIn("dead_candidate", {item.name for item in result.all_items})

    def test_non_code_mentions_do_not_count_as_cross_crate_references(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root, _crate_a, _crate_b = _make_workspace(Path(td), include_non_code_mentions=True)
            result = scan_workspace(root, crate_filter="a")

            item = next(item for item in result.dead_items if item.name == "mention_only_in_non_code")
            self.assertEqual(item.cross_crate_crates, 0)
            self.assertEqual(item.cross_crate_files, 0)
            self.assertEqual(item.cross_crate_sites, 0)

    def test_fail_on_candidates_sets_non_zero_exit_code(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root, _crate_a, _crate_b = _make_workspace(Path(td))
            rc = main(["--root", str(root), "--crate", "a", "--fail-on-candidates"])
            self.assertEqual(rc, 1)

    def test_json_mode_remains_machine_readable(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root, _crate_a, _crate_b = _make_workspace(Path(td))
            rc = main(["--root", str(root), "--crate", "a", "--json"])
            self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
