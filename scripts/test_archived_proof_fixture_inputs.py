#!/usr/bin/env python3
"""Archived proof inputs stay reproducible; real nested locks stay checked."""

from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_workspace_dependency_boundary as boundary


class ArchivedProofFixtureInputs(unittest.TestCase):
    def test_template_is_archived_but_an_active_nested_lock_still_refuses(self):
        def lock(revision):
            return (
                'version = 4\n\n[[package]]\nname = "trust-ir"\nversion = "0.14.0"\n'
                'source = "git+https://github.com/alabsystems/trust-ir.git'
                f'?rev={revision}#{revision}"\n'
            )

        with tempfile.TemporaryDirectory(prefix="clean-proof-inputs-") as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q", "--template=", str(root)], check=True)
            fixture = root / "crates/clean-verify/tests/fixtures/proof"
            fixture.mkdir(parents=True)
            (root / "Cargo.lock").write_text(lock("a" * 40))
            template = fixture / "Cargo.lock.in"
            template.write_text(lock("b" * 40))
            subprocess.run(["git", "add", "--", "."], cwd=root, check=True)
            with patch.object(boundary, "ROOT", root):
                paths = boundary.tracked_lock_paths()
                self.assertEqual(paths, [root / "Cargo.lock"])
                inventory = {str(p.relative_to(root)): p.read_text() for p in paths}
                self.assertEqual(
                    boundary.check_trust_ir_lock_inventory(inventory, "Cargo.lock"),
                    "a" * 40,
                )
                # Restoring an ordinary active lock in the same fixture tree
                # must re-enter the real census and retain its exact refusal.
                active = fixture / "Cargo.lock"
                active.write_bytes(template.read_bytes())
                subprocess.run(["git", "add", "--", "."], cwd=root, check=True)
                paths = boundary.tracked_lock_paths()
                self.assertIn(active, paths)
                inventory = {str(p.relative_to(root)): p.read_text() for p in paths}
                with self.assertRaises(boundary.BoundaryViolation) as refused:
                    boundary.check_trust_ir_lock_inventory(inventory, "Cargo.lock")
                self.assertIn(str(active.relative_to(root)), str(refused.exception))


if __name__ == "__main__":
    unittest.main()
