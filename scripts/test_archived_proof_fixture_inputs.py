#!/usr/bin/env python3
"""Archived proof inputs stay reproducible and live Cargo graphs stay checked."""

from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_workspace_dependency_boundary as boundary
import trust_ir_pin_legs as legs


class ArchivedProofFixtureInputs(unittest.TestCase):
    def test_template_is_archived_but_an_active_report_manifest_still_refuses(self):
        def manifest(section, keys, revision):
            return f"[{section}]\n" + "".join(
                f'{key} = {{ git = "{legs.TRUST_IR_URL}", rev = "{revision}" }}\n'
                for key in keys
            )

        with tempfile.TemporaryDirectory(prefix="clean-proof-inputs-") as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q", "--template=", str(root)], check=True)
            for relative, keys in legs.TRUST_IR_LEGS.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                section = "workspace.dependencies" if relative == "Cargo.toml" else "dependencies"
                path.write_text(manifest(section, keys, "a" * 40))
            preimages = root / "reports/replay/preimages"
            preimages.mkdir(parents=True)
            template = preimages / "Cargo.toml.in"
            template.write_text(manifest("workspace.dependencies", ("trust-ir-contract",), "b" * 40))
            subprocess.run(["git", "add", "--", "."], cwd=root, check=True)
            self.assertEqual(legs.manifest_revision(legs.read_tracked(root, "*Cargo.toml"), "trust-ir"), "a" * 40)

            active = preimages / "Cargo.toml"
            active.write_bytes(template.read_bytes())
            subprocess.run(["git", "add", "--", "."], cwd=root, check=True)
            with self.assertRaises(legs.PinShapeError) as refused:
                legs.census(legs.read_tracked(root, "*Cargo.toml"), "trust-ir")
            self.assertIn(str(active.relative_to(root)), str(refused.exception))

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
