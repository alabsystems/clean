#!/usr/bin/env python3
"""Guard the feature contract of Clean's aterm package recipe."""

from pathlib import Path
import json
import os
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


def requested_features(arguments):
    features = set()
    for index, argument in enumerate(arguments):
        if argument == "--features" and index + 1 < len(arguments):
            features.update(arguments[index + 1].replace(",", " ").split())
        elif argument.startswith("--features="):
            features.update(argument.split("=", 1)[1].replace(",", " ").split())
    return features


class AtpkgRecipeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Use the canonical Trust frontend directly; atpkg installations need
        # not have a rustup launcher. TARGO may name one explicit executable.
        command = [os.environ.get("TARGO") or "targo"]
        result = subprocess.run(
            [*command, "metadata", "--locked", "--no-deps", "--format-version", "1"],
            cwd=ROOT, check=True, capture_output=True, text=True,
        )
        cls.metadata = json.loads(result.stdout)
        cls.packages = {package["name"]: package for package in cls.metadata["packages"]}

    def test_packaged_clean_enables_independent_ay_proof_checking(self):
        recipe = self.metadata["metadata"]["atpkg"]
        self.assertIn("clean", recipe["expose"])
        self.assertIn("clean/carcara-verify", requested_features(recipe["build-args"]))

    def test_feature_reaches_the_checker_and_ay_smt_gate(self):
        for crate, target in [("clean", "clean-cli"), ("clean-cli", "clean-elab")]:
            self.assertIn(f"{target}/carcara-verify", self.packages[crate]["features"]["carcara-verify"])
        features = self.packages["clean-elab"]["features"]["carcara-verify"]
        self.assertIn("ay-smt", features)
        self.assertIn("clean-auto/carcara-verify", features)

    def test_old_default_build_recipe_lacks_the_required_capability(self):
        self.assertNotIn("clean/carcara-verify", requested_features(["-p", "clean", "-p", "clean-lsp"]))

    # Two-language roadmap WS6.13 (F-119, scout-lean B7): the shipped `clean`
    # MUST carry the trust-ir backend, so `--emit trustir|trustir-bin|obj`
    # exist in the pack. Conditional on the facade DECLARING the feature: the
    # private tree declares it and the recipe must request it (strict); the
    # bootstrap public export excises the backend and its recipe mention
    # together (publish/transform.py), so there the clause is vacuous — never
    # a feature the manifest cannot build.
    def test_scout_lean_b7_packaged_clean_enables_trust_ir_backend(self):
        recipe = self.metadata["metadata"]["atpkg"]
        requested = requested_features(recipe["build-args"])
        declared = "trust-ir-backend" in self.packages["clean"]["features"]
        if declared:
            self.assertIn("clean/trust-ir-backend", requested)
        else:
            self.assertNotIn("clean/trust-ir-backend", requested)

    def test_trust_ir_backend_feature_reaches_the_compiler_backend(self):
        if "trust-ir-backend" not in self.packages["clean"]["features"]:
            self.assertNotIn("trust-ir-backend", self.packages["clean-cli"]["features"])
            self.assertNotIn("trust-ir-backend", self.packages["clean-compiler"]["features"])
            return
        for crate, target in [("clean", "clean-cli"), ("clean-cli", "clean-compiler")]:
            self.assertIn(f"{target}/trust-ir-backend", self.packages[crate]["features"]["trust-ir-backend"])
        backend = self.packages["clean-compiler"]["features"]["trust-ir-backend"]
        for dep in ("dep:trust-ir", "dep:trust-ir-build"):
            self.assertIn(dep, backend)

    def test_old_default_build_recipe_lacks_the_trust_ir_backend(self):
        self.assertNotIn(
            "clean/trust-ir-backend",
            requested_features(["-p", "clean", "-p", "clean-lsp", "--features", "clean/carcara-verify"]),
        )

    def test_feature_argument_forms(self):
        expected = {"clean/carcara-verify", "clean/mimalloc"}
        self.assertEqual(requested_features(["--features", "clean/carcara-verify,clean/mimalloc"]), expected)
        self.assertEqual(requested_features(["--features=clean/carcara-verify clean/mimalloc"]), expected)


if __name__ == "__main__":
    unittest.main()
