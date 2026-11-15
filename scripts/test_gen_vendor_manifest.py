#!/usr/bin/env python3
"""Independent CLI checks for the vendor manifest's metadata contract.

No archives, staging tree, compiler or native build is needed. Measured byte
and file counts are checked for domains and internal consistency only.
"""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/gen_vendor_manifest.py"
SOURCE = "registry+https://github.com/rust-lang/crates.io-index"
BAD_COUNTERS = (False, True, -1, 0.5, 1.0, float("nan"), float("inf"), float("-inf"), "1", None)


class VendorManifestSchemaTests(unittest.TestCase):
    def test_missing_cache_advice_uses_the_neutral_fetch_lane(self) -> None:
        name = "missing-cache-" + hashlib.sha256(str(self.root).encode()).hexdigest()[:16]
        lock = self.package(name, "1.2.3", "a" * 64).encode()
        self.lock_path.write_bytes(lock)
        vendor = self.root / "vendor"
        result = subprocess.run([sys.executable, str(SCRIPT), "--stage-third-party", str(vendor)],
                                cwd=self.root, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("is not in cargo's registry cache", result.stderr)
        self.assertIn("`targo fetch --locked`", result.stderr)
        self.assertNotIn("targo --unverified fetch", result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        self.assertEqual(self.lock_path.read_bytes(), lock)
        self.assertFalse(vendor.exists() and any(vendor.iterdir()))

    def test_oversized_derived_sum_refuses_without_traceback(self) -> None:
        from unittest.mock import patch

        data = copy.deepcopy(self.manifest)
        row = copy.deepcopy(data["crates"][0])
        row.update(name="second", dir="second-1.2.3")
        data["crates"].append(row)
        self.lock_path.write_bytes(self.lock_bytes + self.package("second", "1.2.3", "a" * 64).encode())
        data["cargo_lock_sha256"] = hashlib.sha256(self.lock_path.read_bytes()).hexdigest()
        data["summary"].update(total_crates=2, registry_crates=2, total_size_bytes=0)
        del data["summary"]["total_size_mb"]
        raw = json.dumps(data).replace('"size_bytes": 123', '"size_bytes": ' + '9' * 4300)
        with patch.dict("os.environ", {"PYTHONINTMAXSTRDIGITS": "4300"}):
            self.assert_raw_refused(raw)

    def test_optional_mb_display_has_numeric_domain_and_canonical_rounding(self) -> None:
        for value in (0, 0.0):
            data = copy.deepcopy(self.manifest)
            data["summary"]["total_size_mb"] = value
            self.assert_accepted(data)
        for value in (False, True, "0.0", None, -1, 0.1):
            with self.subTest(value=value):
                data = copy.deepcopy(self.manifest)
                data["summary"]["total_size_mb"] = value
                self.assert_refused(data)
        data = copy.deepcopy(self.manifest)
        data["crates"][0]["size_bytes"] = 10 ** 4000
        data["summary"].update(total_size_bytes=10 ** 4000, total_size_mb=0)
        self.assert_refused(data)

    def test_pinned_inputs_include_both_checker_helpers(self) -> None:
        result = subprocess.run([sys.executable, str(SCRIPT), "--pinned-inputs"],
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(),
                         ["scripts/script_import_inputs.py", "scripts/vendor_manifest_format.py"])

    def test_input_walk_is_transitive_and_ignores_comment_and_string_imports(self) -> None:
        from script_import_inputs import first_party_imports

        scripts = self.root / "scripts"
        scripts.mkdir()
        entry = scripts / "entry.py"
        entry.write_text("import middle\ndef late():\n from leaf import value\n"
                         "# import decoy\ntext = 'import decoy'\n")
        (scripts / "middle.py").write_text("import leaf\nimport entry\n")
        (scripts / "leaf.py").write_text("import json\n")
        (scripts / "decoy.py").write_text("raise RuntimeError('must never execute')\n")
        self.assertEqual(first_party_imports(entry), ["scripts/leaf.py", "scripts/middle.py"])

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="vendor-schema-tests-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.manifest_path = self.root / "manifest.json"
        self.lock_path = self.root / "Cargo.lock"
        self.lock_bytes = self.package("demo", "1.2.3", "a" * 64).encode()
        self.lock_path.write_bytes(self.lock_bytes)
        self.manifest = {
            "schema_version": 1,
            "generator": "scripts/gen_vendor_manifest.py",
            "generated_at": "2026-11-13T00:00:00Z",
            "note": "A complete metadata fixture; not staged-source evidence.",
            "cargo_lock_sha256": hashlib.sha256(self.lock_bytes).hexdigest(),
            "summary": {
                "total_crates": 1,
                "registry_crates": 1,
                "git_crates": 0,
                "total_size_bytes": 123,
                "total_size_mb": 0.0,
            },
            "crates": [{
                "name": "demo", "version": "1.2.3", "dir": "demo-1.2.3",
                "source_kind": "registry", "source": SOURCE,
                "checksum": "a" * 64, "checksum_kind": "sha256-registry",
                "size_bytes": 123, "file_count": 2,
            }],
        }

    @staticmethod
    def package(name: str, version: str, checksum: str) -> str:
        return (f'[[package]]\nname = "{name}"\nversion = "{version}"\n'
                f'source = "{SOURCE}"\nchecksum = "{checksum}"\n\n')

    def run_raw(self, raw: str):
        self.manifest_path.write_text(raw, encoding="utf-8")
        before = (self.manifest_path.read_bytes(), self.lock_path.read_bytes())
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--check", str(self.manifest_path), str(self.lock_path)],
            cwd=self.root, text=True, capture_output=True, timeout=10,
        )
        self.assertEqual((self.manifest_path.read_bytes(), self.lock_path.read_bytes()), before)
        return result

    def run_manifest(self, manifest):
        # Nonfinite hostile fixtures are deliberately encoded here; refusal
        # must come from the production reader, not the test fixture writer.
        return self.run_raw(json.dumps(manifest))

    def assert_accepted(self, manifest) -> None:
        result = self.run_manifest(manifest)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("VENDOR_MANIFEST=ok", result.stdout)

    def assert_refused(self, manifest) -> None:
        self.assert_raw_refused(json.dumps(manifest))

    def assert_raw_refused(self, raw: str) -> None:
        result = self.run_raw(raw)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("VENDOR_MANIFEST=ok", result.stdout)
        self.assertNotIn("Traceback (most recent call last)", result.stdout + result.stderr)

    def test_complete_one_crate_metadata_is_valid(self) -> None:
        self.assert_accepted(self.manifest)

    def test_current_committed_manifest_is_valid(self) -> None:
        self.lock_path.write_bytes((ROOT / "Cargo.lock").read_bytes())
        result = self.run_raw((ROOT / "data/vendor_manifest.json").read_text())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("VENDOR_MANIFEST=ok", result.stdout)

    def test_finite_unused_metadata_remains_valid(self) -> None:
        manifest = copy.deepcopy(self.manifest)
        manifest["review_metadata"] = {"finite": 1.25}
        self.assert_accepted(manifest)

    def test_counter_metadata_does_not_claim_to_verify_staged_bytes(self) -> None:
        for size, files in ((0, 0), (456, 17)):
            with self.subTest(size=size, files=files):
                manifest = copy.deepcopy(self.manifest)
                manifest["crates"][0].update(size_bytes=size, file_count=files)
                manifest["summary"].update(total_size_bytes=size,
                                           total_size_mb=round(size / 1_048_576, 1))
                self.assert_accepted(manifest)

    def test_schema_version_requires_exact_supported_integer(self) -> None:
        cases = (("missing", None), ("null", None), ("boolean", True),
                 ("float", 1.0), ("string", "1"), ("unsupported", 999))
        for label, value in cases:
            with self.subTest(schema=label):
                manifest = copy.deepcopy(self.manifest)
                if label == "missing":
                    del manifest["schema_version"]
                else:
                    manifest["schema_version"] = value
                self.assert_refused(manifest)

    def test_generator_requires_the_producer_tag(self) -> None:
        for label, value in (("missing", None), ("null", None), ("boolean", False),
                             ("integer", 1), ("other", "scripts/other_generator.py")):
            with self.subTest(generator=label):
                manifest = copy.deepcopy(self.manifest)
                if label == "missing":
                    del manifest["generator"]
                else:
                    manifest["generator"] = value
                self.assert_refused(manifest)

    def test_summary_counters_require_exact_nonnegative_integers(self) -> None:
        keys = ("total_crates", "registry_crates", "git_crates", "total_size_bytes")
        for key in keys:
            for value in BAD_COUNTERS:
                with self.subTest(counter=key, value=repr(value)):
                    manifest = copy.deepcopy(self.manifest)
                    manifest["summary"][key] = value
                    self.assert_refused(manifest)
            with self.subTest(counter=key, value="missing"):
                manifest = copy.deepcopy(self.manifest)
                del manifest["summary"][key]
                self.assert_refused(manifest)

    def test_summary_matches_row_count_source_kinds_and_sizes(self) -> None:
        for changes in ({"total_crates": 2}, {"registry_crates": 0, "git_crates": 1},
                        {"total_size_bytes": 124}):
            with self.subTest(summary=changes):
                manifest = copy.deepcopy(self.manifest)
                manifest["summary"].update(changes)
                self.assert_refused(manifest)
        manifest = copy.deepcopy(self.manifest)
        manifest["crates"][0]["size_bytes"] = 124
        self.assert_refused(manifest)

    def test_row_counters_require_exact_nonnegative_integers(self) -> None:
        for key in ("file_count", "size_bytes"):
            for value in BAD_COUNTERS:
                with self.subTest(counter=key, value=repr(value)):
                    manifest = copy.deepcopy(self.manifest)
                    manifest["crates"][0][key] = value
                    self.assert_refused(manifest)
            with self.subTest(counter=key, value="missing"):
                manifest = copy.deepcopy(self.manifest)
                del manifest["crates"][0][key]
                self.assert_refused(manifest)

    def test_size_types_cannot_hide_behind_equal_numeric_totals(self) -> None:
        for row_size, summary_size in ((123.0, 123), (123, 123.0), (True, 1)):
            with self.subTest(row_size=repr(row_size), summary_size=repr(summary_size)):
                manifest = copy.deepcopy(self.manifest)
                manifest["crates"][0]["size_bytes"] = row_size
                manifest["summary"].update(total_size_bytes=summary_size,
                                           total_size_mb=round(summary_size / 1_048_576, 1))
                self.assert_refused(manifest)

    def test_top_level_crates_summary_and_rows_require_correct_shapes(self) -> None:
        for value in (None, True, [], "manifest", 1):
            with self.subTest(top_level=value):
                self.assert_refused(value)
        for field, values in (("crates", (None, True, {}, "crates", 1)),
                              ("summary", (None, True, [], "summary", 1))):
            for value in values:
                with self.subTest(field=field, value=value):
                    manifest = copy.deepcopy(self.manifest)
                    manifest[field] = value
                    self.assert_refused(manifest)
            with self.subTest(field=field, value="missing"):
                manifest = copy.deepcopy(self.manifest)
                del manifest[field]
                self.assert_refused(manifest)
        for value in (None, True, 1, "row", []):
            with self.subTest(row=value):
                manifest = copy.deepcopy(self.manifest)
                manifest["crates"] = [value]
                self.assert_refused(manifest)

    def test_row_names_and_versions_are_strings_not_malformed_keys(self) -> None:
        for key in ("name", "version"):
            for value in (None, True, 1, [], {}, ""):
                with self.subTest(key=key, value=value):
                    manifest = copy.deepcopy(self.manifest)
                    manifest["crates"][0][key] = value
                    self.assert_refused(manifest)
            with self.subTest(key=key, value="missing"):
                manifest = copy.deepcopy(self.manifest)
                del manifest["crates"][0][key]
                self.assert_refused(manifest)

    def test_json_numbers_are_finite_even_in_unused_metadata(self) -> None:
        raw = json.dumps(self.manifest)
        for literal in ("NaN", "Infinity", "-Infinity", "1e999", "-1e999"):
            with self.subTest(literal=literal):
                self.assert_raw_refused('{"review_metadata": ' + literal + ", " + raw[1:])

    def test_json_members_are_unique_including_unused_metadata(self) -> None:
        raw = json.dumps(self.manifest)
        cases = (
            '{"review_metadata": 7, "review_metadata": 0, ' + raw[1:],
            raw.replace('"checksum": "' + "a" * 64 + '"',
                        '"checksum": "' + "0" * 64 + '", "checksum": "' + "a" * 64 + '"', 1),
            raw.replace('"cargo_lock_sha256": "', '"cargo_lock_sha256": "wrong", "cargo_lock_sha256": "', 1),
        )
        for index, duplicate in enumerate(cases):
            with self.subTest(duplicate=index):
                self.assertNotEqual(duplicate, raw)
                self.assert_raw_refused(duplicate)

    def test_malformed_json_syntax_is_a_clean_refusal(self) -> None:
        for raw in ('{"schema_version":', '{"crates": [],}', "not JSON"):
            with self.subTest(malformed=raw):
                self.assert_raw_refused(raw)

    def test_lock_derived_refusals_remain_live(self) -> None:
        for kind, marker in (("stale", "STALE"), ("checksum", "DIFFERS"),
                             ("missing", "MISSING"), ("extra", "EXTRA"),
                             ("duplicate", "DUPLICATE")):
            with self.subTest(control=kind):
                self.lock_path.write_bytes(self.lock_bytes)
                manifest = copy.deepcopy(self.manifest)
                if kind == "stale":
                    self.lock_path.write_bytes(self.lock_bytes + b"\n# stale lock control\n")
                elif kind == "checksum":
                    manifest["crates"][0]["checksum"] = "0" * 64
                elif kind == "missing":
                    self.lock_path.write_bytes(self.lock_bytes + self.package("second", "2.0.0", "b" * 64).encode())
                    manifest["cargo_lock_sha256"] = hashlib.sha256(self.lock_path.read_bytes()).hexdigest()
                else:
                    row = copy.deepcopy(manifest["crates"][0])
                    if kind == "extra":
                        row.update(name="extra", dir="extra-1.2.3")
                    manifest["crates"].append(row)
                    manifest["summary"].update(total_crates=2, registry_crates=2,
                                               total_size_bytes=246,
                                               total_size_mb=round(246 / 1_048_576, 1))
                result = self.run_manifest(manifest)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("Traceback (most recent call last)", result.stdout + result.stderr)
                self.assertIn(marker, (result.stdout + result.stderr).upper())


if __name__ == "__main__":
    unittest.main()
