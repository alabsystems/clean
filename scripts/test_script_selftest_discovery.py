#!/usr/bin/env python3
"""Exercise discovery through a copied real controller and tiny fixture suites.

No repository suites, native tools or admission controllers are invoked. Optional
evidence paths retain each fixture and its exact command/output for paired replay.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
CONTROLLER = Path(os.environ.get("CLEAN_SCRIPT_DISCOVERY_CONTROLLER",
                                 ROOT / "scripts/check_script_selftests.sh"))


class ScriptSelftestDiscoveryTests(unittest.TestCase):
    def setUp(self) -> None:
        retained = os.environ.get("CLEAN_SCRIPT_DISCOVERY_EVIDENCE")
        if retained:
            self.root = Path(retained).resolve() / self._testMethodName
            self.root.mkdir(parents=True)
        else:
            temporary = tempfile.TemporaryDirectory(prefix="script-discovery-tests-")
            self.addCleanup(temporary.cleanup)
            self.root = Path(temporary.name)
        scripts = self.root / "scripts"
        (scripts / "nested").mkdir(parents=True)
        (self.root / "data").mkdir()
        (self.root / "bin").mkdir()
        (self.root / "tmp").mkdir()
        self.controller = scripts / "check_script_selftests.sh"
        shutil.copy2(CONTROLLER, self.controller)
        (self.root / "data/script_selftest_quarantine.json").write_text(
            json.dumps({"quarantined": []}) + "\n")
        (scripts / "test_alpha.py").write_text(
            "import os\nfrom pathlib import Path\nimport unittest\n"
            "class PositiveControl(unittest.TestCase):\n"
            "    def test_executed(self):\n"
            "        with Path(os.environ['DISCOVERY_FIXTURE_EXECUTIONS']).open('a') as stream:\n"
            "            stream.write('python\\n')\n"
            "        self.assertEqual(2 + 2, 4)\n"
            "if __name__ == '__main__':\n    unittest.main()\n")
        (scripts / "nested/test_beta.sh").write_text(
            "#!/bin/bash\nset -eu\n"
            "printf '%s\\n' shell >> \"$DISCOVERY_FIXTURE_EXECUTIONS\"\n"
            "echo '=== Results: 1 passed, 0 failed ==='\n")
        # The stubs affect only this child controller's PATH. Successful cases
        # delegate to real discovery tools; failures produce a nonempty partial
        # list and an actual nonzero pipeline status.
        real_find = shutil.which("find")
        real_sort = shutil.which("sort")
        self.assertIsNotNone(real_find)
        self.assertIsNotNone(real_sort)
        (self.root / "bin/find").write_text(
            "#!/bin/bash\n"
            "if [ \"${DISCOVERY_FIXTURE_FAULT:-}\" = find ]; then\n"
            "  printf '%s\\n' scripts/test_alpha.py\n"
            "  echo 'fixture find: partial traversal failure' >&2\n"
            "  exit 7\nfi\n"
            f"exec {shlex.quote(real_find)} \"$@\"\n")
        (self.root / "bin/sort").write_text(
            "#!/bin/bash\n"
            "if [ \"${DISCOVERY_FIXTURE_FAULT:-}\" = sort ]; then\n"
            "  IFS= read -r first\n  printf '%s\\n' \"$first\"\n"
            "  while IFS= read -r rest; do :; done\n"
            "  echo 'fixture sort: partial output failure' >&2\n"
            "  exit 8\nfi\n"
            f"exec {shlex.quote(real_sort)} \"$@\"\n")
        for name in ("find", "sort"):
            (self.root / "bin" / name).chmod(0o755)
        (self.root / "bin/python3.14").symlink_to(Path(sys.executable).resolve())
        self.inputs = [self.controller, scripts / "test_alpha.py",
                       scripts / "nested/test_beta.sh",
                       self.root / "data/script_selftest_quarantine.json",
                       self.root / "bin/find", self.root / "bin/sort",
                       self.root / "bin/python3.14"]
        self.executions = self.root / "executed.txt"
        self.env = {**os.environ, "PATH": str(self.root / "bin") + os.pathsep + os.environ["PATH"],
                    "TMPDIR": str(self.root / "tmp"),
                    "PYTHONDONTWRITEBYTECODE": "1",
                    "DISCOVERY_FIXTURE_EXECUTIONS": str(self.executions)}
        for name in ("BASH_ENV", "ENV", "BASH_FUNC_find%%", "BASH_FUNC_sort%%"):
            self.env.pop(name, None)

    def snapshot(self) -> dict:
        return {str(path.relative_to(self.root)): {
            "mode": stat.S_IMODE(path.lstat().st_mode),
            "link": os.readlink(path) if path.is_symlink() else None,
            "sha256": None if path.is_symlink() else hashlib.sha256(path.read_bytes()).hexdigest(),
        } for path in self.inputs}

    def invoke(self, *, listing: bool, fault: str = "") -> subprocess.CompletedProcess:
        before = self.snapshot()
        argv = ["/bin/bash", str(self.controller)] + (["--list"] if listing else [])
        result = subprocess.run(argv, cwd=self.root,
                                env={**self.env, "DISCOVERY_FIXTURE_FAULT": fault},
                                text=True, capture_output=True, timeout=15)
        after = self.snapshot()
        (self.root / "stdout.log").write_text(result.stdout)
        (self.root / "stderr.log").write_text(result.stderr)
        (self.root / "invocation.json").write_text(json.dumps({
            "argv": argv, "cwd": str(self.root), "exit_status": result.returncode,
            "listing": listing, "fault": fault,
            "controller_source": str(CONTROLLER.resolve()),
            "test_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "python": sys.executable, "inputs_before": before, "inputs_after": after,
            "executions": self.executions.read_text().splitlines() if self.executions.exists() else [],
            "temporary_outputs_remaining": [p.name for p in (self.root / "tmp").iterdir()],
        }, indent=2, sort_keys=True) + "\n")
        self.assertEqual(after, before, "the controller changed a fixture input")
        self.assertEqual(list((self.root / "tmp").iterdir()), [], "controller leaked output files")
        return result

    def assert_discovery_refused(self, *, listing: bool, fault: str) -> None:
        result = self.invoke(listing=listing, fault=fault)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(self.executions.exists(), "a suite ran after incomplete discovery")
        self.assertEqual(result.stdout, "", "the partial suite list was published")
        self.assertNotIn("SCRIPT_SELFTESTS suites=", result.stdout,
                         "the controller reported a partial run")
        self.assertNotIn("Traceback", result.stdout + result.stderr)

    def test_pristine_list_includes_top_level_and_nested_suites_without_execution(self) -> None:
        result = self.invoke(listing=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines(),
                         ["scripts/nested/test_beta.sh", "scripts/test_alpha.py"])
        self.assertFalse(self.executions.exists())

    def test_pristine_normal_mode_runs_both_suites(self) -> None:
        result = self.invoke(listing=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SCRIPT_SELFTESTS suites=2 passed=2", result.stdout)
        self.assertCountEqual(self.executions.read_text().splitlines(), ["python", "shell"])

    def test_partial_find_failure_refuses_list(self) -> None:
        self.assert_discovery_refused(listing=True, fault="find")

    def test_partial_find_failure_refuses_normal_mode_before_suite_execution(self) -> None:
        self.assert_discovery_refused(listing=False, fault="find")

    def test_partial_sort_failure_refuses_list(self) -> None:
        self.assert_discovery_refused(listing=True, fault="sort")

    def test_partial_sort_failure_refuses_normal_mode_before_suite_execution(self) -> None:
        self.assert_discovery_refused(listing=False, fault="sort")

    def assert_quarantine_refused(self, *, fault: str) -> None:
        result = self.invoke(listing=False, fault=fault)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(self.executions.exists(), "a suite ran after quarantine loading failed")
        self.assertNotIn("SCRIPT_SELFTESTS suites=", result.stdout)
        self.assertNotIn("SCRIPT_SELFTESTS=ok", result.stdout)

    def test_malformed_quarantine_root_refuses_before_suite_execution(self) -> None:
        (self.root / "data/script_selftest_quarantine.json").write_text("[]\n")
        self.assert_quarantine_refused(fault="quarantine-root")

    def test_quarantine_helper_exit_seven_refuses_before_suite_execution(self) -> None:
        # Only this fixture's stdin quarantine helper fails. Interpreter
        # resolution and suite invocations still use the actual real Python.
        proxy = self.root / "bin/python3.14"
        proxy.unlink()
        proxy.write_text(
            "#!/bin/bash\n"
            "if [ \"$#\" -ge 2 ] && [ \"$1\" = - ] && "
            "[ \"$2\" = data/script_selftest_quarantine.json ]; then\n"
            "  echo 'fixture Python: quarantine helper failure' >&2\n"
            "  exit 7\nfi\n"
            f"exec {shlex.quote(str(Path(sys.executable).resolve()))} \"$@\"\n")
        proxy.chmod(0o755)
        self.assert_quarantine_refused(fault="quarantine-helper")


    def quarantine_rows(self, names, *, duplicate=False):
        import datetime
        expires = (datetime.date.today() + datetime.timedelta(days=30)).isoformat()
        rows = [{"suite": name, "expires": expires, "max_failed": 1} for name in names]
        if duplicate:
            rows.append(dict(rows[0]))
        (self.root / "data/script_selftest_quarantine.json").write_text(
            json.dumps({"quarantined": rows}) + "\n")

    def red_shell(self, relative):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("#!/bin/bash\nset -eu\n"
                        "printf '%s\n' red >> \"$DISCOVERY_FIXTURE_EXECUTIONS\"\n"
                        "echo '=== Results: 0 passed, 1 failed ==='\nexit 1\n")
        if path not in self.inputs:
            self.inputs.append(path)

    def test_quarantine_metacharacters_do_not_cover_another_suite(self):
        literal = "scripts/nest.ed/test_red.sh"
        other = "scripts/nestXed/test_red.sh"
        self.red_shell(literal)
        self.red_shell(other)
        self.quarantine_rows([other])
        result = self.invoke(listing=False)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("unquarantined red: " + literal, result.stderr)
        self.assertNotIn("SCRIPT_SELFTESTS=ok", result.stdout)

    def test_exact_quarantine_names_cover_both_red_suites(self):
        names = ["scripts/nest.ed/test_red.sh", "scripts/nestXed/test_red.sh"]
        for name in names:
            self.red_shell(name)
        self.quarantine_rows(names)
        result = self.invoke(listing=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SCRIPT_SELFTESTS=ok", result.stdout)
        self.assertEqual(self.executions.read_text().splitlines().count("red"), 2)

    def test_exact_quarantine_name_with_spaces_is_supported(self):
        name = "scripts/space dir/test_red.sh"
        self.red_shell(name)
        self.quarantine_rows([name])
        result = self.invoke(listing=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SCRIPT_SELFTESTS=ok", result.stdout)
        self.assertEqual(self.executions.read_text().splitlines().count("red"), 1)

    def test_duplicate_quarantine_identity_refuses_before_execution(self):
        name = "scripts/nested/test_beta.sh"
        self.red_shell(name)
        self.quarantine_rows([name], duplicate=True)
        self.assert_quarantine_refused(fault="duplicate-quarantine")

    def test_quarantine_object_instead_of_array_refuses_before_execution(self):
        (self.root / "data/script_selftest_quarantine.json").write_text(
            '{"quarantined": {}}\n')
        self.assert_quarantine_refused(fault="quarantine-container")

    def test_unknown_quarantine_identity_refuses_before_execution(self):
        self.quarantine_rows(["scripts/test_absent.py"])
        self.assert_quarantine_refused(fault="unknown-quarantine")

    def test_expired_absent_quarantine_identity_refuses_before_execution(self):
        self.quarantine_rows(["scripts/test_absent.py"])
        ledger = self.root / "data/script_selftest_quarantine.json"
        doc = json.loads(ledger.read_text())
        doc["quarantined"][0]["expires"] = "2020-01-01"
        ledger.write_text(json.dumps(doc) + "\n")
        self.assert_quarantine_refused(fault="expired-unknown-quarantine")

    def test_linebreak_quarantine_identity_refuses_before_execution(self):
        self.quarantine_rows(["scripts/test_absent.py\nunused"])
        self.assert_quarantine_refused(fault="linebreak-quarantine")

    def test_numeric_quarantine_identity_refuses_before_execution(self):
        self.quarantine_rows([123])
        self.assert_quarantine_refused(fault="numeric-quarantine")


class ScriptSelftestPathTests(unittest.TestCase):
    # Reuse the same bounded fixture without inheriting and rerunning its tests.
    setUp = ScriptSelftestDiscoveryTests.setUp
    snapshot = ScriptSelftestDiscoveryTests.snapshot
    invoke = ScriptSelftestDiscoveryTests.invoke

    def newline_alias(self) -> None:
        # The old line walk splits this RED path into the two existing passing
        # paths and executes those twice, never reaching this actual suite.
        directory = self.root / "scripts/test_alpha.py\nscripts/nested"
        directory.mkdir(parents=True)
        suite = directory / "test_beta.sh"
        suite.write_text(
            "#!/bin/bash\nset -eu\n"
            "printf '%s\\n' hidden-red >> \"$DISCOVERY_FIXTURE_EXECUTIONS\"\n"
            "exit 1\n")
        self.inputs.append(suite)

    def carriage_return_path(self) -> None:
        suite = self.root / "scripts/test_carriage\r.sh"
        suite.write_text(
            "#!/bin/bash\nset -eu\n"
            "printf '%s\\n' carriage-return >> \"$DISCOVERY_FIXTURE_EXECUTIONS\"\n"
            "echo '=== Results: 1 passed, 0 failed ==='\n")
        self.inputs.append(suite)

    def assert_path_refused(self, *, listing: bool) -> None:
        result = self.invoke(listing=listing)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "", "an unrepresentable suite list was published")
        self.assertFalse(self.executions.exists(), "a suite ran before all paths were validated")
        self.assertIn("reason=unrepresentable-suite-path", result.stderr)
        self.assertNotIn("Traceback", result.stdout + result.stderr)

    def test_newline_directory_alias_refuses_list(self) -> None:
        self.newline_alias()
        self.assert_path_refused(listing=True)

    def test_newline_directory_alias_refuses_before_execution(self) -> None:
        self.newline_alias()
        self.assert_path_refused(listing=False)

    def test_carriage_return_path_refuses_list(self) -> None:
        self.carriage_return_path()
        self.assert_path_refused(listing=True)

    def test_carriage_return_path_refuses_before_execution(self) -> None:
        self.carriage_return_path()
        self.assert_path_refused(listing=False)

    def test_spaces_and_tabs_in_paths_remain_representable(self) -> None:
        directory = self.root / "scripts/space and\ttab"
        directory.mkdir()
        suite = directory / "test_extra.sh"
        suite.write_text(
            "#!/bin/bash\nset -eu\n"
            "printf '%s\\n' spaced >> \"$DISCOVERY_FIXTURE_EXECUTIONS\"\n"
            "echo '=== Results: 1 passed, 0 failed ==='\n")
        self.inputs.append(suite)
        result = self.invoke(listing=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SCRIPT_SELFTESTS suites=3 passed=3", result.stdout)
        self.assertCountEqual(self.executions.read_text().splitlines(),
                              ["python", "shell", "spaced"])

    def test_symlink_suite_remains_outside_the_selector(self) -> None:
        outside = self.root / "outside-red.sh"
        outside.write_text(
            "#!/bin/bash\nset -eu\n"
            "printf '%s\\n' linked-red >> \"$DISCOVERY_FIXTURE_EXECUTIONS\"\n"
            "exit 1\n")
        link = self.root / "scripts/test_link.sh"
        link.symlink_to(outside)
        self.inputs.extend((outside, link))
        result = self.invoke(listing=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SCRIPT_SELFTESTS suites=2 passed=2", result.stdout)
        self.assertCountEqual(self.executions.read_text().splitlines(), ["python", "shell"])


if __name__ == "__main__":
    unittest.main()
