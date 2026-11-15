#!/usr/bin/env python3
"""Public shell-wrapper regression tests; all test output is synthetic bytes."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


HELPER = Path(__file__).with_name("cargo_test_nonvacuous.sh").resolve()
OBSERVATIONS: list[dict] = []
GOOD = b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n"
BAD = GOOD[:-1] + b"\x00garbage\n"
MODES = ((), ("-T",), ("-e",), ("-e", "-T"), ("-C",), ("-e", "-T", "-C"))


def digest(data: bytes) -> dict:
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(), "hex": data.hex()}


class WrapperLifecycle(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="nonvacuity-interface-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.capture_dir = self.root / "capture"
        self.capture_dir.mkdir()
        self.parent_tmp = self.root / "parent-tmp"
        self.parent_tmp.mkdir()
        self.flag = self.root / "payload-ran"
        self.stubs = self.root / "stubs"
        self.stubs.mkdir()
        self.env = dict(os.environ, TMPDIR=str(self.capture_dir), LC_ALL="C")
        self.env.pop("TMP", None)
        # SHELLOPTS may be exported by an unrelated caller. The tested options
        # are selected explicitly in Bash argv, never through ambient state.
        self.env.pop("SHELLOPTS", None)
        self.env.pop("BASHOPTS", None)
        self.env.pop("BASH_ENV", None)
        self.env.pop("Q6_SELFTEST_UNBOUND_CONTROL", None)

    def stub(self, tool, *, after_payload=True, status=74):
        real = shutil.which(tool)
        self.assertIsNotNone(real)
        real = str(Path(real).resolve())
        code = (
            "import os,pathlib,sys\n"
            f"flag=pathlib.Path({str(self.flag)!r})\n"
            f"active={'flag.exists()' if after_payload else 'True'}\n"
            "args=sys.argv[1:]\n"
            + ("active=active and '-d' not in args\n" if tool == "mktemp" and after_payload else "")
            + "if active:\n"
            + (f" sys.stdout.write({str(self.capture_dir / 'uncreated')!r}+'\\n')\n" if tool == "mktemp" else "")
            + f" sys.stderr.write('INJECTED_{tool.upper()}_FAILURE\\n')\n sys.exit({status})\n"
            + f"os.execv({real!r},[{real!r},*args])\n"
        )
        engine = self.stubs / (tool + "_fault.py")
        engine.write_text(code)
        entry = self.stubs / tool
        entry.write_text("#!/bin/bash\nexec " + shlex.quote(sys.executable) + " -B " + shlex.quote(str(engine)) + ' "$@"\n')
        entry.chmod(0o755)
        self.env["PATH"] = str(self.stubs) + os.pathsep + os.environ["PATH"]
        return {"tool": tool, "real": real, "engine": code, "entry": entry.read_text(), "status": status}

    def invoke(self, args, *, mode=(), tmp_present=False, fault=None, inherited_options=None, helper=None):
        env = dict(self.env)
        if tmp_present:
            env["TMP"] = str(self.parent_tmp)
        if inherited_options is not None:
            env["SHELLOPTS"] = inherited_options
        selected_helper = HELPER if helper is None else helper
        argv = ["bash", *mode, str(selected_helper), *args]
        p = subprocess.Popen(argv, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             start_new_session=True)
        timed_out = False
        try:
            out, err = p.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(p.pid, signal.SIGTERM)
            try:
                out, err = p.communicate(timeout=2)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                out, err = p.communicate()
        leftovers = sorted(str(path.relative_to(self.capture_dir)) for path in self.capture_dir.rglob("*"))
        row = {"test": self.id(), "argv": argv, "mode": list(mode),
               "helper_sha256": hashlib.sha256(selected_helper.read_bytes()).hexdigest(),
               "env_scope": {"TMPDIR": env["TMPDIR"], "TMP": env.get("TMP"), "LC_ALL": env["LC_ALL"],
                             "PATH_stub_prefix": str(self.stubs) if fault else None,
                             "inherited_SHELLOPTS": inherited_options,
                             "removed_ambient_shell_controls": ["SHELLOPTS", "BASHOPTS", "BASH_ENV"]},
               "exit": p.returncode, "stdout": digest(out), "stderr": digest(err),
               "timed_out": timed_out, "payload_ran": self.flag.exists(),
               "leftovers_before_harness_cleanup": leftovers, "fault": fault}
        OBSERVATIONS.append(row)
        # Remove only this invocation's owned remnants, including intentional
        # rm-failure fixtures. Record the wrapper's actual cleanup result first.
        for path in self.capture_dir.iterdir():
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink()
        self.flag.unlink(missing_ok=True)
        self.assertFalse(timed_out, "owned subprocess timed out: " + self.id())
        return row, out, err

    def payload(self, data=GOOD, status=0):
        # Keep explicit argv indices readable rather than depending on shell
        # interpolation; the first argument is the fault-activation sentinel.
        code = "import pathlib,sys;pathlib.Path(sys.argv[1]).touch();sys.stdout.buffer.write(bytes.fromhex(sys.argv[2]));sys.exit(int(sys.argv[3]))"
        return ["fixture", "--", sys.executable, "-B", "-c", code, str(self.flag), data.hex(), str(status)]

    def test_shell_mode_and_tmp_matrix(self):
        for mode in MODES:
            for present in (False, True):
                for name, args, status in (
                    ("selftest", ["--selftest"], 0),
                    ("positive", self.payload(), 0),
                    ("refusal", self.payload(b""), 1),
                    ("child37", self.payload(GOOD, 37), 37),
                ):
                    with self.subTest(mode=mode, TMP=present, case=name):
                        row, out, _ = self.invoke(args, mode=mode, tmp_present=present)
                        self.assertEqual(row["exit"], status)
                        self.assertEqual(row["leftovers_before_harness_cleanup"], [])
                        if name == "selftest":
                            self.assertIn(b"arms=17 passed=17 failed=0", out)
                        elif name == "positive":
                            self.assertTrue(out.startswith(GOOD))
                            self.assertIn(b"NONVACUOUS=ok", out)
                        elif name == "refusal":
                            self.assertIn(b"reason=no-test-result-line", out)
                        else:
                            self.assertEqual(out, GOOD)

    def test_preserves_exported_tmp_for_child(self):
        code = "import os,sys;sys.stdout.buffer.write(os.environ['TMP'].encode()+b'\\n'+bytes.fromhex(sys.argv[1]))"
        row, out, _ = self.invoke(["tmp", "--", sys.executable, "-B", "-c", code, GOOD.hex()], tmp_present=True)
        self.assertEqual(row["exit"], 0)
        self.assertTrue(out.startswith(str(self.parent_tmp).encode() + b"\n" + GOOD), "child TMP was overwritten")
        self.assertTrue(self.parent_tmp.is_dir())
        self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_absent_tmp_stays_absent_for_child(self):
        code = "import os,sys;sys.stdout.buffer.write(str('TMP' in os.environ).encode()+b'\\n'+bytes.fromhex(sys.argv[1]))"
        row, out, _ = self.invoke(["tmp", "--", sys.executable, "-B", "-c", code, GOOD.hex()])
        self.assertEqual(row["exit"], 0)
        self.assertTrue(out.startswith(b"False\n" + GOOD))

    def test_replay_failure_refuses_success(self):
        fault = self.stub("cat")
        row, out, err = self.invoke(self.payload(), mode=("-e", "-T"), fault=fault)
        self.assertEqual(row["exit"], 1, "raw replay failure earned success or escaped typed handling")
        self.assertTrue(row["payload_ran"])
        self.assertIn(b"reason=output-replay-error", out + err)
        self.assertNotIn(b"NONVACUOUS=ok", out + err)
        self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_replay_failure_normal_shell(self):
        fault = self.stub("cat")
        row, out, err = self.invoke(self.payload(), fault=fault)
        self.assertTrue(row["payload_ran"])
        self.assertEqual(row["exit"], 1, "raw replay failure earned success")
        self.assertIn(b"INJECTED_CAT_FAILURE", err)
        self.assertIn(b"reason=output-replay-error", out + err)
        self.assertNotIn(b"NONVACUOUS=ok", out + err)
        self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_replay_failure_keeps_child37(self):
        fault = self.stub("cat")
        row, out, err = self.invoke(self.payload(GOOD, 37), mode=("-e", "-T"), fault=fault)
        self.assertEqual(row["exit"], 37)
        self.assertTrue(row["payload_ran"])
        self.assertIn(b"INJECTED_CAT_FAILURE", err)
        self.assertNotIn(b"NONVACUOUS=ok", out + err)
        self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_replay_failure_keeps_child37_normal_shell(self):
        fault = self.stub("cat")
        row, out, err = self.invoke(self.payload(GOOD, 37), fault=fault)
        self.assertTrue(row["payload_ran"])
        self.assertEqual(row["exit"], 37)
        self.assertIn(b"INJECTED_CAT_FAILURE", err)
        self.assertNotIn(b"NONVACUOUS=ok", out + err)
        self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_cleanup_failure_refuses_success(self):
        fault = self.stub("rm", status=73)
        row, out, err = self.invoke(self.payload(), mode=("-e", "-T"), fault=fault)
        self.assertEqual(row["exit"], 1)
        self.assertTrue(row["payload_ran"])
        self.assertIn(b"reason=capture-cleanup-error", out + err)
        self.assertNotIn(b"NONVACUOUS=ok", out + err)
        self.assertTrue(row["leftovers_before_harness_cleanup"], "rm fault did not retain its owned capture fixture")

    def test_cleanup_failure_keeps_child37(self):
        fault = self.stub("rm", status=73)
        row, out, err = self.invoke(self.payload(GOOD, 37), mode=("-e", "-T"), fault=fault)
        self.assertEqual(row["exit"], 37)
        self.assertTrue(row["payload_ran"])
        self.assertEqual(out, GOOD)
        self.assertIn(b"reason=capture-cleanup-error", err)
        self.assertTrue(row["leftovers_before_harness_cleanup"])

    def test_cleanup_failure_after_parser_refusal(self):
        fault = self.stub("rm", status=73)
        row, out, err = self.invoke(self.payload(b""), mode=("-e", "-T"), fault=fault)
        self.assertEqual(row["exit"], 1)
        self.assertTrue(row["payload_ran"])
        self.assertIn(b"reason=capture-cleanup-error", out + err)
        self.assertNotIn(b"NONVACUOUS=ok", out + err)
        self.assertTrue(row["leftovers_before_harness_cleanup"])

    def test_replay_and_cleanup_failure_keeps_child37(self):
        faults = [self.stub("cat"), self.stub("rm", status=73)]
        row, out, err = self.invoke(self.payload(GOOD, 37), mode=("-e", "-T"), fault=faults)
        self.assertEqual(row["exit"], 37)
        self.assertTrue(row["payload_ran"])
        self.assertIn(b"INJECTED_CAT_FAILURE", err)
        self.assertIn(b"reason=capture-cleanup-error", err)
        self.assertNotIn(b"NONVACUOUS=ok", out + err)

    def test_capture_setup_failure_never_runs_child(self):
        fault = self.stub("mktemp", after_payload=False, status=73)
        # Permit the automatic directory setup, fail only the main capture file.
        engine = self.stubs / "mktemp_fault.py"
        engine.write_text(engine.read_text().replace("active=True", "active='-d' not in sys.argv[1:]"))
        fault["engine"] = engine.read_text()
        row, out, err = self.invoke(self.payload(), fault=fault)
        self.assertEqual(row["exit"], 2)
        self.assertIn(b"reason=capture-setup-error", out + err)
        self.assertFalse(row["payload_ran"], "child ran after mktemp failure")
        self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_selftest_setup_failure_is_explicit(self):
        fault = self.stub("mktemp", after_payload=False, status=73)
        row, out, err = self.invoke(["--selftest"], mode=("-e", "-T"), fault=fault)
        self.assertEqual(row["exit"], 2)
        self.assertIn(b"NONVACUOUS_SELFTEST=fail reason=setup-error", out + err)
        self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_selftest_cleanup_failure_is_explicit(self):
        fault = self.stub("rm", after_payload=False, status=73)
        row, out, err = self.invoke(["--selftest"], mode=("-e", "-T"), fault=fault)
        self.assertEqual(row["exit"], 2)
        self.assertIn(b"NONVACUOUS_SELFTEST=fail reason=cleanup-error", out + err)
        self.assertTrue(row["leftovers_before_harness_cleanup"])

    def test_byte_scope_and_exact_nonzero_exits(self):
        for data, status in ((BAD, 1), (GOOD + BAD, 1), (b"\xff\x00noise\n" + GOOD, 0)):
            with self.subTest(data=data.hex()):
                row, out, _ = self.invoke(self.payload(data), mode=("-e", "-T"))
                self.assertEqual(row["exit"], status)
                self.assertTrue(out.startswith(data))
                self.assertEqual(row["leftovers_before_harness_cleanup"], [])
        for status in (7, 37, 101, 130):
            with self.subTest(exit=status):
                row, out, _ = self.invoke(self.payload(BAD, status), mode=("-e", "-T"))
                self.assertEqual(row["exit"], status)
                self.assertEqual(out, BAD)
                self.assertEqual(row["leftovers_before_harness_cleanup"], [])

    def test_selftest_arity_never_runs_supplied_child(self):
        for suffix in (["extra"], ["--", sys.executable, "-B", "-c", "print('SENTINEL')"]):
            with self.subTest(args=suffix):
                row, out, err = self.invoke(["--selftest", *suffix], mode=("-e", "-T"))
                self.assertEqual(row["exit"], 2)
                self.assertIn(b"--selftest takes no command or trailing arguments", err)
                self.assertEqual(out, b"")

    def test_exported_noclobber_options(self):
        options = "braceexpand:hashall:interactive-comments:noclobber"
        for mode in ((), ("-e", "-T")):
            for name, args, status in (("selftest", ["--selftest"], 0),
                                       ("positive", self.payload(), 0),
                                       ("refusal", self.payload(b""), 1),
                                       ("child37", self.payload(GOOD, 37), 37)):
                with self.subTest(mode=mode, case=name):
                    row, out, _ = self.invoke(args, mode=mode, inherited_options=options)
                    self.assertEqual(row["exit"], status)
                    self.assertEqual(row["leftovers_before_harness_cleanup"], [])
                    if name == "selftest":
                        self.assertIn(b"arms=17 passed=17 failed=0", out)
                    elif name == "positive":
                        self.assertTrue(out.startswith(GOOD))
                    elif name == "child37":
                        self.assertEqual(out, GOOD)

    def test_planted_selftest_crash_never_passes_or_runs_child(self):
        source = HELPER.read_text()
        seam = "    trap selftest_cleanup EXIT\n"
        self.assertEqual(source.count(seam), 1, "missing owned crash-control seam")
        mutant = self.root / "planted-crash.sh"
        mutant.write_text(source.replace(seam, seam + '    : "$Q6_SELFTEST_UNBOUND_CONTROL"\n', 1))
        for mode in ((), ("-e",), ("-e", "-T"), ("-e", "-T", "-C")):
            for name, args in (("selftest", ["--selftest"]), ("public", self.payload())):
                with self.subTest(mode=mode, case=name):
                    row, out, err = self.invoke(args, mode=mode, helper=mutant)
                    if name == "selftest":
                        self.assertNotEqual(row["exit"], 0, "incomplete selftest earned success")
                    else:
                        self.assertEqual(row["exit"], 2, "public guard did not refuse incomplete selftest")
                    self.assertFalse(row["payload_ran"], "child ran after incomplete selftest")
                    self.assertNotIn(b"NONVACUOUS=ok", out + err)
                    self.assertNotIn(b"arms=17 passed=17 failed=0", out)
                    self.assertEqual(row["leftovers_before_harness_cleanup"], [])
                    if name == "selftest":
                        self.assertIn(b"reason=incomplete", err)
                        self.assertIn(b"Q6_SELFTEST_UNBOUND_CONTROL", err)
                    else:
                        self.assertIn(b"refusing to run -- its own self-test arms no longer fire", err)


def main():
    global HELPER
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--helper", type=Path, default=HELPER)
    parser.add_argument("--record", type=Path, help="write exact synthetic subprocess receipts")
    args, remaining = parser.parse_known_args()
    HELPER = args.helper.resolve()
    if not HELPER.is_file():
        parser.error("helper must be an existing file")
    program = unittest.main(argv=[sys.argv[0], *remaining], verbosity=2, exit=False)
    successful = program.result.testsRun > 0 and program.result.wasSuccessful()
    if program.result.testsRun == 0:
        print("CARGO_TEST_NONVACUOUS_INTERFACE=fail reason=zero-tests-selected", file=sys.stderr)
    if args.record:
        args.record.write_text(json.dumps({
            "kind": "synthetic-public-wrapper-interface-tests", "proof_claim": False,
            "Rust_Cargo_libtest_or_image_execution": False,
            "helper": {"path": str(HELPER), "sha256": hashlib.sha256(HELPER.read_bytes()).hexdigest()},
            "test_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "tests_run": program.result.testsRun, "successful": successful,
            "unittest_successful": program.result.wasSuccessful(),
            "failure_count": len(program.result.failures), "error_count": len(program.result.errors),
            "observations": OBSERVATIONS,
        }, indent=2, sort_keys=True) + "\n")
    return 0 if successful else 1


if __name__ == "__main__":
    raise SystemExit(main())
