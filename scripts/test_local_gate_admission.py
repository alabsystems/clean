#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Synthetic process controls for actual local/front-end admission call sites.

Every controller/compiler here is an isolated temporary executable. These tests
exercise orchestration and refusals; they confer no real admission/build credit.
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOCAL = (ROOT / "scripts/local_gate.sh").read_text()
FRONTEND = ROOT / "scripts/frontend_merge_suite.sh"
HELPER = LOCAL.split("_gate_build() (", 1)[1].split("\n# ── THE STANDALONE", 1)[0]
HELPER = "_gate_build() (" + HELPER
BATTERY = LOCAL.split("  _battery_readonly() {", 1)[1].split("\n  # GATE-LEG:", 1)[0]
BATTERY = "_battery_readonly() {" + BATTERY

# One small fake executable implements the three independent process boundaries.
# It lives only inside a TemporaryDirectory and never calls a real controller.
STUB = r'''
import json, os, pathlib, subprocess, sys
role = pathlib.Path(sys.argv[0]).name
a = sys.argv[1:]
e = os.environ.copy()
keys = ("HEAVY_GATE_HELD", "BUILD_SLOT_HELD", "CARGO_BUILD_JOBS", "TARGO_CALLER_JOBS",
        "SYNTHETIC_KEEP", "CLEAN_NATIVE_EXEC_UPDATE", "TRUSTFLAGS", "RUSTFLAGS",
        "RUSTDOCFLAGS", "CARGO_BUILD_RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_ENCODED_RUSTDOCFLAGS", "CARGO_TARGET_DIR", "HEAVY_GATE_AUTO_FLOOR_GB")
def emit(kind, **kw):
    with open(e["TRACE"], "a") as f:
        f.write(json.dumps(dict(kind=kind, role=role, argv=a,
            env={k:e[k] for k in keys if k in e}, **kw)) + "\n")
def finish(rc):
    sys.exit(128 - rc if rc < 0 else rc)
if role == "heavy_gate.sh":
    emit("memory-enter")
    assert a[0] == "run" and a[3] == "--"
    if "MEM_FAIL" in e: sys.exit(int(e["MEM_FAIL"]))
    if a[2] == "frontend-suite-" + e.get("MEM_EARLY_PHASE", ""): sys.exit(0)
    e["HEAVY_GATE_HELD"] = "synthetic-only:" + a[2]
    try: rc = subprocess.call(a[4:], env=e)
    finally: emit("memory-release")
    finish(rc)
elif role == "build-slot":
    emit("cpu-enter", stamps=sorted(p.name for p in pathlib.Path(e["OUT"]).glob("*.admitted")))
    cut = a.index("--")
    assert a[:cut:2] in (["--cpus"], ["--cpus", "--mem-gb"], [])
    n = a[a.index("--cpus") + 1] if "--cpus" in a[:cut] else "2"
    if "CPU_FAIL" in e: sys.exit(int(e["CPU_FAIL"]))
    phase = "build" if "--no-run" in a else "doc" if "--doc" in a else "run"
    if e.get("CPU_EARLY_PHASE") == phase: sys.exit(0)
    if int(n) > int(e.get("SYNTHETIC_CPU_SHARE", "4")): sys.exit(2)
    e["CARGO_BUILD_JOBS"] = n
    e["BUILD_SLOT_HELD"] = "1"
    try: rc = subprocess.call(a[cut+1:], env=e)
    finally: emit("cpu-release")
    finish(rc)
elif role == "trustc":
    emit("compiler-identity")
    assert a == ["-vV"]
    print("host: synthetic-test-host")
elif role == "frontend_merge_suite_report.py":
    emit("report")
    if a[0] == "plan": print("--lib\n--bins\n--tests")
    elif a[0] == "report":
        legs = json.loads(a[a.index("--legs")+1])
        pathlib.Path(a[a.index("--summary-out")+1]).write_text(json.dumps(legs))
        sys.exit(0 if all(legs[p]["rc"] in (0, None) for p in ("build", "run", "doc")) else 1)
elif role == "cargo_test_nonvacuous.sh":
    emit("nonvacuous")
    assert a[1] == "--"
    finish(subprocess.call(a[2:], env=e))
else:
    phase = ("build" if "--no-run" in a else "doc" if "--doc" in a else "run")
    if role == "targo" and a and a[0] == "metadata":
        emit("metadata"); print(e.get("SYNTHETIC_METADATA", "{}")); sys.exit(0)
    emit("payload", phase=phase,
         stamps=sorted(p.name for p in pathlib.Path(e["OUT"]).glob("*.admitted")))
    if role == "u2_battery.sh": pathlib.Path("reports/u2-battery.json").write_text("changed")
    print("payload-out")
    print("payload-err", file=sys.stderr)
    print("test result: ok. 1 passed; 0 failed; 0 ignored") if role == "targo" else None
    if e.get("SYNTHETIC_METADATA") and phase == "run":
        for package in json.loads(e["SYNTHETIC_METADATA"])["packages"]:
            name = package["name"].replace("-", "_")
            print("     Running unittests src/lib.rs (target/debug/deps/" + name + "-0123456789abcdef)")
            print("test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s")
    sys.exit(int(e.get("PAYLOAD_RC", "0")) if e.get("FAIL_PHASE", phase) == phase else 0)
'''


def command(label):
    """Extract a real continued helper call, excluding its shell error handler."""
    start = LOCAL.index(label)
    lines = LOCAL[start:].splitlines()
    out = []
    for line in lines:
        if line.lstrip().startswith("||"): break
        out.append(line)
        if not line.endswith("\\"): break
    return "\n".join(out)


class AdmissionControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="gate-admission-synthetic-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "scripts").mkdir()
        (self.root / "bin").mkdir()
        (self.root / "out with spaces").mkdir()
        (self.root / "receipts").mkdir()
        self.trace = self.root / "trace.jsonl"
        self.env = os.environ.copy()
        # The fixture must never inherit a real controller capability or output path.
        for k in tuple(self.env):
            if k.startswith(("HEAVY_GATE_", "BUILD_SLOT_", "FRONTEND_SUITE_")) or k in (
                "CARGO_BUILD_JOBS", "TARGO", "RUSTC", "CARGO_TARGET_DIR"):
                self.env.pop(k)
        self.env.update(PATH=str(self.root / "bin") + os.pathsep + os.environ["PATH"],
            TRACE=str(self.trace), OUT=str(self.root / "out with spaces"),
            TMPDIR=str(self.root / "receipts"), SYNTHETIC_KEEP="unchanged value")
        fixture_python = self.root / "bin/fixture-python"
        fixture_python.symlink_to(sys.executable)
        for name in ("heavy_gate.sh", "build-slot", "payload", "targo", "trustc",
                     "cargo_test_nonvacuous.sh", "u2_battery.sh", "frontend_merge_suite_report.py"):
            directory = "scripts" if name.endswith((".sh", ".py")) else "bin"
            path = self.root / directory / name
            path.write_text("#!" + str(fixture_python) + "\n" + STUB)
            path.chmod(0o755)
        shutil.copy2(FRONTEND, self.root / "scripts/frontend_merge_suite.sh")
        self.env.update(TARGO=str(self.root / "bin/targo"),
            FRONTEND_SUITE_OUT=self.env["OUT"], CARGO_TARGET_DIR=str(self.root / "target with spaces"))

    def events(self):
        return [json.loads(s) for s in self.trace.read_text().splitlines()] if self.trace.exists() else []

    def shell(self, body, args=(), **env):
        return subprocess.run(["bash", "-c", HELPER + "\n" + body, "synthetic", *args],
            cwd=self.root, env=dict(self.env, **env), text=True, capture_output=True, timeout=15)

    def frontend(self, *args, **env):
        return subprocess.run(["bash", "scripts/frontend_merge_suite.sh", *args],
            cwd=self.root, env=dict(self.env, **env), text=True, capture_output=True, timeout=15)

    def test_exact_argv_environment_streams_status_and_release(self):
        args = ("", "a b", "a\nb", "$(touch forbidden)", "*", "--", "é")
        r = self.shell('_gate_build 19 2 "label with spaces" payload "$@"', args, PAYLOAD_RC="37")
        self.assertEqual(r.returncode, 37, r.stderr)
        self.assertEqual(r.stdout, "payload-out\n")
        self.assertEqual(r.stderr, "local-gate admission: RAISED label with spaces from 19 to 47 GiB (compiler floor)\n"
                         "payload-err\n")
        e = self.events()
        self.assertEqual([v["kind"] for v in e],
            ["memory-enter", "cpu-enter", "payload", "cpu-release", "memory-release"])
        self.assertEqual(e[0]["argv"][:4], ["run", "47", "local-gate-label with spaces", "--"])
        self.assertEqual(e[1]["argv"][:5], ["--cpus", "2", "--mem-gb", "47", "--"])
        self.assertEqual(e[2]["argv"], list(args))
        self.assertEqual(e[2]["env"]["SYNTHETIC_KEEP"], "unchanged value")
        self.assertEqual(e[2]["env"]["CARGO_BUILD_JOBS"], "2")
        self.assertFalse((self.root / "forbidden").exists())
        self.assertEqual(list((self.root / "receipts").iterdir()), [])

    def test_payload_skip_and_failure_statuses_are_preserved(self):
        for rc in (0, 2, 74, 127):
            with self.subTest(rc=rc):
                r = self.shell("_gate_build 12 2 status payload", PAYLOAD_RC=str(rc))
                self.assertEqual(r.returncode, rc, r.stderr)
        self.assertEqual(list((self.root / "receipts").iterdir()), [])

    def test_actual_spawn_mktemp_and_signal_failures(self):
        r = self.shell("_gate_build 12 2 missing definitely-not-an-executable")
        self.assertEqual(r.returncode, 127, r.stderr)
        self.assertNotIn("payload", [v["kind"] for v in self.events()])
        signal_payload = self.root / "bin/terminates"
        signal_payload.write_text('#!/bin/sh\nkill -TERM "$$"\n')
        signal_payload.chmod(0o755)
        r = self.shell("_gate_build 12 2 signal terminates")
        self.assertEqual(r.returncode, 143, r.stderr)
        self.trace.unlink()
        mktemp = self.root / "bin/mktemp"
        mktemp.write_text("#!/bin/sh\nexit 1\n")
        mktemp.chmod(0o755)
        self.assertEqual(self.shell("_gate_build 12 2 temp payload").returncode, 75)
        self.assertEqual(self.events(), [])
        self.assertEqual(list((self.root / "receipts").iterdir()), [])

    def test_admission_refusal_and_vacuous_success_never_become_skip(self):
        for controller in ("MEM_FAIL", "CPU_FAIL"):
            for rc in (0, 2, 75):
                with self.subTest(controller=controller, rc=rc):
                    self.trace.unlink(missing_ok=True)
                    r = self.shell("_gate_build 12 2 refuses payload", **{controller:str(rc)})
                    self.assertEqual(r.returncode, 75, r.stderr)
                    self.assertIn(f"admission exit {rc}", r.stderr)
                    self.assertNotIn("payload", [e["kind"] for e in self.events()])
                    self.assertEqual(list((self.root / "receipts").iterdir()), [])
                    if controller == "MEM_FAIL": self.assertEqual(len(self.events()), 1)
                    else: self.assertEqual(self.events()[-1]["kind"], "memory-release")

    def test_bad_budgets_and_outer_memory_refuse_before_controllers(self):
        for body in ("_gate_build 0 2 x payload", "_gate_build auto:x:12 2 x payload",
                     "_gate_build 12 0 x payload", "_gate_build 12 2 x"):
            self.assertEqual(self.shell(body).returncode, 75)
        for held in ("", "synthetic-only:outer"):
            self.assertEqual(self.shell("_gate_build 12 2 x payload", HEAVY_GATE_HELD=held).returncode, 75)
        self.assertEqual(self.events(), [])

    def test_cpu_inheritance_is_forwarded_to_controller_and_four_is_required(self):
        r = self.shell("_gate_build 19 4 verified payload", BUILD_SLOT_HELD="1",
                       CARGO_BUILD_JOBS="4", SYNTHETIC_CPU_SHARE="4")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.events()[1]["env"]["BUILD_SLOT_HELD"], "1")
        self.trace.unlink()
        r = self.shell("_gate_build 19 4 verified payload", BUILD_SLOT_HELD="1",
                       CARGO_BUILD_JOBS="2", SYNTHETIC_CPU_SHARE="2")
        self.assertEqual(r.returncode, 75)
        self.assertNotIn("payload", [e["kind"] for e in self.events()])

    def test_actual_native_call_strips_update_only_after_admission(self):
        r = self.shell(command("_gate_build 12 2 native-exec-battery"), CLEAN_NATIVE_EXEC_UPDATE="synthetic-update")
        self.assertEqual(r.returncode, 0, r.stderr)
        e = self.events()
        self.assertIn("CLEAN_NATIVE_EXEC_UPDATE", e[1]["env"])
        self.assertNotIn("CLEAN_NATIVE_EXEC_UPDATE", e[-3]["env"])
        self.assertEqual(e[-3]["argv"], ["--unverified", "test", "-p", "clean", "--locked", "--test", "native_exec_battery"])

    def test_actual_verified_call_keeps_j4_and_strips_verifier_flags(self):
        directory = self.root / "verified dir" / "example-crate"
        directory.mkdir(parents=True)
        body = command("_gate_build 19 4 trust-verified-lane")
        flags = dict.fromkeys(("TRUSTFLAGS", "RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_BUILD_RUSTFLAGS",
                              "CARGO_ENCODED_RUSTFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS"), "synthetic-flag")
        r = self.shell(body, tvl_dir=str(directory.parent), tvl_c="example-crate", **flags)
        self.assertEqual(r.returncode, 0, r.stderr)
        e = self.events()
        self.assertEqual(e[1]["argv"][:2], ["--cpus", "4"])
        payload = next(v for v in e if v["kind"] == "payload")
        self.assertTrue(all(k not in payload["env"] for k in flags))
        self.assertEqual(payload["argv"][:11], ["trust", "check", "--allow-l0-gaps", "--keep-going", "--locked", "-j", "4", "-p", "example-crate", "--lib", "--report-dir"])

    def test_actual_battery_wrapper_restores_artifact_after_payload_failure(self):
        (self.root / "reports").mkdir()
        artifact = self.root / "reports/u2-battery.json"
        artifact.write_bytes(b"original\x00bytes\n")
        body = command("_battery_readonly reports/u2-battery.json _gate_build")
        r = self.shell(BATTERY + "\n" + body, PAYLOAD_RC="37")
        self.assertEqual(r.returncode, 37, r.stderr)
        self.assertEqual(artifact.read_bytes(), b"original\x00bytes\n")
        self.assertEqual([e["kind"] for e in self.events()].count("memory-enter"), 1)

    def test_e7_actual_command_still_acquires_one_pair(self):
        expected = 'scripts/heavy_gate.sh run auto:e7-census:2 e7-census -- build-slot -- "$GATE_PYTHON" scripts/check_lean_axiom_census.py'
        self.assertIn("if " + expected + "; then", LOCAL)
        r = self.shell(expected, GATE_PYTHON=str(self.root / "bin/payload"))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual([e["kind"] for e in self.events()].count("memory-enter"), 1)
        self.assertEqual([e["kind"] for e in self.events()].count("cpu-enter"), 1)

    def test_compiler_floor_raises_low_requests_and_keeps_higher_requests(self):
        for requested in (1, 12, 17, 19, 35, 47, 63):
            with self.subTest(requested=requested):
                self.trace.unlink(missing_ok=True)
                r = self.shell(f"_gate_build {requested} 2 floor payload", PAYLOAD_RC="37")
                self.assertEqual(r.returncode, 37, r.stderr)
                e = self.events()
                self.assertEqual([v["kind"] for v in e],
                    ["memory-enter", "cpu-enter", "payload", "cpu-release", "memory-release"])
                expected = str(max(requested, 47))
                self.assertEqual(e[0]["argv"][:4], ["run", expected, "local-gate-floor", "--"])
                self.assertEqual(e[1]["argv"][:5], ["--cpus", "2", "--mem-gb", expected, "--"])
                self.assertEqual(e[2]["argv"], [])
                self.assertEqual("RAISED" in r.stderr, requested < 47)

    def test_frontend_auto_floor_keeps_higher_values_and_refuses_nonnumeric(self):
        self.assertEqual(self.shell("_gate_frontend_auto_floor").stdout, "47\n")
        for value, expected in (("0", "47"), ("1", "47"), ("46", "47"), ("47", "47"),
                                ("96", "96"), ("00096", "96"), ("9" * 24, "9" * 24)):
            with self.subTest(value=value):
                r = self.shell("_gate_frontend_auto_floor", HEAVY_GATE_AUTO_FLOOR_GB=value)
                self.assertEqual(r.returncode, 0, r.stderr)
                self.assertEqual(r.stdout, expected + "\n")
        for value in ("-1", "1.5", "47x", " 96", "x[$(touch forbidden)]"):
            r = self.shell("_gate_frontend_auto_floor", HEAVY_GATE_AUTO_FLOOR_GB=value)
            self.assertEqual(r.returncode, 75, r.stderr)
        self.assertEqual(self.events(), [])
        self.assertFalse((self.root / "forbidden").exists())

    def test_local_frontend_call_preserves_auto_classes_and_scoped_floor(self):
        body = 'fms_auto_floor="$(_gate_frontend_auto_floor)"\n' + command(
            '  FRONTEND_SUITE_PYTHON="$GATE_PYTHON" ')
        r = self.shell(body, GATE_PYTHON=sys.executable, HEAVY_GATE_AUTO_FLOOR_GB="96")
        self.assertEqual(r.returncode, 0, r.stderr)
        memory = [v for v in self.events() if v["kind"] == "memory-enter"]
        self.assertEqual([v["argv"][1] for v in memory],
                         ["47", "auto:frontend-suite-run:47", "auto:frontend-suite-doc:47"])
        self.assertTrue(all(v["env"]["HEAVY_GATE_AUTO_FLOOR_GB"] == "96" for v in memory))
        payloads = [v for v in self.events() if v["kind"] == "payload"]
        self.assertEqual([v["phase"] for v in payloads], ["build", "run", "doc"])

    def test_frontend_three_phases_keep_weights_args_and_timestamp_order(self):
        r = self.frontend()
        self.assertEqual(r.returncode, 0, r.stderr)
        e = self.events()
        memory = [v for v in e if v["kind"] == "memory-enter"]
        self.assertEqual([v["argv"][1] for v in memory], ["12", "auto:frontend-suite-run:6", "auto:frontend-suite-doc:12"])
        cpu = [v for v in e if v["kind"] == "cpu-enter"]
        self.assertEqual(len(cpu), 3)
        for v in cpu: self.assertEqual(v["argv"][:3], ["--cpus", "2", "--"])
        self.assertEqual([v["stamps"] for v in cpu], [[], ["build.admitted"], ["build.admitted", "run.admitted"]])
        payloads = [v for v in e if v["kind"] == "payload"]
        self.assertEqual([v["phase"] for v in payloads], ["build", "run", "doc"])
        packages = ["-p", "clean-parser", "-p", "clean-olean", "-p", "clean-macro", "-p", "clean-elab"]
        self.assertEqual(payloads[0]["argv"], ["--unverified", "test", "--locked", "--no-run", *packages, "--lib", "--bins", "--tests"])
        self.assertEqual(payloads[1]["argv"][:5], ["--unverified", "test", "--locked", "--no-fail-fast", "--config"])
        self.assertIn('target.synthetic-test-host.runner=[', payloads[1]["argv"][5])
        self.assertEqual(payloads[1]["argv"][6:], [*packages, "--lib", "--bins", "--tests"])
        self.assertEqual(payloads[2]["argv"], ["--unverified", "test", "--locked", "--no-fail-fast", "--doc", *packages])

    def test_frontend_refused_cpu_never_stamps_or_runs_or_reports_success(self):
        r = self.frontend(CPU_FAIL="2")
        self.assertEqual(r.returncode, 1, r.stderr)
        e = self.events()
        self.assertEqual(len([v for v in e if v["kind"] == "memory-enter"]), 1)
        self.assertNotIn("payload", [v["kind"] for v in e])
        self.assertFalse(list(Path(self.env["OUT"]).glob("*.admitted")))
        legs = json.loads((Path(self.env["OUT"]) / "summary.json").read_text())
        self.assertEqual(legs["build"]["rc"], 2)
        self.assertIsNone(legs["build"]["ran_s"])
        self.assertIsNone(legs["run"]["rc"])

    def test_frontend_vacuous_success_refuses_each_phase(self):
        for controller in ("CPU_EARLY_PHASE", "MEM_EARLY_PHASE"):
            for phase in ("build", "run", "doc"):
                with self.subTest(controller=controller, phase=phase):
                    r = self.frontend(**{controller: phase})
                    self.assertEqual(r.returncode, 1, r.stderr)
                    legs = json.loads((Path(self.env["OUT"]) / "summary.json").read_text())
                    self.assertEqual(legs[phase]["rc"], 75)
                    self.assertIsNone(legs[phase]["ran_s"])
                    if phase == "build":
                        self.assertIsNone(legs["run"]["rc"])
                        self.assertIsNone(legs["doc"]["rc"])

    def test_frontend_receipt_failures_never_become_green(self):
        date = self.root / "bin/date"
        for mode in ("fail", "empty", "text", "leading-zero", "overflow", "past", "future", "expression"):
            with self.subTest(mode=mode):
                self.trace.unlink(missing_ok=True)
                date.write_text("#!" + str(self.root / "bin/fixture-python") + "\n"
                    "import os,stat,sys,time\n"
                    "regular=stat.S_ISREG(os.fstat(1).st_mode)\n"
                    "if not regular: print(int(time.time())); sys.exit(0)\n"
                    + ("sys.exit(1)\n" if mode == "fail" else
                       "print(" + repr({"empty": "", "text": "bad", "leading-zero": "08",
                           "overflow": "18446744073709551616", "past": "1", "future": "9999999999",
                           "expression": "x[$(touch forbidden)]"}[mode]) + ")\n"))
                date.chmod(0o755)
                r = self.frontend()
                self.assertEqual(r.returncode, 1, r.stderr)
                legs = json.loads((Path(self.env["OUT"]) / "summary.json").read_text())
                self.assertEqual(legs["build"]["rc"], 74 if mode == "fail" else 75)
                self.assertIsNone(legs["build"]["ran_s"])
                self.assertIsNone(legs["run"]["rc"])
                self.assertFalse((self.root / "forbidden").exists())
                if mode == "fail": self.assertNotIn("payload", [v["kind"] for v in self.events()])

    def test_frontend_cannot_reuse_a_receipt_that_cannot_be_removed(self):
        stamp = Path(self.env["OUT"]) / "build.admitted"
        stamp.write_text("1794710000\n")
        rm = self.root / "bin/rm"
        rm.write_text("#!/bin/sh\nexit 1\n")
        rm.chmod(0o755)
        r = self.frontend()
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertIn("cannot clear build phase-start receipt", r.stderr)
        self.assertNotIn("memory-enter", [v["kind"] for v in self.events()])
        self.assertEqual(stamp.read_text(), "1794710000\n")
        legs = json.loads((Path(self.env["OUT"]) / "summary.json").read_text())
        self.assertEqual(legs["build"]["rc"], 75)
        self.assertIsNone(legs["build"]["ran_s"])

    def test_real_reporter_requires_the_build_to_have_started(self):
        shutil.copyfile(ROOT / "scripts/frontend_merge_suite_report.py",
                        self.root / "scripts/frontend_merge_suite_report.py")
        (self.root / "scripts/frontend_merge_suite_slow.txt").write_text("")
        packages = ["clean-parser", "clean-olean", "clean-macro", "clean-elab"]
        metadata = json.dumps({"packages": [dict(name=p, targets=[dict(
            name=p.replace("-", "_"), kind=["lib"], test=True, doctest=False)]) for p in packages]})
        r = self.frontend("--no-doc", SYNTHETIC_METADATA=metadata)
        self.assertEqual(r.returncode, 0, r.stderr + r.stdout)
        summary = Path(self.env["OUT"]) / "summary.json"
        self.assertEqual(json.loads(summary.read_text())["counts"]["GREEN"], 4)
        for controller in ("CPU_EARLY_PHASE", "MEM_EARLY_PHASE"):
            with self.subTest(controller=controller):
                self.trace.unlink()
                r = self.frontend("--no-doc", SYNTHETIC_METADATA=metadata, **{controller: "build"})
                self.assertEqual(r.returncode, 1, r.stderr + r.stdout)
                actual = json.loads(summary.read_text())
                self.assertEqual(actual["verdict"], "red")
                self.assertEqual(actual["legs"]["build"]["rc"], 75)
                self.assertIsNone(actual["legs"]["run"]["rc"])
                self.assertEqual(actual["counts"]["NOT_RUN"], 4)
                self.assertNotIn("payload", [v["kind"] for v in self.events()])

    def test_frontend_memory_refusal_never_calls_cpu_or_payload(self):
        r = self.frontend(MEM_FAIL="2")
        self.assertEqual(r.returncode, 1, r.stderr)
        kinds = [e["kind"] for e in self.events()]
        self.assertEqual(kinds.count("memory-enter"), 1)
        self.assertNotIn("cpu-enter", kinds)
        self.assertNotIn("payload", kinds)
        self.assertFalse(list(Path(self.env["OUT"]).glob("*.admitted")))

    def test_frontend_build_failure_is_not_success_and_skips_unbuilt_phases(self):
        r = self.frontend(PAYLOAD_RC="37", FAIL_PHASE="build")
        self.assertEqual(r.returncode, 1, r.stderr)
        payloads = [v for v in self.events() if v["kind"] == "payload"]
        self.assertEqual([v["phase"] for v in payloads], ["build"])
        legs = json.loads((Path(self.env["OUT"]) / "summary.json").read_text())
        self.assertEqual(legs["build"]["rc"], 37)
        self.assertIsNone(legs["run"]["rc"])
        self.assertIsNone(legs["doc"]["rc"])

    def test_frontend_outer_memory_refuses_before_compiler_or_metadata(self):
        for held in ("", "synthetic-only:outer"):
            self.assertEqual(self.frontend(HEAVY_GATE_HELD=held).returncode, 2)
            self.assertEqual(self.events(), [])
        # The pre-existing pure --selftest arm is usable under an outer hold.
        self.assertEqual(self.frontend("--selftest", HEAVY_GATE_HELD="synthetic-only:outer").returncode, 0)
        self.assertEqual([e["kind"] for e in self.events()], ["report"])

    def test_frontend_cpu_inheritance_reaches_controller_and_no_doc_stays_no_doc(self):
        r = self.frontend("--no-doc", BUILD_SLOT_HELD="1", CARGO_BUILD_JOBS="2")
        self.assertEqual(r.returncode, 0, r.stderr)
        cpu = [v for v in self.events() if v["kind"] == "cpu-enter"]
        self.assertEqual(len(cpu), 2)
        self.assertTrue(all(v["env"]["BUILD_SLOT_HELD"] == "1" for v in cpu))


if __name__ == "__main__":
    unittest.main()
