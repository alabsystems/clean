#!/usr/bin/env python3
"""E4: rebuild Clean, then measure unmodified package modules in ORDER.

The imports use the production `clean check` source-import policy. No Lean
compiler substitutes for Clean's elaborator. A timeout has no logical verdict.
The gate compares named refusal signatures exactly, so closing one is red too.
"""
import argparse
import contextlib
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ("cic_l", "cic_l_model", "kcheck", "kcheck_spec", "kcheck_labelled")
EXECUTION_PROBES = (("kcheck", "KCheckMain"), ("kcheck_labelled", "KCheckLabelledMain"))
EXPECTED_PROBES = [module for _, module in EXECUTION_PROBES] + ["KCheck/Check diagnostic"]
BASELINE = ROOT / "reports/self-proof-elab/baseline.json"


def build_digest():
    names = subprocess.check_output([
        "git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--",
        "crates", "Cargo.toml", "Cargo.lock", ".cargo", "rust-toolchain.toml"
    ], cwd=ROOT).decode().split("\0")
    digest = hashlib.sha256()
    for name in sorted(set(filter(None, names))):
        digest.update(name.encode() + b"\0")
        data = (ROOT / name).read_bytes()
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    return digest.hexdigest()


def pinned_lean_library(pins, toolchains=None):
    if not pins:
        raise ValueError("no pinned Lean packages")
    toolchain = next(iter(pins.values()))
    for package, pin in pins.items():
        if not pin:
            raise ValueError(f"empty pinned Lean toolchain: {package}")
        if pin != toolchain:
            raise ValueError(f"package toolchain differs: {package}: {pin}")
    if toolchains is None:
        toolchains = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains"
    lib = toolchains / toolchain.replace("/", "--").replace(":", "---") / "lib/lean"
    if not (lib / "Init/Prelude.olean").is_file():
        raise ValueError(f"pinned Lean library unavailable: {lib}")
    executable = lib.parents[1] / "bin/lean"
    if not executable.is_file():
        raise ValueError(f"pinned Lean executable unavailable: {executable}")
    return toolchain, lib


def preflight_pinned_lean(commit):
    pins = {package: subprocess.check_output(
        ["git", "show", f"{commit}:theories/{package}/lean-toolchain"],
        cwd=ROOT, text=True).strip() for package in PACKAGES}
    _, lib = pinned_lean_library(pins)
    subprocess.run([str(lib.parents[1] / "bin/lean"), "--version"],
                   check=True, stdout=subprocess.DEVNULL, timeout=30)


def inventory(root=ROOT):
    rows = []
    for package in PACKAGES:
        order = root / "theories" / package / "ORDER"
        listed = set()
        for line in order.read_text().splitlines():
            module = line.partition("#")[0].strip()
            if module:
                source = order.parent / (module + ".lean")
                if module in listed or not source.is_file():
                    raise ValueError(f"duplicate or missing ORDER module: {package}/{module}")
                listed.add(module)
                rows.append((package, module, source))
        if not listed:
            raise ValueError(f"empty ORDER inventory: {package}")
        actual = {
            path.relative_to(order.parent).with_suffix("").as_posix()
            for prefix in {name.split("/")[0] for name in listed}
            for path in (order.parent / prefix).rglob("*.lean")
        }
        if actual != listed:
            raise ValueError(f"ORDER and library source modules disagree in {package}: {sorted(actual ^ listed)}")
    return rows


def stage_sources(snapshot, work):
    # Preflight the union before writing any file: package order must never
    # choose which same-named module Clean actually checks.
    staged = {}
    for package in PACKAGES:
        root = snapshot / "theories" / package
        for source in sorted(root.rglob("*.lean")):
            if ".lake" in source.parts:
                continue
            relative = source.relative_to(root)
            if relative in staged:
                owner, _ = staged[relative]
                raise ValueError(f"source path collision: {relative} in {owner} and {package}")
            staged[relative] = (package, source)
    for relative, (_, source) in staged.items():
        dest = work / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)


def measured(argv, cwd, env, cap, profile=None):
    """wait4 gives this child's actual peak, including a killed child on macOS."""
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        start = time.monotonic()
        child = subprocess.Popen(argv, cwd=cwd, env=env, stdout=out, stderr=err,
                                 start_new_session=True)
        expired = False
        sampled = False
        profile_error = None
        try:
            while True:
                pid, status, usage = os.wait4(child.pid, os.WNOHANG)
                if pid:
                    break
                if profile is not None and not sampled and time.monotonic() - start >= 30:
                    sampled = True
                    profile.parent.mkdir(parents=True, exist_ok=True)
                    sampling = subprocess.run(
                        ["/usr/bin/sample", str(child.pid), "2", "-file", str(profile)],
                        capture_output=True, text=True, timeout=10, check=False)
                    if sampling.returncode != 0 or not profile.is_file():
                        profile_error = sampling.stderr or sampling.stdout or "sample produced no file"
                if time.monotonic() - start >= cap:
                    expired = True
                    os.killpg(child.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(child.pid, 0)
                    break
                time.sleep(0.05)
        except BaseException:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            _, status, _ = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
            raise
        child.returncode = os.waitstatus_to_exitcode(status)
        out.seek(0)
        err.seek(0)
        return {
            "command": argv, "exit": child.returncode, "timed_out": expired,
            "wall_seconds": round(time.monotonic() - start, 3),
            "peak_bytes": int(usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024)),
            "user_seconds": round(usage.ru_utime, 3),
            "system_seconds": round(usage.ru_stime, 3),
            "profile": str(profile) if sampled else None,
            "profile_error": profile_error,
            "stdout": out.read().decode(errors="replace"),
            "stderr": err.read().decode(errors="replace"),
        }


def classify(row):
    if row["timed_out"]:
        return "timed_out", "per-module wall cap exceeded; no verdict"
    if row["exit"] < 0:
        raise ValueError(f"process died from signal {-row['exit']}; no refusal verdict")
    try:
        report = json.loads(row["stdout"])
    except json.JSONDecodeError:
        if row["exit"] == 0:
            raise ValueError("exit 0 without a production check report")
        lines = row["stderr"].splitlines()
        for start, line in enumerate(lines):
            if line.startswith(("Error: ", "error:")):
                # Keep the actual error verbatim, including its multiline
                # detail, but not timestamped informational logs before it.
                return "refused", "\n".join(lines[start:])
        raise ValueError("nonzero exit without a named CLI error")
    if report.get("schema_version") != "Clean-check-report-v2" or report.get("command") != "clean check":
        raise ValueError("unsupported production check report schema")
    if report.get("diverged_count", 0) or report.get("diverged"):
        detail = report.get("diverged") or ["production declaration budget exhausted; no verdict"]
        return "timed_out", detail[0]
    if (row["exit"] == 0 and report.get("status") == "pass"
            and report.get("decl_count", 0) > 0
            and report.get("success_count") == report["decl_count"]
            and not any(report.get(key) for key in
                        ("failed_count", "diverged_count", "errors", "parser_recovery",
                         "trust_failures", "kernel_failures"))):
        return "elaborated", ""
    for key in ("errors", "parser_recovery", "trust_failures", "kernel_failures", "diverged"):
        if report.get(key):
            return "refused", report[key][0]
    raise ValueError("no full acceptance and no named diagnostic")


def signatures(report):
    modules = [(r["package"], r["module"], r["status"], r["first_error"]) for r in report["modules"]]
    probes = [("probe", r["name"], r["status"], r["first_error"]) for r in report.get("probes", [])]
    return modules + probes


def validate_binary_profile(profile, data):
    if profile not in ("debug", "authority"):
        raise ValueError("unknown census build profile")
    if (data.get("opt_level") != ("0" if profile == "debug" else "2")
            or data.get("debug_assertions") is not True
            or data.get("overflow_checks") is not True
            or data.get("test") is not False):
        raise ValueError("measured binary does not retain the pinned profile checks")


def gated_measure(argv, work, env, cap, profile=None):
    # A caller may reserve the complete probe under its own label.
    # Match the registry demonstrator: never acquire a second reservation
    # while the enclosing heavy_gate.sh run already accounts for the job.
    if env.get("HEAVY_GATE_HELD"):
        return measured(argv, work, env, cap, profile)
    # Reserve before starting the clock or the measured process. The 12 GB
    # fallback is the frontend-test weight in verify_runner's measured table.
    token = subprocess.check_output([
        str(ROOT / "scripts/heavy_gate.sh"), "acquire", "12", "e4-module"
    ], cwd=ROOT, env=env, text=True).strip()
    try:
        return measured(argv, work, env, cap, profile)
    finally:
        subprocess.run([str(ROOT / "scripts/heavy_gate.sh"), "release", token], cwd=ROOT, check=True)


def execution_probes(binary, snapshot, work, env, cap, measure=gated_measure):
    rows = []
    for package, module in EXECUTION_PROBES:
        row = measure([str(binary), "run", module + ".lean", "--decl", "main"],
                      work, env, cap)
        # A deadline remains a non-verdict even if the process exited zero
        # with the expected bytes. The source classifier has the same rule.
        if row["exit"] == 0 and not row["timed_out"]:
            expected = (snapshot / "theories" / package / "expected_output.txt").read_text()
            if row["stdout"] != expected:
                raise ValueError(f"{module} ran but did not print the pinned verdict bytes")
            status, error = "executed", ""
        else:
            status, error = classify(row)
        row.update(name=module, status=status, first_error=error)
        rows.append(row)
        print(f"{module}: {status}", flush=True)
    return rows


def compare(actual, expected):
    for report in (actual, expected):
        if report.get("complete") is not True:
            raise ValueError("incomplete census has no gate verdict")
        observed = [[r["package"], r["module"]] for r in report["modules"]]
        if observed != report.get("expected_modules"):
            raise ValueError("census does not cover its complete ordered inventory")
        probes = [r["name"] for r in report.get("probes", [])]
        if probes != report.get("expected_probes"):
            raise ValueError("census does not cover its complete ordered probe inventory")
        # Historical v2 debug reports predate actual Cargo profile metadata.
        profile = report.get("build_profile", "debug")
        if "binary_profile" in report or profile != "debug":
            validate_binary_profile(profile, report.get("binary_profile", {}))
    if actual.get("build_profile", "debug") != expected.get("build_profile", "debug"):
        raise ValueError("census build profile changed")
    if actual["cap_seconds"] != expected["cap_seconds"]:
        raise ValueError("per-module cap changed")
    if signatures(actual) != signatures(expected):
        raise ValueError("named module verdict/refusal changed; inspect and re-mint the baseline")


def selftest():
    from unittest.mock import patch

    child = measured([sys.executable, "-c", "print('measured child')"], ROOT, os.environ, 10)
    assert child["exit"] == 0 and child["stdout"] == "measured child\n"
    assert child["peak_bytes"] > 0 and not child["timed_out"]
    child = measured([sys.executable, "-c", "import time; time.sleep(2)"], ROOT, os.environ, 0.1)
    assert child["exit"] == -signal.SIGKILL and child["timed_out"]
    assert child["peak_bytes"] > 0
    document = {"schema_version": "Clean-check-report-v2", "command": "clean check",
                "status": "pass", "decl_count": 1, "success_count": 1}
    good = {"exit": 0, "timed_out": False, "stderr": "", "stdout": json.dumps(document)}
    assert classify(good) == ("elaborated", "")
    assert classify(good | {"timed_out": True})[0] == "timed_out"
    assert classify(good | {"exit": 1, "stdout": json.dumps(document | {"diverged_count": 1, "diverged": ["budget"]})}) == ("timed_out", "budget")
    # A refused import can derive an error after a resource stop.
    for failures in (0, 1):
        mixed = document | {"failed_count": failures, "diverged_count": 1,
                            "errors": ["source elaboration refused: budget"], "diverged": ["budget"]}
        assert classify(good | {"exit": 1, "stdout": json.dumps(mixed)}) == ("timed_out", "budget")
    logged = good | {"exit": 1, "stdout": "", "stderr": "time INFO imported module\nError: named refusal\n  detail\n"}
    assert classify(logged) == ("refused", "Error: named refusal\n  detail")
    for change in ({"stdout": ""}, {"stdout": "{}"}, {"exit": 1}):
        try:
            classify(good | change)
        except ValueError:
            pass
        else:
            raise AssertionError("empty evidence accepted")
    row = {"package": "p", "module": "M", "status": "refused", "first_error": "named gap"}
    baseline = {"cap_seconds": 120, "complete": True,
                "expected_modules": [["p", "M"]], "modules": [row],
                "expected_probes": [], "probes": []}
    compare(baseline, baseline)
    authority = baseline | {"build_profile": "authority", "binary_profile": {
        "opt_level": "2", "debug_assertions": True, "overflow_checks": True, "test": False}}
    compare(authority, authority)
    for changed in (authority, baseline | {"build_profile": "unknown"},
                    authority | {"binary_profile": {}},
                    authority | {"binary_profile": authority["binary_profile"] | {"debug_assertions": False}},
                    authority | {"binary_profile": authority["binary_profile"] | {"overflow_checks": False}},
                    authority | {"binary_profile": authority["binary_profile"] | {"test": True}}):
        try:
            compare(changed, baseline)
        except ValueError:
            pass
        else:
            raise AssertionError("changed or weakened build profile accepted")
    for mutation in ({"first_error": "different gap"}, {"status": "elaborated", "first_error": ""}):
        try:
            compare(baseline | {"modules": [row | mutation]}, baseline)
        except ValueError:
            pass
        else:
            raise AssertionError("changed refusal accepted")
    try:
        compare(baseline | {"modules": []}, baseline)
    except ValueError:
        pass
    else:
        raise AssertionError("missing subject accepted")
    with tempfile.TemporaryDirectory(prefix="e4-empty-order-") as temp:
        root = Path(temp)
        order = root / "theories" / PACKAGES[0] / "ORDER"
        order.parent.mkdir(parents=True)
        order.write_text("# no modules\n")
        try:
            inventory(root)
        except ValueError as error:
            assert "empty ORDER" in str(error)
        else:
            raise AssertionError("empty ORDER accepted")
    with tempfile.TemporaryDirectory(prefix="e4-package-union-") as temp:
        root = Path(temp)
        for i, package in enumerate(PACKAGES):
            source = root / "theories" / package / f"P{i}" / "Module.lean"
            source.parent.mkdir(parents=True)
            source.write_text(f"def package{i} := {i}\n")
            (source.parent.parent / "ORDER").write_text(f"P{i}/Module\n")
        assert [p for p, _, _ in inventory(root)] == list(PACKAGES)
        stage_sources(root, root / "work")
        assert (root / "work" / f"P{len(PACKAGES)-1}" / "Module.lean").is_file()
        duplicate = root / "theories" / PACKAGES[-1] / "P0" / "Module.lean"
        duplicate.parent.mkdir()
        duplicate.write_text("def overwritten := 9\n")
        try:
            stage_sources(root, root / "collision-output")
        except ValueError as error:
            assert "source path collision" in str(error)
            assert not (root / "collision-output").exists()
        else:
            raise AssertionError("colliding package source silently overwritten")
        (root / "theories" / PACKAGES[-1] / "ORDER").unlink()
        try:
            inventory(root)
        except FileNotFoundError:
            pass
        else:
            raise AssertionError("missing last package accepted")
    probe = {"name": "adopted checker", "status": "refused", "first_error": "named"}
    complete = baseline | {"expected_probes": [probe["name"]], "probes": [probe]}
    compare(complete, complete)
    try:
        compare(complete | {"probes": []}, complete)
    except ValueError:
        pass
    else:
        raise AssertionError("missing adopted-checker probe accepted")
    with tempfile.TemporaryDirectory(prefix="e4-execution-verdict-") as temp:
        root = Path(temp)
        outputs = {}
        for package, module in EXECUTION_PROBES:
            expected = root / "theories" / package / "expected_output.txt"
            expected.parent.mkdir(parents=True)
            outputs[module + ".lean"] = module + " passed\n"
            expected.write_text(outputs[module + ".lean"])

        def fixture_result(changes):
            def measure(argv, *unused):
                return {"exit": 0, "timed_out": False, "stderr": "",
                        "stdout": outputs[argv[2]], **changes}
            return measure

        for changes, status in (({}, "executed"),
                                ({"timed_out": True}, "timed_out"),
                                ({"timed_out": True, "exit": -signal.SIGKILL}, "timed_out"),
                                ({"exit": 1, "stdout": "", "stderr": "Error: refused"}, "refused")):
            rows = execution_probes("fixture-clean", root, root, {}, 120,
                                    measure=fixture_result(changes))
            assert [r["name"] for r in rows] == [m for _, m in EXECUTION_PROBES]
            assert all(r["status"] == status for r in rows)
        for changes in ({"stdout": "wrong bytes\n"}, {"exit": -signal.SIGKILL}):
            try:
                execution_probes("fixture-clean", root, root, {}, 120,
                                 measure=fixture_result(changes))
            except ValueError:
                pass
            else:
                raise AssertionError("execution accepted wrong output or non-cap signal death")
    with tempfile.TemporaryDirectory(prefix="e4-pin-preflight-") as temp:
        root = Path(temp)
        pin = "leanprover/lean4:fixture"
        install = root / pin.replace("/", "--").replace(":", "---")
        lib = install / "lib/lean"
        (lib / "Init").mkdir(parents=True)
        prelude = lib / "Init/Prelude.olean"
        prelude.write_bytes(b"presence-only fixture")
        executable = install / "bin/lean"
        executable.parent.mkdir()
        executable.write_bytes(b"presence-only fixture")
        assert pinned_lean_library({"one": pin, "two": pin}, root) == (pin, lib)
        for pins in ({}, {"one": ""}, {"one": pin, "two": "different"}):
            try:
                pinned_lean_library(pins, root)
            except ValueError:
                pass
            else:
                raise AssertionError("invalid or mismatched pinned Lean accepted")
        prelude.unlink()
        try:
            pinned_lean_library({"one": pin}, root)
        except ValueError as error:
            assert "library unavailable" in str(error)
        else:
            raise AssertionError("missing pinned Lean library accepted")
        prelude.write_bytes(b"presence-only fixture")
        executable.unlink()
        try:
            pinned_lean_library({"one": pin}, root)
        except ValueError as error:
            assert "executable unavailable" in str(error)
        else:
            raise AssertionError("missing pinned Lean executable accepted")
        seen = []

        def recorded_git(argv, **kwargs):
            seen.append(argv)
            if argv == ["git", "rev-parse", "HEAD"]:
                return "preflight-fixture\n"
            if argv[:2] == ["git", "show"] and argv[2].startswith("preflight-fixture:theories/"):
                return pin + "\n"
            raise AssertionError(f"unexpected preflight command: {argv}")

        def no_expensive_work(*args, **kwargs):
            raise AssertionError("fetch or build reached before missing-pin refusal")

        with patch.dict(os.environ, {"ELAN_HOME": str(root / "absent-home")}), \
                patch.object(sys, "argv", ["self_proof_elab_probe.py", "--profile", "authority"]), \
                patch(__name__ + ".selftest", lambda: None), \
                patch.object(subprocess, "check_output", recorded_git), \
                patch.object(subprocess, "run", no_expensive_work):
            try:
                main()
            except ValueError as error:
                assert "pinned Lean library unavailable" in str(error)
            else:
                raise AssertionError("missing pin did not stop the CLI")
        assert len(seen) == 1 + len(PACKAGES)
    print("SELF_PROOF_ELAB_SELFTEST=ok", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--cap-seconds", type=int, default=120)
    parser.add_argument("--profile", choices=("debug", "authority"),
                        help="build profile; defaults to the baseline's recorded profile")
    parser.add_argument("--target-dir", type=Path,
                        help="this lane's own target directory; rebuilt, then deleted")
    parser.add_argument("--keep-target", action="store_true",
                        help="keep an explicit owned target for this active lane; delete it when finished")
    parser.add_argument("--output", type=Path, default=ROOT / "reports/self-proof-elab/latest.json")
    args = parser.parse_args()
    selftest()
    if args.selftest:
        return
    if args.keep_target and not args.target_dir:
        parser.error("--keep-target requires --target-dir")
    if args.cap_seconds <= 0:
        parser.error("cap must be positive")
    profile = args.profile or json.loads(BASELINE.read_text()).get("build_profile", "debug")
    if profile not in ("debug", "authority"):
        parser.error("baseline names an unknown build profile")
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    preflight_pinned_lean(commit)
    # No CARGO_HOME override. Fetch before acquiring any memory reservation.
    subprocess.run(["targo", "fetch", "--locked"], cwd=ROOT, check=True)
    inputs = build_digest()
    (ROOT / ".scratch").mkdir(exist_ok=True)
    with contextlib.ExitStack() as stack:
        if args.target_dir:
            target = str(args.target_dir.resolve())
            owned = Path(target) == ROOT / "target-e4-worker" or (
                Path(target).parent == ROOT / ".scratch" and (
                    Path(target).name.startswith("e4-target-") or
                    Path(target).name in ("e4-frontend-target", "x2-target", "x2-authority-target")))
            if not owned or args.target_dir.is_symlink():
                parser.error("target must be this lane's target-e4-worker, .scratch/e4-target-*, e4-frontend-target, x2-target or x2-authority-target directory")
            if not args.keep_target:
                stack.callback(lambda: shutil.rmtree(target) if Path(target).exists() else None)
        else:
            target = stack.enter_context(tempfile.TemporaryDirectory(prefix="e4-target-", dir=ROOT / ".scratch"))
        env = os.environ | {"CARGO_TARGET_DIR": target}
        # Measured cold peaks: debug 14.38 GiB (19 GiB with margin),
        # authority 18.24 GiB (24 GiB). Keep the appropriate floor on warm
        # rebuilds; each measured class may raise it if later work needs more.
        build = ["scripts/heavy_gate.sh", "run", "auto:e4-authority-build:24" if profile == "authority" else "auto:e4-current-build:19", "e4-clean-build", "--",
                 "targo", "--unverified", "build", "--locked", "-p", "clean", "--bin", "clean",
                 "--message-format=json"]
        if profile == "authority":
            build += ["--profile", "authority"]
        if env.get("HEAVY_GATE_HELD"):
            build = build[5:]  # the enclosing reservation admits the same validated build
        built = subprocess.run(build, cwd=ROOT, env=env, stdout=subprocess.PIPE, text=True)
        if built.returncode:
            print(built.stdout, flush=True)
            built.check_returncode()
        if build_digest() != inputs:
            raise ValueError("compiled inputs moved during build; rebuild the changed tree")
        binary = Path(target) / profile / "clean"
        artifacts = []
        for line in built.stdout.splitlines():
            try:
                item = json.loads(line)
            except json.JSONDecodeError:
                continue
            if (item.get("reason") == "compiler-artifact" and item.get("executable")
                    and item["target"]["name"] == "clean" and "bin" in item["target"]["kind"]):
                artifacts.append(item)
        if len(artifacts) != 1:
            raise ValueError("build did not identify exactly one measured clean binary")
        binary_profile = artifacts[0]["profile"]
        validate_binary_profile(profile, binary_profile)
        binary_hash = hashlib.sha256(binary.read_bytes()).hexdigest()
        if hashlib.sha256(Path(artifacts[0]["executable"]).read_bytes()).hexdigest() != binary_hash:
            raise ValueError("measured binary differs from the fresh build artifact")
        version = subprocess.check_output([binary, "--version"], text=True).strip()
        if commit not in version:
            raise ValueError("measured binary version differs from the source commit")
        report = {"schema": "self-proof-elab-v2", "commit": commit,
                  "measured_at_utc": datetime.now(timezone.utc).isoformat(),
                  "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  "build_command": build, "enclosing_admission": env.get("HEAVY_GATE_HELD"),
                  "version": version,
                  "binary_sha256": binary_hash,
                  "build_profile": profile, "binary_profile": binary_profile,
                  "build_inputs_sha256": inputs,
                  "cap_seconds": args.cap_seconds, "complete": False,
                  "modules": [], "probes": [], "expected_probes": EXPECTED_PROBES}
        # Use a source-only copy with every package root side by side, as the
        # executable's production source-import path requires. Never rewrite
        # a theory or silently reuse a local .olean build.
        with tempfile.TemporaryDirectory(prefix="e4-sources-") as scratch:
            work = Path(scratch)
            report["source_snapshot_commit"] = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            if report["source_snapshot_commit"] != commit:
                raise ValueError("source commit moved during the build")
            archive = subprocess.check_output([
                "git", "archive", report["source_snapshot_commit"],
                *["theories/" + p for p in PACKAGES]
            ], cwd=ROOT)
            snapshot = work / "snapshot"
            with tarfile.open(fileobj=io.BytesIO(archive)) as files:
                for entry in files:
                    if not entry.isfile():
                        continue
                    dest = snapshot / entry.name
                    if not dest.resolve().is_relative_to(snapshot.resolve()):
                        raise ValueError("archive path escaped source snapshot")
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_bytes(files.extractfile(entry).read())
            modules = inventory(snapshot)
            report["expected_modules"] = [[p, m] for p, m, _ in modules]
            (work / "lean-toolchain").write_bytes((snapshot / "theories/cic_l/lean-toolchain").read_bytes())
            stage_sources(snapshot, work)
            pins = {package: (snapshot / "theories" / package / "lean-toolchain").read_text().strip()
                    for package in PACKAGES}
            _, lib = pinned_lean_library(pins)
            env["LEAN_PATH"] = str(lib)
            report["lean_path"] = str(lib)
            report["lean_version"] = subprocess.check_output(
                [lib.parents[1] / "bin/lean", "--version"], text=True, timeout=30).strip()
            report["probes"] = execution_probes(binary, snapshot, work, env, args.cap_seconds)
            # Diagnose the reported ten-minute no-verdict independently of
            # the ordered census, so a long preceding module cannot hide it.
            profile = (args.output.parent / "KCheck-Check-diagnostic.sample.txt").resolve() if sys.platform == "darwin" else None
            diagnostic_env = env | {"CLEAN_CHECK_DECL_BUDGET_TRACE": "1"}
            row = gated_measure([str(binary), "check", "KCheck/Check.lean", "--json"],
                                work, diagnostic_env, args.cap_seconds, profile)
            status, error = classify(row)
            row.update(name="KCheck/Check diagnostic", status=status, first_error=error,
                       trace_env={"CLEAN_CHECK_DECL_BUDGET_TRACE": "1"})
            report["probes"].append(row)
            print(f"KCheck/Check diagnostic: {status}", flush=True)
            for package, module, source in modules:
                argv = [str(binary), "check", module + ".lean", "--json"]
                profile = (args.output.parent / "KCheck-Check.sample.txt").resolve() if module == "KCheck/Check" and sys.platform == "darwin" else None
                row = gated_measure(argv, work, env, args.cap_seconds, profile)
                status, error = classify(row)
                row.update(package=package, module=module, status=status, first_error=error,
                           source_sha256=hashlib.sha256((work / (module + ".lean")).read_bytes()).hexdigest())
                report["modules"].append(row)
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(json.dumps(report, indent=2) + "\n")
                print(f"{package} {module}: {status} {row['wall_seconds']}s {row['peak_bytes']} bytes", flush=True)
        report["complete"] = True
        compare(report, report)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        if args.update:
            BASELINE.parent.mkdir(parents=True, exist_ok=True)
            BASELINE.write_text(json.dumps(report, indent=2) + "\n")
        else:
            compare(report, json.loads(BASELINE.read_text()))
        counts = {p: {s: sum(r["package"] == p and r["status"] == s for r in report["modules"])
                      for s in ("elaborated", "refused", "timed_out")} for p in PACKAGES}
        print("SELF_PROOF_ELAB=measured " + json.dumps(counts), flush=True)


if __name__ == "__main__":
    main()
