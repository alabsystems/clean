#!/usr/bin/env python3
"""Crystal D6 kernel test battery: clean-kernel's OWN lib tests, run from a flipped build.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.

WHAT IT CLAIMS
    A Trust-flipped clean-kernel behaves like rustc's own build on every test in the kernel's
    INTEGRATION suite (`--test '*'`: every `tests/*.rs` crate, each linking the flipped lib), at
    panic=abort, at each codegen-unit count asked for. The per-function object burn-in
    (`crystal_object_burnin.py`) cannot judge codegen-units > 1: partitioning and ThinLTO import
    decisions move with any MIR change, so functions whose inputs are equivalent still differ in
    machine code (measured 2026-09-24: two cu=16 controls agree in all 13,792 functions, and the
    same flip that is object-identical at cu=1 moves 709 of them at cu=16). What a partition cannot
    hide is BEHAVIOUR.

    A BEHAVIOURAL BATTERY IS ONLY AS STRONG AS ITS WITNESSES, AND THIS ONE HAD NONE FOR ITS OWN
    TARGET. Measured 2026-09-24: the retired TRUST_DROP_CITE stack, rebuilt at cu=16, puts gained
    drop glue into `infer_type`'s object, and the kernel's integration suite passed 242 of 242
    against it. The suite does reach `infer_type`'s `?` error path, but never with an error that
    OWNS HEAP: the only such error there is `HeartbeatExceeded { profile: Some(_) }`, which needs
    the heartbeat profiler, and the one test building it is a lib unit test. A double drop of
    plain data frees nothing, so nothing could see it. `tests/infer_error_heap_drop.rs` is the
    witness; against the same defect build both of its tests fail (a use-after-free read, and a
    SIGTRAP from the allocator). So every run now carries its own FALSIFIER: an arm marked
    `"expect": "red"` must be CAUGHT -- at least one test that passes on the control must fail
    there -- or the run fails. A battery whose defect arm goes green has shown only that it cannot
    see that defect.

WHAT IT DOES
    For every arm in the config and every codegen-unit count, build `clean-kernel`'s integration
    test crates with that arm's sealed driver, record which bodies FLIPPED (the flip trace), run the
    harness, and compare each test's outcome with the CONTROL arm (normally `-Ztrust-ir-flip=no`)
    at the same codegen-unit count. Any test whose outcome differs, a test present on one side
    only, and a harness that does not print its `test result:` summary each fail. Outcomes are
    keyed `<test crate>::<test name>`.

    WHY INTEGRATION TESTS AND NOT THE LIB'S UNIT TESTS. Measured 2026-09-24: lowering the lib's
    unit-test harness (every `#[cfg(test)]` body of the crate) peaked at 66 GB, 183% of a 36 GB
    reservation, and was killed before it could endanger the machine. The integration crates link
    the lib unit the object burn-ins measure, lowered once, and each test crate is small. A control that
    ran zero tests refuses: an empty comparison is not a pass.

    The build is `panic=abort`, the strategy that shipped the miscompile, with `-Zpanic-abort-tests`
    (each test runs in its own process, so a double free that malloc traps fails ONE test instead
    of the run). The lane's prebuilt sysroot cannot serve a test harness at abort: its
    `panic_abort` was compiled for UNWIND and it ships no `libtest`. The config's
    `build_std` (e.g. "std,panic_abort,test") supplies both from source; `sysroot` can instead
    name a prepared compile sysroot. The arm's `rustc_flags` reach the
    clean-kernel LIB compilation ONLY, through a generated RUSTC_WRAPPER; the rest of the graph,
    the test crates included, is compiled identically in every arm. `-Ztrust-ir-lower=on` is added to every arm,
    so the control differs from a flipped arm by the flip alone.

    Config (JSON): {"control": "<arm>", "cgus": [1, 16], "src": "<clean checkout>",
    "sysroot": "<optional compile sysroot for every arm>", "build_std": "<optional -Zbuild-std list>",
    "package": "<test package, default clean-kernel>",

    RUNNER. Inside clean's workspace a dev-dependency switches on clean-kernel's `math-overlays`
    feature, so `cargo test -p clean-kernel` compiles a different and much larger kernel than the
    one the object burn-ins measure: lowering it passed 60 GB, against 24.6 GB for the default
    kernel lib. The measured
    configuration therefore uses a generated runner crate outside the workspace (`src` names it,
    `package` its name) whose `[[test]]` targets are clean-kernel's own integration tests that need
    nothing but the kernel, built against the kernel at its default features.
    "arms": {"<arm>": {"seal": "<dir holding tc>", "env": {"K": "V"}, "rustc_flags": ["-Z..."],
                       "expect": "red"  (optional: this arm is a FALSIFIER and must be caught)}}}.

    GENERATING THE RUNNER (`--gen-runner`). Every `tests/*.rs` of the kernel is a candidate. Left
    out, each with its reason in the generated manifest: a target with `required-features`; a
    file naming a crate the runner does not provide (only clean-kernel, proptest and toml are);
    and a file reading `CARGO_MANIFEST_DIR` or another `env!("CARGO_…")`, which would resolve
    against the runner instead of the kernel. `#[path]` and `mod` are kept: every `[[test]]`
    points at the kernel's own file, so they resolve where they always did (the first,
    hand-written runner dropped them, and with them `release_infer_parity`, the test that
    compares the release `infer_type` with the certifying one). `--extra-test FILE` adds a test
    kept outside the kernel's tree. The lockfile is the WORKSPACE lock, copied and pruned by
    cargo; generation refuses unless every package version in it is one the workspace lock
    already pins, so the runner compiles the same kernel the object burn-ins measure.

DEMONSTRATED: see the report directory named in the registry row; `--selftest` pins the verdict
logic on synthetic runs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEAVY_GATE = ROOT / "scripts" / "heavy_gate.sh"
STAGE2_BIN = "$HOME/trust/build/aarch64-apple-darwin/stage2/bin"
TARGET = "aarch64-apple-darwin"
FLIP_LINE = re.compile(r"compiled from trust-ir.*?(clean_kernel\[[0-9a-f]+\]::[^),\s]+)")
TEST_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored(?:, .*)?)$")
FAILED_CRATE = re.compile(r'could not compile `[^`]+` \(test "([^"]+)"\)')
SUMMARY = re.compile(r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored")
WRAPPER = """#!/bin/sh
# Generated by crystal_kernel_test_battery.py: append $KT_KERNEL_FLAGS to the clean-kernel LIB only.
rustc="$1"; shift
case " $* " in
  *" --crate-name clean_kernel "*)
    case " $* " in *" --test "*) exec "$rustc" "$@" ;; esac
    exec "$rustc" "$@" $KT_KERNEL_FLAGS ;;
esac
exec "$rustc" "$@"
"""
# Every behaviour flag the lane knows, so an arm starts from a clean slate.
LANE_FLAGS = (
    "TRUST_DROP_CITE", "TRUST_DROP_COMPUTED", "TRUST_DROP_GATE_PROBE", "TRUST_ENUM_PAYLOAD_AGG",
    "TRUST_ENUM_LOCAL_READ", "TRUST_DROP_EMIT", "TRUST_STRUCT_RET_DROP", "TRUST_ABORT_UNWIND",
    "TRUST_UNWALKED_DEAD", "TRUST_ZST_MARKERS", "TRUST_RS_MARKERS", "TRUST_RED_NO_GATE",
)


def parse_run(text: str) -> dict:
    """Outcome per test name, plus the harness summary (None when the harness never finished)."""
    outcomes: dict = {}
    summary = None
    for line in text.splitlines():
        m = TEST_LINE.match(line.strip())
        if m:
            outcomes[m.group(1)] = "ignored" if m.group(2).startswith("ignored") else m.group(2)
            continue
        m = SUMMARY.match(line.strip())
        if m:
            summary = {"result": m.group(1), "passed": int(m.group(2)),
                       "failed": int(m.group(3)), "ignored": int(m.group(4))}
    return {"outcomes": outcomes, "summary": summary}


def verdict(results: dict, control: str, cgus: list,
            red_arms: frozenset = frozenset()) -> tuple[bool, list[str], dict]:
    """Pure comparison. `results[(arm, cgu)] = {"outcomes": {test: outcome}, "summary": ..,
    "flipped": [...], "build": "ok" | "failed(<rc>)"}`. Pass iff, at every cgu, the control built,
    ran a non-zero number of tests and printed its summary; every SUBJECT arm built, printed its
    summary and gave every test the control's outcome with no test on one side only; and every
    FALSIFIER arm (`red_arms`) built and was CAUGHT: at least one test the control passes fails
    there. Returns (pass, problems, caught), `caught["<arm>@cu<n>"]` = the tests that caught it."""
    problems: list[str] = []
    caught: dict = {}
    for cgu in cgus:
        ctl = results.get((control, cgu))
        if ctl is None:
            problems.append(f"cu={cgu}: control `{control}` has no run -- refusing")
            continue
        if ctl["build"] != "ok":
            problems.append(f"cu={cgu}: control did not build ({ctl['build']}) -- refusing")
            continue
        if ctl["summary"] is None or not ctl["outcomes"]:
            problems.append(f"cu={cgu}: control ran no tests or never finished -- refusing")
            continue
        for (arm, c), run in sorted(results.items()):
            if c != cgu or arm == control:
                continue
            if arm in red_arms:
                if run["build"] != "ok":
                    problems.append(f"cu={cgu} {arm}: FALSIFIER did not build ({run['build']}), "
                                    f"so it demonstrates nothing")
                    continue
                hits = sorted(t for t, o in ctl["outcomes"].items()
                              if o == "ok" and run["outcomes"].get(t) == "FAILED")
                caught[f"{arm}@cu{cgu}"] = hits
                if not hits:
                    problems.append(f"cu={cgu} {arm}: FALSIFIER NOT CAUGHT: no test that passes on "
                                    f"the control fails here, so this battery cannot see that defect")
                continue
            if run["build"] != "ok":
                problems.append(f"cu={cgu} {arm}: build {run['build']}")
                continue
            if run["summary"] is None:
                problems.append(f"cu={cgu} {arm}: harness never printed its summary "
                                f"({len(run['outcomes'])} tests reported)")
            if run.get("failed_crates", []) != ctl.get("failed_crates", []):
                problems.append(f"cu={cgu} {arm}: test crates that failed to compile differ from the "
                                f"control's: {run.get('failed_crates')} vs {ctl.get('failed_crates')}")
            a, b = ctl["outcomes"], run["outcomes"]
            only_c = sorted(set(a) - set(b))
            only_a = sorted(set(b) - set(a))
            changed = sorted(t for t in set(a) & set(b) if a[t] != b[t])
            if only_c:
                problems.append(f"cu={cgu} {arm}: {len(only_c)} test(s) missing, e.g. {only_c[:3]}")
            if only_a:
                problems.append(f"cu={cgu} {arm}: {len(only_a)} extra test(s), e.g. {only_a[:3]}")
            for t in changed:
                problems.append(f"cu={cgu} {arm}: {t}: control {a[t]} vs arm {b[t]}")
    for arm in sorted(red_arms):
        for cgu in cgus:
            if (arm, cgu) not in results:
                problems.append(f"cu={cgu} {arm}: FALSIFIER has no run")
    return (not problems, problems, caught)


def featureless_tests(src: Path, env: dict, package: str) -> list:
    """clean-kernel's integration-test targets that need no feature. Cargo refuses a selection
    (`--test '*'` included) that names a target with unmet `required-features`, so the default
    feature set's test crates are named one by one, read from `cargo metadata`."""
    meta = subprocess.run(["cargo", "metadata", "--format-version", "1", "--no-deps", "--locked"],
                          cwd=src, env=env, capture_output=True, text=True, check=True)
    pkg = next(p for p in json.loads(meta.stdout)["packages"] if p["name"] == package)
    return sorted(t["name"] for t in pkg["targets"]
                  if "test" in t["kind"] and not t.get("required-features"))


def sysroot_tc(seal: Path, sysroot, work: Path, arm: str) -> Path:
    """The seal's own `tc` wrapper (its guard and DYLD path kept byte for byte) with the compile
    sysroot swapped for `sysroot`, or the seal's `tc` untouched when no sysroot is configured."""
    tc = seal / "tc"
    if not sysroot:
        return tc
    text = tc.read_text()
    m = re.findall(r'--sysroot "([^"]+)"', text)
    if len(m) != 1:
        raise SystemExit(f"{tc}: expected exactly one --sysroot in the seal wrapper, found {len(m)}")
    out = work / f"tc-{arm}"
    out.write_text(text.replace(f'--sysroot "{m[0]}"', f'--sysroot "{sysroot}"'))
    out.chmod(0o755)
    return out


def build_and_run(arm: str, spec: dict, cgu: int, src: Path, work: Path, out: Path,
                  weight: int, threads: int, jobs: int, sysroot=None,
                  package: str = "clean-kernel", build_std=None) -> dict:
    tgt = work / f"ckt-kt-{arm}-cu{cgu}"
    env = {k: v for k, v in os.environ.items() if k not in LANE_FLAGS}
    env.update(spec.get("env", {}))
    env.update({
        "PATH": f"{STAGE2_BIN}:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin",
        "RUSTC": str(sysroot_tc(Path(spec["seal"]), sysroot, work, arm)),
        "RUSTC_BOOTSTRAP": "1",
        "RUSTC_LOG": "rustc_mir_transform::trust_ir_flip=info",
        "RUSTFLAGS": "-Ztrust-verify=off -Cdebuginfo=0 -Cpanic=abort -Zpanic-abort-tests",
        "CARGO_TARGET_DIR": str(tgt),
    })
    kflags = ["-Ztrust-ir-lower=on", *spec.get("rustc_flags", [])]
    # The flip flags reach the clean-kernel LIB compilation and nothing else, through a rustc
    # wrapper keyed on `--crate-name clean_kernel` without `--test`. A package-scoped profile
    # rustflag would also lower every integration-test crate, which is memory spent on code nobody
    # asked about: measured 2026-09-24, that build passed 60 GB and the watchdog killed it.
    wrapper = work / "kernel-flags-wrapper.sh"
    wrapper.write_text(WRAPPER)
    wrapper.chmod(0o755)
    env["RUSTC_WRAPPER"] = str(wrapper)
    env["KT_KERNEL_FLAGS"] = " ".join(kflags)
    cargo = [
        "cargo", *([f"-Zbuild-std={build_std}"] if build_std else []), "-Zhost-config",
        "-Ztarget-applies-to-host", "-Zpanic-abort-tests",
        "--config", "target-applies-to-host=false",
        "--config", 'host.rustflags=["-Ztrust-verify=off"]',
        "--config", f"profile.release.codegen-units={cgu}",
        "build", "--tests", "--target", TARGET, "--locked", "--release", "-p", package,
        *[a for t in featureless_tests(src, env, package) for a in ("--test", t)],
        "-j", str(jobs), "--keep-going", "--message-format=json-render-diagnostics",
    ]
    cmd = [str(HEAVY_GATE), "run", str(weight), f"kt-{arm}-cu{cgu}", "--", *cargo]
    b = subprocess.run(cmd, cwd=src, env=env, capture_output=True, text=True)
    (out / f"{arm}-cu{cgu}.build.txt").write_text(b.stderr)
    flipped = sorted(set(FLIP_LINE.findall(b.stderr)))
    exes: dict = {}
    for line in b.stdout.splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if (msg.get("reason") == "compiler-artifact" and msg.get("executable")
                and "test" in msg.get("target", {}).get("kind", [])
                and msg.get("profile", {}).get("test")):
            exes[msg["target"]["name"]] = msg["executable"]
    # `cargo build --tests --keep-going` (NOT `cargo test --no-run --no-fail-fast`, which stops
    # scheduling builds after the first compile error, so which binaries exist depended on timing:
    # measured 1 vs 16 test binaries in two arms of one run). A test crate that does not compile at
    # the kernel's DEFAULT features (it calls
    # a feature-gated API without declaring `required-features`, which only works inside clean's
    # workspace through feature unification) is recorded, and the verdict requires every arm to
    # fail on EXACTLY the control's set. A crate that stops compiling only under a flip is a
    # finding, not noise.
    failed_crates = sorted(set(FAILED_CRATE.findall(b.stderr)))
    if not exes:
        return {"outcomes": {}, "summary": None, "flipped": flipped,
                "build": f"failed({b.returncode})", "failed_crates": failed_crates}
    outcomes: dict = {}
    summary = {"result": "ok", "passed": 0, "failed": 0, "ignored": 0}
    log = []
    for name, exe in sorted(exes.items()):
        r = subprocess.run([exe, f"--test-threads={threads}"], capture_output=True, text=True,
                           cwd=src)
        log.append(f"===== {name} (exit {r.returncode})\n{r.stdout}\n--- stderr ---\n{r.stderr}")
        parsed = parse_run(r.stdout)
        outcomes.update({f"{name}::{t}": o for t, o in parsed["outcomes"].items()})
        if parsed["summary"] is None:
            summary = None   # one crate that never finished poisons the arm's summary
        elif summary is not None:
            for k in ("passed", "failed", "ignored"):
                summary[k] += parsed["summary"][k]
            if parsed["summary"]["result"] != "ok":
                summary["result"] = "FAILED"
    (out / f"{arm}-cu{cgu}.run.txt").write_text("\n".join(log))
    return {"outcomes": outcomes, "summary": summary, "flipped": flipped, "build": "ok",
            "crates": sorted(exes), "failed_crates": failed_crates}


RUNNER_PROVIDES = {"clean_kernel", "proptest", "toml"}
RUNNER_PROFILE = """[profile.release]
lto = false
codegen-units = 16
panic = "abort"
overflow-checks = true
"""
# Rust comments only; string literals are kept (the `env!("CARGO_…")` test needs them, and a
# string cannot make a test crate depend on another crate).
RUST_COMMENT_RE = re.compile(r"/\*.*?\*/|//[^\n]*", re.S)
CARGO_ENV = re.compile(r'\benv!\s*\(\s*"CARGO_|CARGO_MANIFEST_DIR')
LOCK_PKG = re.compile(r'\[\[package\]\]\nname = "([^"]+)"\nversion = "([^"]+)"')


def runner_exclusion(src: str, required: bool, foreign: set) -> str | None:
    """Why a kernel test cannot run from the generated runner, or None. Comments are blanked
    first, so a crate named only in prose does not exclude a test (strings are kept: the
    `env!("CARGO_…")` check needs them, and they cannot name a crate)."""
    if required:
        return "declares required-features"
    code = RUST_COMMENT_RE.sub("", src)
    names = sorted(c for c in foreign if re.search(rf"\b{c}\b", code))
    if names:
        return "names a crate the runner does not provide: " + ", ".join(names)
    if CARGO_ENV.search(code):
        return "reads CARGO_MANIFEST_DIR / env!(\"CARGO_…\"), which would resolve against the runner"
    return None


def lock_versions(text: str) -> dict:
    out: dict = {}
    for m in LOCK_PKG.finditer(text):
        out.setdefault(m.group(1), set()).add(m.group(2))
    return out


def gen_runner(kernel: Path, workspace_lock: Path, runner: Path, package: str,
               extra: list) -> dict:
    """Write the runner crate (Cargo.toml, src/lib.rs, Cargo.lock) and return what it holds."""
    import tomllib  # 3.11+; imported here so the rest of the battery runs on older Pythons
    manifest = tomllib.loads((kernel / "Cargo.toml").read_text())
    required = {t["name"] for t in manifest.get("test", []) if t.get("required-features")}
    deps = set(manifest.get("dependencies", {})) | set(manifest.get("dev-dependencies", {}))
    for tgt in manifest.get("target", {}).values():
        deps |= set(tgt.get("dependencies", {})) | set(tgt.get("dev-dependencies", {}))
    foreign = {d.replace("-", "_") for d in deps} - RUNNER_PROVIDES
    kept, left = [], []
    for f in sorted((kernel / "tests").glob("*.rs")):
        why = runner_exclusion(f.read_text(), f.stem in required, foreign)
        (left.append((f.stem, why)) if why else kept.append((f.stem, f.resolve())))
    for f in extra:
        f = Path(f).resolve()
        if any(n == f.stem for n, _ in kept):
            raise SystemExit(f"--extra-test {f}: a test named {f.stem} is already in the runner")
        why = runner_exclusion(f.read_text(), False, foreign)
        if why:
            raise SystemExit(f"--extra-test {f}: {why}")
        kept.append((f.stem, f))
    if not kept:
        raise SystemExit(f"{kernel}/tests: no test can run from a runner -- refusing")
    lines = [
        "[package]", f'name = "{package}"', 'version = "0.0.0"', 'edition = "2021"',
        "publish = false", "autotests = false", "",
        "# Generated by scripts/crystal_kernel_test_battery.py --gen-runner. Do not edit.",
        f"# kernel: {kernel.resolve()}",
        f"# lock:   {workspace_lock.resolve()} (copied, pruned by cargo, checked to be a subset)",
        f"# {len(kept)} test crate(s) kept, {len(left)} left out:",
        *[f"#   {n}: {why}" for n, why in left],
        "", "[dependencies]", f'clean-kernel = {{ path = "{kernel.resolve()}" }}', "",
        "[dev-dependencies]", 'proptest = "1.4"', 'toml = "1"', "", RUNNER_PROFILE, "[workspace]", "",
        *[f'[[test]]\nname = "{n}"\npath = "{f}"\n' for n, f in kept],
    ]
    runner.mkdir(parents=True, exist_ok=True)
    (runner / "src").mkdir(exist_ok=True)
    (runner / "src" / "lib.rs").write_text("// Generated: the runner has no code of its own.\n")
    (runner / "Cargo.toml").write_text("\n".join(lines))
    ws = workspace_lock.read_text()
    (runner / "Cargo.lock").write_text(ws)
    env = {**os.environ, "PATH": f"{STAGE2_BIN}:{os.environ.get('PATH', '')}"}
    subprocess.run(["cargo", "metadata", "--format-version", "1", "--offline"], cwd=runner, env=env,
                   capture_output=True, text=True, check=True)
    have, pinned = lock_versions((runner / "Cargo.lock").read_text()), lock_versions(ws)
    drift = sorted(f"{n} {sorted(v - pinned.get(n, set()))}" for n, v in have.items()
                   if n != package and not v <= pinned.get(n, set()))
    if drift:
        raise SystemExit("runner lock pins versions the workspace lock does not -- refusing: "
                         + "; ".join(drift))
    return {"kept": [n for n, _ in kept], "left_out": dict(left), "packages": len(have)}


def selftest() -> int:
    ok = {"a": "ok", "b": "ok", "c": "ignored"}
    summ = {"result": "ok", "passed": 2, "failed": 0, "ignored": 1}
    base = {("ctl", 16): {"outcomes": ok, "summary": summ, "flipped": [], "build": "ok"}}
    arms = []

    def check(name, results, want_pass, needle="", red=frozenset()):
        passed_, probs, _ = verdict(results, "ctl", [16], red)
        good = passed_ == want_pass and (not needle or any(needle in p for p in probs))
        arms.append((name, good, probs))

    check("identical outcomes pass", {**base, ("flip", 16): {"outcomes": dict(ok), "summary": summ,
                                                              "flipped": ["x"], "build": "ok"}}, True)
    check("a test that fails only in the arm FAILS",
          {**base, ("flip", 16): {"outcomes": {**ok, "b": "FAILED"}, "summary": summ,
                                  "flipped": ["x"], "build": "ok"}}, False, "b: control ok vs arm FAILED")
    check("a missing test FAILS", {**base, ("flip", 16): {"outcomes": {"a": "ok", "c": "ignored"},
                                                           "summary": summ, "flipped": [], "build": "ok"}},
          False, "missing")
    check("a harness killed before its summary FAILS (a crash between tests)",
          {**base, ("flip", 16): {"outcomes": dict(ok), "summary": None, "flipped": [], "build": "ok"}},
          False, "never printed")
    check("an arm that did not build FAILS",
          {**base, ("flip", 16): {"outcomes": {}, "summary": None, "flipped": [], "build": "failed(101)"}},
          False, "build failed(101)")
    check("a missing control refuses",
          {("flip", 16): {"outcomes": dict(ok), "summary": summ, "flipped": [], "build": "ok"}}, False, "no run")
    check("a control with zero tests refuses",
          {("ctl", 16): {"outcomes": {}, "summary": summ, "flipped": [], "build": "ok"}}, False, "ran no tests")
    check("an ignored-vs-ok change FAILS",
          {**base, ("flip", 16): {"outcomes": {**ok, "c": "ok"}, "summary": summ, "flipped": [],
                                  "build": "ok"}}, False, "c: control ignored vs arm ok")
    check("a test crate that fails to compile only in the arm FAILS",
          {("ctl", 16): {"outcomes": ok, "summary": summ, "flipped": [], "build": "ok",
                         "failed_crates": ["featured"]},
           ("flip", 16): {"outcomes": dict(ok), "summary": summ, "flipped": [], "build": "ok",
                          "failed_crates": ["featured", "infer_suite"]}},
          False, "failed to compile differ")
    foreign = {"clean_elab", "serde"}
    for name, src, req, want in [
        ("a kernel-only test is kept", "use clean_kernel::Expr;\n#[test] fn t() {}", False, None),
        ("required-features leaves a test out", "use clean_kernel::Expr;", True, "required-features"),
        ("a foreign crate leaves a test out", "use clean_elab::X;", False, "clean_elab"),
        ("a foreign crate named only in a comment does not",
         "// uses clean_elab one day\n/* serde */ use clean_kernel::Expr;", False, None),
        ("CARGO_MANIFEST_DIR leaves a test out", 'let d = env!("CARGO_MANIFEST_DIR");', False, "CARGO_MANIFEST"),
        ("#[path] and mod are kept", '#[path = "x/support.rs"]\nmod support;\nuse clean_kernel::Expr;',
         False, None),
    ]:
        got = runner_exclusion(src, req, foreign)
        good = (got is None) if want is None else (got is not None and want in got)
        arms.append((f"runner: {name}", good, [str(got)]))
    red = frozenset({"defect"})
    check("a falsifier that a test catches passes",
          {**base, ("defect", 16): {"outcomes": {**ok, "b": "FAILED"}, "summary": summ,
                                    "flipped": ["x"], "build": "ok"}}, True, red=red)
    check("a falsifier that NO test catches FAILS (the battery cannot see it)",
          {**base, ("defect", 16): {"outcomes": dict(ok), "summary": summ, "flipped": ["x"],
                                    "build": "ok"}}, False, "FALSIFIER NOT CAUGHT", red=red)
    check("a falsifier that did not build FAILS (it demonstrates nothing)",
          {**base, ("defect", 16): {"outcomes": {}, "summary": None, "flipped": [],
                                    "build": "failed(101)"}}, False, "did not build", red=red)
    check("a falsifier caught only by a test the control ALSO fails FAILS",
          {("ctl", 16): {"outcomes": {**ok, "b": "FAILED"}, "summary": summ, "flipped": [], "build": "ok"},
           ("defect", 16): {"outcomes": {**ok, "b": "FAILED"}, "summary": summ, "flipped": ["x"],
                            "build": "ok"}}, False, "FALSIFIER NOT CAUGHT", red=red)
    check("a falsifier with no run at all FAILS", dict(base), False, "has no run", red=red)
    check("a caught falsifier does not excuse a failing SUBJECT",
          {**base, ("defect", 16): {"outcomes": {**ok, "b": "FAILED"}, "summary": summ,
                                    "flipped": ["x"], "build": "ok"},
           ("flip", 16): {"outcomes": {**ok, "a": "FAILED"}, "summary": summ, "flipped": ["x"],
                          "build": "ok"}}, False, "a: control ok vs arm FAILED", red=red)
    parsed = parse_run("running 3 tests\ntest a::b ... ok\ntest a::c ... FAILED\n"
                       "test a::d ... ignored, needs corpus\n\n"
                       "test result: FAILED. 1 passed; 1 failed; 1 ignored; 0 measured; 0 filtered out\n")
    arms.append(("the parser reads outcomes and the summary",
                 parsed["outcomes"] == {"a::b": "ok", "a::c": "FAILED", "a::d": "ignored"}
                 and parsed["summary"] == {"result": "FAILED", "passed": 1, "failed": 1, "ignored": 1},
                 [str(parsed)]))
    failed = [a for a in arms if not a[1]]
    for name, good, probs in arms:
        print(f"  {'ok ' if good else 'BAD'} {name}" + ("" if good else f" -- {probs}"))
    print(f"SELFTEST={'ok' if not failed else 'FAIL'} arms={len(arms)} failed={len(failed)}")
    return 0 if not failed else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--config", help="JSON config (see module docs)")
    ap.add_argument("--out", help="directory for build/run traces and the JSON verdict")
    ap.add_argument("--work", help="directory for the per-arm cargo target dirs")
    ap.add_argument("--weight", type=int, default=40, help="heavy_gate reservation per build, GB")
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--jobs", type=int, default=2, help="cargo -j for the lowered builds")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--gen-runner", action="store_true",
                    help="write the runner crate (--kernel, --workspace-lock, --runner) and exit")
    ap.add_argument("--kernel", type=Path, help="clean-kernel crate dir the runner builds")
    ap.add_argument("--workspace-lock", type=Path, help="the clean workspace Cargo.lock")
    ap.add_argument("--runner", type=Path, help="directory to write the runner crate into")
    ap.add_argument("--package", default="kernel-test-runner", help="runner package name")
    ap.add_argument("--extra-test", action="append", default=[], type=Path,
                    help="a test file kept outside the kernel tree (repeatable)")
    a = ap.parse_args()
    # Hashed at START: a run takes hours, and an edit made meanwhile must not be attributed to it.
    script_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if a.selftest:
        return selftest()
    if a.gen_runner:
        if not (a.kernel and a.workspace_lock and a.runner):
            ap.error("--gen-runner needs --kernel, --workspace-lock and --runner")
        info = gen_runner(a.kernel, a.workspace_lock, a.runner, a.package, a.extra_test)
        for n, why in sorted(info["left_out"].items()):
            print(f"  left out {n}: {why}")
        print(f"RUNNER={a.runner} kept={len(info['kept'])} left_out={len(info['left_out'])} "
              f"lock_packages={info['packages']}")
        return 0
    if not a.config or not a.out or not a.work:
        ap.error("--config, --out and --work are required (or --selftest)")
    cfg = json.loads(Path(a.config).read_text())
    out, work, src = Path(a.out), Path(a.work), Path(cfg["src"])
    out.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True, exist_ok=True)
    results = {}
    for cgu in cfg["cgus"]:
        for arm, spec in cfg["arms"].items():
            r = build_and_run(arm, spec, cgu, src, work, out, a.weight, a.threads, a.jobs,
                              cfg.get("sysroot"), cfg.get("package", "clean-kernel"),
                              cfg.get("build_std"))
            results[(arm, cgu)] = r
            print(f"{arm} cu={cgu}: build={r['build']} tests={len(r['outcomes'])} "
                  f"summary={r['summary']} flipped={len(r['flipped'])}", flush=True)
    red_arms = frozenset(a for a, s in cfg["arms"].items() if s.get("expect") == "red")
    ok, problems, caught = verdict(results, cfg["control"], cfg["cgus"], red_arms)
    report = {"schema": "clean.crystal-kernel-test-battery/v2", "script_sha256": script_sha,
              "config": cfg,
              "falsifiers_caught_by": caught,
              "runs": {f"{k[0]}@cu{k[1]}": {"role": ("control" if k[0] == cfg["control"] else
                                                     "falsifier" if k[0] in red_arms else "subject"),
                                            "build": v["build"], "summary": v["summary"],
                                            "failed_crates": v.get("failed_crates", []),
                                            "tests": len(v["outcomes"]), "flipped": v["flipped"],
                                            "failed_tests": sorted(t for t, o in v["outcomes"].items()
                                                                   if o == "FAILED")}
                       for k, v in results.items()},
              "verdict": "pass" if ok else "fail", "problems": problems}
    (out / "verdict.json").write_text(json.dumps(report, indent=2) + "\n")
    for p in problems[:50]:
        print("  DIFF", p)
    print(f"VERDICT={'pass' if ok else 'fail'} arms={len(cfg['arms'])} cgus={cfg['cgus']} "
          f"problems={len(problems)}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
