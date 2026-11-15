#!/usr/bin/env python3
"""Crystal D6 fixture battery: the double-drop shapes, observed at RUN TIME.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.

WHAT IT CLAIMS
    A flipped body behaves like rustc's own at run time, on the shapes that produced the
    retired TRUST_DROP_CITE double drop. `tests/fixtures/crystal/fixture_drops.rs` has one arm
    per shape. Each arm prints an exact line, and the Drop-bearing error bumps a counter:
      (i)   `?` over an error whose Drop is observable (free functions);
      (ii)  `?` over a heap `String` error, where a double drop is a double FREE that malloc traps;
      (iii) `let s: String = f()?`;
      (iv)  a Drop-bearing value live across an overflow Assert, consumed by the return aggregate;
      (v)   infer_type's EXACT shape: `&self` methods, `self.tick_heartbeat()?; self.infer_type_fast(e)`.
    The fixture builds `no_std`/`no_main` at panic=abort (the lane's sealed sysroot cannot link a
    std binary there, and abort is the strategy that shipped the miscompile) and with std at
    panic=unwind, one source switched on `cfg(panic)`; `panics` in the config selects the axis.

WHAT IT DOES
    For every ARM in the config and every opt level, build the fixture with that arm's sealed
    driver and environment, record which bodies FLIPPED (the flip trace), RUN the binary, and
    compare (stdout, exit status) with the CONTROL arm (normally `-Ztrust-ir-flip=no`) at the
    same opt level. Any difference fails. A run that does not end in `END`, and any non-zero exit,
    is a difference by construction. A missing control refuses.

    Config (JSON): {"control": "<arm name>", "opts": [0, 3], "panics": ["abort", "unwind"] (default
    ["abort"]), "arms": {"<name>": {"seal": "<dir
    holding tc>", "env": {"K": "V"}, "rustc_flags": ["-Z..."]}}}. The caller supplies the seals,
    so this script is lane infrastructure and runs where sealed drivers exist.

DEMONSTRATED (both directions, 2026-09-24; record:
reports/crystal-lane/2026-09-24-fixture-battery/)
    GREEN: the computed-admission stack flips `arm_ii` (O0) and `Tc::infer_type` (O0, O3), and
    both runs are byte-identical to the control, with each error dropped once.
    RED: a throwaway driver carrying the original defect (cite stack, relocation off, gate
    bypassed) flips the same bodies. At O3 `Tc::infer_type` drops its error TWICE (`v-err drops=2`).
    At O0 `arm_ii` double-frees, and malloc traps it (exit 133, SIGTRAP).
    `--selftest` pins the verdict logic on synthetic runs.

    2026-09-24 (later), with the unwind axis, on the drivers of trust 1b84849bc5 (record:
    reports/crystal-lane/2026-09-24-fixture-battery-v2/): GREEN for the default flip and the
    eight-lane set at O0/O3 under both abort and unwind; RED for the original defect re-created on
    that tree (double free at O0, `drops=2` at O3).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "tests" / "fixtures" / "crystal" / "fixture_drops.rs"
CARGO_TOML = """[package]
name = "fixture-drops"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "fixture-drops"
path = "src/main.rs"

[profile.release]
overflow-checks = true
debug = 0
panic = "{panic}"

[workspace]
"""
FLIP_LINE = re.compile(r"compiled from trust-ir.*?fixture_drops\[[0-9a-f]+\]::([^),]+)")
STAGE2_BIN = "$HOME/trust/build/aarch64-apple-darwin/stage2/bin"
# Every behaviour flag the lane knows, so an arm starts from a clean slate.
LANE_FLAGS = (
    "TRUST_DROP_CITE", "TRUST_DROP_COMPUTED", "TRUST_DROP_GATE_PROBE", "TRUST_ENUM_PAYLOAD_AGG",
    "TRUST_ENUM_LOCAL_READ", "TRUST_DROP_EMIT", "TRUST_STRUCT_RET_DROP", "TRUST_ABORT_UNWIND",
    "TRUST_UNWALKED_DEAD", "TRUST_ZST_MARKERS", "TRUST_RS_MARKERS", "TRUST_RED_NO_GATE",
)


def verdict(results: dict, control: str, opts: list) -> tuple[bool, list[str]]:
    """Pure comparison. `results[(arm, opt)] = {"stdout": str, "exit": int, "flipped": [...]}`.
    Pass iff every non-control arm matches the control's (stdout, exit) at the same opt, the
    control itself completed (`END`, exit 0), and every run is present."""
    problems: list[str] = []
    for opt in opts:
        ctl = results.get((control, opt))
        if ctl is None:
            problems.append(f"O{opt}: control `{control}` has no run -- refusing")
            continue
        if ctl["exit"] != 0 or not ctl["stdout"].rstrip().endswith("END"):
            problems.append(f"O{opt}: control did not complete (exit {ctl['exit']})")
        # Levels mix ints (abort: 0, 3) and strings (unwind: "0-unwind"); sort on a string key.
        for (arm, o), run in sorted(results.items(), key=lambda kv: (kv[0][0], str(kv[0][1]))):
            if o != opt or arm == control:
                continue
            if (run["stdout"], run["exit"]) != (ctl["stdout"], ctl["exit"]):
                cl = ctl["stdout"].splitlines()
                rl = run["stdout"].splitlines()
                first = next((i for i in range(max(len(cl), len(rl)))
                              if (cl[i:i + 1] or [None]) != (rl[i:i + 1] or [None])), None)
                what = (f"line {first + 1}: control {cl[first] if first is not None and first < len(cl) else '<end>'!r}"
                        f" vs arm {rl[first] if first is not None and first < len(rl) else '<end>'!r}")
                problems.append(f"O{opt} {arm}: exit {run['exit']} vs {ctl['exit']}; {what}; "
                                f"flipped={run['flipped']}")
    return (not problems, problems)


def build_and_run(arm: str, spec: dict, opt: int, work: Path, trace_dir: Path,
                  panic: str = "abort") -> dict:
    tag = f"O{opt}" if panic == "abort" else f"O{opt}-{panic}"
    proj = work / f"proj-{arm}-{tag}"
    (proj / "src").mkdir(parents=True)
    (proj / "Cargo.toml").write_text(CARGO_TOML.replace("{panic}", panic))
    shutil.copy(FIXTURE, proj / "src" / "main.rs")
    env = {k: v for k, v in os.environ.items() if k not in LANE_FLAGS}
    env.update(spec.get("env", {}))
    env.update({
        "PATH": f"{STAGE2_BIN}:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin",
        "RUSTC": str(Path(spec["seal"]) / "tc"),
        "RUSTC_BOOTSTRAP": "1",
        "RUSTC_LOG": "rustc_mir_transform::trust_ir_flip=info",
        "RUSTFLAGS": "-Ztrust-verify=off -Cdebuginfo=0",
        "CARGO_TARGET_DIR": str(proj / "target"),
    })
    cmd = ["cargo", "rustc", "--release", "--bin", "fixture-drops", "--",
           "-Ztrust-ir-lower=on", f"-Copt-level={opt}", "-Ccodegen-units=1", f"-Cpanic={panic}",
           *spec.get("rustc_flags", [])]
    b = subprocess.run(cmd, cwd=proj, env=env, capture_output=True, text=True)
    (trace_dir / f"{arm}-{tag}.build.txt").write_text(b.stdout + b.stderr)
    flipped = sorted(set(FLIP_LINE.findall(b.stderr)))
    exe = proj / "target" / "release" / "fixture-drops"
    if b.returncode != 0 or not exe.exists():
        return {"stdout": "", "exit": f"build-failed({b.returncode})", "flipped": flipped}
    r = subprocess.run([str(exe)], capture_output=True, text=True)
    (trace_dir / f"{arm}-{tag}.run.txt").write_text(r.stdout)
    return {"stdout": r.stdout, "exit": r.returncode, "flipped": flipped}


def selftest() -> int:
    good = "i-err ok=true drops=1\nv-err ok=true drops=1\nEND\n"
    arms = []

    def check(name, results, want_pass, needle=""):
        ok, probs = verdict(results, "ctl", [3])
        passed = ok == want_pass and (not needle or any(needle in p for p in probs))
        arms.append((name, passed, probs))

    base = {("ctl", 3): {"stdout": good, "exit": 0, "flipped": []}}
    check("identical arm passes", {**base, ("comp", 3): {"stdout": good, "exit": 0, "flipped": ["infer_type"]}}, True)
    check("double drop fails", {**base, ("red", 3): {"stdout": good.replace("v-err ok=true drops=1", "v-err ok=true drops=2"),
                                                     "exit": 0, "flipped": ["infer_type"]}}, False, "drops=2")
    check("malloc trap fails", {**base, ("red", 3): {"stdout": "i-err ok=true drops=1\n", "exit": 133, "flipped": ["arm_ii"]}},
          False, "exit 133")
    check("missing control refuses", {("comp", 3): {"stdout": good, "exit": 0, "flipped": []}}, False, "no run")
    check("control that crashed refuses", {("ctl", 3): {"stdout": "i-err\n", "exit": 134, "flipped": []}}, False, "did not complete")
    check("build failure fails", {**base, ("comp", 3): {"stdout": "", "exit": "build-failed(101)", "flipped": []}}, False)
    mixed = {("ctl", 3): {"stdout": good, "exit": 0, "flipped": []},
             ("ctl", "3-unwind"): {"stdout": good, "exit": 0, "flipped": []},
             ("comp", 3): {"stdout": good, "exit": 0, "flipped": ["x"]},
             ("comp", "3-unwind"): {"stdout": good.replace("drops=1", "drops=2"), "exit": 0,
                                    "flipped": ["x"]}}
    ok_m, probs_m = verdict(mixed, "ctl", [3, "3-unwind"])
    arms.append(("abort and unwind levels together: sorts, and the unwind drop is caught",
                 (not ok_m) and any("3-unwind comp" in p for p in probs_m), probs_m))
    failed = [a for a in arms if not a[1]]
    for name, passed, probs in arms:
        print(f"  {'ok ' if passed else 'BAD'} {name}" + ("" if passed else f" -- {probs}"))
    print(f"SELFTEST={'ok' if not failed else 'FAIL'} arms={len(arms)} failed={len(failed)}")
    return 0 if not failed else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--config", help="JSON config (see module docs)")
    ap.add_argument("--out", help="directory for build/run traces and the JSON verdict")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if not a.config or not a.out:
        ap.error("--config and --out are required (or --selftest)")
    cfg = json.loads(Path(a.config).read_text())
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    results = {}
    levels: list = []
    with tempfile.TemporaryDirectory(prefix="crystal-fixture-") as tmp:
        for panic in cfg.get("panics", ["abort"]):
            for opt in cfg["opts"]:
                level = opt if panic == "abort" else f"{opt}-{panic}"
                levels.append(level)
                for arm, spec in cfg["arms"].items():
                    results[(arm, level)] = build_and_run(arm, spec, opt, Path(tmp), out, panic)
                    r = results[(arm, level)]
                    print(f"{arm} O{level}: exit={r['exit']} flipped={r['flipped']}")
    ok, problems = verdict(results, cfg["control"], levels)
    report = {"schema": "clean.crystal-fixture-battery/v1", "config": cfg, "fixture": str(FIXTURE.relative_to(ROOT)),
              "runs": {f"{k[0]}@O{k[1]}": v for k, v in results.items()}, "verdict": "pass" if ok else "fail",
              "problems": problems}
    (out / "verdict.json").write_text(json.dumps(report, indent=2) + "\n")
    for p in problems:
        print("  DIFF", p)
    print(f"VERDICT={'pass' if ok else 'fail'} arms={len(cfg['arms'])} opts={cfg['opts']} problems={len(problems)}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
