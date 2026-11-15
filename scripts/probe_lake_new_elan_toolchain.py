#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Measure what a real elan does inside a `clean lake new` project.

Plan item `devsurface-lake-env-no-silent-lean`, part (b): the `lean-toolchain`
that `clean lake new` writes must never let elan silently resolve a leanprover
toolchain. This is a MEASUREMENT, not a gate: it executes the elan binaries it
is given, and it records each one's version and sha256 beside its verdicts.

Every run is sealed. Each elan gets a fresh temporary HOME and ELAN_HOME, an
explicit PATH (`$ELAN_HOME/bin:/usr/bin:/bin`), and, unless `--online` is
passed, every proxy variable pointing at a dead local port, so no toolchain can
download. The user's own `~/.elan` is never read or written. The only installed
toolchain is a FAKE `leanprover/lean4:v4.99.0`, set as elan's default, whose
`bin/lean` appends to a sentinel file: if elan falls back to a leanprover
toolchain, the sentinel shows it.

Cases per elan, in this order:
  * `clean lake new`: a project created by the given `clean` binary.
  * `legacy clean:stable`: the spelling `clean lake new` wrote before this item.
  * `positive control`: `leanprover/lean4:v4.99.0`. Its sentinel MUST fire, or
    the harness could not see a fallback and the run proves nothing.
  * `linked clean`: the `clean lake new` project again, after
    `elan toolchain link clean <dir>` names a second fake whose `bin/lean`
    writes its own sentinel. This is how a user points elan at a Clean shim.

In each project the probe runs `elan show` and `lean --version` through elan's
proxy. A case's verdict is `ran-leanprover` when the leanprover sentinel fired,
`ran-linked` when the linked fake's sentinel fired, `refused` when neither
fired and `lean --version` exited non-zero, and `other` otherwise.

Exit status: 0 when every positive control fired, every `clean lake new` case
is `refused` and every `linked clean` case is `ran-linked`; 1 otherwise (the
report is still written); 2 on bad usage.

Usage:
  python3 scripts/probe_lake_new_elan_toolchain.py --clean <clean-binary> \\
      --elan <elan-binary> [--elan <elan-binary> ...] [--online] [--out <file>]
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path

FAKE_RELEASE = "v4.99.0"
FAKE_TOOLCHAIN = f"leanprover/lean4:{FAKE_RELEASE}"
FAKE_DIR = f"leanprover--lean4---{FAKE_RELEASE}"
LINKED_NAME = "clean"
LEGACY_SPELLING = "clean:stable\n"
DEAD_PROXY = "http://127.0.0.1:9"
PROXY_VARS = (
    "https_proxy",
    "HTTPS_PROXY",
    "http_proxy",
    "HTTP_PROXY",
    "all_proxy",
    "ALL_PROXY",
)
STEP_TIMEOUT_S = 120


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def scrub(text: str, tmp: Path) -> str:
    """Replace the run's temporary root so reports do not churn."""
    out = text
    for spelling in sorted({str(tmp), str(tmp.resolve())}, key=len, reverse=True):
        out = out.replace(spelling, "<tmp>")
    return out


def sealed_env(tmp: Path, elan_home: Path, online: bool) -> dict[str, str]:
    env = {
        "HOME": str(tmp / "home"),
        "ELAN_HOME": str(elan_home),
        "PATH": f"{elan_home / 'bin'}:/usr/bin:/bin",
        "LANG": "C",
        "LC_ALL": "C",
        "NO_PROXY": "",
        "no_proxy": "",
        "ELAN_NO_OVERRIDE_NOTICE": "1",
        "SENTINEL": str(tmp / "sentinel"),
        "LINKED_SENTINEL": str(tmp / "linked-sentinel"),
    }
    if not online:
        for var in PROXY_VARS:
            env[var] = DEAD_PROXY
    return env


def write_fake_lean(path: Path, sentinel_var: str, banner: str) -> None:
    path.parent.mkdir(parents=True)
    path.write_text(
        "#!/bin/sh\n"
        f"printf 'ran\\n' >> \"${sentinel_var}\"\n"
        f"echo '{banner}'\n"
    )
    path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


def install_fake_default(elan_home: Path) -> None:
    write_fake_lean(
        elan_home / "toolchains" / FAKE_DIR / "bin" / "lean",
        "SENTINEL",
        f"FAKE leanprover lean {FAKE_RELEASE}",
    )
    (elan_home / "settings.toml").write_text(
        f'default_toolchain = "{FAKE_TOOLCHAIN}"\n'
        'telemetry = false\nversion = "12"\n\n[overrides]\n'
    )


def run_step(argv: list[str], cwd: Path, env: dict[str, str], tmp: Path) -> dict:
    sentinels = {
        "sentinel_fired": Path(env["SENTINEL"]),
        "linked_sentinel_fired": Path(env["LINKED_SENTINEL"]),
    }
    for sentinel in sentinels.values():
        if sentinel.exists():
            sentinel.unlink()
    try:
        proc = subprocess.run(
            argv,
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
            timeout=STEP_TIMEOUT_S,
        )
        exit_code: int | None = proc.returncode
        stdout, stderr = proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as exc:
        exit_code = None
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = f"timeout after {STEP_TIMEOUT_S}s"
    step = {
        "argv": [scrub(arg, tmp) for arg in argv],
        "exit": exit_code,
        "stdout": scrub(stdout, tmp),
        "stderr": scrub(stderr, tmp),
    }
    for key, sentinel in sentinels.items():
        step[key] = sentinel.exists()
    return step


def verdict(steps: list[dict]) -> str:
    if any(step["sentinel_fired"] for step in steps):
        return "ran-leanprover"
    if any(step["linked_sentinel_fired"] for step in steps):
        return "ran-linked"
    lean = steps[-1]
    if lean["exit"] not in (0, None):
        return "refused"
    return "other"


def probe_case(name: str, project: Path, env: dict[str, str], tmp: Path) -> dict:
    toolchain = (project / "lean-toolchain").read_text()
    steps = [
        run_step(["elan", "show"], project, env, tmp),
        run_step(["lean", "--version"], project, env, tmp),
    ]
    return {
        "case": name,
        "lean_toolchain": toolchain,
        "steps": steps,
        "verdict": verdict(steps),
    }


def probe_one_elan(elan: Path, clean: Path, online: bool) -> dict:
    tmp = Path(tempfile.mkdtemp(prefix="clean-elan-probe-"))
    try:
        elan_home = tmp / "elan"
        (tmp / "home").mkdir()
        (elan_home / "bin").mkdir(parents=True)
        (elan_home / "toolchains").mkdir()
        shutil.copy2(elan, elan_home / "bin" / "elan")
        (elan_home / "bin" / "lean").symlink_to("elan")
        install_fake_default(elan_home)
        env = sealed_env(tmp, elan_home, online)

        version = subprocess.run(
            [str(elan_home / "bin" / "elan"), "--version"],
            env=env,
            capture_output=True,
            text=True,
            timeout=STEP_TIMEOUT_S,
        ).stdout.strip()

        work = tmp / "work"
        work.mkdir()
        created = subprocess.run(
            [str(clean), "lake", "new", "probe_proj"],
            cwd=work,
            env=env,
            capture_output=True,
            text=True,
            timeout=STEP_TIMEOUT_S,
        )
        if created.returncode != 0:
            raise SystemExit(
                f"`clean lake new` failed ({created.returncode}): {created.stderr}"
            )

        legacy = work / "legacy"
        legacy.mkdir()
        (legacy / "lean-toolchain").write_text(LEGACY_SPELLING)
        control = work / "control"
        control.mkdir()
        (control / "lean-toolchain").write_text(FAKE_TOOLCHAIN + "\n")

        cases = [
            probe_case("clean lake new", work / "probe_proj", env, tmp),
            probe_case("legacy clean:stable", legacy, env, tmp),
            probe_case("positive control", control, env, tmp),
        ]

        linked = tmp / "linked-clean"
        write_fake_lean(linked / "bin" / "lean", "LINKED_SENTINEL", "FAKE linked clean lean")
        link = run_step(
            ["elan", "toolchain", "link", LINKED_NAME, str(linked)], work, env, tmp
        )
        case = probe_case("linked clean", work / "probe_proj", env, tmp)
        case["link_step"] = link
        cases.append(case)

        return {
            # The file name only: the sha256 identifies the binary, and a
            # local path would make the report name this machine.
            "elan_binary_name": elan.name,
            "elan_sha256": sha256_file(elan),
            "elan_version": version,
            "cases": cases,
        }
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--clean", required=True, type=Path)
    parser.add_argument("--elan", required=True, type=Path, action="append")
    parser.add_argument("--online", action="store_true")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    for path in [args.clean, *args.elan]:
        if not path.is_file() or not os.access(path, os.X_OK):
            print(f"not an executable file: {path}", file=sys.stderr)
            return 2

    clean_version = subprocess.run(
        [str(args.clean), "--version"],
        capture_output=True,
        text=True,
        env={"PATH": "/usr/bin:/bin", "HOME": tempfile.gettempdir()},
    ).stdout.strip()
    runs = [
        probe_one_elan(elan.resolve(), args.clean.resolve(), args.online)
        for elan in args.elan
    ]
    report = {
        "probe": "scripts/probe_lake_new_elan_toolchain.py",
        "plan_item": "devsurface-lake-env-no-silent-lean",
        "date": _dt.date.today().isoformat(),
        "clean_version": clean_version,
        "clean_sha256": sha256_file(args.clean.resolve()),
        "network": "online" if args.online else f"dead proxy {DEAD_PROXY}",
        "fake_default_toolchain": FAKE_TOOLCHAIN,
        "runs": runs,
    }
    text = json.dumps(report, indent=2, sort_keys=False) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text)
    else:
        sys.stdout.write(text)

    ok = True
    for run in runs:
        by_case = {case["case"]: case for case in run["cases"]}
        verdicts = {name: case["verdict"] for name, case in by_case.items()}
        print(
            f"{run['elan_version']}: "
            + "; ".join(f"{name} -> {v}" for name, v in verdicts.items()),
            file=sys.stderr,
        )
        if verdicts["positive control"] != "ran-leanprover":
            print("  the positive control did not fire: the harness is blind", file=sys.stderr)
            ok = False
        if verdicts["clean lake new"] != "refused":
            ok = False
        if verdicts["linked clean"] != "ran-linked":
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
