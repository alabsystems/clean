#!/usr/bin/env python3
"""Mint an explicitly incomplete C4 pilot, including command resource usage.

Build the experiment binary separately, then run this through heavy_gate.sh.
This never turns partial core token counts into an R2/R3 verdict.
"""
import argparse
import json
import os
import platform
import resource
import shlex
import subprocess
import sys
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--module", default="Init")
    parser.add_argument("--operations", type=int, default=100000)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    command = [str(args.binary.resolve()), str(args.out), args.module, str(args.operations)]
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    load_before = os.getloadavg()
    start = time.monotonic()
    with (args.out / "stdout.log").open("w") as stdout, (args.out / "stderr.log").open("w") as stderr:
        result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
    elapsed = time.monotonic() - start
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    peak_bytes = rss if sys.platform == "darwin" else rss * 1024
    record = {
        "revision": revision,
        "command": command,
        "mint_command": shlex.join(sys.argv),
        "machine": platform.node(),
        "platform": platform.platform(),
        "wall_seconds": elapsed,
        "peak_child_rss_bytes": peak_bytes,
        "exit_code": result.returncode,
        "load_average_before": load_before,
        "load_average_after": os.getloadavg(),
        "status": "incomplete_core_pilot_not_R2_R3_evidence",
    }
    (args.out / "run.json").write_text(json.dumps(record, indent=2) + "\n")
    produced = [p.name for p in args.out.iterdir() if p.is_file()]
    record["artifacts"] = sorted(produced)
    (args.out / "run.json").write_text(json.dumps(record, indent=2) + "\n")
    (args.out / "README.md").write_text(
        "# C4 diagnostic tracing run\n\n"
        "This producer is experimental and excluded from ordinary and fenced entry paths. "
        "Its journal is not replayable advice; R2/R3 remain unset until coverage and "
        "certificate accounting are qualified. Failed units and reannotated dependencies "
        "are named, and cannot be excluded silently from whole-Init claims.\n\n"
        f"Source commit: `{revision}`. Machine: `{record['machine']}` "
        f"(`{record['platform']}`). Wall: {elapsed:.3f} s. Peak child RSS: "
        f"{peak_bytes} bytes. Exit: {result.returncode}.\n\n"
        "Mint command (run through scripts/heavy_gate.sh run):\n\n```sh\n"
        + shlex.join(sys.argv) + "\n```\n\n"
        + "Produced files: " + ", ".join(f"`{name}`" for name in sorted(produced)) + ".\n\n"
        "`ordinary.json`, when present, is the completed baseline checkpoint. "
        "`pilot.json`, when present, contains both replay reports, all observations, "
        "coverage refusals, domain problems and diagnostic distributions. Its limitations "
        "are part of the result. stderr.log records replay progress. Absence of either "
        "file is incomplete execution, never a successful experiment.\n\n"
        "Pinned Lean is resolved by the repository's require_pinned_lean_lib_path; "
        "there is no version substitution. Per-bound soundness remains a design target; "
        "no generation establishes more consistency than its base, and independent "
        "re-checkers remain required. Advice emission proper is still owed.\n"
    )
    print(json.dumps(record, indent=2))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
