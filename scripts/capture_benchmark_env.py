#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""
Capture benchmark environment metadata for verification reports.

Usage:
    python3 scripts/capture_benchmark_env.py [--json] [--table] [--command CMD]

Options:
    --json      Output as JSON instead of markdown
    --table     Output as markdown table (matches existing report format)
    --command   Include benchmark command in output

Captures:
- Git commit hash under test
- Machine/CPU info
- OS version
- rustc/cargo versions
- Benchmark command (if provided)

Output can be pasted into verification reports to satisfy #563 requirements.
"""

from __future__ import annotations

import argparse
import json
import platform
import subprocess
import sys
from datetime import datetime, timezone
from typing import Any

DETERMINISTIC_TIMESTAMP = "1970-01-01T00:00:00Z"


def run_cmd(cmd: list[str], timeout: int = 10) -> str:
    """Run command and return stdout, or error message."""
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return (
            result.stdout.strip()
            if result.returncode == 0
            else f"<error: {result.stderr.strip()}>"
        )
    except FileNotFoundError:
        return f"<not found: {cmd[0]}>"
    except subprocess.TimeoutExpired:
        return "<timeout>"
    except Exception as e:
        return f"<error: {e}>"


def get_git_commit() -> str:
    """Get current git commit hash."""
    result = run_cmd(["git", "rev-parse", "HEAD"])
    if result.startswith("<"):
        return result  # Return error message as-is
    return result[:12]


def get_git_branch() -> str:
    """Get current git branch."""
    return run_cmd(["git", "rev-parse", "--abbrev-ref", "HEAD"])


def get_git_dirty() -> bool:
    """Check if working directory has uncommitted changes."""
    result = run_cmd(["git", "status", "--porcelain"])
    return bool(result and not result.startswith("<"))


def get_cpu_info() -> str:
    """Get CPU model info."""
    system = platform.system()
    if system == "Darwin":
        # Works on both Intel and Apple Silicon Macs
        brand = run_cmd(["sysctl", "-n", "machdep.cpu.brand_string"])
        if not brand.startswith("<"):
            return brand
        # Fallback for older macOS or missing sysctl
        return f"Apple {platform.machine()}"
    if system == "Linux":
        try:
            with open("/proc/cpuinfo") as f:
                for line in f:
                    if line.startswith("model name"):
                        return line.split(":")[1].strip()
        except Exception:
            pass
        return platform.processor() or platform.machine()
    return platform.processor() or platform.machine()


def get_rustc_version() -> str:
    """Get rustc version."""
    return run_cmd(["rustc", "--version"])


def get_cargo_version() -> str:
    """Get cargo version."""
    return run_cmd(["cargo", "--version"])


def get_memory_info() -> str:
    """Get total system memory."""
    system = platform.system()
    if system == "Darwin":
        mem_bytes = run_cmd(["sysctl", "-n", "hw.memsize"])
        try:
            gb = int(mem_bytes) / (1024**3)
            return f"{gb:.0f} GB"
        except ValueError:
            return mem_bytes
    elif system == "Linux":
        try:
            with open("/proc/meminfo") as f:
                for line in f:
                    if line.startswith("MemTotal"):
                        kb = int(line.split()[1])
                        return f"{kb / (1024**2):.0f} GB"
        except Exception:
            pass
    return "<unknown>"


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def capture_environment(*, timestamp: str | None = None) -> dict[str, Any]:
    """Capture all environment metadata."""
    return {
        "commit": get_git_commit(),
        "branch": get_git_branch(),
        "dirty": get_git_dirty(),
        "timestamp": timestamp or utc_now(),
        "machine": {
            "os": f"{platform.system()} {platform.release()}",
            "cpu": get_cpu_info(),
            "memory": get_memory_info(),
            "arch": platform.machine(),
        },
        "toolchain": {
            "rustc": get_rustc_version(),
            "cargo": get_cargo_version(),
        },
    }


def format_markdown(
    env: dict[str, Any], command: str | None = None, table: bool = False
) -> str:
    """Format environment as markdown for reports.

    Args:
        env: Environment dictionary from capture_environment()
        command: Optional benchmark command to include
        table: If True, output as markdown table instead of list
    """
    commit_str = f"`{env['commit']}`" + (" (dirty)" if env["dirty"] else "")

    if table:
        lines = [
            "### Benchmark Environment",
            "",
            "| Field | Value |",
            "|-------|-------|",
            f"| Commit | {commit_str} |",
            f"| Branch | `{env['branch']}` |",
            f"| Timestamp | {env['timestamp']} |",
            f"| OS | {env['machine']['os']} |",
            f"| CPU | {env['machine']['cpu']} |",
            f"| Memory | {env['machine']['memory']} |",
            f"| rustc | {env['toolchain']['rustc']} |",
            f"| cargo | {env['toolchain']['cargo']} |",
        ]
        if command:
            lines.append(f"| Command | `{command}` |")
    else:
        lines = [
            "### Benchmark Environment",
            "",
            f"- **Commit**: {commit_str}",
            f"- **Branch**: `{env['branch']}`",
            f"- **Timestamp**: {env['timestamp']}",
            f"- **OS**: {env['machine']['os']}",
            f"- **CPU**: {env['machine']['cpu']}",
            f"- **Memory**: {env['machine']['memory']}",
            f"- **rustc**: {env['toolchain']['rustc']}",
            f"- **cargo**: {env['toolchain']['cargo']}",
        ]
        if command:
            lines.append(f"- **Command**: `{command}`")

    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Capture benchmark environment metadata for verification reports."
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output as JSON instead of markdown",
    )
    parser.add_argument(
        "--table",
        action="store_true",
        help="Output as markdown table (matches existing report format)",
    )
    parser.add_argument(
        "--command",
        type=str,
        help="Benchmark command to include in output",
    )
    parser.add_argument(
        "--timestamp",
        help="override timestamp in output for reproducible benchmark evidence",
    )
    parser.add_argument(
        "--deterministic",
        action="store_true",
        help="use a stable timestamp when --timestamp is omitted",
    )
    args = parser.parse_args(argv)

    timestamp = args.timestamp
    if timestamp is None and args.deterministic:
        timestamp = DETERMINISTIC_TIMESTAMP

    env = capture_environment(timestamp=timestamp)

    if args.json:
        output = env
        if args.command:
            output["command"] = args.command
        print(json.dumps(output, indent=2, sort_keys=True))
    else:
        print(format_markdown(env, args.command, table=args.table))

    return 0


if __name__ == "__main__":
    sys.exit(main())
