#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECK_PASS = "pass"
CHECK_WARN = "warn"
CHECK_FAIL = "fail"
CHECK_SKIP = "skip"
DETERMINISTIC_GENERATED_AT = "1970-01-01T00:00:00Z"


class CheckResult:
    def __init__(
        self,
        name: str,
        status: str,
        message: str,
        details: dict[str, object] | None = None,
    ) -> None:
        self.name = name
        self.status = status
        self.message = message
        self.details = details


def _resolve_git_common_dir(repo_root: Path = ROOT) -> tuple[Path | None, str | None]:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--git-common-dir"],
            capture_output=True,
            text=True,
            timeout=10,
            cwd=repo_root,
        )
    except FileNotFoundError:
        return None, "git not found"
    except subprocess.TimeoutExpired:
        return None, "timeout resolving git common dir"

    if result.returncode != 0:
        output = f"{result.stdout}{result.stderr}".strip()
        return None, output if output else f"exit {result.returncode}"

    common_dir_text = result.stdout.strip()
    if not common_dir_text:
        return None, "git rev-parse --git-common-dir returned no path"

    common_dir = Path(common_dir_text)
    if not common_dir.is_absolute():
        common_dir = repo_root / common_dir
    return common_dir.resolve(), None


def find_worktree_gc_logs(git_common_dir: Path) -> list[Path]:
    worktrees_dir = git_common_dir / "worktrees"
    if not worktrees_dir.is_dir():
        return []
    return sorted(path for path in worktrees_dir.glob("*/gc.log") if path.is_file())


def find_git_gc_logs(git_common_dir: Path) -> list[Path]:
    gc_logs: list[Path] = []
    common_gc_log = git_common_dir / "gc.log"
    if common_gc_log.is_file():
        gc_logs.append(common_gc_log)
    gc_logs.extend(find_worktree_gc_logs(git_common_dir))
    return sorted(gc_logs)


def _display_gc_log_path(path: Path, git_common_dir: Path) -> str:
    base = git_common_dir.parent if git_common_dir.name == ".git" else git_common_dir
    try:
        return str(path.relative_to(base))
    except ValueError:
        return str(path)


def check_worktree_gc_logs(
    repo_root: Path = ROOT, git_common_dir: Path | None = None
) -> tuple[bool, str]:
    if git_common_dir is None:
        git_common_dir, error = _resolve_git_common_dir(repo_root)
        if error is not None or git_common_dir is None:
            return False, f"could not inspect git gc logs: {error}"

    worktrees_dir = git_common_dir / "worktrees"
    gc_logs = find_git_gc_logs(git_common_dir)
    if not gc_logs:
        return True, f"none found under {git_common_dir / 'gc.log'} or {worktrees_dir}"

    paths = ", ".join(_display_gc_log_path(path, git_common_dir) for path in gc_logs)
    return (
        False,
        "stale git gc.log file(s) found: "
        f"{paths}; inspect the failed git gc output before removing them",
    )


def _get_env_with_cargo_path() -> dict[str, str]:
    """Return environment with common cargo/rustup paths added."""
    env = os.environ.copy()
    home = Path.home()
    rustup_toolchains = home / ".rustup" / "toolchains"
    toolchain_bins: list[str] = []
    if rustup_toolchains.exists():
        toolchain_bins = sorted(
            str(path / "bin")
            for path in rustup_toolchains.iterdir()
            if path.is_dir() and (path / "bin").exists()
        )
    extra_paths = [
        str(home / ".cargo" / "bin"),
        str(rustup_toolchains / "stable-aarch64-apple-darwin" / "bin"),
        str(rustup_toolchains / "stable-x86_64-apple-darwin" / "bin"),
        *toolchain_bins,
    ]
    current_path = env.get("PATH", "")
    for path in extra_paths:
        if path not in current_path and Path(path).exists():
            current_path = f"{path}:{current_path}"
    env["PATH"] = current_path
    return env


def run_cmd(cmd: list[str]) -> tuple[bool, str]:
    env = _get_env_with_cargo_path()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=10,
            env=env,
        )
    except FileNotFoundError:
        return False, "not found"
    except subprocess.TimeoutExpired:
        return False, "timeout"
    if result.returncode != 0:
        output = f"{result.stdout}{result.stderr}".strip()
        return False, output if output else f"exit {result.returncode}"
    output = f"{result.stdout}{result.stderr}".strip()
    return True, output if output else "ok"


def check_ay_updates() -> tuple[bool, str, dict[str, object]]:
    """Validate the committed AY graph and compare its pin with remote main."""
    check_script = ROOT / "scripts" / "check_ay_updates.py"
    if not check_script.exists():
        return False, "check script not installed", {"pin_status": "invalid"}
    try:
        result = subprocess.run(
            [sys.executable, str(check_script), "--json"],
            capture_output=True,
            text=True,
            timeout=90,
            cwd=ROOT,
        )
        try:
            payload = json.loads(result.stdout)
        except json.JSONDecodeError:
            message = result.stderr.strip() or result.stdout.strip()
            return (
                False,
                message or f"pin checker exited {result.returncode} without JSON",
                {"pin_status": "invalid"},
            )
        if not isinstance(payload, dict):
            return False, "pin checker returned non-object JSON", {"pin_status": "invalid"}

        details = {
            key: value
            for key, value in payload.items()
            if key
            in {
                "pin_status",
                "ay_dependency_rev",
                "ay_lockfile_rev",
                "ay_lockfile_commit",
                "ay_manifest_pin_count",
                "ay_lock_source_count",
                "ay_remote_rev",
                "remote_status",
                "pin_in_sync",
            }
        }
        if result.returncode == 0 and payload.get("status") == "up_to_date":
            return (
                True,
                "committed manifest/lock pin matches AY remote main",
                details,
            )
        if result.returncode == 1 and payload.get("status") == "updates_available":
            return (
                False,
                "committed AY pin is stale relative to remote main "
                "(see .flags/ay_updates)",
                details,
            )
        error = payload.get("error")
        return (
            False,
            str(error) if error else f"pin checker exited {result.returncode}",
            details,
        )
    except subprocess.TimeoutExpired:
        return False, "timeout checking ay", {"pin_status": "invalid"}
    except Exception as e:
        return False, str(e), {"pin_status": "invalid"}


def _get_git_commit(repo_root: Path = ROOT) -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=10,
            cwd=repo_root,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return "unknown"
    if result.returncode != 0:
        return "unknown"
    return result.stdout.strip() or "unknown"


def _get_project_name(repo_root: Path = ROOT) -> str:
    try:
        result = subprocess.run(
            ["git", "remote", "get-url", "origin"],
            capture_output=True,
            text=True,
            timeout=10,
            cwd=repo_root,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return repo_root.name
    if result.returncode != 0:
        return repo_root.name
    remote_url = result.stdout.strip().rstrip("/")
    if not remote_url:
        return repo_root.name
    return remote_url.split("/")[-1].removesuffix(".git")


def run_checks() -> list[CheckResult]:
    results: list[CheckResult] = []

    if not (ROOT / "Cargo.toml").exists():
        results.append(
            CheckResult(
                "cargo_toml",
                CHECK_FAIL,
                "missing Cargo.toml in repo root",
            )
        )
    else:
        results.append(CheckResult("cargo_toml", CHECK_PASS, "Cargo.toml present"))

    if not (ROOT / "Cargo.lock").exists():
        results.append(
            CheckResult(
                "cargo_lock",
                CHECK_WARN,
                "missing Cargo.lock (reproducible builds may be impacted)",
            )
        )
    else:
        results.append(CheckResult("cargo_lock", CHECK_PASS, "Cargo.lock present"))

    ok, msg = run_cmd(["rustc", "--version"])
    if ok:
        results.append(CheckResult("rustc", CHECK_PASS, f"rustc: {msg}"))
    else:
        results.append(
            CheckResult("rustc", CHECK_FAIL, f"rustc --version failed: {msg}")
        )

    ok, msg = run_cmd(["cargo", "--version"])
    if ok:
        results.append(CheckResult("cargo", CHECK_PASS, f"cargo: {msg}"))
    else:
        results.append(
            CheckResult("cargo", CHECK_FAIL, f"cargo --version failed: {msg}")
        )

    ay_ok, ay_msg, ay_details = check_ay_updates()
    if ay_details.get("pin_status") != "valid":
        results.append(
            CheckResult(
                "ay_path",
                CHECK_FAIL,
                f"committed AY Git graph is invalid: {ay_msg}",
                ay_details,
            )
        )
    else:
        results.append(
            CheckResult(
                "ay_path",
                CHECK_PASS,
                "committed AY Git graph is coherent "
                f"({ay_details.get('ay_manifest_pin_count')} manifest pins, "
                f"{ay_details.get('ay_lock_source_count')} lock sources)",
                ay_details,
            )
        )

    if ay_ok:
        results.append(
            CheckResult("ay_updates", CHECK_PASS, f"AY: {ay_msg}", ay_details)
        )
    else:
        results.append(
            CheckResult("ay_updates", CHECK_FAIL, f"AY check failed: {ay_msg}", ay_details)
        )

    gc_ok, gc_msg = check_worktree_gc_logs()
    if gc_ok:
        results.append(CheckResult("git_gc_logs", CHECK_PASS, f"git gc logs: {gc_msg}"))
    else:
        results.append(CheckResult("git_gc_logs", CHECK_FAIL, f"git gc logs: {gc_msg}"))

    return results


def _summary_status(results: list[CheckResult]) -> str:
    if any(result.status == CHECK_FAIL for result in results):
        return CHECK_FAIL
    if any(result.status == CHECK_WARN for result in results):
        return CHECK_WARN
    return CHECK_PASS


def utc_now() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def build_manifest(
    results: list[CheckResult],
    *,
    generated_at: str | None = None,
) -> dict[str, object]:
    checks: dict[str, dict[str, object]] = {}
    for result in results:
        check: dict[str, object] = {
            "status": result.status,
            "message": result.message,
        }
        if result.details:
            check.update(result.details)
        checks[result.name] = check

    return {
        "schema_version": "1.0",
        "generated_at": generated_at or utc_now(),
        "git_commit": _get_git_commit(),
        "project": _get_project_name(),
        "summary": {
            "status": _summary_status(results),
            "passed": sum(result.status == CHECK_PASS for result in results),
            "warnings": sum(result.status == CHECK_WARN for result in results),
            "errors": sum(result.status == CHECK_FAIL for result in results),
            "skipped": sum(result.status == CHECK_SKIP for result in results),
        },
        "checks": checks,
    }


def _write_json_manifest(path: Path, manifest: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _print_human_output(results: list[CheckResult]) -> None:
    for result in results:
        if result.status == CHECK_PASS:
            print(f"INFO {result.message}")

    for result in results:
        if result.status == CHECK_WARN:
            print(f"WARN {result.message}")

    for result in results:
        if result.status == CHECK_FAIL:
            print(f"FAIL {result.message}")


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="System health check - verify the clean system is connected."
    )
    parser.add_argument(
        "--json-output",
        metavar="PATH",
        type=Path,
        help="write JSON manifest to PATH while still printing human output",
    )
    parser.add_argument(
        "--generated-at",
        help="override generated_at in JSON evidence for reproducible output",
    )
    parser.add_argument(
        "--deterministic",
        action="store_true",
        help="use a stable generated_at value when --generated-at is omitted",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    results = run_checks()
    _print_human_output(results)

    if args.json_output:
        generated_at = args.generated_at
        if generated_at is None and args.deterministic:
            generated_at = DETERMINISTIC_GENERATED_AT
        manifest = build_manifest(results, generated_at=generated_at)
        _write_json_manifest(args.json_output, manifest)
        print(f"INFO JSON manifest written to: {args.json_output}")

    if any(result.status == CHECK_FAIL for result in results):
        return 1

    print("OK system health check passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
