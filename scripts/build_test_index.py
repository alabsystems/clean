#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Build and query a cached workspace test index.

The index scans workspace crates for Rust unit and integration tests and
stores copy-pasteable cargo invocations in:

    .cleancache/test_index.json

Usage:
    python3 scripts/build_test_index.py build
    python3 scripts/build_test_index.py query <keyword-or-name>
    python3 scripts/build_test_index.py stats

Examples:
    python3 scripts/build_test_index.py build
    python3 scripts/build_test_index.py query linarith
    python3 scripts/build_test_index.py query parser_roundtrip --workspace-root /tmp/workspace
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from collections.abc import Sequence
from datetime import datetime, timezone
from pathlib import Path

import tomllib

INDEX_VERSION = 3
DEFAULT_CACHE_RELATIVE = Path(".cleancache") / "test_index.json"
DETERMINISTIC_GENERATED_AT = "1970-01-01T00:00:00Z"


def find_workspace_root(start: Path | None = None) -> Path:
    """Find the workspace root containing Cargo.toml with a [workspace] table."""
    search_root = start or Path.cwd()
    if search_root.is_file():
        search_root = search_root.parent

    for candidate in [search_root, *search_root.parents]:
        cargo_toml = candidate / "Cargo.toml"
        if cargo_toml.exists():
            try:
                data = tomllib.loads(cargo_toml.read_text(encoding="utf-8"))
            except (OSError, tomllib.TOMLDecodeError):
                continue
            if "workspace" in data:
                return candidate

    script_root = Path(__file__).resolve().parent.parent
    cargo_toml = script_root / "Cargo.toml"
    if cargo_toml.exists():
        try:
            data = tomllib.loads(cargo_toml.read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError):
            data = {}
        if "workspace" in data:
            return script_root

    raise SystemExit("ERROR: Could not find workspace root")


def cache_path_for(workspace_root: Path) -> Path:
    return workspace_root / DEFAULT_CACHE_RELATIVE


def load_toml(path: Path) -> dict:
    return tomllib.loads(path.read_text(encoding="utf-8"))


def parse_workspace_members(workspace_root: Path) -> list[dict]:
    """Return workspace crate metadata from the root Cargo.toml."""
    workspace_manifest = workspace_root / "Cargo.toml"
    data = load_toml(workspace_manifest)
    workspace = data.get("workspace", {})
    members = workspace.get("members", [])

    crates: list[dict] = []
    seen: set[str] = set()
    for member in members:
        if member in seen:
            continue
        seen.add(member)
        member_dir = workspace_root / member
        member_manifest = member_dir / "Cargo.toml"
        if not member_manifest.exists():
            continue
        try:
            member_data = load_toml(member_manifest)
        except (OSError, tomllib.TOMLDecodeError):
            continue
        package = member_data.get("package", {}).get("name")
        if not package:
            continue
        crates.append(
            {
                "package": package,
                "path": str(member_dir),
                "relative_path": member,
            }
        )

    crates.sort(key=lambda item: (item["package"], item["relative_path"]))
    return crates


def compute_module_path_from_file(file_path: Path, crate_src_dir: Path) -> list[str]:
    """Compute the Rust module path segments for a source file."""
    try:
        rel = file_path.relative_to(crate_src_dir)
    except ValueError:
        return []

    parts = list(rel.parts)
    if not parts:
        return []

    last = parts[-1]
    if not last.endswith(".rs"):
        return []

    stem = last[:-3]
    if stem in {"lib", "main"}:
        return []
    if stem == "mod":
        return list(parts[:-1])

    parts[-1] = stem
    return parts


def _find_comment_start(line: str) -> int:
    """Find the start of a line comment while skipping string literals."""
    in_string = False
    i = 0
    while i < len(line):
        c = line[i]
        if in_string:
            if c == "\\" and i + 1 < len(line):
                i += 2
                continue
            if c == '"':
                in_string = False
        else:
            if c == '"':
                in_string = True
            elif c == "/" and i + 1 < len(line) and line[i + 1] == "/":
                return i
        i += 1
    return -1


def parse_test_functions(file_path: Path, text: str | None = None) -> list[dict]:
    """Extract #[test] and #[tokio::test] functions from a Rust source file."""
    if text is None:
        try:
            text = file_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            return []

    if "#[test]" not in text and "#[tokio::test]" not in text:
        return []

    lines = text.splitlines()
    tests: list[dict] = []
    mod_stack: list[tuple[str, int]] = []
    brace_depth = 0
    pending_test = False

    test_attr_re = re.compile(r"^\s*#\[(?:test|tokio::test)\]")
    fn_re = re.compile(r"^\s*(?:pub(?:\(crate\))?\s+)?(?:async\s+)?fn\s+(\w+)")
    mod_re = re.compile(r"^\s*(?:pub(?:\(crate\))?\s+)?mod\s+(\w+)\s*\{")

    for line_no, line in enumerate(lines, start=1):
        comment_pos = _find_comment_start(line)
        code_part = line[:comment_pos] if comment_pos >= 0 else line
        opens = code_part.count("{")
        closes = code_part.count("}")
        new_depth = brace_depth + opens - closes

        if test_attr_re.search(line):
            pending_test = True
        elif pending_test:
            fn_match = fn_re.match(line)
            if fn_match:
                fn_name = fn_match.group(1)
                tests.append(
                    {
                        "name": fn_name,
                        "line": line_no,
                        "module_segments": [segment for segment, _ in mod_stack],
                    }
                )
                pending_test = False
            else:
                stripped = line.strip()
                if (
                    stripped
                    and not stripped.startswith("#")
                    and not stripped.startswith("//")
                ):
                    pending_test = False

        mod_match = mod_re.match(line)
        if mod_match:
            mod_stack.append((mod_match.group(1), brace_depth))

        brace_depth = new_depth
        while mod_stack and brace_depth <= mod_stack[-1][1]:
            mod_stack.pop()

    return tests


def build_cargo_cmd(
    package: str,
    cargo_target_flag: str | None,
    cargo_target_name: str | None,
    module_path: str,
    test_name: str,
) -> str:
    """Build a copy-pasteable cargo test invocation."""
    filter_path = f"{module_path}::{test_name}" if module_path else test_name
    base = f"cargo test --locked --message-format=short -j 1 -p {package}"
    if cargo_target_flag is None:
        return f"{base} -- {filter_path}"
    if cargo_target_name is None:
        return f"{base} {cargo_target_flag} -- {filter_path}"
    return f"{base} {cargo_target_flag} {cargo_target_name} -- {filter_path}"


def resolve_binary_target(
    file_path: Path, src_dir: Path
) -> tuple[str, Path | None] | None:
    """Return the cargo binary target name and module root for a bin source file."""
    bin_dir = src_dir / "bin"
    try:
        rel_to_bin = file_path.relative_to(bin_dir)
    except ValueError:
        return None

    parts = rel_to_bin.parts
    if not parts or not parts[-1].endswith(".rs"):
        return None

    target_name = parts[0][:-3] if len(parts) == 1 else parts[0]
    if len(parts) == 1:
        return target_name, None
    return target_name, bin_dir / target_name


def scan_crate(crate_info: dict, workspace_root: Path) -> list[dict]:
    """Scan a single workspace crate for test functions."""
    crate_path = Path(crate_info["path"])
    package = crate_info["package"]
    results: list[dict] = []

    src_dir = crate_path / "src"
    if src_dir.is_dir():
        for rs_file in sorted(src_dir.rglob("*.rs")):
            try:
                text = rs_file.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            if "#[test]" not in text and "#[tokio::test]" not in text:
                continue

            test_fns = parse_test_functions(rs_file, text=text)
            if not test_fns:
                continue

            rel_file = rs_file.relative_to(workspace_root)
            cargo_target_flag = "--lib"
            cargo_target_name: str | None = None
            module_root: Path | None = src_dir

            if rs_file == src_dir / "main.rs":
                cargo_target_flag = "--bin"
                cargo_target_name = package
                module_root = None
            else:
                binary_target = resolve_binary_target(rs_file, src_dir)
                if binary_target is not None:
                    cargo_target_flag = "--bin"
                    cargo_target_name, module_root = binary_target

            file_mod_segments = (
                []
                if module_root is None
                else compute_module_path_from_file(rs_file, module_root)
            )
            crate_module = package.replace("-", "_")

            for test_fn in test_fns:
                full_segments = file_mod_segments + test_fn["module_segments"]
                module_path = "::".join(full_segments) if full_segments else ""
                if cargo_target_flag == "--lib":
                    full_module = (
                        f"{crate_module}::{module_path}"
                        if module_path
                        else crate_module
                    )
                elif cargo_target_name is not None:
                    full_module = (
                        f"{cargo_target_name}::{module_path}"
                        if module_path
                        else cargo_target_name
                    )
                else:
                    full_module = module_path

                results.append(
                    {
                        "name": test_fn["name"],
                        "module": full_module,
                        "file": str(rel_file),
                        "line": test_fn["line"],
                        "cargo_cmd": build_cargo_cmd(
                            package=package,
                            cargo_target_flag=cargo_target_flag,
                            cargo_target_name=cargo_target_name,
                            module_path=module_path,
                            test_name=test_fn["name"],
                        ),
                        "package": package,
                        "kind": "bin" if cargo_target_flag == "--bin" else "lib",
                    }
                )

    tests_dir = crate_path / "tests"
    if tests_dir.is_dir():
        for rs_file in sorted(tests_dir.rglob("*.rs")):
            try:
                text = rs_file.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            if "#[test]" not in text and "#[tokio::test]" not in text:
                continue

            test_fns = parse_test_functions(rs_file, text=text)
            if not test_fns:
                continue

            rel_file = rs_file.relative_to(workspace_root)
            try:
                rel_to_tests = rs_file.relative_to(tests_dir)
            except ValueError:
                continue

            parts = rel_to_tests.parts
            if not parts:
                continue

            if len(parts) == 1:
                integ_name = rs_file.stem
                sub_segments: list[str] = []
            else:
                target_name = parts[0]
                directory_harness = tests_dir / target_name / "main.rs"
                flat_harness = tests_dir / f"{target_name}.rs"
                if directory_harness.exists():
                    integ_name = target_name
                    sub_segments = list(parts[1:])
                    if sub_segments == ["main.rs"]:
                        sub_segments = []
                elif flat_harness.exists():
                    integ_name = target_name
                    sub_segments = list(parts[1:])
                else:
                    continue
                if sub_segments:
                    last = sub_segments[-1]
                    if last.endswith(".rs"):
                        sub_segments[-1] = last[:-3]
                    if sub_segments and sub_segments[-1] == "mod":
                        sub_segments = sub_segments[:-1]

            for test_fn in test_fns:
                full_segments = sub_segments + test_fn["module_segments"]
                module_path = "::".join(full_segments) if full_segments else ""

                results.append(
                    {
                        "name": test_fn["name"],
                        "module": f"{integ_name}::{module_path}"
                        if module_path
                        else integ_name,
                        "file": str(rel_file),
                        "line": test_fn["line"],
                        "cargo_cmd": build_cargo_cmd(
                            package=package,
                            cargo_target_flag="--test",
                            cargo_target_name=integ_name,
                            module_path=module_path,
                            test_name=test_fn["name"],
                        ),
                        "package": package,
                        "kind": "integration",
                    }
                )

    return results


def build_index(workspace_root: Path, *, generated_at: str | None = None) -> dict:
    """Build the complete test index for the workspace."""
    crates = parse_workspace_members(workspace_root)
    all_tests: list[dict] = []

    for crate_info in crates:
        all_tests.extend(scan_crate(crate_info, workspace_root))

    all_tests.sort(
        key=lambda item: (item["package"], item["module"], item["name"], item["file"])
    )
    return {
        "schema_version": INDEX_VERSION,
        "generated_at": generated_at
        or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "workspace_root": str(workspace_root),
        "total_tests": len(all_tests),
        "total_crates": len(crates),
        "tests": all_tests,
    }


def write_index(index: dict, cache_path: Path) -> None:
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = cache_path.with_suffix(cache_path.suffix + ".tmp")
    tmp_path.write_text(
        json.dumps(index, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    tmp_path.replace(cache_path)


def load_index(cache_path: Path) -> dict | None:
    if not cache_path.exists():
        return None
    try:
        index = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if index.get("schema_version") != INDEX_VERSION:
        return None
    if not isinstance(index.get("tests"), list):
        return None
    return index


def ensure_index(
    workspace_root: Path,
    cache_path: Path,
    *,
    rebuild: bool = False,
    generated_at: str | None = None,
) -> dict:
    if not rebuild:
        cached = load_index(cache_path)
        if cached is not None:
            return cached

    index = build_index(workspace_root, generated_at=generated_at)
    write_index(index, cache_path)
    return index


def tokenize_query(pattern: str) -> list[str]:
    tokens = [token for token in re.split(r"[\s:/,]+", pattern.lower()) if token]
    return tokens or [pattern.lower()]


def score_test(test: dict, pattern: str) -> tuple[int, int, int, str]:
    """Rank candidates by how well they match a query."""
    needle = pattern.lower()
    tokens = tokenize_query(pattern)
    haystack = " ".join(
        [
            test["name"],
            test["module"],
            test["file"],
            test["package"],
            test["cargo_cmd"],
        ]
    ).lower()

    score = 0
    if test["name"].lower() == needle:
        score += 10_000
    if test["module"].lower() == needle:
        score += 8_000
    if needle in test["name"].lower():
        score += 4_000
    if needle in test["module"].lower():
        score += 3_000
    if needle in test["file"].lower():
        score += 1_500
    if needle in test["package"].lower():
        score += 1_200

    for token in tokens:
        if token in haystack:
            score += 250
            if token in test["name"].lower():
                score += 250
            if token in test["module"].lower():
                score += 150

    return (score, -len(test["module"]), -len(test["name"]), test["cargo_cmd"])


def query_tests(index: dict, pattern: str) -> list[dict]:
    scored = []
    for test in index["tests"]:
        score = score_test(test, pattern)
        if score[0] > 0:
            scored.append((score, test))

    scored.sort(key=lambda item: item[0], reverse=True)
    return [test for _, test in scored]


def print_stats(index: dict) -> None:
    tests = index["tests"]
    by_package: dict[str, int] = {}
    for test in tests:
        by_package[test["package"]] = by_package.get(test["package"], 0) + 1

    lib_count = sum(1 for test in tests if test["kind"] == "lib")
    bin_count = sum(1 for test in tests if test["kind"] == "bin")
    integ_count = sum(1 for test in tests if test["kind"] == "integration")
    unique_files = len({test["file"] for test in tests})

    print("Test Index Statistics")
    print("=" * 60)
    print(f"Generated:      {index['generated_at']}")
    print(f"Workspace root: {index['workspace_root']}")
    print(f"Total tests:    {len(tests):>8}")
    print(f"  Lib tests:    {lib_count:>8}")
    print(f"  Bin tests:    {bin_count:>8}")
    print(f"  Integ tests:  {integ_count:>8}")
    print(f"Unique files:   {unique_files:>8}")
    print(f"Crates scanned: {index['total_crates']:>8}")
    print()
    print("Tests by crate:")
    print("-" * 60)
    for package in sorted(by_package):
        count = by_package[package]
        bar = "#" * min(count // 10, 40)
        print(f"  {package:<30} {count:>6}  {bar}")


def print_query_result(index: dict, pattern: str) -> int:
    results = query_tests(index, pattern)
    if not results:
        print(f"No tests matching '{pattern}'", file=sys.stderr)
        return 1

    best = results[0]
    print(best["cargo_cmd"])
    return 0


def resolve_generated_at(args: argparse.Namespace) -> str | None:
    generated_at = getattr(args, "generated_at", None)
    if generated_at is None and getattr(args, "deterministic", False):
        generated_at = DETERMINISTIC_GENERATED_AT
    return generated_at


def build_command(args: argparse.Namespace, workspace_root: Path) -> int:
    cache_path = cache_path_for(workspace_root)
    start = time.monotonic()
    index = ensure_index(
        workspace_root,
        cache_path,
        rebuild=True,
        generated_at=resolve_generated_at(args),
    )
    elapsed = time.monotonic() - start
    print(f"Scanning workspace at {workspace_root}")
    print(
        f"Indexed {index['total_tests']} tests from {index['total_crates']} crates in {elapsed:.2f}s"
    )
    print(f"Written to {cache_path}")
    return 0


def query_command(args: argparse.Namespace, workspace_root: Path) -> int:
    cache_path = cache_path_for(workspace_root)
    index = ensure_index(
        workspace_root,
        cache_path,
        rebuild=args.refresh,
        generated_at=resolve_generated_at(args),
    )
    return print_query_result(index, args.pattern)


def stats_command(args: argparse.Namespace, workspace_root: Path) -> int:
    cache_path = cache_path_for(workspace_root)
    index = ensure_index(
        workspace_root,
        cache_path,
        rebuild=args.refresh,
        generated_at=resolve_generated_at(args),
    )
    print_stats(index)
    return 0


def build_parser() -> argparse.ArgumentParser:
    common_parser = argparse.ArgumentParser(add_help=False)
    common_parser.add_argument(
        "--workspace-root",
        metavar="PATH",
        help="Workspace root or Cargo.toml directory (defaults to auto-detect)",
    )
    common_parser.add_argument(
        "--generated-at",
        help="override generated_at for reproducible index evidence",
    )
    common_parser.add_argument(
        "--deterministic",
        action="store_true",
        help="use a stable generated_at value when --generated-at is omitted",
    )

    parser = argparse.ArgumentParser(
        description="Build and query a cached workspace test index.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        parents=[common_parser],
        epilog=(
            "Commands:\n"
            "  build   Rebuild .cleancache/test_index.json\n"
            "  query   Return a copy-pasteable cargo test command\n"
            "  stats   Show index coverage summary\n"
        ),
    )

    subparsers = parser.add_subparsers(dest="command")

    build_parser = subparsers.add_parser(
        "build",
        help="Rebuild the cached test index",
        parents=[common_parser],
    )
    build_parser.set_defaults(command="build")

    query_parser = subparsers.add_parser(
        "query",
        help="Query the cached index",
        parents=[common_parser],
    )
    query_parser.add_argument("pattern", help="Keyword or test name to search for")
    query_parser.add_argument(
        "--refresh",
        action="store_true",
        help="Rebuild the cache before querying",
    )
    query_parser.set_defaults(command="query")

    stats_parser = subparsers.add_parser(
        "stats",
        help="Show cached index statistics",
        parents=[common_parser],
    )
    stats_parser.add_argument(
        "--refresh",
        action="store_true",
        help="Rebuild the cache before showing stats",
    )
    stats_parser.set_defaults(command="stats")

    return parser


def _resolve_workspace_root(raw_root: str | None) -> Path:
    if raw_root:
        candidate = Path(raw_root).expanduser().resolve()
        if candidate.is_file():
            candidate = candidate.parent
        cargo_toml = candidate / "Cargo.toml"
        if cargo_toml.exists():
            try:
                data = load_toml(cargo_toml)
            except (OSError, tomllib.TOMLDecodeError) as exc:
                raise SystemExit(f"ERROR: invalid Cargo.toml at {candidate}") from exc
            if "workspace" in data:
                return candidate
        raise SystemExit(f"ERROR: {candidate} is not a Cargo workspace root")

    return find_workspace_root()


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)

    if not args.command:
        args.command = "build"

    workspace_root = _resolve_workspace_root(getattr(args, "workspace_root", None))

    if args.command == "build":
        return build_command(args, workspace_root)
    if args.command == "query":
        return query_command(args, workspace_root)
    if args.command == "stats":
        return stats_command(args, workspace_root)

    parser.error(f"unknown command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
