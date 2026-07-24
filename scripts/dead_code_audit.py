#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""
Cross-crate dead code detection for pub API surface hygiene.

Scans the clean workspace and reports `pub` items that have no cross-crate
references. The tool is intentionally heuristic: it is designed to surface
review candidates, not to prove deadness.

Usage:
    python3 scripts/dead_code_audit.py                    # Full report
    python3 scripts/dead_code_audit.py --json             # JSON output
    python3 scripts/dead_code_audit.py --summary          # Summary only
    python3 scripts/dead_code_audit.py --crate clean-kernel
    python3 scripts/dead_code_audit.py --ignore-file data/dead_code_ignore.toml
    python3 scripts/dead_code_audit.py --fail-on-candidates
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import re
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Optional

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python 3.10 fallback
    tomllib = None  # type: ignore[assignment]


IDENTIFIER_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\b")
PUB_ITEM_RE = re.compile(
    r"^\s*pub\s+"
    r"(?!use\b)"
    r"(?!mod\b)"
    r"(?!\()"
    r"(?:async\s+|unsafe\s+|const\s+)*"
    r"(fn|struct|enum|trait|type|const|static)\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\b",
)
TRAIT_BLOCK_RE = re.compile(r"^\s*(?:pub\s+)?(?:unsafe\s+)?trait\b")
IMPL_BLOCK_RE = re.compile(r"^\s*(?:unsafe\s+)?impl\b")

TRAIT_METHOD_NAMES: frozenset[str] = frozenset({
    "new",
    "default",
    "from",
    "into",
    "fmt",
    "clone",
    "clone_from",
    "eq",
    "ne",
    "hash",
    "cmp",
    "partial_cmp",
    "drop",
    "deref",
    "deref_mut",
    "index",
    "index_mut",
    "next",
    "size_hint",
    "try_from",
    "try_into",
    "as_ref",
    "as_mut",
    "borrow",
    "borrow_mut",
    "display",
    "from_str",
    "to_string",
    "to_owned",
    "into_iter",
    "from_iter",
    "extend",
    "write_str",
    "write_fmt",
    "poll",
    "resume",
    "add",
    "sub",
    "mul",
    "div",
    "rem",
    "neg",
    "not",
    "shl",
    "shr",
    "bitand",
    "bitor",
    "bitxor",
    "add_assign",
    "sub_assign",
    "mul_assign",
    "div_assign",
})

TOO_COMMON_NAMES: frozenset[str] = frozenset({
    "id",
    "ty",
    "e",
    "n",
    "s",
    "t",
    "x",
    "a",
    "b",
    "i",
    "v",
    "ok",
    "err",
    "is",
    "of",
    "it",
    "to",
    "as",
    "in",
    "on",
    "at",
    "get",
    "set",
    "run",
    "put",
    "has",
    "map",
    "len",
    "name",
    "kind",
    "data",
    "info",
    "key",
    "val",
    "value",
    "self_",
    "Self_",
})


@dataclass(frozen=True)
class IgnoreRule:
    crate: Optional[str] = None
    kind: Optional[str] = None
    name: Optional[str] = None
    file: Optional[str] = None
    line: Optional[int] = None
    path_glob: Optional[str] = None

    def matches(self, item: "PubItem") -> bool:
        if self.crate is not None and item.crate_name != self.crate:
            return False
        if self.kind is not None and item.kind != self.kind:
            return False
        if self.name is not None and item.name != self.name:
            return False
        if self.file is not None and item.file_path != self.file:
            return False
        if self.line is not None and item.line_number != self.line:
            return False
        if self.path_glob is not None and not fnmatch.fnmatch(item.file_path, self.path_glob):
            return False
        return True


@dataclass
class ReferenceSite:
    crate_name: str
    file_path: str
    line_number: int
    line_text: str = ""


@dataclass
class PubItem:
    crate_name: str
    file_path: str
    line_number: int
    kind: str
    name: str
    cross_crate_crates: int = 0
    cross_crate_files: int = 0
    cross_crate_sites: int = 0
    reference_crates: list[str] = field(default_factory=list)
    references: list[ReferenceSite] = field(default_factory=list)


@dataclass
class WorkspaceFile:
    crate_name: str
    file_path: str
    content: str
    lines: list[str]
    search_lines: list[str]
    identifiers: frozenset[str]


@dataclass
class ScanResult:
    repo_root: Path
    crates_scanned: int
    files_scanned: int
    ignored_items: list[PubItem]
    all_items: list[PubItem]
    dead_items: list[PubItem]


def _mask_char(ch: str) -> str:
    return "\n" if ch == "\n" else " "


def _match_raw_string_start(content: str, start: int) -> tuple[int, int] | None:
    idx = start
    if content.startswith(("br", "rb"), idx):
        idx += 2
    elif content.startswith("r", idx):
        idx += 1
    else:
        return None

    hash_count = 0
    while idx < len(content) and content[idx] == "#":
        idx += 1
        hash_count += 1

    if idx < len(content) and content[idx] == '"':
        return idx + 1 - start, hash_count
    return None


def strip_rust_non_code(content: str) -> str:
    """Mask comments and string literals while preserving line numbers."""

    out: list[str] = []
    block_comment_depth = 0
    in_string = False
    raw_string_hashes: int | None = None
    i = 0

    while i < len(content):
        ch = content[i]

        if block_comment_depth > 0:
            if content.startswith("/*", i):
                block_comment_depth += 1
                out.extend((" ", " "))
                i += 2
                continue
            if content.startswith("*/", i):
                block_comment_depth -= 1
                out.extend((" ", " "))
                i += 2
                continue
            out.append(_mask_char(ch))
            i += 1
            continue

        if in_string:
            out.append(_mask_char(ch))
            i += 1
            if ch == "\\" and i < len(content):
                out.append(_mask_char(content[i]))
                i += 1
            elif ch == '"':
                in_string = False
            continue

        if raw_string_hashes is not None:
            if ch == '"' and content.startswith("#" * raw_string_hashes, i + 1):
                out.append(" ")
                out.extend(" " for _ in range(raw_string_hashes))
                i += 1 + raw_string_hashes
                raw_string_hashes = None
                continue
            out.append(_mask_char(ch))
            i += 1
            continue

        if content.startswith("//", i):
            out.extend((" ", " "))
            i += 2
            while i < len(content) and content[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if content.startswith("/*", i):
            block_comment_depth = 1
            out.extend((" ", " "))
            i += 2
            continue

        raw_start = _match_raw_string_start(content, i)
        if raw_start is not None:
            prefix_len, hash_count = raw_start
            out.extend(" " for _ in range(prefix_len))
            i += prefix_len
            raw_string_hashes = hash_count
            continue

        if content.startswith(('b"', 'c"'), i):
            out.extend((" ", " "))
            i += 2
            in_string = True
            continue

        if ch == '"':
            out.append(" ")
            i += 1
            in_string = True
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def find_crates(crates_dir: Path) -> list[tuple[str, Path]]:
    crates: list[tuple[str, Path]] = []
    for d in sorted(crates_dir.iterdir()):
        if d.is_dir() and (d / "Cargo.toml").exists():
            crates.append((d.name, d))
    return crates


def find_repo_root(start: Path) -> Path:
    candidate = start.resolve()
    while candidate != candidate.parent:
        cargo = candidate / "Cargo.toml"
        if cargo.exists():
            try:
                if "[workspace]" in cargo.read_text(encoding="utf-8", errors="replace"):
                    return candidate
            except OSError:
                pass
        candidate = candidate.parent
    return start.resolve()


def classify_block_header(line: str) -> str | None:
    stripped = line.strip()
    if TRAIT_BLOCK_RE.match(stripped):
        return "trait"
    if IMPL_BLOCK_RE.match(stripped):
        header = stripped.split("{", 1)[0]
        if " for " in header:
            return "trait_impl"
        return "inherent_impl"
    return None


def is_test_context(lines: list[str], line_idx: int) -> bool:
    cfg_idx: Optional[int] = None
    for i in range(line_idx, -1, -1):
        if lines[i].strip() == "#[cfg(test)]":
            cfg_idx = i
            break
    if cfg_idx is None:
        return False

    mod_idx: Optional[int] = None
    for j in range(cfg_idx + 1, min(cfg_idx + 6, len(lines))):
        if lines[j].strip().startswith("mod "):
            mod_idx = j
            break
    if mod_idx is None or mod_idx > line_idx:
        return False

    brace_depth = 0
    for k in range(mod_idx, line_idx + 1):
        brace_depth += lines[k].count("{") - lines[k].count("}")
    return brace_depth > 0


def has_cfg_test_attribute(lines: list[str], line_idx: int) -> bool:
    attr_idx = line_idx - 1
    while attr_idx >= 0:
        stripped = lines[attr_idx].strip()
        if not stripped:
            attr_idx -= 1
            continue
        if stripped.startswith("#["):
            if stripped == "#[cfg(test)]":
                return True
            attr_idx -= 1
            continue
        break
    return False


def find_workspace_rust_files(
    crates: list[tuple[str, Path]],
    repo_root: Path,
) -> list[WorkspaceFile]:
    files: list[WorkspaceFile] = []
    for crate_name, crate_dir in crates:
        src_dir = crate_dir / "src"
        if not src_dir.exists():
            continue
        for rs_file in sorted(src_dir.rglob("*.rs")):
            rel_path = rs_file.relative_to(repo_root)
            rel_str = str(rel_path)
            if "/bin/" in rel_str or rel_str.endswith("/main.rs"):
                continue
            if "_test.rs" in rs_file.name or "/tests/" in rel_str:
                continue
            try:
                content = rs_file.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            search_content = strip_rust_non_code(content)
            files.append(
                WorkspaceFile(
                    crate_name=crate_name,
                    file_path=rel_str,
                    content=content,
                    lines=content.splitlines(),
                    search_lines=search_content.splitlines(),
                    identifiers=frozenset(IDENTIFIER_RE.findall(search_content)),
                )
            )
    return files


def collect_pub_items_from_file(
    file: WorkspaceFile,
) -> list[PubItem]:
    items: list[PubItem] = []
    block_depth_thresholds: list[tuple[str, int]] = []
    brace_depth = 0
    pending_block_kind: str | None = None

    for line_number, line in enumerate(file.lines, start=1):
        header_kind = classify_block_header(line)
        open_count = line.count("{")
        close_count = line.count("}")
        line_enters_block_kind: str | None = None

        if header_kind is not None:
            if open_count > close_count:
                line_enters_block_kind = header_kind
            elif open_count > 0:
                line_enters_block_kind = header_kind
            else:
                pending_block_kind = header_kind

        if pending_block_kind is not None and open_count > 0:
            line_enters_block_kind = pending_block_kind
            pending_block_kind = None

        inside_trait_surface = (
            line_enters_block_kind in {"trait", "trait_impl"}
            or any(
                kind in {"trait", "trait_impl"} and brace_depth >= threshold
                for kind, threshold in block_depth_thresholds
            )
        )

        match = PUB_ITEM_RE.match(line)
        if match and not inside_trait_surface:
            kind = match.group(1)
            name = match.group(2)

            if has_cfg_test_attribute(file.lines, line_number - 1):
                pass
            elif is_test_context(file.lines, line_number - 1):
                pass
            elif kind == "fn" and name in TRAIT_METHOD_NAMES:
                pass
            elif name in TOO_COMMON_NAMES:
                pass
            else:
                items.append(
                    PubItem(
                        crate_name=file.crate_name,
                        file_path=file.file_path,
                        line_number=line_number,
                        kind=kind,
                        name=name,
                    )
                )

        brace_depth += open_count - close_count

        if line_enters_block_kind is not None and open_count > close_count:
            block_depth_thresholds.append((line_enters_block_kind, brace_depth))

        while block_depth_thresholds and brace_depth < block_depth_thresholds[-1][1]:
            block_depth_thresholds.pop()

    return items


def load_ignore_rules(ignore_file: Optional[Path]) -> list[IgnoreRule]:
    if ignore_file is None:
        return []
    if not ignore_file.exists():
        return []

    raw: object
    if ignore_file.suffix.lower() == ".json":
        raw = json.loads(ignore_file.read_text(encoding="utf-8"))
    else:
        if tomllib is None:
            raise RuntimeError("tomllib is unavailable; cannot read TOML ignore file")
        raw = tomllib.loads(ignore_file.read_text(encoding="utf-8"))

    entries: object
    if isinstance(raw, dict):
        entries = raw.get("ignore", raw.get("rules", []))
    else:
        entries = raw

    if not isinstance(entries, list):
        raise ValueError(f"ignore file {ignore_file} must contain a list of rules")

    rules: list[IgnoreRule] = []
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        line_value = entry.get("line")
        if isinstance(line_value, str) and line_value.isdigit():
            line_value = int(line_value)
        if line_value is not None and not isinstance(line_value, int):
            raise ValueError(f"ignore rule line must be an integer: {entry!r}")
        rules.append(
            IgnoreRule(
                crate=entry.get("crate"),
                kind=entry.get("kind"),
                name=entry.get("name"),
                file=entry.get("file"),
                line=line_value,
                path_glob=entry.get("path_glob") or entry.get("glob"),
            )
        )
    return rules


def should_ignore(item: PubItem, ignore_rules: Iterable[IgnoreRule]) -> bool:
    return any(rule.matches(item) for rule in ignore_rules)


def collect_reference_sites(
    item: PubItem,
    files: list[WorkspaceFile],
    max_sites: int = 5,
) -> list[ReferenceSite]:
    pattern = re.compile(rf"\b{re.escape(item.name)}\b")
    sites: list[ReferenceSite] = []
    seen_files: set[str] = set()
    seen_crates: set[str] = set()
    site_count = 0

    for file in files:
        if file.crate_name == item.crate_name:
            continue
        if item.name not in file.identifiers:
            continue

        file_seen = False
        for line_number, search_line in enumerate(file.search_lines, start=1):
            if not pattern.search(search_line):
                continue
            line = file.lines[line_number - 1]
            stripped = line.lstrip()
            site_count += 1
            seen_files.add(file.file_path)
            seen_crates.add(file.crate_name)
            if not file_seen and len(sites) < max_sites:
                sites.append(
                    ReferenceSite(
                        crate_name=file.crate_name,
                        file_path=file.file_path,
                        line_number=line_number,
                        line_text=stripped[:160],
                    )
                )
                file_seen = True

    item.cross_crate_sites = site_count
    item.cross_crate_files = len(seen_files)
    item.cross_crate_crates = len(seen_crates)
    item.reference_crates = sorted(seen_crates)
    item.references = sites
    return sites


def scan_workspace(
    repo_root: Path,
    crate_filter: Optional[str] = None,
    ignore_rules: Optional[list[IgnoreRule]] = None,
    verbose: bool = False,
) -> ScanResult:
    crates_dir = repo_root / "crates"
    if not crates_dir.exists():
        raise FileNotFoundError(f"{crates_dir} not found")

    crates = find_crates(crates_dir)
    if not crates:
        raise FileNotFoundError("no crates found")

    target_crates = crates
    if crate_filter is not None:
        target_crates = [(n, d) for n, d in crates if n == crate_filter]
        if not target_crates:
            raise FileNotFoundError(f"crate '{crate_filter}' not found")

    t0 = time.monotonic()
    files = find_workspace_rust_files(crates, repo_root)
    if verbose:
        print(f"scanned {len(files)} rust files across {len(crates)} crates", file=sys.stderr)

    target_names = {name for name, _ in target_crates}
    all_items: list[PubItem] = []
    for file in files:
        if file.crate_name not in target_names:
            continue
        all_items.extend(collect_pub_items_from_file(file))

    ignore_rules = ignore_rules or []
    ignored_items: list[PubItem] = []
    kept_items: list[PubItem] = []
    for item in all_items:
        if should_ignore(item, ignore_rules):
            ignored_items.append(item)
        else:
            kept_items.append(item)

    for item in kept_items:
        collect_reference_sites(item, files)

    dead_items = [item for item in kept_items if item.cross_crate_crates == 0]
    dead_items.sort(key=lambda it: (it.crate_name, it.file_path, it.line_number))

    elapsed = time.monotonic() - t0
    if verbose:
        print(f"dead-code audit finished in {elapsed:.2f}s", file=sys.stderr)

    return ScanResult(
        repo_root=repo_root,
        crates_scanned=len(target_crates),
        files_scanned=len(files),
        ignored_items=ignored_items,
        all_items=kept_items,
        dead_items=dead_items,
    )


def print_report(
    result: ScanResult,
    verbose: bool = False,
    top_n: Optional[int] = None,
) -> None:
    dead_items = result.dead_items if top_n is None else result.dead_items[:top_n]

    if not dead_items:
        print("No dead code candidates found.")
        return

    print("DEAD CODE CANDIDATES")
    print()

    current_file: Optional[str] = None
    for item in dead_items:
        if item.file_path != current_file:
            if current_file is not None:
                print()
            current_file = item.file_path
            print(f"{item.file_path}:")

        print(
            f"  L{item.line_number} pub {item.kind} {item.name} "
            f"-> {item.cross_crate_crates} crates, {item.cross_crate_files} files, "
            f"{item.cross_crate_sites} sites"
        )
        if item.references:
            refs = item.references if verbose else item.references[:3]
            for ref in refs:
                print(f"    {ref.file_path}:{ref.line_number}")
                if verbose and ref.line_text:
                    print(f"      {ref.line_text}")

    print()
    print(
        f"Summary: {len(result.dead_items)} candidates from {len(result.all_items)} public items "
        f"({len(result.ignored_items)} ignored), across {result.crates_scanned} crates "
        f"and {result.files_scanned} files"
    )


def print_summary(result: ScanResult) -> None:
    crate_counts: dict[str, int] = {}
    kind_counts: dict[str, int] = {}
    for item in result.dead_items:
        crate_counts[item.crate_name] = crate_counts.get(item.crate_name, 0) + 1
        kind_counts[item.kind] = kind_counts.get(item.kind, 0) + 1

    print("Dead Code Audit Summary")
    print("=" * 60)
    print(f"Crates scanned:              {result.crates_scanned}")
    print(f"Rust files scanned:          {result.files_scanned}")
    print(f"Public items kept:           {len(result.all_items)}")
    print(f"Public items ignored:        {len(result.ignored_items)}")
    print(f"Dead code candidates:        {len(result.dead_items)}")
    if result.all_items:
        print(f"Candidate rate:              {100 * len(result.dead_items) / len(result.all_items):.1f}%")
    print()

    if crate_counts:
        print(f"{'Crate':<30} {'Candidates':>12}")
        print(f"{'-' * 30} {'-' * 12}")
        for crate, count in sorted(crate_counts.items(), key=lambda x: (-x[1], x[0])):
            print(f"{crate:<30} {count:>12}")

    if kind_counts:
        print()
        print(f"{'Kind':<15} {'Candidates':>12}")
        print(f"{'-' * 15} {'-' * 12}")
        for kind, count in sorted(kind_counts.items(), key=lambda x: (-x[1], x[0])):
            print(f"{kind:<15} {count:>12}")


def print_json(result: ScanResult) -> None:
    output = {
        "repo_root": str(result.repo_root),
        "crates_scanned": result.crates_scanned,
        "files_scanned": result.files_scanned,
        "public_items_kept": len(result.all_items),
        "public_items_ignored": len(result.ignored_items),
        "dead_candidates": len(result.dead_items),
        "dead_percentage": (
            round(100 * len(result.dead_items) / len(result.all_items), 1)
            if result.all_items
            else 0.0
        ),
        "candidates": [asdict(item) for item in result.dead_items],
    }
    print(json.dumps(output, indent=2))


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Cross-crate dead code detection for pub API surface hygiene",
    )
    parser.add_argument("--json", action="store_true", help="output results as JSON")
    parser.add_argument("--summary", action="store_true", help="print summary statistics only")
    parser.add_argument("--crate", type=str, default=None, help="filter to a single crate")
    parser.add_argument("--verbose", action="store_true", help="show progress and reference lines")
    parser.add_argument("--top", type=int, default=None, help="limit output to top N candidates")
    parser.add_argument("--root", type=str, default=None, help="repository root directory")
    parser.add_argument(
        "--ignore-file",
        type=str,
        default=None,
        help="TOML or JSON ignore file (default: data/dead_code_ignore.toml if present)",
    )
    parser.add_argument(
        "--fail-on-candidates",
        action="store_true",
        help="exit 1 when dead-code candidates are found",
    )
    return parser


def main(argv: Optional[list[str]] = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    if args.root is not None:
        repo_root = Path(args.root).resolve()
    else:
        repo_root = find_repo_root(Path.cwd())

    if args.ignore_file is not None:
        ignore_path = Path(args.ignore_file).resolve()
        if not ignore_path.exists():
            print(f"Error: ignore file {ignore_path} not found", file=sys.stderr)
            return 1
    else:
        default_ignore = repo_root / "data" / "dead_code_ignore.toml"
        ignore_path = default_ignore if default_ignore.exists() else None

    try:
        ignore_rules = load_ignore_rules(ignore_path)
        result = scan_workspace(
            repo_root,
            crate_filter=args.crate,
            ignore_rules=ignore_rules,
            verbose=args.verbose,
        )
    except (FileNotFoundError, ValueError, RuntimeError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print_json(result)
    elif args.summary:
        print_summary(result)
    else:
        print_report(result, verbose=args.verbose, top_n=args.top)
        print_summary(result)

    if args.fail_on_candidates and result.dead_items:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
