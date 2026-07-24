#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Carrier reducibility linter — detect argument-discarding Definition bodies.

Scans `Declaration::Definition { ... }` registrations in
`crates/clean-kernel/src/env/nn_verify_*.rs` and flags suspected MASQUERADE
carriers (Rule M2 from `designs/2026-04-19-demasquerade-cxxx-pattern.md`):

    1. Argument-discarding lambdas.
       `let value = { ... let (x_id, _) = b.fresh_local(T); ...
                          b.mk_lam(x_id, _, T, body) ... }`
       where the lambda-bound var is never used in the body.

    2. Collapse-to-constant bodies.
       Body reduces to `Rat.zero`, `Nat.zero`, `True`, `False`, or a
       literal `Expr::const_(...)` with no dependence on the lambda args.

    3. Structural-constant-under-lambda (M2 flavour).
       Every `fresh_local` return inside the value block binds to `_` or
       `_<name>`, meaning every param is formally bound but unused.

This linter is the carrier-side counterpart to the Theorem-side MASQUERADE
commit gate (#3597). It catches the pattern before a companion Eq.refl
Theorem is written.

Usage
-----

    python3 scripts/carrier_reducibility_lint.py                # scan
    python3 scripts/carrier_reducibility_lint.py --staged       # pre-commit
    python3 scripts/carrier_reducibility_lint.py --fix=ERROR    # exit 1 on finding

Output (one line per suspect Definition):

    <file>:<line>:<decl_name>  <REASON>  (suggest: <remediation>)

Fixes #3601.
"""
from __future__ import annotations

import argparse
import logging
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

_LOG = logging.getLogger("carrier_reducibility_lint")

REPO_ROOT = Path(__file__).resolve().parent.parent
SCAN_ROOT = REPO_ROOT / "crates" / "clean-kernel" / "src" / "env"
FILE_GLOB = "nn_verify_*.rs"

# --- Patterns ---------------------------------------------------------------

# Match a `let value = { ... };` block.  We walk braces manually to find the
# matching closing brace (regex alone can't balance nesting).
VALUE_BLOCK_START = re.compile(r"\blet\s+value\s*=\s*\{")

# Match the start of a `self.add_decl(Declaration::Definition { ... })`.
DEFINITION_DECL = re.compile(
    r"self\.add_decl\(\s*Declaration::Definition\s*\{",
)

# Capture the `name` field in a Definition block.  Supported shapes:
#   name,                       // reuses local `name`/`n`/<id> binding
#   name: Name::from_string("..."),
#   name: some_ident,           // reuses `some_ident` binding
# When the form is `name: <ident>,` we then look back for
# `let <ident> = Name::from_string("...");` in the enclosing fn body.
NAME_FIELD_IDENT = re.compile(r"\bname\s*:\s*(\w+)\s*[,}]")
NAME_FROM_STRING = re.compile(r'Name::from_string\(\s*"([^"]+)"\s*\)')

# Track `fresh_local` destructurings inside a value block.
FRESH_LOCAL = re.compile(
    r"let\s+\(\s*(\w+)\s*,\s*(_\w*|\w+)\s*\)\s*=\s*\w+\.fresh_local\("
)

# Track `mk_lam` calls — binds (id, _, ty, body).
MK_LAM = re.compile(r"\bmk_lam\(\s*(\w+)\s*,")

# Sentinels for "constant" bodies.
CONSTANT_TOKENS = (
    '"Rat.zero"',
    '"Nat.zero"',
    '"True"',
    '"False"',
    "nat_zero",
    "rat_zero",
    "zero_ib",
    "zero_bound",
)

# Kinds of collapse-to-constant we report.
CONSTANT_BODY_HINT_RE = re.compile(
    r"\b(Rat\.zero|Nat\.zero|True|False|zero_ib|zero_bound|nat_zero|rat_zero)\b"
)


@dataclass
class Finding:
    path: Path
    line: int
    decl_name: str
    reason: str
    remediation: str

    def format(self, relative_to: Path | None = None) -> str:
        path = self.path.relative_to(relative_to) if relative_to else self.path
        return (
            f"{path}:{self.line}:{self.decl_name}  "
            f"{self.reason}  (suggest: {self.remediation})"
        )


# --- Brace-balanced block extraction ---------------------------------------


def find_block_end(text: str, brace_pos: int) -> int:
    """Return the index of the closing `}` that matches the `{` at `brace_pos`.

    Naive brace balancer — handles Rust strings and line comments but not
    block comments or char literals (not expected in register_* bodies)."""
    depth = 0
    i = brace_pos
    n = len(text)
    in_str = False
    str_ch = ""
    while i < n:
        ch = text[i]
        if in_str:
            if ch == "\\":
                i += 2
                continue
            if ch == str_ch:
                in_str = False
            i += 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i)
            if nl < 0:
                return -1
            i = nl + 1
            continue
        if ch == '"':
            in_str = True
            str_ch = '"'
            i += 1
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def line_of(text: str, idx: int) -> int:
    return text.count("\n", 0, idx) + 1


# --- Analysis ---------------------------------------------------------------


def nearest_name_before(text: str, upto: int, ident: str = "name") -> str:
    """Look backward for `let <ident> = Name::from_string("...");`.

    `ident` defaults to `name` but can be any local binding referenced in the
    Definition's `name: <ident>,` field."""
    start = max(0, upto - 3000)
    window = text[start:upto]
    matches = list(
        re.finditer(
            rf'let\s+{re.escape(ident)}\s*=\s*Name::from_string\(\s*"([^"]+)"\s*\)\s*;',
            window,
        )
    )
    if matches:
        return matches[-1].group(1)
    return f"<dynamic:{ident}>"


def body_uses_vars(body: str, bound_vars: list[str]) -> bool:
    """Return True if any bound var name appears as an identifier in body.

    Uses word-boundary matching.  Bound vars must be names that `fresh_local`
    returned as a real binding (not the `_` discard).
    """
    for v in bound_vars:
        if not v or v == "_" or v.startswith("_"):
            continue
        if re.search(rf"\b{re.escape(v)}\b", body):
            return True
    return False


def _count_args_discarded(id_to_val: dict[str, str], lam_ids: list[str]) -> tuple[int, int]:
    """Return (discarded_count, real_count) over the lambda binders."""
    discarded = 0
    real = 0
    for lam_id in lam_ids:
        val_name = id_to_val.get(lam_id)
        if val_name is None:
            continue
        if val_name == "_" or val_name.startswith("_"):
            discarded += 1
        else:
            real += 1
    return discarded, real


def _body_is_effectively_constant(
    value_src: str, id_to_val: dict[str, str], total_lams: int
) -> bool:
    """Return True if the value block's body collapses to a constant hint
    and no non-discarded bound var is referenced outside the binder sites."""
    bound_vals = [v for v in id_to_val.values() if v and not v.startswith("_")]
    if total_lams < 2 or not CONSTANT_BODY_HINT_RE.search(value_src):
        return False
    # Strip mk_lam(id_name, ...) calls and fresh_local declarations so they
    # don't self-match against the bound-var names.
    stripped = MK_LAM.sub("", value_src)
    stripped = FRESH_LOCAL.sub("", stripped)
    return not body_uses_vars(stripped, bound_vals)


def analyze_value_block(value_src: str) -> tuple[bool, bool]:
    """Classify a `let value = { ... }` body.

    Returns (all_args_discarded, body_is_constant).
    """
    fresh = FRESH_LOCAL.findall(value_src)
    if not fresh:
        return False, False
    id_to_val = {id_name: val_name for id_name, val_name in fresh}
    lam_ids = MK_LAM.findall(value_src)
    if not lam_ids:
        return False, False
    discarded, real = _count_args_discarded(id_to_val, lam_ids)
    total_lams = discarded + real
    all_args_discarded = total_lams > 0 and real == 0
    body_is_constant = _body_is_effectively_constant(
        value_src, id_to_val, total_lams
    )
    return all_args_discarded, body_is_constant


REMEDIATION = (
    "replace body with a non-trivial computation that depends on "
    "at least one lambda-bound argument, or demote to "
    "Declaration::Opaque / Declaration::Axiom per designs/"
    "2026-04-19-demasquerade-cxxx-pattern.md"
)


def _resolve_decl_name(decl_src: str, text: str, decl_start: int) -> str:
    inline = NAME_FROM_STRING.search(decl_src)
    if inline:
        return inline.group(1)
    ident_match = NAME_FIELD_IDENT.search(decl_src)
    ident = ident_match.group(1) if ident_match else "name"
    return nearest_name_before(text, decl_start, ident)


def _extract_value_block(text: str, decl_start: int) -> tuple[str, int] | None:
    """Return (value_src, abs_start_index) or None if no value block is found.

    Searches backward 4KB for the last `let value = {` before the decl."""
    search_start = max(0, decl_start - 4000)
    scope = text[search_start:decl_start]
    val_starts = list(VALUE_BLOCK_START.finditer(scope))
    if not val_starts:
        return None
    last_start = val_starts[-1]
    abs_start = search_start + last_start.start()
    vb_open = search_start + last_start.end() - 1
    vb_close = find_block_end(text, vb_open)
    if vb_close < 0:
        return None
    return text[vb_open : vb_close + 1], abs_start


def _classify_finding(
    path: Path,
    text: str,
    decl_match: re.Match[str],
) -> Finding | None:
    brace_pos = text.find("{", decl_match.end() - 1)
    if brace_pos < 0:
        return None
    decl_end = find_block_end(text, brace_pos)
    if decl_end < 0:
        return None
    decl_src = text[brace_pos : decl_end + 1]
    decl_name = _resolve_decl_name(decl_src, text, decl_match.start())

    block = _extract_value_block(text, decl_match.start())
    if block is None:
        return None
    value_src, abs_start = block

    all_discarded, body_constant = analyze_value_block(value_src)
    if not (all_discarded or body_constant):
        return None

    reason_parts: list[str] = []
    if all_discarded:
        reason_parts.append("M2_ALL_ARGS_DISCARDED")
    if body_constant:
        reason_parts.append("M2_COLLAPSE_TO_CONSTANT")

    return Finding(
        path=path,
        line=line_of(text, abs_start),
        decl_name=decl_name,
        reason="+".join(reason_parts),
        remediation=REMEDIATION,
    )


def scan_file(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    try:
        text = path.read_text()
    except (OSError, UnicodeDecodeError):
        return findings
    for decl_match in DEFINITION_DECL.finditer(text):
        finding = _classify_finding(path, text, decl_match)
        if finding is not None:
            findings.append(finding)
    return findings


# --- File discovery --------------------------------------------------------


def discover_scan_files() -> list[Path]:
    return sorted(SCAN_ROOT.glob(FILE_GLOB))


def discover_staged_files() -> list[Path]:
    try:
        out = subprocess.run(
            ["git", "diff", "--cached", "--name-only", "--diff-filter=ACM"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    files: list[Path] = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        p = REPO_ROOT / line
        try:
            p.relative_to(SCAN_ROOT)
        except ValueError:
            continue
        if p.match(FILE_GLOB):
            files.append(p)
    return files


# --- CLI -------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument(
        "--scan",
        action="store_true",
        help="Scan all nn_verify_*.rs files in the kernel env dir (default).",
    )
    scope.add_argument(
        "--staged",
        action="store_true",
        help="Only scan files staged for commit.",
    )
    parser.add_argument(
        "--fix",
        choices=("WARN", "ERROR"),
        default="WARN",
        help="WARN (exit 0) or ERROR (exit 1) when findings exist.",
    )
    parser.add_argument(
        "--report",
        type=Path,
        help="Optional path to write a markdown report of findings.",
    )
    return parser


def render_report(findings: list[Finding], files_scanned: int) -> str:
    lines = [
        "# Carrier Reducibility Linter Report",
        "",
        f"Scan root: `{SCAN_ROOT.relative_to(REPO_ROOT)}`",
        f"File glob: `{FILE_GLOB}`",
        f"Files scanned: {files_scanned}",
        f"Findings: {len(findings)}",
        "",
        "## Findings",
        "",
    ]
    if not findings:
        lines.append("_No findings._")
        return "\n".join(lines) + "\n"
    lines.append("| File | Line | Decl | Reason |")
    lines.append("|------|------|------|--------|")
    for f in findings:
        rel = f.path.relative_to(REPO_ROOT)
        lines.append(
            f"| `{rel}` | {f.line} | `{f.decl_name}` | `{f.reason}` |"
        )
    lines.append("")
    lines.append("## Remediation")
    lines.append("")
    lines.append(
        "See `designs/2026-04-19-demasquerade-cxxx-pattern.md` "
        "(Branch A demote / Branch B faithful carrier)."
    )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    files = discover_staged_files() if args.staged else discover_scan_files()

    findings: list[Finding] = []
    for path in files:
        findings.extend(scan_file(path))
    findings.sort(key=lambda x: (str(x.path), x.line))

    # Plain text to stdout (logging would route to stderr and mangle the
    # one-line-per-finding contract expected by pre-commit wiring).
    for finding in findings:
        sys.stdout.write(finding.format(relative_to=REPO_ROOT) + "\n")

    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(render_report(findings, len(files)))

    if findings and args.fix == "ERROR":
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
