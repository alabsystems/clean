# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Rust source parsing helpers — brace-balanced block extraction and
let-binding resolution. Respects string literals and `//` + `/* */`
comments so that braces inside strings/comments are not counted as
structural.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

_IDENT_RE = re.compile(r"^[a-zA-Z_][a-zA-Z0-9_]*$")
_PARENS_RE = re.compile(r"^\(\s*(.*)\s*\)$", re.DOTALL)
_CLONE_RE = re.compile(
    r"^([a-zA-Z_][a-zA-Z0-9_]*)\s*\.\s*clone\s*\(\s*\)\s*$", re.DOTALL
)
_REF_RE = re.compile(
    r"^&\s*(?:mut\s+)?([a-zA-Z_][a-zA-Z0-9_]*)\s*$", re.DOTALL
)
_DEREF_RE = re.compile(r"^\*\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*$", re.DOTALL)

# Keep alias chasing intentionally shallow: the gate only needs to
# resolve the small local binding ladders used by `Declaration::Theorem`
# registrations, and a bounded walk avoids pathological loops.
_IDENT_RESOLUTION_LIMIT = 8


@dataclass
class _ScanState:
    in_string: bool = False
    escape: bool = False
    in_line_comment: bool = False
    in_block_comment: bool = False


def _advance_state(state: _ScanState, ch: str, next_ch: str) -> tuple[int, bool]:
    """Advance scanner by one char. Returns (skip_ahead, structural)."""
    if state.in_line_comment:
        if ch == "\n":
            state.in_line_comment = False
        return 0, False
    if state.in_block_comment:
        if ch == "*" and next_ch == "/":
            state.in_block_comment = False
            return 1, False
        return 0, False
    if state.in_string:
        if state.escape:
            state.escape = False
        elif ch == "\\":
            state.escape = True
        elif ch == '"':
            state.in_string = False
        return 0, False
    if ch == "/" and next_ch == "/":
        state.in_line_comment = True
        return 1, False
    if ch == "/" and next_ch == "*":
        state.in_block_comment = True
        return 1, False
    if ch == '"':
        state.in_string = True
        return 0, False
    return 0, True


def extract_block(source: str, start_brace_idx: int) -> tuple[str, int]:
    """Return (block_contents, end_index) for a `{ ... }` starting at
    `start_brace_idx`. The returned end_index is one past the matching `}`.
    """
    state = _ScanState()
    depth = 0
    i = start_brace_idx
    n = len(source)
    while i < n:
        ch = source[i]
        next_ch = source[i + 1] if i + 1 < n else ""
        skip, structural = _advance_state(state, ch, next_ch)
        if skip:
            i += 1 + skip
            continue
        if structural:
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    return source[start_brace_idx : i + 1], i + 1
        i += 1
    return source[start_brace_idx:], n


def _read_simple_rhs(window: str, start: int) -> str:
    state = _ScanState()
    depth = 0
    j = start
    n = len(window)
    while j < n:
        ch = window[j]
        next_ch = window[j + 1] if j + 1 < n else ""
        skip, structural = _advance_state(state, ch, next_ch)
        if skip:
            j += 1 + skip
            continue
        if structural:
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth -= 1
            elif ch == ";" and depth == 0:
                break
        j += 1
    return window[start:j]


def _window_start(source: str, offset: int, lines_back_max: int = 200) -> int:
    lines_back = 0
    pos = offset
    while lines_back < lines_back_max and pos > 0:
        prev = source.rfind("\n", 0, pos - 1)
        pos = prev if prev != -1 else 0
        lines_back += 1
        if pos == 0:
            break
    return pos


def find_preceding_ident_binding(
    source: str, offset: int, ident: str
) -> str | None:
    """Search upwards from `offset` for a `let <ident> = ...;` binding
    and return its right-hand side text, or None.
    """
    window_start = _window_start(source, offset)
    window = source[window_start:offset]

    pat = re.compile(
        r"let\s+(?:mut\s+)?"
        + re.escape(ident)
        + r"(?:\s*:\s*[^=;]+)?\s*=\s*"
    )
    last_rhs: str | None = None
    for m in pat.finditer(window):
        rhs_start = m.end()
        i = rhs_start
        n = len(window)
        while i < n and window[i] in " \t":
            i += 1
        if i >= n:
            continue
        if window[i] == "{":
            abs_idx = window_start + i
            block, _end_abs = extract_block(source, abs_idx)
            last_rhs = block
        else:
            last_rhs = _read_simple_rhs(window, i)
    return last_rhs


def _unwrap_parens(expr: str) -> str:
    text = expr.strip()
    while True:
        m = _PARENS_RE.match(text)
        if m is None:
            return text
        inner = m.group(1).strip()
        if not inner:
            return text
        depth = 0
        state = _ScanState()
        i = 0
        n = len(text)
        balanced = True
        while i < n:
            ch = text[i]
            next_ch = text[i + 1] if i + 1 < len(text) else ""
            skip, structural = _advance_state(state, ch, next_ch)
            if skip:
                i += 1 + skip
                continue
            if not structural:
                i += 1
                continue
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(text) - 1:
                    balanced = False
                    break
            i += 1
        if not balanced or depth != 0:
            return text
        text = inner


def _extract_simple_ident(expr: str) -> str | None:
    text = _unwrap_parens(expr)
    if _IDENT_RE.fullmatch(text):
        return text
    m = _CLONE_RE.match(text)
    if m is not None:
        return m.group(1)
    m = _REF_RE.match(text)
    if m is not None:
        return m.group(1)
    m = _DEREF_RE.match(text)
    if m is not None:
        return m.group(1)
    return None


def resolve_ident_rhs(source: str, offset: int, rhs: str) -> str:
    """If `rhs` is a simple identifier wrapper, follow preceding
    `let <ident> = ...` bindings and return the final binding text.
    Otherwise return `rhs`.
    """
    if not rhs:
        return rhs
    seen: set[str] = set()
    resolved = rhs
    for _ in range(_IDENT_RESOLUTION_LIMIT):
        ident = _extract_simple_ident(resolved)
        if ident is None or ident in seen:
            return resolved
        seen.add(ident)
        binding = find_preceding_ident_binding(source, offset, ident)
        if binding is None:
            return resolved
        resolved = binding
    return resolved


def field_rhs(block: str, field_name: str) -> str:
    """Extract the RHS of `field_name: ...` inside a struct-literal block.

    Supports Rust struct field shorthand: `field_name,` (no colon) resolves
    to the identifier `field_name` itself, so callers can follow the
    enclosing `let field_name = ...;` binding via `resolve_ident_rhs`.
    """
    pat = re.compile(rf"\b{re.escape(field_name)}\s*:", re.MULTILINE)
    m = pat.search(block)
    if m is None:
        # Rust struct shorthand: `field_name,` or `field_name }` with no
        # colon means the field borrows the identically-named local.
        shorthand = re.compile(
            rf"\b{re.escape(field_name)}\s*(?:,|\}})", re.MULTILINE
        )
        if shorthand.search(block) is not None:
            return field_name
        return ""
    i = m.end()
    n = len(block)
    depth = 0
    state = _ScanState()
    start = i
    while i < n:
        ch = block[i]
        next_ch = block[i + 1] if i + 1 < n else ""
        skip, structural = _advance_state(state, ch, next_ch)
        if skip:
            i += 1 + skip
            continue
        if structural:
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                if depth == 0:
                    return block[start:i].strip()
                depth -= 1
            elif ch == "," and depth == 0:
                return block[start:i].strip()
        i += 1
    return block[start:].strip()


def trim_snippet(block: str, max_lines: int = 8) -> str:
    """Shorten a `{...}` block preview to at most `max_lines` lines."""
    lines = block.splitlines()
    if len(lines) <= max_lines:
        return block
    head = lines[: max_lines - 1]
    return "\n".join(head + ["    ... (truncated)"])
