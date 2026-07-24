# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""MASQUERADE detector — returns Finding records for Branch A patterns."""
from __future__ import annotations

import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

from scripts.masquerade_gate.constants import (
    ALLOW_MARKER,
    ARG_DISCARDING_HELPERS,
    CARRIER_HELPER_HINTS,
    DECL_DEFINITION_HEADER,
    DECL_THEOREM_HEADER,
    IS_REDUCIBLE_TRUE,
    KNOWN_MASQUERADE_CARRIERS,
    NAME_FROM_STRING,
    TRIVIAL_PROOFS,
)
from scripts.masquerade_gate.parser import (
    extract_block,
    field_rhs,
    resolve_ident_rhs,
    trim_snippet,
)

logger = logging.getLogger(__name__)


@dataclass
class Finding:
    """One suspected MASQUERADE Theorem registration."""

    file_path: str
    theorem_name: str
    trivial_proof: str
    carrier_hint: str
    line_number: int
    snippet: str = ""
    reasons: list[str] = field(default_factory=list)

    def render(self) -> str:
        header = (
            f"[masquerade-gate] {self.file_path}:{self.line_number}: "
            f"Declaration::Theorem `{self.theorem_name}` closes via "
            f"`{self.trivial_proof}` over carrier `{self.carrier_hint}`"
        )
        why = "\n".join(f"    - {r}" for r in self.reasons)
        snip = self.snippet.strip()
        if snip:
            snip = "\n    snippet:\n" + "\n".join(
                f"      {line}" for line in snip.splitlines()
            )
        return f"{header}\n{why}{snip}"


@dataclass
class AllowedSite:
    """A Declaration::Theorem that matched the MASQUERADE detector but was
    suppressed by an in-file `// MASQUERADE-ALLOW:` marker within ±5 lines
    of the Theorem header. Recorded so operators can see the allow-list
    decisions without having to re-read the source.
    """

    file_path: str
    theorem_name: str
    line_number: int
    marker_text: str

    def render(self) -> str:
        return (
            f"[masquerade-gate] {self.file_path}:{self.line_number}: "
            f"ALLOWED Declaration::Theorem `{self.theorem_name}` via "
            f"marker: {self.marker_text}"
        )


# Number of lines of context to scan on EACH SIDE of a flagged
# Declaration::Theorem header when looking for a MASQUERADE-ALLOW marker.
# Symmetric window by design: markers may legitimately sit either above
# the `self.add_decl(Declaration::Theorem { ... })` call (most common) or
# immediately inside/after the struct literal (some hand-written sites).
ALLOW_MARKER_LINE_WINDOW: int = 5


_BUILDER_SUFFIXES: tuple[str, ...] = (
    "refl_proof",
    "rfl_proof",
    "trivial_proof",
    "eq_refl_proof",
    "nat_rec_proof",
)


def _scan_direct_trivial(value_src: str) -> str | None:
    for m in NAME_FROM_STRING.finditer(value_src):
        if m.group(1) in TRIVIAL_PROOFS:
            return m.group(1)
    if re.search(r"\beq_refl\b", value_src):
        return "Eq.refl"
    if re.search(r"\brat_le_refl\b", value_src):
        return "Rat.le_refl"
    if re.search(r"\bnat_le_refl\b", value_src):
        return "Nat.le_refl"
    if re.search(r"\btrue_intro\b", value_src):
        return "True.intro"
    if re.search(r"\brfl\b", value_src):
        return "rfl"
    return None


def _scan_builder_suffix(value_src: str) -> str | None:
    for suffix in _BUILDER_SUFFIXES:
        if re.search(rf"\b[a-zA-Z_0-9]+_{re.escape(suffix)}\b", value_src):
            return f"<builder:{suffix}>"
    return None


def contains_trivial_proof(value_src: str) -> str | None:
    """Return the name of the first trivial combinator referenced in
    `value_src`, or None. Also flags cross-file proof builders named
    `build_*_proof` with known trivial suffixes.
    """
    direct = _scan_direct_trivial(value_src)
    if direct is not None:
        return direct
    return _scan_builder_suffix(value_src)


def _carrier_by_literal_or_suffix(
    type_src: str, carriers: Iterable[str]
) -> str | None:
    for carrier in carriers:
        if carrier in type_src:
            return carrier
        ident_suffix = carrier.rsplit(".", 1)[-1]
        if len(ident_suffix) >= 5 and re.search(
            rf"\b{re.escape(ident_suffix)}\b", type_src
        ):
            return carrier
    return None


def _carrier_by_helper(type_src: str) -> str | None:
    for carrier, helpers in CARRIER_HELPER_HINTS:
        for h in helpers:
            if re.search(rf"\b{re.escape(h)}\b", type_src):
                return carrier
    return None


def type_references_carrier(
    type_src: str, carriers: Iterable[str]
) -> str | None:
    """Return the first carrier name referenced in `type_src`, or None."""
    if not type_src:
        return None
    hit = _carrier_by_literal_or_suffix(type_src, carriers)
    if hit is not None:
        return hit
    return _carrier_by_helper(type_src)


def _describe_definition(block: str) -> str | None:
    if not IS_REDUCIBLE_TRUE.search(block):
        return None
    name_m = NAME_FROM_STRING.search(block)
    name = name_m.group(1) if name_m else "<anonymous>"
    helper_m = ARG_DISCARDING_HELPERS.search(block)
    if helper_m:
        return f"{name} ({helper_m.group(0)})"
    return None


def file_has_arg_discarding_carrier(source: str) -> str | None:
    """Return a brief description of an argument-discarding reducible
    Definition in this file, or None.
    """
    for header in DECL_DEFINITION_HEADER.finditer(source):
        open_brace = source.find("{", header.start())
        if open_brace == -1:
            continue
        block, _ = extract_block(source, open_brace)
        desc = _describe_definition(block)
        if desc is not None:
            return desc
    return None


def _file_level_carrier(source: str) -> str | None:
    for carrier in KNOWN_MASQUERADE_CARRIERS:
        if f'"{carrier}"' in source or carrier in source:
            return carrier
    return None


def _resolve_trivial_or_cross_file(
    resolved_value: str, file_level_carrier: str | None
) -> str | None:
    trivial = contains_trivial_proof(resolved_value)
    if trivial is not None:
        return trivial
    m_defs = re.search(
        r"\b([a-zA-Z0-9_]+_defs)::build_[a-zA-Z0-9_]+_proof\b", resolved_value
    )
    if m_defs is not None and file_level_carrier is not None:
        return f"<cross-file {m_defs.group(1)}::build_*_proof>"
    return None


@dataclass
class _FileContext:
    source: str
    local_carrier_desc: str | None
    file_level_carrier: str | None


def _find_allow_marker(
    source: str, header_start: int, window_lines: int
) -> str | None:
    """Return the captured rationale text of a `// MASQUERADE-ALLOW:`
    marker within `window_lines` lines on EITHER side of the Theorem
    header at `header_start`, or None.

    The window is symmetric by design: markers may sit above the
    `self.add_decl(Declaration::Theorem { ... })` call (most common),
    within the struct literal (e.g. inline justification), or a handful
    of lines below it (rarer but observed). Requiring developers to
    always place the marker above the call would force code-churn at
    sites that already justify the allowance in a different comment
    style; a symmetric window is both more ergonomic and more
    Rust-idiomatic.
    """
    # Compute the line index of header_start (0-based).
    preceding_newlines = source.count("\n", 0, header_start)
    # Find the byte offsets of the window's first and last line.
    start_line = max(0, preceding_newlines - window_lines)
    end_line = preceding_newlines + window_lines + 1
    # Walk the newline offsets to build a line-indexed view cheaply.
    # For the small window sizes here, splitlines() over the slice is
    # simplest and still linear in the window size.
    lines = source.splitlines()
    lo = max(0, min(start_line, len(lines)))
    hi = max(0, min(end_line, len(lines)))
    window = "\n".join(lines[lo:hi])
    m = ALLOW_MARKER.search(window)
    if m is None:
        return None
    # Group 1 holds the rationale text after `MASQUERADE-ALLOW:`.
    return m.group(1).strip()


def _extract_theorem_name(
    source: str, header_start: int, block: str
) -> str:
    """Resolve the theorem name from the struct literal, following Rust
    shorthand `name,` bindings when present.
    """
    name_src = field_rhs(block, "name")
    if name_src:
        resolved_name = resolve_ident_rhs(source, header_start, name_src)
        name_m = NAME_FROM_STRING.search(resolved_name)
        if name_m is not None:
            return name_m.group(1)
    name_m = NAME_FROM_STRING.search(block)
    if name_m is not None:
        return name_m.group(1)
    return "<anonymous>"


def _build_finding(
    ctx: _FileContext,
    file_path: str,
    header_start: int,
    block: str,
    resolved_value: str,
    resolved_type: str,
    type_src: str,
    trivial: str,
) -> tuple[Finding | None, AllowedSite | None]:
    name = _extract_theorem_name(ctx.source, header_start, block)
    carrier_hint = type_references_carrier(
        (type_src or "") + "\n" + (resolved_type or ""),
        KNOWN_MASQUERADE_CARRIERS,
    )
    if carrier_hint is None and ctx.file_level_carrier is not None:
        carrier_hint = ctx.file_level_carrier

    reasons: list[str] = [
        f"proof term contains trivial combinator `{trivial}`"
    ]
    if carrier_hint is None and ctx.local_carrier_desc is None:
        return None, None
    if carrier_hint is not None:
        reasons.append(
            f"type references known-aliased carrier `{carrier_hint}` "
            "(demoted in prior demasquerade sweep)"
        )
    if ctx.local_carrier_desc is not None:
        reasons.append(
            "file registers a reducible Definition with an "
            f"argument-discarding body: `{ctx.local_carrier_desc}`"
        )
    line_number = ctx.source.count("\n", 0, header_start) + 1
    marker = _find_allow_marker(
        ctx.source, header_start, ALLOW_MARKER_LINE_WINDOW
    )
    if marker is not None:
        return None, AllowedSite(
            file_path=file_path,
            theorem_name=name,
            line_number=line_number,
            marker_text=marker,
        )
    return (
        Finding(
            file_path=file_path,
            theorem_name=name,
            trivial_proof=trivial,
            carrier_hint=carrier_hint or (ctx.local_carrier_desc or "<local>"),
            line_number=line_number,
            snippet=trim_snippet(block),
            reasons=reasons,
        ),
        None,
    )


def _analyze_theorem(
    ctx: _FileContext, file_path: str, header_start: int
) -> tuple[Finding | None, AllowedSite | None]:
    open_brace = ctx.source.find("{", header_start)
    if open_brace == -1:
        return None, None
    block, _ = extract_block(ctx.source, open_brace)
    type_src = field_rhs(block, "type_")
    value_src = field_rhs(block, "value")
    if not value_src:
        return None, None
    resolved_value = resolve_ident_rhs(ctx.source, header_start, value_src)
    resolved_type = resolve_ident_rhs(ctx.source, header_start, type_src)
    trivial = _resolve_trivial_or_cross_file(
        resolved_value, ctx.file_level_carrier
    )
    if trivial is None:
        return None, None
    return _build_finding(
        ctx,
        file_path,
        header_start,
        block,
        resolved_value,
        resolved_type,
        type_src,
        trivial,
    )


def detect_in_text_with_allowed(
    file_path: str, source: str
) -> tuple[list[Finding], list[AllowedSite]]:
    """Scan `source` and return both the unallowed findings AND the
    allow-list hits. Used by the CLI's `--scan` mode and by tests that
    want to assert the skip record is populated.
    """
    if "Declaration::Theorem" not in source:
        return [], []
    ctx = _FileContext(
        source=source,
        local_carrier_desc=file_has_arg_discarding_carrier(source),
        file_level_carrier=_file_level_carrier(source),
    )
    findings: list[Finding] = []
    allowed: list[AllowedSite] = []
    for header in DECL_THEOREM_HEADER.finditer(source):
        finding, allow = _analyze_theorem(ctx, file_path, header.start())
        if finding is not None:
            findings.append(finding)
        if allow is not None:
            allowed.append(allow)
    return findings, allowed


def detect_in_text(file_path: str, source: str) -> list[Finding]:
    """Scan `source` for Branch A MASQUERADE registrations."""
    findings, _allowed = detect_in_text_with_allowed(file_path, source)
    return findings


def detect_in_file_with_allowed(
    path: Path,
) -> tuple[list[Finding], list[AllowedSite]]:
    try:
        source = path.read_text(encoding="utf-8")
    except OSError as exc:
        logger.warning(
            "[masquerade-gate] ERROR: cannot read %s: %s", path, exc
        )
        return [], []
    return detect_in_text_with_allowed(str(path), source)


def detect_in_file(path: Path) -> list[Finding]:
    findings, _allowed = detect_in_file_with_allowed(path)
    return findings
