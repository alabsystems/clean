#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed gate for the enum discriminants the crystal chains prove about.

A crystal chain proves a theorem about the trust-ir `trustc` emits for one
shipped body. Where that body is a `match` over a kernel enum, the emitted IR
names no variants -- it switches on the NUMERIC DISCRIMINANT, and Clean's side
of the proof encodes the same numbers (`clean_mode_tag`, `level_kind_tag`).

The Rust Reference guarantees the VALUES given a declaration order (unspecified
first discriminant is 0, each later one is previous + 1). Nothing guaranteed the
ORDER. Reordering two variants changes no behaviour of the Rust program, but it
moves `Cubical` off 2 while the registered module, the recorded fixture and
every gate over them stay byte-identical -- the chain goes on reporting green
while proving something false about the shipped body.

This gate re-derives, from source, everything that mapping rests on and compares
it against data/crystal_enum_tag_pin.json:

  1. declaration order and discriminant values of each chained enum;
  2. `#[repr(u8)]` and an explicit `= N` on every variant, where the manifest
     says the enum takes them;
  3. discriminant == declaration index, so the ABI tag and serde's variant index
     (which keys off declaration position, NOT the discriminant) cannot silently
     diverge and break a compact-format wire;
  4. the Rust-side pin tables in crates/clean-kernel/src/crystal_tag_pin.rs;
  5. the spec's reflected tag definitions (`clean_mode_tag`, `level_kind_tag`);
  6. the recorded trust-ir artifacts: every `switch` arm and every
     `const <ir_type> { k }` aggregate tag is a pinned discriminant, the
     explicit arms plus the pinned default coverage are EXACTLY the full
     discriminant set (so a new variant fires here, because it changes what
     `default` means in a proved module), and the IR type token still matches.

Point 6's type-token check WAS the only place that token is read at all --
crystal_a1_lineage's CFG parser took `t.last()` for `load` (the pointer
register) and dropped the type at `t.get(1)`. The 2026-08-19
operand-completeness audit closed that hole: `load_tys` and `extract_tys` are
lanes of the CFG gate now, and closing the first one turned the flagship chain
RED (`ir_h2_b0` loaded `ir_tLevel`, i.e. `IRTy.enum_ 0`, where this manifest
says enum.13) until the registered module was corrected.

The two readings are not redundant. The lane compares the token against the
REGISTERED SPEC; point 6 compares it against the ENUM DECLARATION. A drift that
moved both the spec and the artifact together would pass the lane and fail here.

Wired into scripts/local_gate.sh. Pure-stdlib; no cargo build required.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST = REPO_ROOT / "data" / "crystal_enum_tag_pin.json"
PIN_TABLES = REPO_ROOT / "crates" / "clean-kernel" / "src" / "crystal_tag_pin.rs"

SWITCH_RE = re.compile(r"switch %\d+ \[([^\]]*)\]")
ARM_RE = re.compile(r"(\d+):")


def enum_body(source: str, ident: str) -> tuple[str, str]:
    """Return (attribute block, brace body) of `pub enum <ident> { ... }`.

    The attribute block is everything from the last blank line before the
    declaration up to the `pub enum` line, which is where `#[repr(..)]` lives.
    """
    decl = re.search(rf"^pub enum {re.escape(ident)} \{{$", source, re.M)
    if decl is None:
        raise LookupError(f"no `pub enum {ident} {{` in the source")
    head = source[: decl.start()]
    # Attributes are the run of `#[...]` lines immediately above the decl.
    attrs: list[str] = []
    for line in reversed(head.splitlines()):
        stripped = line.strip()
        if stripped.startswith("#["):
            attrs.append(stripped)
        elif stripped.startswith("///") or stripped.startswith("//") or not stripped:
            continue
        else:
            break
    depth = 0
    for idx in range(decl.end() - 1, len(source)):
        if source[idx] == "{":
            depth += 1
        elif source[idx] == "}":
            depth -= 1
            if depth == 0:
                return "\n".join(attrs), source[decl.end() : idx]
    raise LookupError(f"unterminated `pub enum {ident}` body")


def parse_variants(body: str) -> list[tuple[str, int | None]]:
    """Variant name and explicit discriminant, in declaration order.

    Comments and attributes are stripped LINE-WISE first: prose inside a doc
    comment routinely contains commas and parentheses (`/// Maximum: max(l1,
    l2)`), and letting those reach the splitter mis-parses the enum. What is
    left is split on commas at bracket depth zero, so a payload variant
    `Succ(LevelArc)` is one entry and `Max(LevelArc, LevelArc)` is one entry.
    """
    code_lines = [
        line
        for line in body.splitlines()
        if not line.strip().startswith(("///", "//!", "//", "#["))
    ]
    code = "\n".join(code_lines)

    out: list[tuple[str, int | None]] = []
    depth = 0
    token = ""
    for ch in code:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and ch == ",":
            entry = token.strip()
            token = ""
            if not entry:
                continue
            m = re.match(
                r"^([A-Za-z_][A-Za-z0-9_]*)\s*(?:\([^)]*\)|\{[^}]*\})?\s*(?:=\s*(\d+))?$",
                entry,
                re.S,
            )
            if m is None:
                raise ValueError(f"unparsed enum entry: {entry!r}")
            out.append((m.group(1), int(m.group(2)) if m.group(2) is not None else None))
        else:
            token += ch
    if token.strip():
        raise ValueError(f"trailing enum entry without a comma: {token.strip()!r}")
    return out


def check_enum(spec: dict, errors: list[str]) -> None:
    ident = spec["ident"]
    src_path = REPO_ROOT / spec["source"]
    label = spec["rust_path"]
    if not src_path.is_file():
        errors.append(f"{label}: source {spec['source']} is missing")
        return
    source = src_path.read_text(encoding="utf-8")
    try:
        attrs, body = enum_body(source, ident)
        found = parse_variants(body)
    except (LookupError, ValueError) as exc:
        errors.append(f"{label}: {exc}")
        return

    pinned = [(name, int(tag)) for name, tag in spec["variants"]]

    if [n for n, _ in found] != [n for n, _ in pinned]:
        errors.append(
            f"{label}: DECLARATION ORDER moved.\n"
            f"    pinned:  {[n for n, _ in pinned]}\n"
            f"    source:  {[n for n, _ in found]}\n"
            f"    Every chained module and recorded artifact for this enum encodes the OLD "
            f"numbering. Re-pin data/crystal_enum_tag_pin.json only together with the "
            f"registered modules and a re-dumped artifact."
        )
        return

    repr_want = spec.get("repr")
    if repr_want is not None:
        if f"#[repr({repr_want})]" not in attrs:
            errors.append(
                f"{label}: `#[repr({repr_want})]` is gone. The emitted body reads the tag as "
                f"`extractfield {repr_want}`; without the repr that width is a layout choice."
            )

    for idx, ((name, got), (_, want)) in enumerate(zip(found, pinned)):
        if spec.get("explicit_discriminants"):
            if got is None:
                errors.append(
                    f"{label}::{name}: explicit discriminant `= {want}` was removed. Implicit "
                    f"numbering makes a later reorder silent again."
                )
            elif got != want:
                errors.append(
                    f"{label}::{name}: discriminant {got}, pinned {want}."
                )
        if want != idx:
            errors.append(
                f"{label}::{name}: pinned discriminant {want} != declaration index {idx}. "
                f"serde keys its variant index off the declaration POSITION, so the ABI tag and "
                f"the compact-format wire have diverged."
            )


def check_pin_tables(manifest: dict, errors: list[str]) -> None:
    # Stage 1 of this pin carries no Rust-side tables (see `staged_upgrade` in the
    # manifest): nothing declares a `pin_table`, so there is nothing here to check
    # and the absent file is not a failure. The moment any enum declares one, a
    # missing file IS a failure -- the check fails closed on the configuration it
    # is asked to enforce, not on the one it is not.
    if not any(spec.get("pin_table") for spec in manifest["enums"]):
        return
    if not PIN_TABLES.is_file():
        errors.append("crates/clean-kernel/src/crystal_tag_pin.rs is missing")
        return
    text = PIN_TABLES.read_text(encoding="utf-8")
    for spec in manifest["enums"]:
        table = spec.get("pin_table")
        if table is None:
            continue
        m = re.search(rf"pub const {re.escape(table)}: \[\(&str, u8\); (\d+)\] = \[(.*?)\];",
                      text, re.S)
        if m is None:
            errors.append(f"{spec['rust_path']}: pin table {table} is missing from crystal_tag_pin.rs")
            continue
        entries = [(n, int(v)) for n, v in re.findall(r'\("([A-Za-z0-9_]+)",\s*(\d+)\)', m.group(2))]
        pinned = [(n, int(v)) for n, v in spec["variants"]]
        if int(m.group(1)) != len(pinned) or entries != pinned:
            errors.append(
                f"{spec['rust_path']}: {table} in crystal_tag_pin.rs disagrees with the manifest.\n"
                f"    table:    {entries}\n"
                f"    manifest: {pinned}"
            )
        for name, tag in pinned:
            if f"assert!({spec['ident']}::{name} as u8 == {tag});" not in text:
                errors.append(
                    f"{spec['rust_path']}::{name}: the compile-time tripwire "
                    f"`assert!({spec['ident']}::{name} as u8 == {tag});` is gone from "
                    f"crystal_tag_pin.rs."
                )


def check_spec_tag_defs(spec: dict, errors: list[str]) -> None:
    for tag_def in spec.get("spec_tag_defs", []):
        path = REPO_ROOT / tag_def["file"]
        if not path.is_file():
            errors.append(f"{spec['rust_path']}: spec file {tag_def['file']} is missing")
            continue
        text = path.read_text(encoding="utf-8")
        if tag_def["must_contain"] not in text:
            errors.append(
                f"{spec['rust_path']}: {tag_def['const']} in {tag_def['file']} no longer contains "
                f"the pinned reflected tag definition. Clean's side of the chain now encodes a "
                f"different mapping from the one the artifact switches on."
            )


def check_artifact(spec: dict, art: dict, errors: list[str]) -> None:
    path = REPO_ROOT / art["file"]
    label = f"{spec['rust_path']} @ {art['body']}"
    if not path.is_file():
        errors.append(f"{label}: artifact {art['file']} is missing")
        return
    text = path.read_text(encoding="utf-8")
    tags = {int(t) for _, t in spec["variants"]}
    ir_type = art["ir_type"]

    if ir_type not in text:
        errors.append(
            f"{label}: the recorded IR type token `{ir_type}` is no longer in the artifact. "
            f"The artifact was re-dumped and the type renumbered; re-pin deliberately "
            f"(see ir_type_note in the manifest)."
        )

    arms_want = art.get("switch_arms")
    if arms_want is not None:
        switches = SWITCH_RE.findall(text)
        if len(switches) != 1:
            errors.append(f"{label}: expected exactly one `switch`, found {len(switches)}")
        else:
            arms_got = [int(a) for a in ARM_RE.findall(switches[0])]
            if arms_got != [int(a) for a in arms_want]:
                errors.append(
                    f"{label}: switch arms {arms_got}, pinned {arms_want}."
                )
            covered = set(arms_got) | {int(d) for d in art["switch_default_covers"]}
            if covered != tags:
                errors.append(
                    f"{label}: explicit arms + pinned default coverage = {sorted(covered)}, "
                    f"but the enum's discriminants are {sorted(tags)}. A variant was added or "
                    f"removed, so `default` in the proved module now covers a different set."
                )
            stray = set(arms_got) - tags
            if stray:
                errors.append(f"{label}: switch arms {sorted(stray)} are not discriminants of the enum")

    consts_want = art.get("agg_const_tags")
    if consts_want is not None:
        consts_got = sorted({int(k) for k in
                             re.findall(rf"const {re.escape(ir_type)} \{{ (\d+) \}}", text)})
        if consts_got != sorted(int(k) for k in consts_want):
            errors.append(
                f"{label}: `const {ir_type} {{ k }}` tags {consts_got}, pinned "
                f"{sorted(int(k) for k in consts_want)}."
            )
        stray = set(consts_got) - tags
        if stray:
            errors.append(
                f"{label}: aggregate constants {sorted(stray)} are not discriminants of the enum"
            )


def main() -> int:
    if not MANIFEST.is_file():
        print(f"FAIL: {MANIFEST} is missing", file=sys.stderr)
        return 1
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    errors: list[str] = []

    for spec in manifest["enums"]:
        check_enum(spec, errors)
        check_spec_tag_defs(spec, errors)
        for art in spec.get("artifacts", []):
            check_artifact(spec, art, errors)
    check_pin_tables(manifest, errors)

    if errors:
        print("FAIL: crystal enum tag pin", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    n_enums = len(manifest["enums"])
    n_variants = sum(len(s["variants"]) for s in manifest["enums"])
    n_artifacts = sum(len(s.get("artifacts", [])) for s in manifest["enums"])
    n_tag_defs = sum(len(s.get("spec_tag_defs", [])) for s in manifest["enums"])
    # Name what was ACTUALLY enforced, not the full menu: the manifest can be in
    # stage 1 (declaration order only) or stage 2 (repr + explicit discriminants
    # + the Rust pin tables), and a summary that reads the same either way would
    # be the exact kind of claim this gate exists to stop.
    enforced = ["declaration order", "serde-index coherence"]
    n_repr = sum(1 for s in manifest["enums"] if s.get("repr"))
    if n_repr:
        enforced.append(f"#[repr] on {n_repr}")
    if any(s.get("explicit_discriminants") for s in manifest["enums"]):
        enforced.append("explicit discriminants")
    if any(s.get("pin_table") for s in manifest["enums"]):
        enforced.append("Rust pin tables")
    enforced.append(f"{n_tag_defs} reflected tag defs")
    enforced.append(f"{n_artifacts} recorded artifacts")
    print(
        f"OK: crystal enum tag pin — {n_enums} chained enums, {n_variants} discriminants; "
        + ", ".join(enforced)
        + " all agree."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
