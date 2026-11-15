#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The `cfg` predicates the module walk (scripts/rust_modules.py) decides, and the host facts it decides them from.

Split out of rust_modules.py on 2026-11-01 (the 500-line rule). `cfg(pred)` is
three-valued: True or False where the facts decide it, None where they do not.
The facts are the host target's platform cfgs, which `cargo test` builds for
(no `--target`, no `build.target` here): the compiler's own `--print cfg`
answer for PLATFORM_KEYS and `unix` / `windows`. Every other cfg -- `feature`,
`debug_assertions` (the profile), `trust_verify` (the lane), `kani`, `miri`,
`target_feature`, `target_has_atomic` -- is undecided; the walk adds `test`
itself (true under the libtest harness).

With no compiler answering (2026-11-01 review: an environment without
trustc/rustc on PATH, or a broken toolchain link), the facts fall back to the
few Python's `sys.platform` names surely (`python_facts`), never to none at
all: an empty set left `#![cfg(unix)]` undecided and turned three honest
Justfile tests into a silent VACUOUS. `host_source` says where the facts came
from, so a gate can say so.
"""

from __future__ import annotations

import re
import subprocess
import sys

WS = r"[\s\u200e\u200f]"  # Rust's Pattern_White_Space: Python's \s lacks U+200E/U+200F
IDENT = r"[^\W\d]\w*"
PLATFORM_KEYS = ("target_os", "target_family", "target_arch", "target_pointer_width", "target_endian",
                 "target_vendor", "target_env", "target_abi")
COMPILERS = ("trustc", "rustc")
_HOST: dict[tuple[str, ...], tuple[dict, str]] = {}
CFG_TOK = re.compile(rf'{WS}*(?:(?P<id>{IDENT})|"(?P<s>[^"\\]*)"|(?P<p>[(),=]))')


def python_facts(platform: str) -> dict:
    """The platform cfgs Python's `sys.platform` names surely of the host rustc
    would build for: darwin is a unix macOS, linux a unix (its target_os may be
    android), win32 a windows. Anything else (cygwin, msys, ios, ...) decides
    nothing, because there the two can disagree."""
    if platform == "darwin":
        return {"unix": True, "windows": False, "target_family": frozenset({"unix"}),
                "target_os": frozenset({"macos"})}
    if platform.startswith("linux"):
        return {"unix": True, "windows": False, "target_family": frozenset({"unix"})}
    if platform == "win32":
        return {"unix": False, "windows": True, "target_family": frozenset({"windows"}),
                "target_os": frozenset({"windows"})}
    return {}


def host_facts(compilers: tuple[str, ...] = COMPILERS) -> dict:
    """{name: bool, key: frozenset of values} for the host target: the first of
    `compilers` that answers `--print cfg`, else `python_facts(sys.platform)`."""
    if compilers not in _HOST:
        facts, source = python_facts(sys.platform), f"python sys.platform={sys.platform}"
        for exe in compilers:
            try:
                out = subprocess.run([exe, "--print", "cfg"], capture_output=True, text=True, timeout=60)
            except (OSError, subprocess.TimeoutExpired):
                continue
            if out.returncode == 0:
                pairs = [line.partition("=") for line in out.stdout.split()]
                facts = {"unix": any(k == "unix" for k, _, _ in pairs),
                         "windows": any(k == "windows" for k, _, _ in pairs)}
                for key in PLATFORM_KEYS:
                    facts[key] = frozenset(v.strip('"') for k, eq, v in pairs if k == key and eq)
                source = f"{exe} --print cfg"
                break
        _HOST[compilers] = (facts, source)
    return _HOST[compilers][0]


def host_source(compilers: tuple[str, ...] = COMPILERS) -> str:
    """Where `host_facts(compilers)` came from: "trustc --print cfg", "rustc
    --print cfg" or "python sys.platform=<platform>" (no compiler answered)."""
    host_facts(compilers)
    return _HOST[compilers][1]


def cfg(pred: str, facts: dict) -> bool | None:
    """`cfg(pred)` under `facts`: True or False where they decide it, None
    where they do not (a name or key they lack, a value it cannot read)."""
    toks, i = [], 0
    while (m := CFG_TOK.match(pred, i)) and m.end() > i:
        toks.append((m.lastgroup, m.group(m.lastgroup)))
        i = m.end()
    if pred[i:].strip(" \t\n\u200e\u200f") or toks[:1] != [("p", "(")] or toks[-1:] != [("p", ")")]:
        return None

    def one(j: int) -> tuple[bool | None, int]:
        kind, val = toks[j]
        if kind != "id":
            raise ValueError
        if toks[j + 1] == ("p", "(") and val in ("all", "any", "not"):
            vals, j = [], j + 2
            while toks[j] != ("p", ")"):
                v, j = one(j)
                vals.append(v)
                j += toks[j] == ("p", ",")
            if val == "not":
                return (None if len(vals) != 1 or vals[0] is None else not vals[0]), j + 1
            if val == "all":
                return (False if False in vals else True if None not in vals else None), j + 1
            return (True if True in vals else False if None not in vals else None), j + 1
        known = facts.get(val)
        if toks[j + 1] == ("p", "=") and toks[j + 2][0] == "s":
            return (toks[j + 2][1] in known if isinstance(known, frozenset) else None), j + 3
        return (known if isinstance(known, bool) else None), j + 1

    try:
        val, j = one(1)
    except (IndexError, ValueError):
        return None
    return val if j == len(toks) - 1 else None
