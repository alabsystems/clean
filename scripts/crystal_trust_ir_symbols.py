#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The ONE reader of trust-ir's definition-site SYMBOLS for the crystal link scripts.

Imported by `scripts/crystal_link3_reconcile.py` and `scripts/crystal_link4_executability.py`,
and since M2 (2026-09-27) by every other script that reads a trust-ir TEXT module's definition
sites: `crystal_link4_join.py`, `crystal_a0_census.py`, `crystal_frontier_census.py`,
`crystal_sidecar_closure.py`, `crystal_sidecar_disposition.py`, `crystal_lzd_readiness.py`,
`check_lzd_layout_facts.py`, `check_lowering_adequacy.py` and `trust_ir_unbacked.py`. None
carries its own copy of any rule below, so they cannot drift apart. A script that reads a whole
module reads it through `ModuleSymbols`, which holds the module to ONE grammar.

WHAT TRUST-IR PRINTS (trust-ir `display.rs`, `write_symbol` / `write_escaped_string`, WS4.3,
first reaching a crystal dump at trust-ir `dcc5b9a3` through Trust main `909cd903f0`)
    A definition-site symbol -- the name after `fn @`, `struct @`, `enum @`, `record @` and
    `global .. @`, and a struct/record field or enum variant name -- is printed
      * BARE when it is in the parser's bare alphabet (`text_loss::is_bare_ident`: non-empty,
        ASCII alphanumerics, `_`, `.`, `$`), and
      * otherwise QUOTED: `"` .. `"` with exactly these escapes -- `\\\\`, `\\"`, `\\n`, `\\t`,
        `\\r`, `\\0`, and `\\u{<lowercase hex>}` for every OTHER char whose Rust
        `char::is_control` holds (Unicode general category Cc). Every other char is printed
        verbatim.
    The parser (`Parser::read_symbol`) refuses the quoted spelling of a bare-able name and the
    empty symbol, so printing and parsing are a bijection: ONE SPELLING PER CONSTRUCT.

    Producers before WS4.3 printed every symbol RAW (the name verbatim, however many `<`, `>`,
    spaces or quotes it held); every committed crystal baseline (`dump-link-O3-s17b`,
    `dump-link-O3-dp`) is such a producer's dump. A raw name is delimited by what FOLLOWS it,
    which differs per construct, so the caller passes that delimiter (`legacy`).

THE RULES THIS READER ENFORCES (each a refusal, never a guess)
    * A quoted symbol decodes with the printer's escapes ONLY: any other escape, a raw control
      char, a `\\u{..}` that is upper-case, zero-padded or names a char the printer spells
      otherwise (a non-control char, or one of the four with a short escape), an unterminated
      string -- the printer cannot have written it.
    * A quoted symbol that is empty, or whose decoding is bare-able, is refused: trust-ir's own
      parser refuses both.
    * ONE GRAMMAR PER MODULE (`Spellings`): a module that holds a QUOTED symbol was printed by a
      WS4.3 printer, which never prints a non-bare name unquoted; so a RAW (unquoted, non-bare)
      symbol beside a quoted one is a refusal. A module with no quoted symbol is a legacy module
      and reads exactly as before.

IDENTITY TOKENS (`canonical_identity`)
    A resolved instance name carries identity HASHES that rustc and the trust sidecar derive
    from the sysroot build, not from the program: the `::<__trust_args@<hex>>` instance-args
    suffix, the `__trust_crate@<hex>::` crate prefix of a crate linked twice, and rustc's
    `<crate>[<hex>]` DefId disambiguator. Rebuilding the sysroot renames every one of them while
    the program -- the callee, its path and its printed generic arguments -- is unchanged
    (memo §19 item 6; measured at M0, memo §20). `canonical_identity` replaces the hex of
    exactly those three spellings by `#` and NOTHING else, so two names that differ anywhere
    outside an identity token still differ.
"""

from __future__ import annotations

import ast
import re
import unicodedata
from pathlib import Path

BARE_ALPHABET = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.$")
# The four control chars the printer spells with a SHORT escape; every other Cc char is `\u{..}`.
_SHORT_ESCAPES = {"\\": "\\", '"': '"', "n": "\n", "t": "\t", "r": "\r", "0": "\0"}
_SHORT_SPELLED = frozenset("\n\t\r\0")
_HEX_LOWER = re.compile(r"[0-9a-f]+")

QUOTED = "quoted"
BARE = "bare"
RAW = "raw"


class SymbolRefusal(ValueError):
    """A symbol spelling the trust-ir printer cannot have produced."""


def is_bare_ident(name: str) -> bool:
    """trust-ir `text_loss::is_bare_ident`: the names printed without quotes."""
    return bool(name) and all(c in BARE_ALPHABET for c in name)


def _is_control(c: str) -> bool:
    """Rust `char::is_control`: Unicode general category Cc."""
    return unicodedata.category(c) == "Cc"


def decode_quoted(s: str, i: int) -> tuple[str, int]:
    """(decoded text, index just past the closing quote) of the quoted string at s[i].

    Strict: only what `write_escaped_string` emits decodes; anything else is a SymbolRefusal."""
    if not s.startswith('"', i):
        raise SymbolRefusal(f"expected a quoted symbol at {s[i:i + 40]!r}")
    out: list[str] = []
    j, n = i + 1, len(s)
    while j < n:
        c = s[j]
        if c == '"':
            return "".join(out), j + 1
        if c == "\\":
            if j + 1 >= n:
                break
            e = s[j + 1]
            if e in _SHORT_ESCAPES:
                out.append(_SHORT_ESCAPES[e])
                j += 2
                continue
            if e == "u":
                close = s.find("}", j + 2)
                hexs = s[j + 3:close] if s.startswith("{", j + 2) and close > 0 else ""
                if not hexs or not _HEX_LOWER.fullmatch(hexs) or (len(hexs) > 1 and hexs[0] == "0"):
                    raise SymbolRefusal(f"malformed \\u escape in quoted symbol at {s[j:j + 16]!r} "
                                        f"(the printer writes `{{:x}}`: lowercase, unpadded)")
                code = int(hexs, 16)
                if code > 0x10FFFF or 0xD800 <= code <= 0xDFFF:
                    raise SymbolRefusal(f"\\u{{{hexs}}} is not a Unicode scalar value")
                ch = chr(code)
                if not _is_control(ch) or ch in _SHORT_SPELLED:
                    raise SymbolRefusal(f"\\u{{{hexs}}} spells a char the printer writes otherwise "
                                        f"(only a control char without a short escape is `\\u{{..}}`)")
                out.append(ch)
                j = close + 1
                continue
            raise SymbolRefusal(f"escape `\\{e}` is not one the trust-ir printer emits "
                                f"(at {s[j:j + 16]!r})")
        if _is_control(c):
            raise SymbolRefusal(f"raw control char U+{ord(c):04X} inside a quoted symbol "
                                f"(the printer escapes every control char)")
        out.append(c)
        j += 1
    raise SymbolRefusal(f"unterminated quoted symbol at {s[i:i + 60]!r}")


def spell_symbol(name: str) -> str:
    """The WS4.3 PRINTER's spelling of `name` (`write_symbol`): bare when bare-able, else quoted.

    Used by the link scripts' self-tests to print the artifacts the reader must decode; every
    spelling it returns reads back to `name` (`read_def_symbol`), which those self-tests check."""
    if is_bare_ident(name):
        return name
    out = ['"']
    for c in name:
        short = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\t": "\\t", "\r": "\\r", "\0": "\\0"}.get(c)
        out.append(short or (f"\\u{{{ord(c):x}}}" if _is_control(c) else c))
    out.append('"')
    return "".join(out)


def read_def_symbol(s: str, i: int, legacy: re.Pattern) -> tuple[str, int, str]:
    """(name, end, spelling) of the definition-site symbol at s[i:] (just after its `@`).

    `legacy` delimits an UNQUOTED symbol for this construct: it is matched at i and its group 1
    is the name (a raw pre-WS4.3 name, or a bare one). The spelling is QUOTED, BARE (in the bare
    alphabet, so identical under both printers) or RAW (legacy only; see `Spellings`)."""
    if s.startswith('"', i):
        name, end = decode_quoted(s, i)
        if not name:
            raise SymbolRefusal("empty quoted symbol (trust-ir's parser refuses `\"\"`)")
        if is_bare_ident(name):
            raise SymbolRefusal(f"symbol {name!r} is in the bare alphabet and must be spelled bare "
                                f"(trust-ir's parser refuses its quoted spelling)")
        return name, end, QUOTED
    m = legacy.match(s, i)
    if m is None or not m.group(1):
        raise SymbolRefusal(f"no symbol at {s[i:i + 60]!r}")
    name = m.group(1)
    return name, m.end(1), BARE if is_bare_ident(name) else RAW


class Spellings:
    """One grammar per module: quoted and raw symbols never share a module."""

    def __init__(self) -> None:
        self.first: dict[str, str] = {}

    def note(self, spelling: str, where: str) -> None:
        self.first.setdefault(spelling, where)
        if QUOTED in self.first and RAW in self.first:
            raise SymbolRefusal(
                f"the module mixes a QUOTED symbol ({self.first[QUOTED][:100]}) with a RAW one "
                f"({self.first[RAW][:100]}): a WS4.3 printer quotes every non-bare name, a legacy "
                f"printer quotes none, so no trust-ir printer wrote this module")

    @property
    def quoted(self) -> bool:
        return QUOTED in self.first


# `fn @<symbol>(functy.N) {`: a legacy name runs to the LAST `(functy.N) {` of the line.
_FN_LEGACY = re.compile(r"(.*)(?=\(functy\.\d+\) \{$)")
_FN_TAIL = re.compile(r"\(functy\.(\d+)\) \{")


def parse_fn_header(line: str, prefix: re.Pattern) -> tuple[str, int, str] | None:
    """(name, functy, spelling) of a `fn` header line, or None when the line is not one.

    `prefix` matches what may stand before `fn @` for the caller (a calling-convention word the
    caller admits), anchored at the start of the line."""
    pm = prefix.match(line)
    if pm is None or not line.startswith("fn @", pm.end()):
        return None
    name, end, spelling = read_def_symbol(line, pm.end() + len("fn @"), _FN_LEGACY)
    tm = _FN_TAIL.fullmatch(line, end)
    if tm is None:
        raise SymbolRefusal(f"fn header does not end `(functy.N) {{` after its symbol: {line[:120]!r}")
    return name, int(tm.group(1)), spelling


# `global <flags> @<symbol> <type> [= <init>]`: a legacy global name holds no space.
_GLOBAL_LEGACY = re.compile(r"(\S+)(?= )")


def read_global_symbol(s: str, i: int) -> tuple[str, int, str]:
    """(name, end, spelling) of the global symbol at s[i:] (just after its `@`)."""
    return read_def_symbol(s, i, _GLOBAL_LEGACY)


# What may stand before `fn @` in a crystal dump's header: nothing (a callee-sidecar member,
# `ccc`) or the `rustcc` calling-convention word (a crate-module function). No crystal dump
# carries a linkage word there; a header with one is not read as a header by a caller using this.
RUSTCC_PREFIX = re.compile(r"(?:rustcc )?")

# `struct @<symbol> { `, `enum @<symbol>[ repr(..)] { `, `record @<symbol> { ` (display.rs): a
# legacy name runs to the FIRST ` {` -- or ` repr(..) {` -- that follows it.
_TYPE_HEAD = re.compile(r"(struct|enum|record) @")
_TYPE_LEGACY = re.compile(r"(.+?)(?= (?:repr\([^)]*\) )?\{ )")


def parse_type_row(line: str) -> tuple[str, str, int, int, str] | None:
    """(kind, name, start, end, spelling) of the symbol a top-level `struct`/`enum`/`record` row
    DEFINES, or None when the line is no such row. `line[start:end]` is the symbol as printed."""
    m = _TYPE_HEAD.match(line)
    if m is None:
        return None
    name, end, spelling = read_def_symbol(line, m.end(), _TYPE_LEGACY)
    if not line.startswith(" ", end):
        raise SymbolRefusal(f"{m.group(1)} row does not continue after its symbol: {line[:120]!r}")
    return m.group(1), name, m.end(), end, spelling


# `global [<linkage> ][mutable ][tls(..) ][align(N) ]@<symbol> <type>`: the flag words link 4's
# `parse_global` reads. The printer can also write `visibility(..)`, `section("..")` and
# `retained`; no crystal dump carries one, and a row this cannot locate the symbol of is REFUSED.
_GLOBAL_HEAD = re.compile(r"global (?:[a-z_]+ |tls\([^)]*\) |align\(\d+\) )*@")


def parse_global_row(line: str) -> tuple[str, int, int, str] | None:
    """(name, start, end, spelling) of the symbol a top-level `global` row DEFINES, or None when
    the line is no `global` row. `line[start:end]` is the symbol as printed."""
    if not line.startswith("global "):
        return None
    m = _GLOBAL_HEAD.match(line)
    if m is None:
        raise SymbolRefusal(f"global row whose symbol this reader cannot locate: {line[:120]!r}")
    name, end, spelling = read_global_symbol(line, m.end())
    return name, m.end(), end, spelling


def legacy_spelling(line: str, start: int, end: int, name: str) -> str:
    """`line` with the symbol at [start, end) printed RAW, as a pre-WS4.3 printer printed it: the
    identity on a legacy module, and on a WS4.3 one the decoded name in place of its quoted
    spelling -- so two printers' rows of one definition compare equal."""
    return line[:start] + name + line[end:]


class ModuleSymbols:
    """ONE module's definition-site symbols, read line by line under ONE grammar.

    Every read notes its spelling in `spellings`, so a module mixing a quoted and a raw symbol is
    refused whichever construct each sits on (see `Spellings`). A caller reads each line through
    the method for its construct; every method returns None for a line that is not one."""

    def __init__(self, fn_prefix: re.Pattern = RUSTCC_PREFIX) -> None:
        self.fn_prefix = fn_prefix
        self.spellings = Spellings()

    def fn_header(self, line: str, where: str = "") -> tuple[str, int] | None:
        """(name, functy) of a `fn` header, the name DECODED."""
        fh = parse_fn_header(line, self.fn_prefix)
        if fh is None:
            return None
        self.spellings.note(fh[2], where or line)
        return fh[0], fh[1]

    def type_row(self, line: str, where: str = "") -> tuple[str, str, int, int] | None:
        """(kind, name, start, end) of a `struct`/`enum`/`record` row, the name DECODED."""
        tr = parse_type_row(line)
        if tr is None:
            return None
        self.spellings.note(tr[4], where or line)
        return tr[0], tr[1], tr[2], tr[3]

    def global_row(self, line: str, where: str = "") -> tuple[str, int, int] | None:
        """(name, start, end) of a `global` row, the name DECODED."""
        gr = parse_global_row(line)
        if gr is None:
            return None
        self.spellings.note(gr[3], where or line)
        return gr[0], gr[1], gr[2]


def respell_ws43(text: str, fn_prefix: re.Pattern = RUSTCC_PREFIX) -> str:
    """`text` as the WS4.3 printer would print it: every definition-site symbol of a `fn` header
    and of a `struct`/`enum`/`record`/`global` row in `spell_symbol`'s spelling, everything else
    byte for byte. For SELF-TESTS: a script proves it reads a quoted-symbol module by reading
    `respell_ws43(<its own legacy input>)` to the same answer."""
    out = []
    for line in text.split("\n"):
        fh = parse_fn_header(line, fn_prefix)
        if fh is not None:
            pm = fn_prefix.match(line)
            line = f"{line[:pm.end()]}fn @{spell_symbol(fh[0])}(functy.{fh[1]}) {{"
        else:
            tr = parse_type_row(line)
            gr = None if tr is not None else parse_global_row(line)
            if tr is not None:
                line = line[:tr[2]] + spell_symbol(tr[1]) + line[tr[3]:]
            elif gr is not None:
                line = line[:gr[1]] + spell_symbol(gr[0]) + line[gr[2]:]
        out.append(line)
    return "\n".join(out)


# ─────────────────────────────── identity tokens ────────────────────────────────

_IDENTITY_TOKENS = (
    # `::<__trust_args@<hex>>`: the trust sidecar's instance-args identity.
    re.compile(r"(__trust_args@)[0-9a-f]+(?=>)"),
    # `__trust_crate@<hex>::`: the crate-identity prefix of a crate linked more than once.
    re.compile(r"(__trust_crate@)[0-9a-f]+(?=::)"),
    # `<crate>[<hex>]::`: rustc's crate disambiguator, as a DefId prints it.
    re.compile(r"(\b[A-Za-z_][A-Za-z0-9_]*\[)[0-9a-f]+(?=\]::)"),
)


def canonical_identity(name: str) -> str:
    """`name` with the hex of every identity token replaced by `#`, and nothing else changed."""
    for pat in _IDENTITY_TOKENS:
        name = pat.sub(r"\1#", name)
    return name


# ─────────────────────────────── pinned inputs ────────────────────────────────


def first_party_imports(script: Path) -> list[str]:
    """The first-party Python modules `script` executes besides itself: every module it imports
    (at any depth in its source, a function-local import included) that resolves to a file BESIDE
    it in `scripts/`, closed transitively, as repo-relative paths, sorted. DERIVED from the parse,
    never listed, so the gate registry pins what the instrument really runs (`--pinned-inputs`,
    check_gate_registry.py R7): a change to a helper it imports moves its row's pin."""
    here = script.resolve().parent
    seen: set[Path] = set()
    todo = [script.resolve()]
    while todo:
        tree = ast.parse(todo.pop().read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            names = [a.name for a in node.names] if isinstance(node, ast.Import) else (
                [node.module] if isinstance(node, ast.ImportFrom) and node.module and not node.level
                else [])
            for name in names:
                cand = here / (name.split(".")[0] + ".py")
                if cand.is_file() and cand.resolve() != script.resolve() and cand not in seen:
                    seen.add(cand)
                    todo.append(cand)
    root = here.parent
    return sorted(p.relative_to(root).as_posix() for p in seen)
