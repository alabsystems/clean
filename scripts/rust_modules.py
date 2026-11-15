#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The module tree rustc compiles from a crate root: every file, with its module path.

ONE walk, imported by every reader that needs it, so a fix lands once: `check_test_target_coverage.py`
(CERTAIN files: is a tests/*.rs built at all), `check_cargo_test_selectors.py` (CERTAIN module paths and
`fn` items: does a filter match a test libtest can name, does a `--test` target hold one; MAYBE: can it
say that one holds none) and `verify_runner.py` (POSSIBLE files: the `@reach:` digest scopes). It reads
code that R9's reference lexer (`scripts/check_add_decl_ratchet.py`) blanked, repaired where rustc_lexer
reads a span otherwise (`_lex`), and decides `cfg` with `scripts/rust_cfg.py`.

The oracles are rustc's own: `trustc --edition 2021 --test --emit=dep-info` for the files, the built
binary's `--list --format=terse` for the paths. `rust_modules_arms.py` holds the walk's arms, each
checked against both on a synthetic crate; the two gates importing this walk run them on every
invocation (`verify_runner`, which imports it for its POSSIBLE scopes, does not).
"""

from __future__ import annotations

import enum
import importlib.util
import re
import types
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEXER = Path("scripts") / "check_add_decl_ratchet.py"
ARMS = Path("scripts") / "rust_modules_arms.py"
CFG = Path("scripts") / "rust_cfg.py"
# What a gate that imports this walk prints for `--pinned-inputs` (check_gate_registry R7).
PINNED_INPUTS = (Path("scripts") / "rust_modules.py", ARMS, CFG, LEXER)

WS = r"[\s\u200e\u200f]"  # Rust's Pattern_White_Space: Python's \s lacks U+200E/U+200F
IDENT = r"[^\W\d]\w*"
# One pass over CODE (comments and literals blanked): a module item (`mod x;`
# loads a file, `mod x {` opens an inline module, Trust's `clean mod x;` loads
# x.clean), an `include!`, a `fn` item (when asked for), a bracket, or the `;`
# that ends an item.
_ITEMS = (rf"(?P<mod>\b(?P<clean>clean{WS}+)?mod{WS}+(?:(?P<dollar>\$\w+)|(?P<raw>r#)?(?P<name>{IDENT}))"
          rf"{WS}*(?P<kind>[{{;]))|(?P<inc>\binclude{WS}*!)")
SCAN = re.compile(rf"{_ITEMS}|[{{}}()\[\];]")
SCAN_FN = re.compile(rf"{_ITEMS}|(?P<fn>\bfn{WS}+(?P<fraw>r#)?(?P<fname>{IDENT}))|[{{}}()\[\];]")
# CERTAIN lexes a file only when its RAW text holds `mod` then a `;` before any
# `{`, or an `include!` (a speed filter: code is raw text with spans blanked, so a
# file it skips declares no file module or splice; only a `{` in a comment between
# a `mod x;`'s tokens is under-read, CERTAIN's side). Led by a literal, no `\b`:
# 41 MB of clean-kernel in 0.04 s, against 0.52 s for one `\bmod..|\binclude..`.
WORTH_LEXING = (re.compile(r"mod\b[^;{]*;"), re.compile(rf"include{WS}*!"))
OPEN, CLOSE = "{([", "})]"
ATTR = re.compile(rf"#{WS}*(?P<bang>!)?{WS}*\[")
INNER = re.compile(rf"{WS}*#{WS}*!{WS}*\[")
INC_ARG = re.compile(rf"{WS}*[(\[{{]")
_STR = r'(?:r(?P<h>#*)"(?P<raw>.*?)"(?P=h)|"(?P<s>[^"\\]*)")'
LIT = re.compile(rf"{WS}*{_STR}", re.S)
INC_ONLY = re.compile(rf"{WS}*{_STR}{WS}*,?{WS}*", re.S)
# Matched on the REVERSED code before a bracket: `name!`, `macro_rules! name`
# (and `!x`, the safe misreading) open a macro's tokens, not a block.
MACRO_BEFORE = re.compile(rf"{WS}*(?:(?P<defn>\w+)(?:#r)?{WS}*)?!{WS}*(?P<call>\w*)")
CALL = re.compile(rf"(?P<n>{IDENT}){WS}*!(?!=)")  # a macro named anywhere in code (MAYBE)
FN_SIG = re.compile(r"[{(\[;]")
CONST_ARG = re.compile(rf"[<,=]{WS}*$")  # a `{` after these in a signature is a const generic argument
# rustc_lexer nests block comments and reads `'\x7b'` / `'\u{7b}'` as ONE char
# literal; the reference lexer does neither, so `_lex` repairs those spans.
NEST = re.compile(r"/\*|\*/")
ESC_CHAR = re.compile(r"'\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f](?:_*[0-9A-Fa-f]){0,5}_*\})'")
# libtest prints `r#type` for a raw keyword, `foo` for `r#foo`: measured on --list (2026-11-01, editions
# 2015 to 2024 alike), the strict and reserved keywords and async/await/dyn/try keep `r#`; the weak ones
# (union, macro_rules, raw, safe, auto, default) and gen print bare, in 2024 too.
KEYWORDS = set("""as async await become box break const continue crate do dyn else enum extern false final
    fn for if impl in let loop macro match mod move mut override priv pub ref return self static struct super
    trait true try type typeof unsafe unsized use virtual where while yield abstract""".split())


class Reach(enum.Enum):
    """Which side of rustc's answer a walk errs on, where it cannot know it.

    CERTAIN: only what rustc surely compiles for the host (its dep-info and `--list` are the oracle);
    a file or path wrongly believed compiled is one a gate stops asking about. POSSIBLE
    (`verify_runner`'s `@reach:` digest scopes): every file rustc may compile; there a missed file
    keeps a stale digest fresh. They differ where rustc's answer depends on more than this reads: a
    `mod` or `include!` in a macro body (expanded where it is invoked) or `mod $x`; a `cfg` the host
    facts do not decide (`rust_cfg.cfg`), the cfg of a block's owner included; a `cfg_attr` that may
    add a `cfg` or `path`; an escaped `path` value; an `include!` that is not one literal at item
    level, or whose file opens with an inner attribute (an error there); a by-name `mod x;` in a
    block, or with a non-ASCII name (errors); E0761; `clean mod`; a file it cannot lex as rustc does.
    CERTAIN follows none of them; POSSIBLE ignores `cfg`, follows every candidate it can read and,
    where it cannot place a file, takes every `.rs` under every directory in force. MAYBE (the
    selectors gate's "cannot say" for an empty `--test` target) is POSSIBLE less what the facts
    decide FALSE, and a macro_rules! body places files only once its name is invoked in what it walked.
    """

    CERTAIN = "certain"
    POSSIBLE = "possible"
    MAYBE = "maybe"


_LOADED: dict[Path, object] = {}


def _load(rel: Path):
    """A sibling script, imported rather than re-typed: copies drift."""
    if rel not in _LOADED:
        ref = REPO / rel
        spec = importlib.util.spec_from_file_location(f"_clean_{rel.stem}", ref)
        if not ref.is_file() or spec is None or spec.loader is None:
            raise SystemExit(f"cannot load {ref}")
        mod = importlib.util.module_from_spec(spec)
        # Consumers inventory this source, not an existing bytecode cache.
        exec(compile(ref.read_bytes(), str(ref), "exec", dont_inherit=True), mod.__dict__)
        _LOADED[rel] = mod
    return _LOADED[rel]


def _lexer():
    """R9's reference lexer from scripts/check_add_decl_ratchet.py."""
    mod = _load(LEXER)
    return mod.NONCODE_RE, mod.strip_noncode, mod.strip_comments_keep_strings


def strip_noncode(text: str) -> str:
    """The reference lexer's `strip_noncode`, for a gate that lexes beside this walk."""
    return _lexer()[1](text)


def rust_cfg():
    """scripts/rust_cfg.py: `cfg`, `host_facts` (the host's platform cfgs) and `host_source`."""
    return _load(CFG)


def _facts(reach: Reach, test_cfg: bool, facts: dict | None) -> dict | None:
    """What CERTAIN and MAYBE decide `cfg` from (`facts`, else the host's, and `test`); None: POSSIBLE ignores it."""
    return None if reach is Reach.POSSIBLE else dict(rust_cfg().host_facts() if facts is None else facts, test=test_cfg)


class _Lexed:
    """A file as rustc_lexer reads it: `code` (comments, literals blanked), bracket `pairs`, and `kept`
    (comments blanked: a `path`, `include!` or `cfg` value IS a literal), same offsets, made on first use."""

    def __init__(self, code: str, pairs: dict[int, int], text: str) -> None:
        self.code, self.pairs, self._text, self._kept = code, pairs, text, None

    @property
    def kept(self) -> str:
        if self._kept is None:
            self._kept = _lexer()[2](self._text)
        return self._kept


def _divergence(noncode: re.Pattern[str], text: str) -> int | None:
    """Where the reference lexer first reads `text` otherwise than rustc_lexer: a block comment
    holding another `/*`, or a `'\\` left in code."""
    prev = 0
    for m in noncode.finditer(text):
        q = text.find("'\\", prev, m.start())
        if q >= 0 or (m.group().startswith("/*") and "/*" in m.group()[2:]):
            return q if q >= 0 else m.start()
        prev = m.end()
    q = text.find("'\\", prev)
    return q if q >= 0 else None


def _lex(raw: str) -> _Lexed | None:
    """`raw` as rustc's lexer reads it, or None. Each span the reference lexer misreads is blanked as
    rustc reads it and the text lexed again; None for a span it cannot repair, or unbalanced brackets."""
    noncode, strip_noncode, _ = _lexer()
    text = raw
    while (at := _divergence(noncode, text)) is not None:
        end, depth = None, 0
        if text[at] == "'":
            end = (c := ESC_CHAR.match(text, at)) and c.end()
        else:
            for t in NEST.finditer(text, at):
                depth += 1 if t.group() == "/*" else -1
                if not depth:
                    end = t.end()
                    break
        if not end:
            return None
        text = text[:at] + re.sub(r"[^\n]", " ", text[at:end]) + text[end:]
    code = strip_noncode(text)
    stack: list[int] = []
    pairs: dict[int, int] = {}
    for b in re.finditer(r"[{}()\[\]]", code):
        if b.group() in OPEN:
            stack.append(b.start())
        elif not stack or OPEN.index(code[stack[-1]]) != CLOSE.index(b.group()):
            return None
        else:
            pairs[stack.pop()] = b.start()
    return None if stack else _Lexed(code, pairs, text)


def _attrs(lx: _Lexed, lo: int, hi: int, inner: bool) -> list[tuple[str, int]]:
    """(code, offset) of each attribute body: the inner `#![..]` run opening at `lo`, or the outer
    `#[..]` groups in code[lo:hi], an item's own region."""
    out = []
    while m := (INNER.match(lx.code, lo) if inner else ATTR.search(lx.code, lo, hi)):
        close = lx.pairs[m.end() - 1]
        if inner or not m.group("bang"):
            out.append((lx.code[m.end():close], m.end()))
        lo = close + 1
    return out


def _str(m: re.Match[str] | None) -> str | None:
    return None if m is None else m.group("raw") if m.group("raw") is not None else m.group("s")


def _verdict(lx: _Lexed, groups: list[tuple[str, int]], certain: bool, facts: dict | None
             ) -> tuple[list[str], bool, bool, bool]:
    """(the `path` values in force, whether rustc may look the module up by name, whether the item
    is compiled -- surely (CERTAIN), or possibly (MAYBE: no `cfg` the facts decide false; POSSIBLE,
    `facts` None: always) -- and whether POSSIBLE/MAYBE must widen). CERTAIN takes rustc's first
    `#[path]`, and is unsure of a `cfg` the facts do not decide true, a `cfg_attr` that may add a
    `cfg` or `path`, and a value it cannot read; the others take every `path` value in any attribute.
    """
    paths, firsts, sure, wide, off = [], [], True, False, False
    for code, at in groups:
        head = re.match(rf"{WS}*(\w+){WS}*", code)
        name, rest = (head.group(1), head.end()) if head else ("", 0)
        if name == "cfg" and facts is not None:
            val = rust_cfg().cfg(lx.kept[at + rest:at + len(code)] if "=" in code else code[rest:], facts)
            sure, off = sure and val is True, off or val is False
        elif name == "cfg_attr":
            sure &= not re.search(r"\b(?:cfg|cfg_attr|path)\b", code[rest:])
        for k in re.finditer(rf"\bpath{WS}*=", code) if name in ("path", "cfg_attr") else ():
            val = _str(LIT.match(lx.kept, at + k.end()))
            wide, sure = wide or val is None, sure and val is not None
            paths += [] if val is None else [val]
            firsts += [val] if val is not None and name == "path" else []
    if certain:
        return firsts[:1], not firsts, sure, False
    return paths, not firsts, not off, wide


def _segment(raw: str | None, name: str) -> str:
    return f"r#{name}" if raw and name in KEYWORDS else name


def _join(modpath: str | None, seg: str) -> str | None:
    return None if modpath is None else f"{modpath}::{seg}" if modpath else seg


def _macro(rcode: str, at: int) -> str:
    """"" when the bracket at len(rcode) - at opens no macro's tokens; else the
    name a `macro_rules!` there defines, or "!" and the macro invoked."""
    m = MACRO_BEFORE.match(rcode, at)
    if m is None:
        return ""
    call, defn = m.group("call")[::-1], m.group("defn")
    return defn[::-1] if call == "macro_rules" and defn else f"!{call}"


def _fn_body(lx: _Lexed, i: int) -> int | None:
    """Where the `fn` item whose signature starts at `i` opens its body: the
    first `{` at its own level that is no const generic argument, or None."""
    while b := FN_SIG.search(lx.code, i):
        if b.group() == ";":
            return None
        if b.group() == "{" and not CONST_ARG.search(lx.code, max(0, b.start() - 80), b.start()):
            return b.start()
        i = lx.pairs[b.start()] + 1
    return None


def _opens_inner(raw: str, code: str) -> bool:
    """Whether a file opens with an inner attribute or inner doc comment, which an `include!`d file may
    not (rustc: E0753, "an inner attribute is not permitted in this context")."""
    first = len(code) - len(code.lstrip())
    docs = (m.group().startswith(("//!", "/*!")) for m in _lexer()[0].finditer(raw, 0, first))
    return bool(INNER.match(code)) or any(docs)


def _file(lx: _Lexed, ctx: tuple, certain: bool, facts: dict | None, fns: list | None = None,
          macs: list | None = None):
    """Scan one lexed file loaded in `ctx`: (children, directories in force, whether POSSIBLE/MAYBE
    must widen, the macro_rules! names MAYBE widens for once invoked). A child is (file, directory in
    force, its `relative`, the directory its `#![path]` joins to, module path, how it is loaded:
    "mod", "include" or "leaf"). With `fns`, each `fn` item in a module libtest can name goes in as
    (its path, its outer attribute bodies); with `macs` each item-level macro group there, as
    (`_macro`'s answer, the outer attribute bodies in its tokens)."""
    cur, d0, rel0, decl, modpath = ctx
    code = lx.code
    rcode = code[::-1]
    children: list[tuple] = []
    defer: set[str] = set()
    paths, by_name, sure, wide = _verdict(lx, _attrs(lx, 0, 0, True), certain, facts)
    ctxs = [((decl / p).parent, None, False) for p in paths] if decl else []
    ctxs += [(d0, rel0, False)] if by_name or decl is None else []
    dirs = {c[0] for c in ctxs}
    # One frame per open bracket: [where the next item's attributes start, the (directory, relative,
    # in-a-block) contexts in force, the macro whose tokens these are ("" none; `_macro`), the module
    # path an item here takes (None: not one libtest can name, or not compiled), at item level,
    # items here compiled].
    frames: list[list] = [[0, ctxs if sure else [], "", modpath if sure else None, True, sure]]
    scan, pos = SCAN if fns is None else SCAN_FN, 0

    def unplaced(mac: str) -> None:  # POSSIBLE widens; MAYBE waits, in a macro_rules! body, for its call
        nonlocal wide
        if mac and not mac.startswith("!") and facts is not None:
            defer.add(mac)
        else:
            wide = True

    while m := scan.search(code, pos):
        pos, top, item = m.end(), frames[-1], m.lastgroup  # "mod", "inc", "fn", or None: a bracket or `;`
        if item is None:
            tok = m.group()
            if tok == ";":
                top[0] = m.end()
            elif tok in OPEN:
                # A group holding no `mod` or `include` changes nothing here but where the next
                # item's attributes start, so it is jumped (fn_items jumps every one: nothing in a
                # block or a macro's tokens is a path libtest can name).
                close = lx.pairs[m.start()]
                if fns is not None or code.find("mod", pos, close) < 0 and code.find("include", pos, close) < 0:
                    if macs is not None and top[3] is not None and (mac := _macro(rcode, len(code) - m.start())) \
                            not in ("", "!") and _verdict(lx, _attrs(lx, top[0], m.start(), False), certain, facts)[2]:
                        macs.append((mac, [c for c, _ in _attrs(lx, pos, close, False)]))
                    pos = close + 1
                    top[0] = pos if tok == "{" else top[0]
                    continue
                mac = top[2] or _macro(rcode, len(code) - m.start())
                # The item that owns a block decides it: `#[cfg(..)] fn f() { #[path] mod x; }`,
                # or `#![cfg(..)]` opening the body, strips everything in it (2026-11-01 review).
                own = not mac and _verdict(lx, _attrs(lx, top[0], m.start(), False)
                                           + (_attrs(lx, pos, 0, True) if tok == "{" else []), certain, facts)[2]
                ctx_in = [(d, None, True) for d, _, _ in top[1]] if own else []
                frames.append([pos, ctx_in, mac, None, False, top[5] and own])
            else:
                frames.pop()
                if tok == "}":
                    frames[-1][0] = m.end()
            continue
        if item == "fn":
            groups = _attrs(lx, top[0], m.start(), False)
            body = _fn_body(lx, m.end())  # a `#![cfg]` opening the body strips the fn (2026-11-01 review)
            inner = [] if body is None else _attrs(lx, body + 1, 0, True)
            if top[3] is not None and _verdict(lx, groups + inner, certain, facts)[2]:
                fns.append((_join(top[3], _segment(m.group("fraw"), m.group("fname"))), [c for c, _ in groups]))
            continue
        if item == "inc":
            arg = INC_ARG.match(code, m.end())
            if certain:  # one literal at item level, surely compiled; resolved beside the file
                val = arg and _str(INC_ONLY.fullmatch(lx.kept, arg.end(), lx.pairs[arg.end() - 1]))
                ok = val and top[4] and top[5] and _verdict(lx, _attrs(lx, top[0], m.start(), False), True, facts)[2]
            else:  # in a macro body it resolves where the macro is invoked (2026-11-01 review)
                val = _str(LIT.match(lx.kept, arg.end())) if arg else None
                ok = bool(val) and (facts is None or top[5])  # MAYBE: not where a cfg decides it false
                if val is None or top[2]:
                    unplaced(top[2])
            children += [(cur.parent / val, (cur.parent / val).parent, None, None, top[3], "include")] if ok else []
            continue
        name, inline, clean = m.group("name"), m.group("kind") == "{", m.group("clean")
        groups = _attrs(lx, top[0], m.start(), False) + (_attrs(lx, m.end(), 0, True) if inline else [])
        paths, by_name, sure, w = _verdict(lx, groups, certain, facts)
        unknown = bool(top[2]) or m.group("dollar") is not None
        wide |= w
        if unknown and not certain:
            unplaced(top[2])
        ctxs = [] if unknown or not sure else top[1]
        sub = None if unknown or not sure else _join(top[3], _segment(m.group("raw"), name))
        if inline:
            new = [(d / p, None, False) for d, _, _ in ctxs for p in paths]
            new += [((d / rel if rel else d) / name, None, u) for d, rel, u in ctxs if by_name]
            dirs.update(c[0] for c in new)
            frames.append([m.end(), new, top[2], sub, True, top[5] and sure and not unknown])
            continue
        top[0] = m.end()
        for d, rel, unowned in [] if clean and certain else ctxs:
            found = [(d / p, (d / p).parent, None, None, sub, "mod") for p in paths]
            base = d / rel if rel else d
            flat, nested = base / f"{name}.{'clean' if clean else 'rs'}", base / name / "mod.rs"
            # E0761 (both files) and E0754 (a non-ASCII name looked up by name) fail the crate
            if by_name and not (certain and (unowned or not name.isascii() or flat.exists() and nested.exists())):
                found += [(flat, base, name, d, sub, "mod")] + ([] if clean else [(nested, base / name, None, d, sub, "mod")])
            # a .clean unit is a leaf: Clean text, never walked as Rust
            children += [f[:5] + ("leaf",) for f in found] if clean else found
    return children, dirs, wide, defer


def walk(root: Path, reach: Reach = Reach.CERTAIN, unreadable: set[Path] | None = None,
         test_cfg: bool = True, facts: dict | None = None) -> set[tuple[Path, str | None]]:
    """Every (file, module path) rustc compiles from the crate root `root`.

    Files are resolved; `root` is taken as given (rustc resolves beside the path it is handed, not
    beside a symlink's target), and its module path is "". A path is None where libtest can name no
    test: a module in a block (fn body, const block; rustc warns "cannot test inner items", --list
    omits it), and outside CERTAIN also a file placed by widening, whose path is unknown.

    rustc's own resolution (`compiler/rustc_expand/src/module.rs`): a crate
    root, a `mod.rs`, and every `#[path]` or `include!`d file own their
    directory (`mod x;` is `x.rs` or `x/mod.rs` beside them); any other `y.rs`
    owns `y/`; `mod z { .. }` puts `z/` (after `y/`) in force, or the `p` of a
    `#[path = "p"]` / `#![path = "p"]` on it; a loaded file's `#![path]` moves
    its children when no outer `#[path]` won; `#[path = "p"] mod x;` is `p`
    joined to the directory in force, read from the item's own attributes; a
    block drops `y/`, and a by-name `mod x;` there is an error; a `#[cfg]` that
    strips the item (a block's owner included), or a `#![cfg]` that strips a
    loaded file or a block, stops the walk there (that file is still loaded).
    `include!("p")` at item level splices `p` (beside the INVOKING file, in any
    module) at the module path in force, and the `mod`s in `p` resolve beside
    `p` (rustc_builtin_macros' expand_include). A file re-entered on its own
    load chain (circular modules, include! recursion: rustc errors) is not
    walked again.

    `reach`: see `Reach`; `unreadable` collects (CERTAIN) each file this cannot lex as rustc does,
    (MAYBE) each whose items it could not place (unlexable, an unreadable value, a macro's `mod` or
    `include!` once invoked); `test_cfg` is False for a `harness = false` target; `facts` (the host's
    when None; and `test`) decide CERTAIN's and MAYBE's cfgs. Known POSSIBLE gaps: a macro's `#[path]`
    or `include!` reaching outside every directory in force; a macro from another crate (and for
    MAYBE a macro_rules! invoked under another name).
    """
    certain, maybe = reach is Reach.CERTAIN, reach is Reach.MAYBE
    facts = _facts(reach, test_cfg, facts)
    out, files, walked, dirs, wide = set[tuple](), set[Path](), set[tuple](), set[Path](), False
    defer: dict[str, set[Path]] = {}  # MAYBE: macro_rules! name -> the files whose items wait for its call
    calls: set[str] = set()
    stack: list[tuple] = [(root, root.parent, None, None, "", "mod", ())]
    while True:
        if not stack and (wide or calls & defer.keys()):
            stack = [(p, p.parent, None, None, None, "mod", ()) for d in sorted(dirs) for p in sorted(d.rglob("*.rs"))
                     if p.is_file() and p.resolve() not in files]
        if not stack:
            if maybe and unreadable is not None:
                unreadable.update(f for n in calls & defer.keys() for f in defer[n])
            return out
        cur, d0, rel0, decl, modpath, how, chain = stack.pop()
        if not cur.is_file() or (real := cur.resolve()) in chain:
            continue
        key = (real, d0.resolve(), rel0, decl and decl.resolve(), modpath, how)
        if key in walked:
            continue
        walked.add(key)
        raw = "" if how == "leaf" else cur.read_text(encoding="utf-8-sig", errors="replace")
        # CERTAIN skips the lexer where nothing can be declared; the others lex all (widening reads dirs).
        worth = not certain or how == "include" or any(p.search(raw) for p in WORTH_LEXING)
        lx = _lex(raw) if worth else _Lexed("", {}, "")
        if certain and how == "include" and (lx is None or _opens_inner(raw, lx.code)):
            (unreadable if lx is None and unreadable is not None else set()).add(real)
            continue
        out.add((real, modpath))
        files.add(real)
        dirs.add(cur.parent)
        if lx is None:
            (unreadable if (certain or maybe) and unreadable is not None else set()).add(real)
            wide |= not certain
            continue
        if how == "leaf" or not lx.code:
            continue
        calls |= set(CALL.findall(lx.code)) - {"macro_rules"} if maybe else set()
        children, more, w, names = _file(lx, (cur, d0, rel0, decl, modpath), certain, facts)
        dirs |= more
        wide |= w
        (unreadable if maybe and w and unreadable is not None else set()).add(real)
        for n in names:
            defer.setdefault(n, set()).add(real)
        stack += [c + (chain + (real,),) for c in children]


def reachable_from(root: Path, reach: Reach = Reach.CERTAIN, unreadable: set[Path] | None = None,
                   test_cfg: bool = True, facts: dict | None = None) -> set[Path]:
    """Every file (resolved) rustc compiles from the crate root `root` (`walk`)."""
    return {f for f, _ in walk(root, reach, unreadable, test_cfg, facts)}


def _items(path: Path, modpath: str | None, reach: Reach, test_cfg: bool, facts: dict | None, macs: list | None):
    """(`path` lexed, or None; its `fn` items, `macs` filled): fn_items' and macro_items' one scan."""
    lx, fns = _lex(path.read_text(encoding="utf-8-sig", errors="replace")), []
    if lx is not None and modpath is not None:
        _file(lx, (path, path.parent, None, None, modpath), reach is Reach.CERTAIN, _facts(reach, test_cfg, facts), fns,
              macs)
    return lx, fns


def fn_items(path: Path, modpath: str | None, reach: Reach = Reach.CERTAIN, test_cfg: bool = True,
             facts: dict | None = None) -> list[tuple[str, list[str]]]:
    """(libtest path, outer attribute bodies) of each `fn` item of `path`,
    loaded at `modpath` (as `walk` gives it), in a module libtest can name:
    not in a block, a macro body, or under a `cfg` (its own, its body's
    `#![cfg]`, or its module's) the facts do not decide true (CERTAIN) or
    decide false (MAYBE). A file it cannot lex as rustc does has none."""
    return [] if modpath is None else _items(path, modpath, reach, test_cfg, facts, None)[1]


def macro_items(path: Path, modpath: str | None, reach: Reach = Reach.MAYBE, test_cfg: bool = True,
                facts: dict | None = None) -> tuple[list[tuple[str, list[str]]], set[str]]:
    """(each item-level macro group of `path` in a module libtest can name, as (the `macro_rules!` name
    it defines, or "!" and the macro it invokes; the outer attribute bodies in its tokens)), and every
    macro its code invokes anywhere (at any module path): where a test a macro writes may come from."""
    macs: list[tuple[str, list[str]]] = []
    lx, _ = _items(path, modpath, reach, test_cfg, facts, macs)
    return macs, (set(CALL.findall(lx.code)) - {"macro_rules"} if lx is not None else set())


def selftest() -> int:
    """Run the walk's own arms (rust_modules_arms.py): their count, or SystemExit naming the first that fails."""
    return _load(ARMS).run(types.SimpleNamespace(walk=walk, fn_items=fn_items, macro_items=macro_items, Reach=Reach,
                                                 cfg=rust_cfg().cfg, rust_cfg=rust_cfg()))
