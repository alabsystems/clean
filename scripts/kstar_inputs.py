#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Q4's source inputs: a coarse lexical conjunct of `kstar_recheck --check-record`.

Freshness rests on the members' own build read sets (`kstar_recheck.build_reads`,
from cargo's dep-info; docs/DECISIONS.md, 2026-11-19, "Q4 freshness rests on the
members' build read sets"). This rule no longer decides it alone: it is one
conjunct, and the set `receipt.py`'s clean-tree check reads. A record is stale
when one of these files moves, and not knowable when `inputs` raises, whatever
the build read set says. The rule claims no more than this docstring lists: for each form under
"Evaluated" the file stock rustc or cargo reads is an input, each form under
"Refused" raises, and the rule says nothing about any other form (docs/DECISIONS.md,
2026-11-19, "Q4 source inputs: evaluate an include or refuse", and its corrections).
"Evaluated" holds only forms this repository's own tree uses; that entry names the
use behind each one. Each listed form, or group sharing one branch, has a self-test
arm over a synthetic tree (`kstar_selftest.FORM_ARMS` and `REFUSALS`); where stock
rustc or cargo builds the tree, the arm checks what it reads
(`KSTAR_STOCK_RUSTC`/`_CARGO`).

Hashed: (1) the caller's fixed files, every `.rs` and `.toml` under crates/ and
every `.lean` and `.toml` under theories/cic_l; (2) every git-tracked file under
crates/; (3) every manifest of the workspace and every package one reaches, and
every tracked file of such a package outside crates/; (4) what the evaluated forms
name, from those packages' Rust sources and every file they reach; (5) for a build
script, the repository files its string literals name (relative to its file, its
package or a directory above), the reads its row in data/kstar_build_reads.json
declares, and each repository path named by a file its literals or includes
name, or by a file its row declares as data (one level). A mention in a comment
or a string literal (the reference lexer in `check_add_decl_ratchet.py` decides
which) adds only what a plain-literal argument names.

Evaluated (a plain literal is `"..."` with no prefix and no backslash):
- `include_str!`, `include_bytes!` and `include!`, unqualified and written `name!(`,
  of one plain literal: relative to the file it is written in;
- `include_str!` and `include_bytes!` of `concat!(env!("CARGO_MANIFEST_DIR"), "/...")`
  (one plain literal after it): relative to each package the file is read for,
  when the file's package lies inside no other package directory and has no build
  script or one whose row lists, under `rustc_env`, every cargo:rustc-env key it
  can print, CARGO_MANIFEST_DIR not among them;
- `include!(concat!(env!("OUT_DIR"), "/<name>"))`, <name> one file name the
  package's build-script row lists under `out_dir` (the row's review says that
  file holds no include), OUT_DIR not among its `rustc_env` keys: no repository file;
- an include in a `macro_rules!` body whose argument is one plain literal or a
  `concat!` of plain literals and one metavariable, `$x` of fragment `literal`
  that every invocation binds to one plain literal or `stringify!($x)` of
  fragment `ident`: relative to the file of each invocation in the macro's
  package (rustc reads it against the outermost invocation's file), `$x` ranging
  over the literals or identifiers those invocations, or the macro's own
  recursive ones, pass;
- `#[path = "..."]` (one plain literal) on `mod x;` outside any inline module:
  relative to the directory of the file it is written in;
- `mod x;` outside any inline module, in a file reached outside crates/ or in a
  build script's closure: `x.rs` and `x/mod.rs` under the file's directory and
  under its stem directory;
- Cargo manifests, parsed with tomllib: every `path` string (dependency, `[patch]`
  and target tables) and plain `members`, `exclude` and `default-members` entries;
- a build script at `build.rs` none of whose module-closure files names a word of
  `FS_RE` in code (the file system, processes, the network, `unsafe`, `extern`,
  `asm!`) or a link flag, and whose package has no build-dependencies: it reads
  its closure; any other build script, through its row;
- `.cargo/config.toml` and `.cargo/config` at the root and at each directory
  between it and a package, holding only `build.jobs`, `rustflags` made of
  `-C target-cpu=<name>` pairs under `[build]` or `[target.<t>]`, `[env]
  RUST_MIN_STACK` (a value, optionally with `force`) and `[alias]`.

Refused:
- in the code of any scanned Rust file: a character outside ASCII; a `use` that
  renames `include_str`, `include_bytes`, `include`, `concat`, `stringify` or
  `env`, or a `macro_rules!` that defines one of them; a macro invoked through a
  metavariable (`$m!`) or by a computed name in a macro body; a `mod` declared in
  a macro body; the `macro` keyword;
- an include written another way: path-qualified, as a raw identifier, or with a
  space, a comment or a delimiter other than `(` after its name;
- an include argument of any other shape: a number (decimal or not), a boolean,
  `stringify!` outside a macro body, a string literal with a prefix or a
  backslash, a `concat!` with no metavariable and no `env!`, a qualified or raw
  `concat!`, `env!` or `stringify!`, any other `env!` name, another piece around
  `env!`, more than one metavariable; an include that names no repository file;
- an `env!` include in a file whose package lies inside another package
  directory; a CARGO_MANIFEST_DIR or OUT_DIR include in a package whose build
  script has no row with `rustc_env` for its closure, or lists that key there;
  an OUT_DIR include of another shape or of a file its row does not list, and
  one in a package without a build script;
- for an include in a macro body: an exported macro, one a `use` renames anywhere
  in its package, one defined inside another macro or invoked inside a different
  one, an `include!`, an `env!`, a build script's macro, a fragment other than
  `literal` for `$x` or `ident` for `stringify!($x)`, and a `literal` macro an
  invocation passes anything but plain literals;
- a `#[path]` written another way (a value other than one plain literal,
  `r#path`, `#![path]`, `# [`, a comment in the attribute), inside `cfg_attr`, on
  an inline module or an item other than `mod x;`, inside an inline module, or
  naming no file; `mod x;` inside an inline module or naming no file where it is
  evaluated;
- a symbolic link under crates/, an input reached through one, and a read through
  one (the OS resolves `..` after a link physically);
- in a manifest: a `build` key, a `package.workspace` key, a members, exclude or
  default-members entry with a glob character, a target `path` outside its
  package directory, a package at the workspace root, a path dependency outside
  the repository, and a manifest tomllib cannot read (or a Python without tomllib);
- in Cargo configuration at any level above: every other key or value, among
  them `build.rustc-wrapper`, `rustc-workspace-wrapper`, `rustc`, `rustdoc` and
  `target-dir`, `target.<t>.linker` and `runner`, any other flag, any other
  `[env]` name or `relative`, `include`, `paths`, `[patch]` and `[source]`;
- a build script outside the evaluated class (a read through `format!`, a `join`
  chain or `read_dir` among them) unless data/kstar_build_reads.json declares its
  reads for its closure's exact digest (its module closure's bytes and its
  build-dependencies tables).

Not seen, and not claimed: what a procedural macro or a macro from outside the
repository reads; a builtin name bound by an import from another crate (plain,
glob or `#[macro_use]`); what a declared build script reads, prints or writes
beyond its row (a row is a review, not a measurement) and anything outside the
repository (toolchains, git metadata, the environment, Cargo configuration
outside the repository, rustflags from the environment and linker inputs); a
file git does not track that a build finds without a listed form (a target cargo
discovers by its location); reads at run time; and every form not listed above. A later finding adds a form to
this list or to "Refused"; it does not make a listed form wrong unless its arm is.

Known misses, left unfixed because the rule no longer decides freshness alone
(the fourth adversarial round, 2026-11-19): a char literal holding `"` (`'"'`,
`b'"'`) starts a string token in `TOKEN_RE`, hiding the identifiers of a macro
invocation and the `path` of a `cfg_attr`; a manifest that spells `[package]` as
`[project]` escapes the `build`-key, root-package and build-script refusals; a
`mod x { .. }` a macro makes is not refused, so `mod`/`#[path]` resolve against
the wrong directory; a file one package reaches through another package's `mod`
is read for the wrong package; a link flag built with `format!` or `concat!`
leaves a build script in the auto class; and `#![debugger_visualizer(..)]` is in
neither list. Stock rustc's dep-info lists each read rustc makes in these cases
(the round's probes), and cargo's dep-info for a member carries every local
unit's; it lists neither a native link input nor a file a build script reads
without naming it in rerun-if-changed (measured).
"""
import argparse
import bisect
import functools
import glob
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

import check_add_decl_ratchet as reference_lexer

ANSWERS_PINNED_INPUTS = True
BUILD_DECLARATIONS = 'data/kstar_build_reads.json'
INCLUDE_RE = re.compile(r'\b(include_str|include_bytes|include)\s*!\s*([(\[{])')
PATH_KV_RE = re.compile(r'path\s*=\s*(?=[bc]?r#*"|b?")')
ATTR_HEAD_RE = re.compile(r'(?:#!?\[\s*|\bcfg_attr\s*\([^\]]*?,\s*)\Z')
MOD_RE = re.compile(r'\bmod\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)\s*;')
INLINE_MOD_RE = re.compile(r'\bmod\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)\s*([{])')
ITEM_MOD_RE = re.compile(r'(?:(?:pub\s*(?:\([^()]*\))?|unsafe|clean)\s+)*(?P<mod>mod)\s+(?:r#)?[A-Za-z_]\w*\s*([;{])')
WHITESPACE_RE = re.compile(r'\s*')
STRING_RE = re.compile(r'(?<![A-Za-z0-9_\'])[bc]?r(#*)"(.*?)"\1|b?"((?:\\.|[^"\\])*)"', re.S)
PLAIN_RE = re.compile(r'"[^"\\]*"')
TOKEN_RE = re.compile(r'\s+|(?P<str>(?<![A-Za-z0-9_\'])[bc]?r(#*)"(?:.*?)"\2|b?"(?:\\.|[^"\\])*")'
                      r'|(?P<num>\d[0-9A-Za-z_]*(?:\.\d[0-9A-Za-z_]*)?)'
                      r'|(?P<id>\$?(?:r#)?[A-Za-z_][A-Za-z0-9_]*)|(?P<p>.)', re.S)
MACRO_DEF_RE = re.compile(r'\bmacro_rules\s*!\s*(?:r#)?([A-Za-z_][A-Za-z0-9_]*)\s*([(\[{])')
DELIM_RE = re.compile(r'[()\[\]{}]')
DATA_TOKEN_RE = re.compile(r'[^\s"\'`,;()\[\]{}<>=|]+')
OUT_NAME_RE = re.compile(r'/[A-Za-z0-9_][A-Za-z0-9_.-]*')
TARGET_CPU_RE = re.compile(r'target-cpu=[A-Za-z0-9_.-]+')
# Forms refused wherever they are in code: a builtin macro renamed or shadowed, a
# macro named by a metavariable or a computed group, a module declared in a macro
# body, and a `macro` 2.0 item.
BUILTIN_WORD_RE = re.compile(r'\b(?:include_str|include_bytes|include|concat|stringify|env)\b')
BUILTIN = r'(?:r#)?(?:include_str|include_bytes|include|concat|stringify|env)\b'
INCLUDE_WORD_RE = re.compile(r'(?<![\w$])(?:r#)?(include_str|include_bytes|include)\b')
SHADOW_RE = re.compile(rf'\b{BUILTIN}\s*as\b|\bas\s+{BUILTIN}')
SHADOW_DEF_RE = re.compile(rf'\bmacro_rules\s*!\s*{BUILTIN}')
USE_KW_RE, AS_RE, MACRO_KW_RE = re.compile(r'\buse\b'), re.compile(r'\bas\b'), re.compile(r'\bmacro\b')
METAVAR_RE = re.compile(r'\$(?:r#)?[A-Za-z_]\w*')
NON_ASCII_RE, HASH_RE, MACRO_EXPORT_RE = re.compile(r'[^\x00-\x7f]'), re.compile('#'), re.compile(r'\bmacro_export\b')
GROUP_CALL_RE = re.compile(r'[)\]]\s*(?:[^\s()\[\]{}]{0,3}?\s*[*+?])?\s*!\s*[(\[{]')
MACRO_MOD_RE = re.compile(r'\bmod\s+(?:r#)?\$?[A-Za-z_]\w*\s*;')
# A build script that names one of these (in code), or links (in a string), can
# read files the rule cannot evaluate; it needs a reviewed declaration.
FS_RE = re.compile(r'\b(?:fs|File|OpenOptions|process|Command|net|read_dir|read_link|metadata|symlink_metadata'
                   r'|exists|try_exists|is_file|is_dir|is_symlink|canonicalize|extern|asm|global_asm|naked_asm'
                   r'|unsafe|concat_idents)\b')
LINK_RE = re.compile(r'rustc-(?:link|flags|cdylib)')
CLOSE = {'(': ')', '[': ']', '{': '}'}
TARGET_TABLES = ('lib', 'bin', 'test', 'example', 'bench')
SIMPLE_ESCAPES = {'n': '\n', 't': '\t', 'r': '\r', '0': '\0', '\\': '\\', '"': '"', "'": "'"}
END = [('end', '', '')] * 4


def unescape(text):
    """A Rust string literal's value (for mentions and build-script literals only)."""
    def one(m):
        e = m.group(1)
        if e[0] == 'x':
            return chr(int(e[1:], 16))
        if e[0] == 'u':
            return chr(int(e[2:-1].replace('_', ''), 16))
        return SIMPLE_ESCAPES.get(e[0], '')  # '' for a backslash-newline continuation
    return re.sub(r'\\(x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f_]+\}|\n\s*|.)', one, text)


def path_attributes(src):
    """Each `path = "..."` that looks like a `#[path]` or a `cfg_attr` path: mentions only."""
    for m in PATH_KV_RE.finditer(src) if 'path' in src else ():
        before = src[m.start() - 1:m.start()]
        if not (before.isalnum() or before == '_') and ATTR_HEAD_RE.search(src, max(0, m.start() - 400), m.start()):
            yield m


def literal_value(m):
    return m.group(2) if m.group(2) is not None else unescape(m.group(3))


def tokens(body):
    """(kind, value, source text) of each token, then END; a string's value is unescaped."""
    out = []
    for m in TOKEN_RE.finditer(body):
        kind = m.lastgroup if m.lastgroup in ('num', 'id', 'p') else 'str' if m.group('str') else None
        if kind == 'str':
            out.append(('s', literal_value(STRING_RE.fullmatch(m.group('str'))), m.group('str')))
        elif kind:
            out.append((kind, m.group(kind), m.group(kind)))
    return out + END


def plain(token):
    """The value of a plain string literal token (no prefix, no backslash), or None."""
    return token[2][1:-1] if token[0] == 's' and PLAIN_RE.fullmatch(token[2]) else None


def group(ts, i):
    """(comma-separated parts, index after the close) of the group opening at ts[i]; (None, i) if unclosed."""
    depth, parts, part, j = 0, [], [], i + 1
    while ts[j][0] != 'end':
        kind, value = ts[j][:2]
        if kind == 'p' and value in CLOSE:
            depth += 1
        elif kind == 'p' and value in ')]}':
            if depth == 0:
                return parts + [part], j + 1
            depth -= 1
        elif (kind, value, depth) == ('p', ',', 0):
            parts, part, j = parts + [part], [], j + 1
            continue
        part.append(ts[j])
        j += 1
    return None, i


def call(ts, name):
    """The arguments of `name!( ... )` filling `ts` (tokens then END) exactly, or None."""
    if ts[0][:2] == ('id', name) and ts[1][:2] == ('p', '!') and ts[2][:2] == ('p', '('):
        parts, j = group(ts, 2)
        return parts if parts is not None and ts[j][0] == 'end' else None
    return None


def piece(part):
    """One `concat!` argument: a plain literal's value, ('env', name), ('$', name, how), or None."""
    ts = part + END
    if ts[1][0] == 'end' and plain(ts[0]) is not None:
        return plain(ts[0])
    if ts[1][0] == 'end' and ts[0][0] == 'id' and re.fullmatch(r'\$[A-Za-z_]\w*', ts[0][1]):
        return ('$', ts[0][1][1:], 'concat')
    args = call(ts, 'env')
    if args is not None and len(args) == 1 and len(args[0]) == 1 and plain(args[0][0]) in ('CARGO_MANIFEST_DIR', 'OUT_DIR'):
        return ('env', plain(args[0][0]))
    args = call(ts, 'stringify')
    if args is not None and len(args) == 1 and len(args[0]) == 1 and re.fullmatch(r'\$[A-Za-z_]\w*', args[0][0][1]):
        return ('$', args[0][0][1][1:], 'stringify')
    return None


def argument_form(ts):
    """The form of an include argument's tokens (then END): ('lit', value);
    ('env', name, value) for `concat!(env!(name), value)`; ('meta', pieces) for a
    `concat!` of plain literals and one metavariable piece; None for any other."""
    if ts[1][0] == 'end' and plain(ts[0]) is not None:
        return ('lit', plain(ts[0]))
    parts = call(ts, 'concat')
    pieces = [piece(p) for p in parts or [[]]]
    if None in pieces:
        return None
    if len(pieces) == 2 and isinstance(pieces[0], tuple) and pieces[0][0] == 'env' and isinstance(pieces[1], str):
        return ('env', pieces[0][1], pieces[1])
    metas = [p for p in pieces if isinstance(p, tuple)]
    return ('meta', pieces) if len(metas) == 1 and metas[0][0] == '$' else None


def mention_form(text):
    """The form of the first argument of an include mentioned in a comment or string, from its delimiter."""
    parts, _ = group(tokens(text[:4096]), 0)
    return argument_form(parts[0] + END) if parts else None


def path_values(ts, where):
    """The value of each `path = ...` an attribute's tokens assign; a `path` written
    other than `path = "..."` refuses, and so does one inside `cfg_attr`."""
    head = ts[0][1] if ts[0][0] == 'id' else None
    if head in ('path', 'r#path'):
        if head == 'path' and ts[1][:2] == ('p', '=') and plain(ts[2]) is not None and ts[3][0] == 'end':
            return [plain(ts[2])]
        raise ValueError(f'{where}: a #[path] attribute other than `#[path = "..."]`')
    if head in ('cfg_attr', 'r#cfg_attr') and ts[1][:2] == ('p', '('):
        parts, _ = group(ts, 1)
        if parts is None:
            raise ValueError(f'{where}: an unbalanced cfg_attr')
        if any(path_values(part + END, where) for part in parts[1:]):
            raise ValueError(f'{where}: a #[path] inside cfg_attr')
    return []


def balanced(code, at):
    """The index of the delimiter closing the one at `at` in blanked code, or None."""
    depth = 0
    for m in DELIM_RE.finditer(code, at):
        depth += 1 if m.group() in '([{' else -1
        if depth == 0:
            return m.start()
    return None


class Source:
    """One source file, read through the reference lexer's spans (comments, strings and
    chars). A match counts only where it starts in code; comments between tokens are
    skipped; text lexed from a position in code is lexed as rustc reads it there."""
    def __init__(self, path, src, rel):
        self.path, self.src, self.rel = path, src, rel

    @functools.cached_property
    def code(self):
        return reference_lexer.strip_noncode(self.src)

    @functools.cached_property
    def noncode(self):
        spans = [m.span() for m in reference_lexer.NONCODE_RE.finditer(self.src)]
        return [a for a, _ in spans], spans

    def in_code(self, at):
        starts, spans = self.noncode
        k = bisect.bisect_right(starts, at) - 1
        return k < 0 or not spans[k][0] <= at < spans[k][1]

    def where(self, at):
        return f'{self.rel}:{self.src.count(chr(10), 0, at) + 1}'

    def matches(self, pattern):
        return [m for m in pattern.finditer(self.src) if self.in_code(m.start())]

    def lexed(self, start, end, keep_strings=False):
        """src[start:end] with comments (and, unless kept, literals) blanked; `start` is in code."""
        text = self.src[start:end]
        return (reference_lexer.strip_comments_keep_strings if keep_strings else reference_lexer.strip_noncode)(text)

    def skip(self, pos):
        """The first position at or after `pos` that is neither whitespace nor in a comment."""
        starts, spans = self.noncode
        while True:
            pos = WHITESPACE_RE.match(self.src, pos).end()
            k = bisect.bisect_right(starts, pos) - 1
            if k < 0 or spans[k][0] != pos or self.src[pos] != '/':
                return pos
            pos = spans[k][1]

    def before(self, pos):
        """The position after the last character before `pos` that is neither whitespace nor in a comment."""
        starts, spans = self.noncode
        while True:
            while pos > 0 and self.src[pos - 1].isspace():
                pos -= 1
            k = bisect.bisect_left(starts, pos) - 1
            if k < 0 or spans[k][1] != pos or self.src[spans[k][0]] != '/':
                return pos
            pos = spans[k][0]

    def after(self, pos, chars):
        pos = self.skip(pos)
        return pos if self.src[pos:pos + 1] and self.src[pos] in chars else None

    def call(self, end):
        """The opening delimiter of a macro call whose name ends at `end`, or None."""
        bang = self.after(end, '!')
        return None if bang is None else self.after(bang + 1, '([{')

    def balanced(self, at):
        """The index of the delimiter in code closing the one at `at`, or None."""
        depth = 0
        for m in DELIM_RE.finditer(self.src, at):
            if self.in_code(m.start()):
                depth += 1 if m.group() in '([{' else -1
                if depth == 0:
                    return m.start()
        return None

    def until(self, pos, char=';'):
        """The first `char` in code at or after `pos`, or the end."""
        while True:
            pos = self.src.find(char, pos)
            if pos < 0 or self.in_code(pos):
                return len(self.src) if pos < 0 else pos
            pos += 1

    def spans(self, pattern):
        """(name, start, opening delimiter, closing delimiter) of each match of `pattern` in code."""
        out = [(m.group(1), m.start(), m.end() - 1, balanced(self.code, m.end() - 1))
               for m in pattern.finditer(self.code)]
        if any(d[3] is None for d in out):
            raise ValueError(f'{self.rel}: an unbalanced delimiter after `{pattern.pattern[:12]}`')
        return out

    @functools.cached_property
    def defs(self):
        return self.spans(MACRO_DEF_RE) if 'macro_rules' in self.src else []

    @functools.cached_property
    def inline(self):
        return self.spans(INLINE_MOD_RE)

    @functools.cached_property
    def attrs(self):
        """{start: (opening bracket, closing bracket, inner)} of each attribute, by bracket balancing in code."""
        out = {}
        for m in self.matches(HASH_RE) if '#' in self.src else ():
            bang = self.after(m.end(), '!')
            open_ = self.after(m.end() if bang is None else bang + 1, '[')
            if open_ is None:
                continue
            close = self.balanced(open_)
            if close is None:
                raise ValueError(f'{self.where(m.start())}: an unbalanced attribute')
            out[m.start()] = (open_, close, bang is not None)
        return out

    @functools.cached_property
    def path_attrs(self):
        """(start, value, position of the `mod` it is on) of each `#[path = "..."]` in code.
        Any other `path` attribute refuses, and so does one off a file-level `mod x;`."""
        out = []
        for start, (open_, close, inner) in self.attrs.items() if 'path' in self.src else ():
            if 'path' not in self.src[open_:close]:
                continue
            body = self.lexed(open_ + 1, close, keep_strings=True)
            values = path_values(tokens(body), self.where(start))
            if not values:
                continue
            if inner or open_ != start + 1 or body != self.src[open_ + 1:close]:
                raise ValueError(f'{self.where(start)}: a #[path] attribute other than `#[path = "..."]`')
            pos = close + 1
            while self.skip(pos) in self.attrs:
                pos = self.attrs[self.skip(pos)][1] + 1
            item = ITEM_MOD_RE.match(self.code, self.skip(pos))
            if item and item.group(2) == '{':
                raise ValueError(f'{self.where(start)}: a #[path] on an inline module')
            if not item:
                raise ValueError(f'{self.where(start)}: a #[path] on an item other than `mod x;`')
            if self.components(start):
                raise ValueError(f'{self.where(start)}: a #[path] inside an inline module')
            out.append((start, values[0], item.start('mod')))
        return out

    def enclosing(self, at):
        return [d for d in self.defs if d[2] < at < d[3]]

    def components(self, at):
        """The names of the inline modules around `at`, outermost first."""
        return [d[0] for d in self.inline if d[2] < at < d[3]]


def refuse_unfollowed(s):
    """Raise for a form in a Rust file's code that the rule does not follow, wherever it is."""
    src, fail = s.src, None
    if not src.isascii():
        _, spans = s.noncode
        gaps = zip([0, *(b for _, b in spans)], [*(a for a, _ in spans), len(src)])
        fail = next(((NON_ASCII_RE.search(src, a, b).start(), 'a character outside ASCII in code')
                     for a, b in gaps if not src[a:b].isascii()), None)
    for u in s.matches(USE_KW_RE) if not fail and BUILTIN_WORD_RE.search(src) else ():
        semi = s.until(u.end())
        if BUILTIN_WORD_RE.search(src, u.start(), semi) and AS_RE.search(src, u.start(), semi) \
                and SHADOW_RE.search(s.lexed(u.start(), semi)):
            fail = (u.start(), 'a builtin include, concat!, stringify! or env! renamed by a use')
            break
    for m in s.matches(METAVAR_RE) if not fail and '$' in src else ():
        if s.call(m.end()) is not None:
            fail = (m.start(), 'a macro invoked through a metavariable')
            break
    for m in s.matches(MACRO_KW_RE)[:1] if not fail and 'macro' in src else ():
        fail = (m.start(), 'the `macro` keyword (a macro 2.0 definition)')
    if fail:
        raise ValueError(f'{s.where(fail[0])}: {fail[1]}')
    s.path_attrs  # a #[path] other than `#[path = "..."]` on a file-level `mod x;` refuses
    for m in SHADOW_DEF_RE.finditer(s.code) if s.defs else ():
        raise ValueError(f'{s.where(m.start())}: a builtin include, concat!, stringify! or env! shadowed')
    for name, _, open_, close in s.defs:
        for pattern, why in ((GROUP_CALL_RE, 'a macro invoked by a computed name'),
                             (MACRO_MOD_RE, 'a module declared')):
            m = pattern.search(s.code, open_, close)
            if m:
                raise ValueError(f'{s.where(m.start())}: {why} in the body of {name}!')


def macro_variants(source, at, pieces, invokers, where):
    """(base directory, path text) of each read an include at `at` in a macro body makes.

    rustc resolves the include against the file of the outermost invocation, so
    every invocation of the macro in its package is found (`invokers`, each file
    of the package whose text names the macro), and the metavariable ranges over
    each plain literal (fragment `literal`) or identifier (`ident`, under
    `stringify!`) the invocations in that file, or the macro's own recursive
    invocations, pass."""
    enclosing = source.enclosing(at)
    if len(enclosing) != 1:
        raise ValueError(f'{where}: an include in a macro defined inside another macro')
    name, start, open_, close = enclosing[0]
    if source.matches(MACRO_EXPORT_RE):
        raise ValueError(f'{where}: {name}! may be invoked from another crate')
    meta = next((p for p in pieces if isinstance(p, tuple)), None)
    literal = meta is not None and meta[2] == 'concat'
    unfollowed = ValueError(f'{where}: ${meta[1] if meta else ""} of {name}! can bind what this rule cannot evaluate')
    if meta and set(re.findall(rf'\${meta[1]}\s*:\s*([A-Za-z_]\w*)', source.code[open_:close])) \
            != {'literal' if literal else 'ident'}:
        raise unfollowed
    word = re.compile(rf'(?<![\w$])(?:r#)?{name}\b')
    rename = re.compile(rf'(?<![\w$])(?:r#)?{name}\s+as\b')
    pools, recursion = {}, set()
    for g in invokers:
        for u in g.matches(USE_KW_RE):
            semi = g.until(u.end())
            if word.search(g.src, u.start(), semi) and AS_RE.search(g.src, u.start(), semi) \
                    and rename.search(g.lexed(u.start(), semi)):
                raise ValueError(f'{where}: {name}! is renamed by a use in {g.rel}')
        for m in g.matches(word):
            delim = g.call(m.end())
            if delim is None:
                continue  # the definition, a use, or an identifier that is no invocation
            inside = g.enclosing(m.start())
            if any(d[0] != name for d in inside):
                raise ValueError(f'{where}: {name}! is invoked inside another macro in {g.rel}')
            end = g.balanced(delim)
            if end is None:
                raise ValueError(f'{where}: an unbalanced invocation of {name}! in {g.rel}')
            pool = recursion if inside else pools.setdefault(g.path.parent, set())
            for token in tokens(g.lexed(delim + 1, end, keep_strings=True))[:-4]:
                if token[0] == 'id' and token[1].startswith('$') or token[:2] == ('p', ','):
                    continue  # a recursive invocation's metavariable, or an argument separator
                if literal and plain(token) is None:
                    raise unfollowed
                if literal or token[0] == 'id':
                    pool.add(plain(token) if literal else token[2])
    return [(base, ''.join(v if p is meta else p for p in pieces))
            for base, pool in sorted(pools.items()) for v in (sorted(pool | recursion) if meta else [None])]


def read_toml(path, rel):
    try:
        import tomllib
    except ImportError as e:
        raise ValueError(f'{rel}: Cargo manifests are read with tomllib, which needs Python >= 3.11') from e
    try:
        return tomllib.loads(path.read_text())
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as e:
        raise ValueError(f'{rel}: a manifest this rule cannot read: {e}') from e


def manifest_paths(table):
    """Every string a manifest gives a `path` key, at any depth, and each workspace member."""
    stack, out = [table], []
    while stack:
        t = stack.pop()
        for k, v in t.items() if isinstance(t, dict) else enumerate(t) if isinstance(t, list) else ():
            if k == 'path' and isinstance(v, str):
                out.append(v)
            else:
                stack.append(v)
    ws = table.get('workspace')
    return out + [m for m in (ws.get('members', []) if isinstance(ws, dict) else []) if isinstance(m, str)]


def refuse_manifest(table, rel, directory):
    """Raise for a manifest key the rule does not evaluate."""
    package, ws = table.get('package'), table.get('workspace')
    for key in ('build', 'workspace') if isinstance(package, dict) else ():
        if key in package:
            raise ValueError(f'{rel}: a `{key}` key in [package] (only build.rs and the root workspace are read)')
    for key in ('members', 'exclude', 'default-members') if isinstance(ws, dict) else ():
        for v in ws.get(key, []):
            if not isinstance(v, str) or glob.has_magic(v):
                raise ValueError(f'{rel}: a workspace {key} entry other than a plain path: {v!r}')
    for key in TARGET_TABLES:
        targets = table.get(key)
        for t in [targets] if isinstance(targets, dict) else targets if isinstance(targets, list) else []:
            p = t.get('path') if isinstance(t, dict) else None
            if isinstance(p, str) and not Path(os.path.normpath(directory / p)).is_relative_to(directory):
                raise ValueError(f'{rel}: a target path outside its package directory: {p}')


def config_refusal(table):
    """The first key of a Cargo configuration table the rule does not hash, or None."""
    def flags(v):
        return isinstance(v, list) and len(v) % 2 == 0 and all(
            a == '-C' and isinstance(b, str) and TARGET_CPU_RE.fullmatch(b) for a, b in zip(v[::2], v[1::2]))
    for key, value in table.items():
        rows = value.items() if isinstance(value, dict) else [('', value)]
        if key == 'alias':
            continue
        for k, v in rows:
            if key == 'build' and (k == 'jobs' and isinstance(v, int) or k == 'rustflags' and flags(v)):
                continue
            if key == 'target' and isinstance(v, dict) and all(kk == 'rustflags' and flags(vv) for kk, vv in v.items()):
                continue
            if key == 'env' and k == 'RUST_MIN_STACK' and (
                    isinstance(v, str) or isinstance(v, dict) and 'value' in v and set(v) <= {'value', 'force'}):
                continue
            return f'{key}.{k}' if k else key
    return None


def build_dependencies(table):
    keys = ('build-dependencies', 'build_dependencies')
    out = {k: table[k] for k in keys if k in table}
    for cfg, t in sorted((table.get('target') or {}).items()):
        out.update({f'target.{cfg}.{k}': t[k] for k in keys if isinstance(t, dict) and k in t})
    return out


def closure_digest(root, rels, deps):
    """The identity a build-script declaration pins: its module closure's bytes and its build-dependencies."""
    h = hashlib.sha256(json.dumps(deps, sort_keys=True, default=str).encode())
    for r in sorted(rels):
        h.update(f'\n{r}\0{hashlib.sha256((Path(root) / r).read_bytes()).hexdigest()}'.encode())
    return h.hexdigest()


class Scan:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.found = set()

    def rel(self, p):
        """`p` relative to the root, or None outside it, at it or under .git."""
        try:
            r = Path(os.path.normpath(p)).relative_to(self.root)
        except ValueError:
            return None
        return None if '.git' in r.parts or not r.parts else r.as_posix()

    def tracked(self, prefix):
        try:
            out = subprocess.run(['git', '-C', str(self.root), 'ls-files', '-z', '--', prefix],
                                 capture_output=True, check=True).stdout
        except (OSError, subprocess.CalledProcessError) as e:
            raise ValueError(f'cannot list the tracked files under {prefix}: {e}')
        return [p for p in out.decode().split('\0') if p]

    def add(self, p, strict=False):
        """The repository file `p` names as the OS reads it (`..` after a link is physical).
        A symbolic link on the way refuses when `strict` and is ignored otherwise."""
        if not os.path.isfile(p):
            return None
        full, real = os.path.normpath(p), os.path.realpath(p)
        if real != full:
            if strict:
                raise ValueError(f'{self.rel(full) or full}: read through a symbolic link (the OS reads {real})')
            return None
        r = self.rel(full)
        if r is not None:
            self.found.add(r)
        return r

    def names(self, fulls, strict=False):
        """The repository files the paths `fulls` name."""
        return {r for full in fulls for r in [self.add(full, strict)] if r}


def symlinks(directory):
    """Every symbolic link under `directory`, without following one."""
    out, todo = [], [directory]
    while todo:
        with os.scandir(todo.pop()) as entries:
            for e in entries:
                if e.is_symlink():
                    out.append(e.path)
                elif e.is_dir():
                    todo.append(e.path)
    return out


def inputs(root, fixed):
    """Repository-relative paths of every input, by the rule in this module's docstring."""
    scan = Scan(root)
    root = scan.root
    scan.found |= set(fixed)
    crates, theory = root / 'crates', root / 'theories/cic_l'
    walked = [*crates.rglob('*.rs'), *crates.rglob('*.toml'), *theory.rglob('*.lean'), *theory.rglob('*.toml')]
    scan.found |= {p.relative_to(root).as_posix() for p in walked if p.is_file() and '.lake' not in p.parts}
    scan.found |= set(scan.tracked('crates'))
    links = symlinks(crates) if crates.is_dir() else []
    if links:
        raise ValueError(f'{scan.rel(links[0])}: a symbolic link under crates/')

    @functools.lru_cache(maxsize=None)
    def package_of(directory):
        if (directory / 'Cargo.toml').is_file():
            return directory
        return None if directory in (root, directory.parent) else package_of(directory.parent)

    # Packages: the workspace manifest and every manifest under crates/, then every
    # package a manifest reaches by `path` or `members`. One outside the repository cannot be hashed.
    todo = sorted(root / p for p in scan.found if p.startswith('crates/') and p.endswith('Cargo.toml'))
    todo += [root / 'Cargo.toml'] if (root / 'Cargo.toml').is_file() else []
    packages, tables = set(), {}
    while todo:
        manifest = todo.pop()
        if manifest.parent in packages:
            continue
        packages.add(manifest.parent)
        scan.add(manifest, strict=True)
        table = tables[manifest.parent] = read_toml(manifest, scan.rel(manifest))
        if manifest.parent == root and 'package' in table:
            raise ValueError('Cargo.toml: a package at the workspace root, whose sources rule 1 does not name')
        refuse_manifest(table, scan.rel(manifest), manifest.parent)
        for value in manifest_paths(table):
            target = Path(os.path.normpath(manifest.parent / value))
            if target.is_file():
                scan.add(target, strict=True)
            elif not (target / 'Cargo.toml').is_file():
                continue
            elif scan.rel(target) is None and target != root:
                raise ValueError(f'{scan.rel(manifest)}: a path dependency outside the repository: {value}')
            else:
                scan.add(target / 'Cargo.toml', strict=True)
                todo.append(target / 'Cargo.toml')
                rel = scan.rel(target)  # None for the workspace root, whose files rule 1 names
                if rel is not None and not rel.startswith('crates/'):
                    scan.found |= set(scan.tracked(rel))
    # Cargo configuration at every level cargo reads for a package: hashed when it
    # holds only pure flags, refused otherwise.
    for level in sorted({root} | {d for p in packages for d in (p, *p.parents) if scan.rel(d)}):
        for name in ('.cargo/config.toml', '.cargo/config'):
            rel = scan.add(level / name, strict=True)
            bad = rel and config_refusal(read_toml(level / name, rel))
            if bad:
                raise ValueError(f'{rel}: `{bad}` in Cargo configuration can run a program, read a file '
                                 'or point a build at sources this rule does not follow')

    def nested(pkg):
        return any((d / 'Cargo.toml').is_file() for d in pkg.parents if scan.rel(d))

    # Rust sources, as (file, its packages, part of a build script): every `.rs` of
    # those packages and every build script, then whatever they reach.
    queue = [(root / p, None, False) for p in sorted(scan.found)
             if p.endswith('.rs') and package_of((root / p).parent) in packages]
    scripts = {}
    for pkg in sorted(packages):
        if (pkg / 'build.rs').is_file() and 'package' in tables[pkg]:
            scripts[pkg] = scan.add(pkg / 'build.rs', strict=True)
            queue.append((pkg / 'build.rs', frozenset([pkg]), True))
    seen, build_reads, build_bases = set(), set(), set()
    rust_files, sites, sources, env_sites = {}, [], {}, []
    while queue:
        path, pkgs, build = queue.pop()
        if pkgs is None:
            pkgs = frozenset(p for p in [package_of(path.parent)] if p)
        if (path, pkgs, build) in seen or scan.add(path, strict=True) is None:
            continue
        seen.add((path, pkgs, build))
        rust_files[path] = rust_files.get(path, frozenset()) | pkgs
        rel, src = scan.rel(path), path.read_text(errors='replace')
        source = sources.get(path) or Source(path, src, rel)
        if path.suffix == '.rs':
            refuse_unfollowed(source)
        if build or 'macro_rules' in src:
            sources[path] = source
        outside = path.suffix != '.rs' or not rel.startswith('crates/') or build
        if not (build or 'include' in src or 'path' in src or outside and 'mod' in src):
            continue
        for m in source.matches(INCLUDE_WORD_RE) if 'include' in src else ():
            kind, at = m.group(1), source.where(m.start())
            pos = source.before(m.start())
            if src[m.end():m.end() + 2] != '!(' or m.group().startswith('r#') or src[pos - 2:pos] == '::':
                if source.call(m.end()) is not None:
                    raise ValueError(f'{at}: an include spelled other than `{kind}!(` unqualified')
                continue  # an identifier, not an invocation
            close = source.balanced(m.end() + 1)
            if close is None:
                raise ValueError(f'{at}: an unbalanced {kind}! invocation')
            form = argument_form(tokens(source.lexed(m.end() + 2, close, keep_strings=True)))
            if 'macro_rules' in src and source.enclosing(m.start()):
                if kind == 'include' or build:
                    raise ValueError(f'{at}: an include! in a macro body' if kind == 'include'
                                     else f'{at}: an include in a macro body of a build script')
                if form is None or form[0] == 'env':
                    raise ValueError(f'{at}: cannot evaluate the {kind}! argument')
                sites.append((source, path, m, [form[1]] if form[0] == 'lit' else form[1], pkgs, at))
                continue  # read where the macro is invoked, once every file is known
            if form is None or form[0] == 'meta':
                raise ValueError(f'{at}: cannot evaluate the {kind}! argument')
            if form[0] == 'env':
                name, value = form[1], form[2]
                if nested(package_of(path.parent) or root):
                    raise ValueError(f'{at}: an env!("{name}") include in a package inside another package directory')
                if name == 'OUT_DIR' and (kind != 'include' or not OUT_NAME_RE.fullmatch(value)):
                    raise ValueError(f'{at}: an OUT_DIR include other than include!(concat!(env!("OUT_DIR"), "/<name>"))')
                if name == 'OUT_DIR' and not pkgs & set(scripts):
                    raise ValueError(f'{at}: OUT_DIR in a package without a build script')
                if name == 'CARGO_MANIFEST_DIR' and (kind == 'include' or not value.startswith('/')):
                    raise ValueError(f'{at}: cannot evaluate the {kind}! argument')
                env_sites += [(p, name, value[1:], at) for p in sorted(pkgs) if p in scripts]
                if name == 'OUT_DIR':
                    continue  # a build output, never a repository file; its row's review says what made it
                hits = scan.names([f'{p}{value}' for p in sorted(pkgs)], strict=True)
            else:
                hits = scan.names([path.parent / form[1]], strict=True)
            if not hits:
                raise ValueError(f'{at}: {kind}! names no repository file')
            if kind == 'include':
                queue += [(root / h, pkgs, build) for h in hits]
            elif build:
                build_reads |= hits
        # A mention inside a comment or a string literal only adds what a plain literal names.
        for m in INCLUDE_RE.finditer(src) if 'include' in src else ():
            form = None if source.in_code(m.start()) else mention_form(src[m.end() - 1:])
            if form and form[0] == 'lit':
                hits = scan.names([path.parent / form[1]])
                queue += [(root / h, pkgs, build) for h in hits] if m.group(1) == 'include' else []
                build_reads |= hits if build else set()
        pathed = set()
        for start, value, mod_at in source.path_attrs if 'path' in src else ():
            pathed.add(mod_at)
            hits = scan.names([path.parent / value], strict=True)
            if not hits:
                raise ValueError(f'{source.where(start)}: #[path] names no repository file')
            queue += [(root / h, pkgs, build) for h in sorted(hits)]
        for m in path_attributes(src):
            if not source.in_code(m.start()):
                lit = STRING_RE.match(src, m.end())
                value = literal_value(lit) if lit else '\0'
                hits = scan.names([path.parent / value, path.parent / path.stem / value])
                queue += [(root / h, pkgs, build) for h in hits]
        for m in MOD_RE.finditer(source.code) if outside and 'mod' in src else ():
            if source.components(m.start()):
                raise ValueError(f'{source.where(m.start())}: mod {m.group(1)}; inside an inline module')
            cands = [d / f for d in (path.parent, path.parent / path.stem)
                     for f in (f'{m.group(1)}.rs', f'{m.group(1)}/mod.rs')]
            hits = [h for c in cands for h in [scan.add(c, strict=True)] if h]
            if not hits and m.start() not in pathed and path.suffix == '.rs':
                raise ValueError(f'{source.where(m.start())}: mod {m.group(1)}; names no repository file')
            queue += [(root / h, pkgs, build) for h in hits]
        if build:
            bases = {path.parent, *pkgs, root}
            bases |= {a for p in pkgs for a in p.parents if scan.rel(a)}
            build_bases |= bases
            for m in STRING_RE.finditer(src):
                value = literal_value(m)
                for v in {value.strip(), value.rpartition('=')[2].strip()} - {''}:
                    build_reads |= {r for b in bases for r in [scan.add(b / v)] if r}

    # An include in a macro body: read at every invocation in the macro's package.
    names, invokers = {}, {}
    for site in sites:
        names.setdefault(site[4], set()).add(site[0].enclosing(site[2].start())[0][0])
    for pkgs, ns in names.items():
        word = re.compile(rf'\b(?:{"|".join(sorted(ns))})\b')
        for f in sorted(f for f, ps in rust_files.items() if ps & pkgs):
            g = sources.get(f)
            text = g.src if g else f.read_text(errors='replace')
            for n in sorted(set(word.findall(text))):
                g = sources[f] = g or Source(f, text, scan.rel(f))
                invokers.setdefault((pkgs, n), []).append(g)
    for source, path, m, pieces, pkgs, at in sites:
        name = source.enclosing(m.start())[0][0]
        variants = macro_variants(source, m.start(), pieces, invokers.get((pkgs, name), [source]), at)
        if not scan.names([os.path.join(base, text) for base, text in variants], strict=True):
            raise ValueError(f'{at}: {m.group(1)}! names no repository file')
    # A build script that can read files, or whose package reads env!("CARGO_MANIFEST_DIR")
    # or env!("OUT_DIR"), is admitted only by a reviewed row pinned to its module
    # closure and build-dependencies.
    declarations = None
    for pkg, script in sorted(scripts.items()):
        closure = sorted({scan.rel(p) for p, ps, b in seen if b and pkg in ps})
        hit = next(((sources[root / r], m) for r in closure for m in [FS_RE.search(sources[root / r].code)] if m), None)
        link = next((sources[root / r] for r in closure if LINK_RE.search(sources[root / r].src)), None)
        deps = build_dependencies(tables[pkg])
        envs = [s for s in env_sites if s[0] == pkg]
        if not (hit or link or deps or envs):
            continue  # reads no file but its own sources and its includes
        why = (f'`{hit[1].group()}` at {hit[0].where(hit[1].start())}' if hit else
               f'link flags in {link.rel}' if link else 'build-dependencies' if deps else
               f'its package reads env!("{envs[0][1]}") at {envs[0][3]}')
        if declarations is None:
            declarations = {}
            if (root / BUILD_DECLARATIONS).is_file():
                try:
                    declarations = json.loads((root / BUILD_DECLARATIONS).read_text())['scripts']
                except (ValueError, KeyError, TypeError) as e:
                    raise ValueError(f'{BUILD_DECLARATIONS}: unreadable: {e}') from e
        digest = closure_digest(root, closure, deps)
        row = declarations.get(script)
        if not isinstance(row, dict) or row.get('closure') != digest or envs and not isinstance(row.get('rustc_env'), list):
            raise ValueError(f'{script}: a build script ({why}) has no reviewed declaration of its reads'
                             f'{" and the cargo:rustc-env keys it can print" if envs else ""} '
                             f'for closure {digest} in {BUILD_DECLARATIONS}')
        for _, name, value, at in envs:
            if name in row['rustc_env']:
                raise ValueError(f'{at}: {script} can print cargo:rustc-env={name}')
            if name == 'OUT_DIR' and value not in row.get('out_dir', []):
                raise ValueError(f'{at}: {value} is not a file {script} declares under out_dir')
        for key in ('reads', 'data'):
            for r in row.get(key, []):
                if scan.add(root / r, strict=True) != r:
                    raise ValueError(f'{BUILD_DECLARATIONS}: {script} declares {r}, which is no repository file')
                build_reads |= {r} if key == 'data' else set()
    # One level of data: each repository path a non-Rust file a build script reads names.
    for r in sorted(build_reads):
        data = (root / r).read_bytes()
        if r.endswith('.rs') or b'\0' in data:
            continue
        for t in set(DATA_TOKEN_RE.findall(data.decode(errors='replace'))):
            for b in build_bases | {(root / r).parent}:
                scan.add(b / t)

    @functools.lru_cache(maxsize=None)
    def linked(directory):
        return directory != root and (directory.is_symlink() or linked(directory.parent))
    for r in sorted(scan.found):
        if (root / r).is_symlink() or linked((root / r).parent):
            raise ValueError(f'{r}: an input reached through a symbolic link')
    return sorted(scan.found)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--pinned-inputs', action='store_true')
    args = ap.parse_args(argv)
    if args.pinned_inputs:
        import kstar_recheck
        print('\n'.join(p for p in kstar_recheck.pinned_inputs() if p != 'scripts/kstar_inputs.py'))
        return 0
    if not args.selftest:
        ap.error('a library of the Q4 driver (`scripts/kstar_recheck.py`): only --selftest and --pinned-inputs run it')
    from kstar_selftest import input_controls, run
    return run(input_controls, 'KSTAR_INPUTS_SELFTEST', 'no record verdict')


if __name__ == '__main__':
    sys.exit(main())
