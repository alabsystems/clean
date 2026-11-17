#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Q4's source inputs: every repository file a member's build can read.

`kstar_recheck.source_inputs` hashes what `inputs` returns, so a record is
stale when any of these files moves. The rule (docs/DECISIONS.md, 2026-11-17,
"Q4 source inputs: every file a member's build reads"):

1. the caller's fixed files, and the 2026-11-13 rule, kept whole: every `.rs`
   and `.toml` under crates/ and every `.lean` and `.toml` under theories/cic_l;
2. every git-tracked file under crates/, whatever its suffix;
3. every package a Cargo manifest reaches by `path`, and for one outside
   crates/ every git-tracked file under it;
4. what those packages' Rust sources read at compile time, wherever it lives:
   the target of every `include_str!`, `include_bytes!` and `include!`
   (`concat!` and `env!("CARGO_MANIFEST_DIR")` evaluated; a macro
   metavariable or any other piece is a wildcard over every file under the
   literal prefix), every `#[path]` module, and the modules a file reached
   that way declares; and a build script's reads: each string literal in its
   module closure that names a repository file (relative to the file, its
   package or any directory above the package), and each repository path that
   such a file names in turn (one level).

A mention inside a comment or a string literal (the reference lexer in
`check_add_decl_ratchet.py` decides which) may only add an input: its target is
hashed when it resolves exactly, and is otherwise ignored. A use in code that
resolves to no file raises, so the record is not knowable rather than fresh.
`env!("OUT_DIR")` names a build script's output, whose reads rule 4 hashes; a
package without a build script cannot include from it. Nothing outside the
repository or under `.git` is source, and none of it is hashed.
"""
import bisect
import functools
import os
import re
import subprocess
from pathlib import Path

import check_add_decl_ratchet as reference_lexer

INCLUDE_RE = re.compile(r'\b(include_str|include_bytes|include)!\s*([(\[{])')
PATH_KV_RE = re.compile(r'path\s*=\s*(?=[bc]?r#*"|b?")')
ATTR_HEAD_RE = re.compile(r'(?:#!?\[\s*|\bcfg_attr\s*\([^\]]*?,\s*)\Z')
MOD_RE = re.compile(r'\bmod\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)\s*;')
STRING_RE = re.compile(r'(?<![A-Za-z0-9_\'])[bc]?r(#*)"(.*?)"\1|b?"((?:\\.|[^"\\])*)"', re.S)
TOKEN_RE = re.compile(r'\s+|(?P<str>(?<![A-Za-z0-9_\'])[bc]?r(#*)"(?:.*?)"\2|b?"(?:\\.|[^"\\])*")'
                      r'|(?P<id>\$?[A-Za-z_][A-Za-z0-9_]*)|(?P<p>.)', re.S)
MANIFEST_PATH_RE = re.compile(r'\b(?:path|build|workspace)\s*=\s*"([^"]+)"')
DATA_TOKEN_RE = re.compile(r'[^\s"\'`,;()\[\]{}<>=|]+')
CLOSE = {'(': ')', '[': ']', '{': '}'}
WILD, OUT_DIR, MANIFEST_DIR = object(), object(), object()
SIMPLE_ESCAPES = {'n': '\n', 't': '\t', 'r': '\r', '0': '\0', '\\': '\\', '"': '"', "'": "'"}


def unescape(text):
    """A Rust string literal's value."""
    def one(m):
        e = m.group(1)
        if e[0] == 'x':
            return chr(int(e[1:], 16))
        if e[0] == 'u':
            return chr(int(e[2:-1].replace('_', ''), 16))
        return SIMPLE_ESCAPES.get(e[0], '')  # '' for a backslash-newline continuation
    return re.sub(r'\\(x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f_]+\}|\n\s*|.)', one, text)


def path_attributes(src):
    """Each `path = "..."` that is a `#[path]` or a `cfg_attr` path, as its match."""
    for m in PATH_KV_RE.finditer(src) if 'path' in src else ():
        before = src[m.start() - 1:m.start()]
        if not (before.isalnum() or before == '_') and ATTR_HEAD_RE.search(src, max(0, m.start() - 400), m.start()):
            yield m


def literal_value(m):
    return m.group(2) if m.group(2) is not None else unescape(m.group(3))


def tokens(body):
    out = []
    for m in TOKEN_RE.finditer(body):
        if m.group('str'):
            out.append(('s', literal_value(STRING_RE.fullmatch(m.group('str')))))
        elif m.group('id'):
            out.append(('id', m.group('id')))
        elif m.group('p'):
            out.append(('p', m.group('p')))
    return out + [('end', '')] * 3


def expression(ts, i):
    """(pieces, next index) of one macro argument: strings, WILD, OUT_DIR and MANIFEST_DIR."""
    kind, text = ts[i]
    if kind == 's':
        return [text], i + 1
    if kind == 'id' and ts[i + 1] == ('p', '!') and ts[i + 2][1] in CLOSE:
        close, j, parts = CLOSE[ts[i + 2][1]], i + 3, []
        while ts[j][0] != 'end' and ts[j] != ('p', close):
            if ts[j] == ('p', ','):
                j += 1
                continue
            piece, j = expression(ts, j)
            parts.append(piece)
        if text == 'concat':
            return [p for part in parts for p in part], j + 1
        if text == 'env' and parts and len(parts[0]) == 1 and isinstance(parts[0][0], str):
            return [{'CARGO_MANIFEST_DIR': MANIFEST_DIR, 'OUT_DIR': OUT_DIR}.get(parts[0][0], WILD)], j + 1
        return [WILD], j + 1
    return [WILD], i + 1


def argument(src, at):
    """The pieces of the first macro argument after the opening delimiter at `at`."""
    try:
        return expression(tokens(src[at + 1:at + 4096]), 0)[0]
    except RecursionError:
        return [WILD]


class Scan:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.found = set()
        self.walked = {}

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

    def add(self, p):
        r = self.rel(p)
        if r is not None and (self.root / r).is_file():
            self.found.add(r)
            return r
        return None

    def files_under(self, top):
        if top not in self.walked:
            if top == self.root:
                self.walked[top] = [self.root / p for p in self.tracked('.')]
            else:
                self.walked[top] = [Path(d) / f for d, ds, fs in os.walk(top)
                                    for f in fs if '.git' not in Path(d).parts]
        return self.walked[top]

    def resolve(self, pieces, base, packages):
        """The repository files a macro argument names; None for a build script's output."""
        if OUT_DIR in pieces:
            return None
        manifest = pieces[:1] == [MANIFEST_DIR]
        bases, pieces = (sorted(packages), pieces[1:]) if manifest else ([base], pieces)
        text = ''.join('\0' if p is WILD or p is MANIFEST_DIR else p for p in pieces)
        hits = set()
        for b in bases:
            # env!("CARGO_MANIFEST_DIR") has no trailing slash; the literal after it supplies one.
            full = os.path.normpath(f'{b}{text}' if manifest else os.path.join(b, text))
            if '\0' not in full:
                hits |= {r for r in [self.add(full)] if r}
                continue
            top = Path(full[:full.index('\0')].rpartition('/')[0])
            if self.rel(top) is None and top != self.root:
                raise ValueError(f'an include pattern leaves the repository: {full!r}')
            pattern = re.compile('.*'.join(map(re.escape, full.split('\0'))), re.S)
            hits |= {r for f in self.files_under(top) if pattern.fullmatch(str(f)) for r in [self.add(f)] if r}
        return hits


def inputs(root, fixed):
    """Repository-relative paths of every input, by the rule in this module's docstring."""
    scan = Scan(root)
    root = scan.root
    scan.found |= set(fixed)
    for directory, suffixes in [('crates', ('.rs', '.toml')), ('theories/cic_l', ('.lean', '.toml'))]:
        scan.found |= {p.relative_to(root).as_posix() for p in (root / directory).rglob('*')
                       if p.is_file() and p.suffix in suffixes and '.lake' not in p.parts}
    scan.found |= set(scan.tracked('crates'))

    @functools.lru_cache(maxsize=None)
    def package_of(directory):
        if (directory / 'Cargo.toml').is_file():
            return directory
        return None if directory in (root, directory.parent) else package_of(directory.parent)

    # Packages: the workspace manifest and every manifest under crates/, then every
    # package a manifest reaches by `path`. One outside the repository cannot be hashed.
    todo = sorted(root / p for p in scan.found if p.startswith('crates/') and p.endswith('Cargo.toml'))
    todo += [root / 'Cargo.toml'] if (root / 'Cargo.toml').is_file() else []
    packages = set()
    while todo:
        manifest = todo.pop()
        if manifest.parent in packages:
            continue
        packages.add(manifest.parent)
        scan.add(manifest)
        for line in manifest.read_text(errors='replace').splitlines():
            for value in MANIFEST_PATH_RE.findall(line):
                target = Path(os.path.normpath(manifest.parent / value))
                if target.is_file():
                    scan.add(target)
                elif not (target / 'Cargo.toml').is_file():
                    continue
                elif scan.rel(target) is None and target != root:
                    if not line.lstrip().startswith('#'):
                        raise ValueError(f'{scan.rel(manifest)}: a path dependency outside the repository: {value}')
                else:
                    todo.append(target / 'Cargo.toml')
                    rel = scan.rel(target)  # None for the workspace root, whose files rule 1 names
                    if rel is not None and not rel.startswith('crates/'):
                        scan.found |= set(scan.tracked(rel))
    # Rust sources, as (file, its packages, part of a build script): every `.rs` of
    # those packages and every build script, then whatever they reach.
    queue = [(root / p, None, False) for p in sorted(scan.found)
             if p.endswith('.rs') and package_of((root / p).parent) in packages]
    has_build = set()
    for pkg in sorted(packages):
        text = (pkg / 'Cargo.toml').read_text(errors='replace')
        m = re.search(r'^\s*build\s*=\s*"([^"]+)"', text, re.M)
        script = pkg / (m.group(1) if m else 'build.rs')
        if not re.search(r'^\s*build\s*=\s*false', text, re.M) and script.is_file():
            has_build.add(pkg)
            queue.append((script, frozenset([pkg]), True))
    seen, build_reads, build_bases = set(), set(), set()
    while queue:
        path, pkgs, build = queue.pop()
        if pkgs is None:
            pkgs = frozenset(p for p in [package_of(path.parent)] if p)
        if (path, pkgs, build) in seen or scan.add(path) is None:
            continue
        seen.add((path, pkgs, build))
        rel, src = scan.rel(path), path.read_text(errors='replace')
        outside = path.suffix != '.rs' or not rel.startswith('crates/') or build
        includes = list(INCLUDE_RE.finditer(src)) if 'include' in src else []
        attributes = list(path_attributes(src))
        mods = list(MOD_RE.finditer(src)) if outside and 'mod' in src else []
        if not (build or includes or attributes or mods):
            continue
        spans = [m.span() for m in reference_lexer.NONCODE_RE.finditer(src)]
        starts = [a for a, _ in spans]

        def in_code(at):
            k = bisect.bisect_right(starts, at) - 1
            return k < 0 or not spans[k][0] <= at < spans[k][1]

        def where(at):
            return f'{rel}:{src.count(chr(10), 0, at) + 1}'
        for m in includes:
            code, pieces = in_code(m.start()), argument(src, m.end() - 1)
            if not code and any(p is WILD or p is OUT_DIR for p in pieces):
                continue  # a mention only adds what it names exactly
            hits = scan.resolve(pieces, path.parent, pkgs)
            if hits is None:
                if code and not pkgs & has_build:
                    raise ValueError(f'{where(m.start())}: OUT_DIR in a package without a build script')
                continue
            if code and not hits:
                raise ValueError(f'{where(m.start())}: {m.group(1)}! names no repository file')
            if m.group(1) == 'include':
                queue += [(root / h, pkgs, build) for h in hits]
            elif build:
                build_reads |= hits
        for m in attributes:
            lit = STRING_RE.match(src, m.end())
            value = literal_value(lit) if lit else '\0'
            hits = [h for h in (scan.add(path.parent / value), scan.add(path.parent / path.stem / value)) if h]
            if in_code(m.start()) and not hits:
                raise ValueError(f'{where(m.start())}: #[path] names no repository file')
            queue += [(root / h, pkgs, build) for h in hits]
        for m in mods:
            if in_code(m.start()):
                for d in (path.parent, path.parent / path.stem):
                    for c in (d / f'{m.group(1)}.rs', d / m.group(1) / 'mod.rs'):
                        if scan.add(c):
                            queue.append((c, pkgs, build))
        if build:
            bases = {path.parent, *pkgs, root}
            bases |= {a for p in pkgs for a in p.parents if scan.rel(a)}
            build_bases |= bases
            for m in STRING_RE.finditer(src):
                value = literal_value(m)
                for v in {value.strip(), value.rpartition('=')[2].strip()} - {''}:
                    build_reads |= {r for b in bases for r in [scan.add(b / v)] if r}
    # One level of data: each repository path a non-Rust file a build script reads names.
    for r in sorted(build_reads):
        data = (root / r).read_bytes()
        if r.endswith('.rs') or b'\0' in data:
            continue
        for t in set(DATA_TOKEN_RE.findall(data.decode(errors='replace'))):
            for b in build_bases | {(root / r).parent}:
                scan.add(b / t)
    return sorted(scan.found)
