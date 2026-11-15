#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Inventory every self-verification model declaration registered from a Rust string literal.

Embed memo W1 (designs/2026-08-28-embedding-the-kernel-model.md, Step 1) instrument. Scans
crates/clean-verify/src/spec/**/*.rs at a git revision (or the working tree with WORKTREE) for
the three literal registration shapes:

  self.add_inductive(<src>, <desc>)                 -- <src>: "…" / r"…" / concat!(…) / same-file const
  self.add_recursive_def(<src>, <desc>)
  self.add_definition*(SpecDefinition { name: "<n>", … })   -- and the same-module helper-fn form

and prints JSON: rows (file, line, kind, name, deps), plus counts of calls whose source is
computed at run time (`unmatched`), helper-built SpecDefinitions (`helper_calls`) and
test-fixture mentions of the call text (`test_mentions`). Dependencies of an inductive/def row are
the inventory names its source references (whole-identifier match); of a SpecDefinition row, its
declared `dependencies:` field. This is an INVENTORY, not a gate: it decides nothing and is wired
to no leg. Rendered output: docs/analysis/2026-09-11-model-literal-inventory.md.

Usage:
  python3 scripts/model_literal_inventory.py [REV|WORKTREE] > inventory.json
"""
import json, re, subprocess, sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REV = sys.argv[1] if len(sys.argv) > 1 else 'HEAD'

def git_files(rev):
    if rev == 'WORKTREE':
        out = subprocess.check_output(['git', '-C', ROOT, 'ls-files', '--cached', '--others', '--exclude-standard', 'crates/clean-verify/src/spec'], text=True)
        return [f for f in out.split('\n') if f.endswith('.rs')]
    out = subprocess.check_output(['git', '-C', ROOT, 'ls-tree', '-r', '--name-only', rev, 'crates/clean-verify/src/spec'], text=True)
    return [f for f in out.split('\n') if f.endswith('.rs')]

def git_show(rev, path):
    if rev == 'WORKTREE':
        return open(os.path.join(ROOT, path), encoding='utf-8').read()
    return subprocess.check_output(['git', '-C', ROOT, 'show', f'{rev}:{path}'], text=True)

def parse_string(s, i):
    """Parse a Rust string literal starting at s[i]. Returns (value, next_index)."""
    if s.startswith('r', i):
        j = i + 1
        hashes = 0
        while s[j] == '#':
            hashes += 1; j += 1
        assert s[j] == '"', f"raw string expected at {i}"
        j += 1
        closer = '"' + '#' * hashes
        k = s.index(closer, j)
        return s[j:k], k + len(closer)
    assert s[i] == '"', f"string expected at {i}: {s[i:i+20]!r}"
    j = i + 1
    out = []
    while True:
        c = s[j]
        if c == '"':
            return ''.join(out), j + 1
        if c == '\\':
            n = s[j+1]
            if n == '\n':
                j += 2
                while s[j] in ' \t\r\n':
                    j += 1
                continue
            m = {'n': '\n', 't': '\t', '"': '"', '\\': '\\', "'": "'", '0': '\0'}
            assert n in m, f"unsupported escape \\{n} at {j}"
            out.append(m[n]); j += 2; continue
        out.append(c); j += 1

def skip_ws_comments(s, i):
    while True:
        while i < len(s) and s[i] in ' \t\r\n':
            i += 1
        if s.startswith('//', i):
            i = s.index('\n', i)
            continue
        return i

CALL = re.compile(r'self\.(add_inductive|add_recursive_def)\s*\(')
def literal_calls(s):
    """Yield (kind, line, source) for every add_inductive/add_recursive_def call whose
    first argument is a plain or raw string literal; (kind, line, None) otherwise."""
    for m in CALL.finditer(s):
        i = skip_ws_comments(s, m.end())
        line = s.count('\n', 0, m.start()) + 1
        if s[i] == '"' or s.startswith('r"', i) or s.startswith('r#', i):
            src, _ = parse_string(s, i)
            yield m.group(1), line, src, 'literal'
        elif s.startswith('concat!(', i):
            j = i + len('concat!(')
            parts = []
            while True:
                j = skip_ws_comments(s, j)
                if s[j] == ')':
                    break
                part, j = parse_string(s, j)
                parts.append(part)
                j = skip_ws_comments(s, j)
                if s[j] == ',':
                    j += 1
            yield m.group(1), line, ''.join(parts), 'concat!'
        else:
            ident = re.match(r'[A-Z_][A-Z0-9_]*\b', s[i:])
            if ident:
                cm = re.search(r'const\s+' + ident.group(0) + r'\s*:\s*&str\s*=\s*', s)
                if cm:
                    j = skip_ws_comments(s, cm.end())
                    src, _ = parse_string(s, j)
                    yield m.group(1), line, src, 'const ' + ident.group(0)
                    continue
            yield m.group(1), line, None, None
DEF = re.compile(r'self\.(add_definition(?:_checked|_reducible|_structural|_if_absent|_structural_if_absent)?)\s*\(\s*SpecDefinition\s*\{\s*name:\s*"([^"]+)"')
DEPS = re.compile(r'dependencies:\s*Some\(HashSet::from\(\[(.*?)\]\)\)', re.S)
VALUE_NONE = re.compile(r'value_src:\s*None')

def raw_string_at(s, i):
    """Return the raw-string content starting at s[i] == 'r'."""
    j = i + 1; h = 0
    while s[j] == '#': h += 1; j += 1
    assert s[j] == '"'; j += 1
    k = s.index('"' + '#' * h, j)
    return s[j:k]

rows = []
unmatched = {}
test_mentions = {}
helper_calls = {}
HELPER = re.compile(r'self\.add_definition(?:_checked|_reducible|_structural|_if_absent|_structural_if_absent)?\s*\(\s*(?:Self::)?([a-z_][a-z0-9_]*)\(\s*"([^"]+)"')
ANY_IND = re.compile(r'self\.add_inductive\s*\(')
ANY_REC = re.compile(r'self\.add_recursive_def\s*\(')
ANY_DEF = re.compile(r'self\.add_definition(?:_checked|_reducible|_structural|_if_absent|_structural_if_absent)?\s*\(')
for path in git_files(REV):
    s = git_show(REV, path)
    n_def_calls = len(ANY_DEF.findall(s)); n_def_matched = len(DEF.findall(s)) + len(HELPER.findall(s))
    if n_def_calls != n_def_matched:
        unmatched[path] = unmatched.get(path, 0) + n_def_calls - n_def_matched
    for kind, line, src, via in literal_calls(s):
        if src is None:
            unmatched[path] = unmatched.get(path, 0) + 1
            continue
        nm = re.match(r'(?:inductive|def)\s+([^\s(:]+)', src)
        if not nm:
            test_mentions[path] = test_mentions.get(path, 0) + 1
            continue
        k = 'inductive' if kind == 'add_inductive' else 'def (recursive)'
        if via != 'literal':
            k += ' via ' + via
        rows.append(dict(file=path, line=line, kind=k, name=nm.group(1), src=src))
    for m in HELPER.finditer(s):
        rows.append(dict(file=path, line=s.count('\n', 0, m.start()) + 1,
                         kind='SpecDefinition via helper %s' % m.group(1), name=m.group(2), deps=None))
        helper_calls[path] = helper_calls.get(path, 0) + 1
    for m in DEF.finditer(s):
        # the SpecDefinition block extends to the matching `})` — approximate by next "})?;" or "});"
        end = s.find('})', m.end())
        block = s[m.start():end]
        deps = DEPS.search(block)
        dep_list = re.findall(r'"([^"]+)"', deps.group(1)) if deps else None
        kind = 'axiom (value-less SpecDefinition)' if VALUE_NONE.search(block) else 'SpecDefinition (%s)' % m.group(1)
        rows.append(dict(file=path, line=s.count('\n', 0, m.start()) + 1, kind=kind, name=m.group(2), deps=dep_list))
names = {r['name'] for r in rows}
names |= {n + '.rec' for r in rows if r['kind'] == 'inductive' for n in [r['name']]}
ident = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")
for r in rows:
    if 'src' in r:
        refs = sorted({t for t in ident.findall(r['src']) if t in names and t != r['name']})
        r['deps'] = refs
        del r['src']
json.dump(dict(rev=REV, rows=rows, unmatched=unmatched, test_mentions=test_mentions, helper_calls=helper_calls), sys.stdout, indent=0)
