#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Q4 subjects: the Ax0 restriction of an export, and fenced Clean's refusals.

`restrict` keeps every declaration of a lean4export 3.1 stream whose axiom
closure lies within Ax0 and removes the others' declaration records, byte for
byte; each removed declaration is reported by name with the non-Ax0 axioms its
closure reaches. Name, level and expression tables, the header and every kept
record are left as they were. The closure follows every constant an
expression mentions, through declarations stated in any order, to a fixpoint.
A stream whose expression table is not dense and children-first, or whose
declarations cannot be read, is refused (ValueError): no subject is derived.

`classify_clean` sorts fenced Clean's refusals on a subject into roots (a
declaration refused for its own reason: a completeness gap or a rule Clean
enforces) grouped by cause, and cascades (refused because a dependency was),
each traced to its root. Nothing is dropped from the subject.

This file is a library of `scripts/kstar_recheck.py`; run on its own it
takes --selftest, which runs the restriction and classification controls of
`scripts/kstar_subjects_selftest.py` (synthetic streams; no subject verdict),
and --pinned-inputs.
"""
from array import array
import argparse
import json
import re
import sys

AX0 = ('Classical.choice', 'Quot.sound', 'propext')
ANSWERS_PINNED_INPUTS = True
EXPR_CHILDREN = {'app': ('fn', 'arg'), 'lam': ('type', 'body'), 'forallE': ('type', 'body'),
                 'letE': ('type', 'value', 'body'), 'proj': ('struct',), 'mdata': ('expr',)}
DECL_KINDS = ('axiom', 'def', 'thm', 'opaque', 'quot', 'inductive')


def _entries(kind, d):
    """(names, root expression ids) of one declaration record."""
    if kind == 'inductive':
        parts = d['types'] + d['ctors'] + d['recs']
        roots = [p['type'] for p in parts] + [r['rhs'] for p in d['recs'] for r in p['rules']]
        return [p['name'] for p in parts], roots
    roots = [d['type']] + ([d['value']] if 'value' in d else [])
    return [d['name']], roots


def _dotted(parts):
    return '.'.join(map(str, parts))


def restrict(data, permitted=AX0):
    lines = data.split(b'\n')
    names = {0: ()}
    kids_start, kids = array('q', [0]), array('q')
    const_of = {}
    decls = []  # (line index, kind, [name tuples], [root ids])
    for i, line in enumerate(lines):
        if not line:
            continue
        r = json.loads(line)
        if 'ie' in r:
            ie = r['ie']
            if ie != len(kids_start) - 1:
                raise ValueError(f'expression table not dense at line {i + 1}')
            kind = next(k for k in r if k != 'ie')
            body = r[kind]
            for key in EXPR_CHILDREN.get(kind, ()):
                child = body[key]
                if not isinstance(child, int) or not 0 <= child < ie:
                    raise ValueError(f'expression {ie} is not children-first')
                kids.append(child)
            kids_start.append(len(kids))
            if kind == 'const':
                const_of[ie] = names[body['name']]
        elif 'in' in r:
            v = r.get('str', r.get('num'))
            names[r['in']] = names[v['pre']] + (v['str'] if 'str' in v else v['i'],)
        elif 'il' in r or 'meta' in r:
            continue
        else:
            kind = next(iter(r))
            if kind not in DECL_KINDS or len(r) != 1:
                raise ValueError(f'unknown record at line {i + 1}')
            ids, roots = _entries(kind, r[kind])
            decls.append((i, kind, [names[n] for n in ids], roots))
    count = len(kids_start) - 1
    axioms = sorted({n for (_, k, ns, _) in decls if k == 'axiom' for n in ns})
    bad = [a for a in axioms if _dotted(a) not in permitted or a != tuple(_dotted(a).split('.'))]
    bit = {a: 1 << j for j, a in enumerate(bad)}
    mask = dict(bit)  # constant name -> non-Ax0 axioms its closure reaches
    changed = True
    while changed:
        changed = False
        emask = array('q', bytes(8 * count))
        for ie in range(count):
            m = mask.get(const_of.get(ie), 0) if ie in const_of else 0
            for j in range(kids_start[ie], kids_start[ie + 1]):
                m |= emask[kids[j]]
            emask[ie] = m
        for (_, _, ns, roots) in decls:
            m = 0
            for root in roots:
                if not 0 <= root < count:
                    raise ValueError('declaration names a missing expression')
                m |= emask[root]
            for n in ns:
                m |= bit.get(n, 0)
            for n in ns:
                if mask.get(n, 0) != m:
                    mask[n] = m
                    changed = True
    excluded, drop = [], set()
    for (i, kind, ns, _) in decls:
        m = 0
        for n in ns:
            m |= mask.get(n, 0)
        if m:
            drop.add(i)
            excluded.append(dict(names=[_dotted(n) for n in ns], kind=kind, line=i + 1,
                                 axioms=sorted(_dotted(a) for a in bad if m & bit[a])))
    kept = b'\n'.join(line for i, line in enumerate(lines) if i not in drop)
    roots = {_dotted(n): rs for (_, _, ns, rs) in decls for n in ns}
    block = {_dotted(n): frozenset(map(_dotted, ns)) for (_, _, ns, _) in decls for n in ns}
    return kept, excluded, Graph(roots, block, kids_start, kids, const_of)


class Graph:
    """The constants each declaration of a subject mentions."""

    def __init__(self, roots, block, kids_start, kids, const_of):
        self.roots, self.block = roots, block
        self.kids_start, self.kids, self.const_of = kids_start, kids, const_of

    def constants(self, name):
        seen, stack, found = set(), list(self.roots.get(name, ())), set()
        while stack:
            ie = stack.pop()
            if ie in seen:
                continue
            seen.add(ie)
            if ie in self.const_of:
                found.add(_dotted(self.const_of[ie]))
            stack.extend(self.kids[j] for j in range(self.kids_start[ie], self.kids_start[ie + 1]))
        return found


REFUSAL = re.compile(r'^DependencyRefused \{ name: "(?P<name>(?:[^"\\]|\\.)*)", blocked_by: "(?P<by>(?:[^"\\]|\\.)*)" \}$')
COMPANION = "declared by the export and not in the entry's environment"


def _normal(name):
    """A name as Clean renders it in a refusal line, as the export's dotted
    name. One line kind quotes a component outside the identifier alphabet
    as `«…»` with `\\u{…}` and `\\\\` escapes; the other prints it raw, with a
    `.` inside a component as `\u2024` and one more before the component, and
    an inductive block as `inductive <type>`."""
    name = re.sub(r'\\u\{([0-9a-fA-F]+)\}', lambda m: chr(int(m[1], 16)), name)
    name = name.replace('\\\\', '\\').replace('«', '').replace('»', '')
    if name.startswith('inductive '):  # an inductive block, by its type
        name = name[len('inductive '):]
    return re.sub(r'(^|\.)\u2024', r'\1', name).replace('\u2024', '.')


def _unescape(debug):
    """A name as Rust's `Debug` quoted it (only `\\` and `\"` occur in names)."""
    return _normal(re.sub(r'\\(.)', r'\1', debug))


def _split(line):
    """`<name>: <reason>`, splitting at the first `: ` outside `«…»`."""
    depth = 0
    for i, ch in enumerate(line):
        if ch == '«':
            depth += 1
        elif ch == '»':
            depth = max(0, depth - 1)
        elif ch == ':' and depth == 0 and line.startswith(': ', i) and i:
            return line[:i], line[i + 2:]
    raise ValueError(f'refusal names no declaration: {line[:120]}')


def classify_clean(refusals, graph, excluded=()):
    """Roots by cause and cascades by root for every refused declaration.

    Clean prints the companion line for each declaration it leaves out, and
    for some a reason: its own (a root) or `DependencyRefused` (a cascade,
    `blocked_by` naming the dependency). A declaration with the companion line
    alone is a cascade when a constant it mentions (`graph`) was refused or
    removed by the restriction (`excluded`), else a root with no stated
    reason. A cascade's root is found by following `blocked_by`; a chain that
    reaches no root is listed under `unresolved`."""
    excluded = set(excluded)
    reasons = {}
    for line in refusals:
        name, reason = _split(line)
        reasons.setdefault(_normal(name), []).append(reason)
    blocked, roots = {}, {}
    for name, rs in reasons.items():
        cascade = [m for m in map(REFUSAL.match, rs) if m]
        own = [r for r in rs if not REFUSAL.match(r) and r != COMPANION]
        if cascade and not own:
            blocked[name] = _unescape(cascade[0]['by'])
        elif not own:
            own_block = graph.block.get(name, frozenset({name}))
            hit = sorted(c for c in graph.constants(name) - own_block if c in reasons or c in excluded)
            if hit:
                blocked[name] = hit[0]
            else:
                roots[name] = rs[0]
        else:
            roots[name] = own[0]
    by_cause = {}
    for name, reason in sorted(roots.items()):
        cause = reason.split(' {', 1)[0].split(':', 1)[0]
        by_cause.setdefault(cause, []).append(dict(name=name, reason=reason))
    cascade_root, unresolved = {}, []
    for name in sorted(blocked):
        seen, cur = set(), name
        while cur in blocked and cur not in seen:
            seen.add(cur)
            cur = blocked[cur]
        if cur in roots or cur in excluded:
            cascade_root[name] = cur
        else:
            unresolved.append(dict(name=name, blocked_by=blocked[name], reached=cur))
    per_root = {}
    for name, root in cascade_root.items():
        per_root[root] = per_root.get(root, 0) + 1
    stated = sum(1 for rs in reasons.values() if COMPANION in rs)
    return dict(refused=len(reasons), left_out=stated, roots=len(roots), roots_by_cause=by_cause,
                cascades=len(cascade_root), cascades_per_root=dict(sorted(per_root.items())),
                cascades_from_excluded=sum(1 for r in cascade_root.values() if r in excluded),
                cascade_root=cascade_root, unresolved=unresolved)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--pinned-inputs', action='store_true')
    args = ap.parse_args(argv)
    if args.pinned_inputs:
        print('scripts/kstar_subjects_selftest.py')
        return 0
    if not args.selftest:
        ap.error('a library of the Q4 driver (`scripts/kstar_recheck.py`): only --selftest and --pinned-inputs run it')
    from kstar_subjects_selftest import restriction_controls
    checks = []

    def check(label, condition):
        if not condition:
            raise AssertionError(label)
        checks.append(label)
    restriction_controls(check)
    print(f'KSTAR_SUBJECTS_SELFTEST=ok checks={len(checks)}; no subject verdict')
    return 0


if __name__ == '__main__':
    sys.exit(main())
