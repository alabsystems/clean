#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Controls for `scripts/kstar_subjects.py` on synthetic lean4export streams:
the Ax0 restriction and fenced Clean's refusal classification. Run by
`kstar_subjects.py --selftest` and by `kstar_selftest.py`. No subject verdict."""
import json

import kstar_subjects as subj


def export(records):
    """A lean4export 3.1 stream from records, with a fixed header."""
    head = [{'meta': {'format': {'version': '3.1.0'}}}]
    return ''.join(json.dumps(r) + '\n' for r in head + records).encode()


def names(*parts):
    return [{'in': i + 1, 'str': {'pre': 0, 'str': p}} for i, p in enumerate(parts)]


def restriction_controls(check):
    # 1 bad (a non-Ax0 axiom), 2 uses_bad, 3 clean, 4 propext, 5 late (uses 6,
    # declared after it), 6 later_bad (uses bad).
    tables = names('bad', 'uses_bad', 'clean', 'propext', 'late', 'later_bad') + [
        {'ie': 0, 'sort': 0}, {'ie': 1, 'const': {'name': 1, 'us': []}},
        {'ie': 2, 'const': {'name': 6, 'us': []}}]
    ax = lambda n: {'axiom': {'name': n, 'levelParams': [], 'type': 0, 'isUnsafe': False}}  # noqa: E731
    thm = lambda n, v: {'thm': {'name': n, 'levelParams': [], 'type': 0, 'value': v, 'all': [n]}}  # noqa: E731
    records = tables + [ax(1), thm(2, 1), ax(4), thm(3, 0), thm(5, 2), thm(6, 1)]
    data = export(records)
    kept, excluded, graph = subj.restrict(data)
    removed = sorted(n for e in excluded for n in e['names'])
    check('restriction removes the closure of a non-Ax0 axiom, forward references included',
          removed == ['bad', 'late', 'later_bad', 'uses_bad'])
    check('restriction names each removal with its axioms', all(e['axioms'] == ['bad'] for e in excluded))
    check('restriction keeps every other line byte for byte',
          kept == export(tables + [ax(4), thm(3, 0)]))
    check('dependency graph', graph.constants('late') == {'later_bad'})
    clean = export(tables + [ax(4), thm(3, 0)])
    check('an Ax0 export is its own restriction', subj.restrict(clean)[0] == clean)
    alias = export([{'in': 1, 'num': {'pre': 0, 'i': 7}}, {'ie': 0, 'sort': 0}, ax(1)])
    check('a numeric axiom name is outside Ax0', subj.restrict(alias)[1][0]['axioms'] == ['7'])
    for label, bad in [('sparse expression table', [{'ie': 1, 'sort': 0}]),
                       ('child after parent', [{'ie': 0, 'app': {'fn': 0, 'arg': 0}}]),
                       ('unknown record', [{'mystery': {}}])]:
        try:
            subj.restrict(export(bad))
        except ValueError:
            check('restriction refuses a ' + label, True)
        else:
            raise AssertionError(label)
    refusals = [
        'root: ExtensionBindingMismatch { name: "root", detail }',
        "root: declared by the export and not in the entry's environment",
        'a: DependencyRefused { name: "a", blocked_by: "root" }',
        "a: declared by the export and not in the entry's environment",
        'b.\u2024x\u2024y: DependencyRefused { name: "b.\u2024x\u2024y", blocked_by: "a" }',
        "b.«x.y»: declared by the export and not in the entry's environment",
        "silent: declared by the export and not in the entry's environment",
        "lone: declared by the export and not in the entry's environment",
        'cut: DependencyRefused { name: "cut", blocked_by: "gone" }',
        "cut: declared by the export and not in the entry's environment",
    ]
    graph = subj.Graph({}, {}, None, None, None)
    graph.constants = lambda n: {'silent': {'b.x.y'}}.get(n, set())
    c = subj.classify_clean(refusals, graph, excluded=['gone'])
    check('classification roots by cause', c['roots_by_cause'] == {
        'ExtensionBindingMismatch': [dict(name='root', reason='ExtensionBindingMismatch { name: "root", detail }')],
        "declared by the export and not in the entry's environment": [
            dict(name='lone', reason="declared by the export and not in the entry's environment")]})
    check('classification traces cascades to roots across renderings',
          c['cascade_root'] == {'a': 'root', 'b.x.y': 'root', 'silent': 'root', 'cut': 'gone'})
    check('classification counts every refusal', c['refused'] == c['left_out'] == 6 and not c['unresolved'])
    check('cascade from a removed declaration', c['cascades_from_excluded'] == 1)
    loop = ['p: DependencyRefused { name: "p", blocked_by: "q" }',
            'q: DependencyRefused { name: "q", blocked_by: "p" }']
    check('a cascade cycle is unresolved', len(subj.classify_clean(loop, graph)['unresolved']) == 2)
