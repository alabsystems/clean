#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Inventory the pinned official protocol overview; no implementation credit.

This deliberately accepts the overview's record layout, not arbitrary Lean.
The source must match its blob in the complete frozen release tree. Unexpected
layout, duplicate identities or missing fields refuse instead of losing rows.
The default remains the historical 4.35 profile. The explicit reviewed 4.36
profile can also emit its method and selected wire-source delta against 4.35;
unchanged names or source hashes confer no semantic qualification.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
from pathlib import PurePosixPath
import re

UPSTREAM_PATH = 'src/Lean/Server/ProtocolOverview.lean'
REVISION = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
DEFAULT_PROFILE = 'v4.35.0'
PROFILES = {
    DEFAULT_PROFILE: (REVISION, 'ddd3587f89804c5c05e49b9b7432514066266322'),
    'v4.36.0': ('611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9',
                'ddd3587f89804c5c05e49b9b7432514066266322'),
}
WIRE_SOURCE_ROOTS = (
    'src/Lean/Data/Lsp', 'src/Lean/Data/JsonRpc',
    'src/Lean/Server', 'src/Lean/Widget',
)
METHOD_FIELDS = ('method', 'kind', 'direction', 'parameter_type',
                 'response_type', 'extension_kinds')


def profile_revision(profile):
    if profile not in PROFILES:
        raise ValueError('unreviewed protocol profile: ' + str(profile))
    return PROFILES[profile][0]


def inventory(source, expected_blob, profile=DEFAULT_PROFILE):
    revision = profile_revision(profile)
    blob = hashlib.sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest()
    if blob != expected_blob:
        raise ValueError('protocol source does not match the frozen release blob')
    text = source.decode('utf-8')
    marker = 'def protocolOverview : Array MessageOverview := #['
    if text.count(marker) != 1:
        raise ValueError('missing or repeated protocol overview')
    body = text.split(marker, 1)[1]
    if not body.endswith(']\n'):
        raise ValueError('truncated or unexpected overview ending')
    body = body[:-2]
    pattern = re.compile(r'^  \.(request|notification|rpcRequest) \{\n(.*?)^  \},\n', re.M | re.S)
    matches = list(pattern.finditer(body))
    if not matches or pattern.sub('', body).strip():
        raise ValueError('unclassified overview syntax')
    rows, seen = [], set()
    for match in matches:
        kind, record = match.groups()
        fields = re.findall(r'^    ([A-Za-z]+) := (.*?)(?=^    [A-Za-z]+ := |\Z)', record, re.M | re.S)
        data = {k: v.strip() for k, v in fields}
        required = {'method', 'parameterType', 'description'}
        if kind != 'rpcRequest':
            required |= {'direction', 'kinds'}
        if kind != 'notification':
            required.add('responseType')
        if len(data) != len(fields) or set(data) != required:
            raise ValueError('missing, duplicated or unknown fields')
        method = data['method']
        if kind == 'rpcRequest':
            if not re.fullmatch(r'`[A-Za-z_][A-Za-z0-9_.]*', method):
                raise ValueError('unexpected RPC name')
            method = method[1:]
            direction = 'clientToServer-via-$/lean/rpc/call'
        else:
            method = json.loads(method)
            direction = data['direction'].removeprefix('.')
            if not isinstance(method, str) or direction not in ('clientToServer', 'serverToClient'):
                raise ValueError('unexpected method or direction')
        identity = ('rpc:' if kind == 'rpcRequest' else 'lsp:') + method
        if identity in seen:
            raise ValueError('duplicate protocol identity: ' + identity)
        seen.add(identity)
        rows.append({'id': identity, 'method': method, 'kind': kind,
                     'direction': direction, 'parameter_type': data['parameterType'],
                     'response_type': data.get('responseType'),
                     'extension_kinds': data.get('kinds'),
                     'source_line': text[:text.index(marker)].count('\n') + 1
                     + marker.count('\n') + body[:match.start()].count('\n'),
                     'qualification': 'not-measured'})
    return {'schema': 'clean-replacement-protocol-inventory-v1',
            'upstream_revision': revision, 'upstream_path': UPSTREAM_PATH,
            'source_git_blob': blob, 'source_sha256': hashlib.sha256(source).hexdigest(),
            'counts': dict(sorted(Counter(row['kind'] for row in rows).items())),
            'total': len(rows), 'qualified': 0, 'methods': rows,
            'scope': 'All builtin records in the pinned official overview; no wire behavior or Clean parity measured.',
            'remaining': ['Cross-check registrations and runtime capability negotiation against overview',
                          'Enumerate parameter/response variants and ordering/cancellation/error contracts',
                          'Execute real Lean/Clean differential editor sessions for each contract',
                          'Qualify user-defined server_rpc_method extension mechanism']}


def read_tree(path, profile):
    raw = Path(path).read_bytes()
    tree = json.loads(gzip.decompress(raw) if str(path).endswith('.gz') else raw)
    if (not isinstance(tree, dict) or tree.get('sha') != profile_revision(profile)
            or tree.get('truncated') is not False or not isinstance(tree.get('tree'), list)):
        raise ValueError('wrong or incomplete release tree')
    return tree


def from_paths(source, tree_path, profile=DEFAULT_PROFILE):
    tree = read_tree(tree_path, profile)
    entries = [e for e in tree['tree'] if e.get('path') == UPSTREAM_PATH]
    if len(entries) != 1 or entries[0].get('type') != 'blob':
        raise ValueError('missing or duplicate protocol source in release tree')
    if entries[0].get('sha') != PROFILES[profile][1]:
        raise ValueError('unreviewed protocol overview blob in release tree')
    return inventory(Path(source).read_bytes(), entries[0]['sha'], profile), tree


def method_index(report, profile):
    if (report.get('schema') != 'clean-replacement-protocol-inventory-v1'
            or report.get('upstream_revision') != profile_revision(profile)
            or report.get('upstream_path') != UPSTREAM_PATH
            or report.get('source_git_blob') != PROFILES[profile][1]
            or type(report.get('qualified')) is not int or report['qualified'] != 0
            or not isinstance(report.get('methods'), list)):
        raise ValueError('unreviewed or qualified protocol inventory')
    methods = {}
    counts = Counter()
    for row in report['methods']:
        if (not isinstance(row, dict) or row.get('qualification') != 'not-measured'
                or row.get('kind') not in ('request', 'notification', 'rpcRequest')
                or any(key not in row for key in METHOD_FIELDS)
                or not isinstance(row.get('method'), str)):
            raise ValueError('malformed or qualified protocol method')
        identity = ('rpc:' if row['kind'] == 'rpcRequest' else 'lsp:') + row['method']
        if row.get('id') != identity or identity in methods:
            raise ValueError('duplicate or misbound protocol method')
        methods[identity] = {field: row[field] for field in METHOD_FIELDS}
        counts[row['kind']] += 1
    if (not methods or type(report.get('total')) is not int
            or report['total'] != len(methods) or report.get('counts') != dict(counts)):
        raise ValueError('protocol inventory counts disagree')
    return methods


def wire_sources(tree, profile):
    if (tree.get('sha') != profile_revision(profile) or tree.get('truncated') is not False
            or not isinstance(tree.get('tree'), list)):
        raise ValueError('wrong or incomplete wire-source tree')
    files, seen = {}, set()
    for entry in tree['tree']:
        path = entry.get('path')
        if (not isinstance(path, str) or not path or path.startswith('/')
                or '..' in PurePosixPath(path).parts or str(PurePosixPath(path)) != path
                or path in seen):
            raise ValueError('invalid or duplicate release tree path')
        seen.add(path)
        if entry.get('type') == 'tree' or not any(
                path == root + '.lean' or path.startswith(root + '/')
                for root in WIRE_SOURCE_ROOTS):
            continue
        if (entry.get('type') != 'blob' or entry.get('mode') not in ('100644', '100755')
                or not isinstance(entry.get('sha'), str)
                or re.fullmatch('[0-9a-f]{40}', entry['sha']) is None):
            raise ValueError('unclassified wire-source tree entry')
        files[path] = {'blob': entry['sha'], 'mode': entry['mode'], 'type': entry['type']}
    for root in WIRE_SOURCE_ROOTS:
        if root + '.lean' not in files:
            raise ValueError('missing wire-source root: ' + root)
    return files


def delta(baseline, target, baseline_tree, target_tree,
          baseline_profile=DEFAULT_PROFILE, target_profile='v4.36.0'):
    if (baseline_profile, target_profile) != (DEFAULT_PROFILE, 'v4.36.0'):
        raise ValueError('unreviewed protocol comparison pair')
    before = method_index(baseline, baseline_profile)
    after = method_index(target, target_profile)
    methods = []
    for identity in sorted(before.keys() | after.keys()):
        old, new = before.get(identity), after.get(identity)
        changed = [field for field in METHOD_FIELDS if old and new and old[field] != new[field]]
        change = ('added' if old is None else 'removed' if new is None
                  else 'changed' if changed else 'unchanged')
        methods.append(dict(id=identity, change=change, changed_fields=changed,
                            baseline=old, target=new, qualification='not-measured'))
    before_files = wire_sources(baseline_tree, baseline_profile)
    after_files = wire_sources(target_tree, target_profile)
    files = []
    for path in sorted(before_files.keys() | after_files.keys()):
        old, new = before_files.get(path), after_files.get(path)
        change = ('added' if old is None else 'removed' if new is None
                  else 'unchanged' if old == new else 'changed')
        files.append(dict(path=path, change=change, baseline=old, target=new,
                          qualification='not-measured'))
    return {
        'schema': 'clean-replacement-protocol-source-delta-v1',
        'profiles': {'baseline': baseline_profile, 'target': target_profile},
        'revisions': {'baseline': profile_revision(baseline_profile),
                      'target': profile_revision(target_profile)},
        'overview_sources': {
            'baseline': {key: baseline[key] for key in ('source_git_blob', 'source_sha256')},
            'target': {key: target[key] for key in ('source_git_blob', 'source_sha256')},
        },
        'method_comparison_fields': list(METHOD_FIELDS),
        'method_changes': dict(sorted(Counter(row['change'] for row in methods).items())),
        'methods': methods,
        'wire_source_roots': list(WIRE_SOURCE_ROOTS),
        'wire_source_changes': dict(sorted(Counter(row['change'] for row in files).items())),
        'wire_sources': files,
        'semantic_cases_measured': 0, 'qualified': 0,
        'scope': 'Overview method fields and all tracked files under the named wire-source roots; no JSON schema, registration, runtime or Clean parity measured.',
        'remaining': ['Resolve transitive parameter and response schemas and serializers',
                      'Reconcile actual registrations and negotiated capabilities',
                      'Execute differential semantic highlighting and request lifecycle sessions',
                      'Qualify all other runtime, cancellation, ordering and error contracts'],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', required=True)
    p.add_argument('--tree', required=True)
    p.add_argument('--output', required=True)
    p.add_argument('--profile', choices=PROFILES, default=DEFAULT_PROFILE)
    p.add_argument('--baseline-source')
    p.add_argument('--baseline-tree')
    p.add_argument('--delta-output')
    a = p.parse_args()
    comparison = (a.baseline_source, a.baseline_tree, a.delta_output)
    present = tuple(value is not None for value in comparison)
    compare_requested = any(present)
    if compare_requested and not all(present):
        p.error('protocol delta needs --baseline-source, --baseline-tree and --delta-output together')
    if compare_requested:
        if any(not value.strip() for value in comparison):
            p.error('protocol comparison paths must be nonempty')
        if not Path(a.baseline_source).is_file() or not Path(a.baseline_tree).is_file():
            p.error('protocol baseline paths must name regular files')
        for value in (a.output, a.delta_output):
            path = Path(value)
            if (not value.strip() or not path.parent.is_dir()
                    or (path.exists() and not path.is_file())):
                p.error('protocol output paths must name files in existing directories')
        if Path(a.output).resolve() == Path(a.delta_output).resolve():
            p.error('protocol inventory and delta outputs must differ')
    report, tree = from_paths(a.source, a.tree, a.profile)
    if compare_requested:
        baseline, baseline_tree = from_paths(a.baseline_source, a.baseline_tree)
        changes = delta(baseline, report, baseline_tree, tree, target_profile=a.profile)
    Path(a.output).write_text(json.dumps(report, indent=2) + '\n')
    if compare_requested:
        Path(a.delta_output).write_text(json.dumps(changes, indent=2) + '\n')
    print(json.dumps({'total': report['total'], 'counts': report['counts'], 'qualified': 0}))


if __name__ == '__main__':
    main()
