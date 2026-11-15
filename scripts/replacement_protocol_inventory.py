#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Inventory the pinned official protocol overview; no implementation credit.

This deliberately accepts the overview's record layout, not arbitrary Lean.
The source must match its blob in the complete frozen release tree. Unexpected
layout, duplicate identities or missing fields refuse instead of losing rows.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re

UPSTREAM_PATH = 'src/Lean/Server/ProtocolOverview.lean'
REVISION = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'


def inventory(source, expected_blob):
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
            'upstream_revision': REVISION, 'upstream_path': UPSTREAM_PATH,
            'source_git_blob': blob, 'source_sha256': hashlib.sha256(source).hexdigest(),
            'counts': dict(sorted(Counter(row['kind'] for row in rows).items())),
            'total': len(rows), 'qualified': 0, 'methods': rows,
            'scope': 'All builtin records in the pinned official overview; no wire behavior or Clean parity measured.',
            'remaining': ['Cross-check registrations and runtime capability negotiation against overview',
                          'Enumerate parameter/response variants and ordering/cancellation/error contracts',
                          'Execute real Lean/Clean differential editor sessions for each contract',
                          'Qualify user-defined server_rpc_method extension mechanism']}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', required=True)
    p.add_argument('--tree', required=True)
    p.add_argument('--output', required=True)
    a = p.parse_args()
    raw = Path(a.tree).read_bytes()
    tree = json.loads(gzip.decompress(raw) if a.tree.endswith('.gz') else raw)
    if tree.get('sha') != REVISION or tree.get('truncated') is not False:
        raise ValueError('wrong or incomplete release tree')
    entries = [e for e in tree['tree'] if e['path'] == UPSTREAM_PATH and e['type'] == 'blob']
    if len(entries) != 1:
        raise ValueError('missing or duplicate protocol source in release tree')
    report = inventory(Path(a.source).read_bytes(), entries[0]['sha'])
    Path(a.output).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'total': report['total'], 'counts': report['counts'], 'qualified': 0}))


if __name__ == '__main__':
    main()
