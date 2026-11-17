# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Closed release profiles and input/output contracts for case inventories.

Profiles admit exact complete source inventories, never arbitrary revisions.
The historical default keeps its original source and driver denominator.
"""
import argparse
import base64
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath

WORLDS = ('v4.35.0', 'v4.36.0')


def case_profile(world, legacy):
    if world == 'v4.35.0':
        revision, inventory_sha256, catalog_blob = legacy
        return dict(world=world, revision=revision, inventory_sha256=inventory_sha256,
            catalog_blob=catalog_blob, driver_count=355,
            starting_manifest_sha256='bcb0f5a06fa9dc5959bc59bfc78e1ea4afaed91aaac8789876e48f11e20c3470')
    if world == 'v4.36.0':
        return dict(world=world, revision='611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9',
            inventory_sha256='ce0f0b57bf455e38773b24f39ec5151220197d887007e702baaf287beebc887a',
            catalog_blob='92b9228b9a52edd6235f4343eee4d8e95636e12f',
            driver_count=489, starting_manifest_sha256='2c4dd8e318968ad609c620f4303a3e6b0bcc0d2b36a290199b60cdac4935b782',
            harness_sha256='03fe3eecd5c67f6b324b4926cef9f6f89adc7abaeb1e3a85844414bb0e8d6191')
    raise ValueError('unreviewed test-case world: ' + world)


def load_profile_inputs(inventory_path, bundle_path, profile):
    raw = Path(inventory_path).read_bytes()
    if str(inventory_path).endswith('.gz'):
        raw = gzip.decompress(raw)
    if hashlib.sha256(raw).hexdigest() != profile['inventory_sha256']:
        raise ValueError('file inventory does not match the reviewed complete manifest')
    inventory = json.loads(raw)
    if inventory.get('worlds', {}).get(profile['world']) != profile['revision']:
        raise ValueError('wrong upstream inventory revision')
    targets, seen = {}, set()
    for row in inventory['files']:
        path = row['id']
        if path in seen or str(PurePosixPath(path)) != path or '..' in PurePosixPath(path).parts or path.startswith('/'):
            raise ValueError('duplicate or invalid upstream path: ' + path)
        seen.add(path)
        if row['target']:
            targets[path] = row['target']
    bundle_raw = Path(bundle_path).read_bytes()
    bundle_raw = gzip.decompress(bundle_raw) if str(bundle_path).endswith('.gz') else bundle_raw
    if 'harness_sha256' in profile and hashlib.sha256(bundle_raw).hexdigest() != profile['harness_sha256']:
        raise ValueError('harness bundle does not match the reviewed complete source bundle')
    bundle = json.loads(bundle_raw)
    if bundle.get('upstream_revision') != profile['revision']:
        raise ValueError('wrong harness-source revision')
    sources = {}
    for row in bundle['files']:
        path = row['path']
        raw = base64.b64decode(row['content_base64'], validate=True)
        git_blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if (path in sources or path not in targets or git_blob != targets[path]['blob']
                or row['blob'] != targets[path]['blob'] or row['mode'] != targets[path]['mode']
                or hashlib.sha256(raw).hexdigest() != row['sha256'] or len(raw) != row['bytes']):
            raise ValueError('missing, duplicate or mismatched harness source: ' + path)
        sources[path] = raw.decode('utf-8')
    catalog = 'tests/CMakeLists.txt'
    if targets.get(catalog, {}).get('blob') != profile['catalog_blob']:
        raise ValueError('unreviewed CMake catalog: update the parser contract before changing the pin')
    if not {catalog, 'tests/util.sh', 'tests/with_env.sh.in'} <= sources.keys():
        raise ValueError('missing pinned CMake catalog or common harness')
    return targets, sources


def arguments(description):
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('--inventory', required=True)
    parser.add_argument('--harness-sources', required=True)
    parser.add_argument('--oracle', required=True)
    parser.add_argument('--out-dir', required=True)
    parser.add_argument('--world', choices=WORLDS, default='v4.35.0')
    return parser.parse_args()


def write_manifest(manifest, args, producer):
    raw = (json.dumps(manifest, sort_keys=True, separators=(',', ':')) + '\n').encode()
    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    (out / 'manifest.json.gz').write_bytes(gzip.compress(raw, mtime=0))
    summary = dict(manifest['summary'],
        driver_contract_producer_sha256=hashlib.sha256(producer.with_name('replacement_driver_contracts.py').read_bytes()).hexdigest(),
        schema='clean-upstream-test-case-summary-v2', upstream_revision=manifest['upstream_revision'],
        manifest_sha256=hashlib.sha256(raw).hexdigest(),
        input_sha256={Path(p).name: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in
            (args.inventory, args.harness_sources, args.oracle)},
        producer_sha256=hashlib.sha256(producer.read_bytes()).hexdigest(),
        remaining_inventory=manifest['remaining_inventory'], claim=manifest['claim'])
    # Record newly factored inputs truthfully; old data artifacts stay untouched.
    summary['profile_producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.world == 'v4.36.0':
        summary['docparse_producer_sha256'] = hashlib.sha256(producer.with_name('replacement_docparse_436.py').read_bytes()).hexdigest()
    (out / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
