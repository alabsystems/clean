#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Derive an offline P01/P02 seed inventory, never run or qualify workloads.

The reviewed B01 inputs are frozen. Changing them requires an explicit new
cohort/pin, not silently absorbing a new denominator. --check compares bytes
with a regeneration; it is a reporting consistency check, not a launch gate.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
REVISION = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
INPUTS = {
    'cases': ('reports/replacement-inventory-2026-11-12/cases/manifest.json.gz',
              '9521500e003fdf14cf1428a8c37990fa07967710d14a3e2dd9f4f532144f1b0e'),
    'files': ('reports/replacement-inventory-2026-11-12/files.json.gz',
              'a5ecfaa3d5ac1e8be8969bbe345e730361751d383481d0e32066fd85a7f23d43'),
}
OUTPUT = 'reports/replacement-performance-inventory-2026-11-15'
IMPORT_MODULES = (
    'Init.Prelude', 'Init', 'Std.Data.HashMap', 'Std', 'Lean',
    'Mathlib.Data.Subtype', 'Mathlib.Logic.Basic', 'Mathlib.Order.Basic', 'Mathlib',
)
COMMON_BLOCKERS = [
    'shipping-executables-and-platform-not-bound',
    'transitive-source-artifact-and-option-inputs-not-bound',
    'correctness-and-dependency-closed-proof-replay-not-qualified',
    'equivalent-clean-and-lean-command-semantics-not-qualified',
    'cold-warm-cache-protocol-and-resource-budgets-not-bound',
    'paired-wall-and-rss-samples-not-measured',
]


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def load_inputs(root):
    objects, provenance = {}, {}
    for name, (path, digest) in INPUTS.items():
        raw = (root / path).read_bytes()
        content = gzip.decompress(raw)
        if sha256(content) != digest:
            raise ValueError('unreviewed inventory: ' + path)
        objects[name] = json.loads(content)
        provenance[name] = dict(path=path, sha256=sha256(raw), content_sha256=digest)
    return objects, provenance


def build_manifest(cases, files, provenance):
    if (cases.get('schema') != 'clean-upstream-test-case-manifest-v2'
            or files.get('schema') != 'clean-replacement-file-inventory-v1'
            or cases.get('upstream_revision') != REVISION
            or files.get('worlds', {}).get('v4.35.0') != REVISION):
        raise ValueError('unreviewed schema or upstream revision')
    if cases.get('status') != 'not-measured':
        raise ValueError('source cohort is not the frozen unmeasured inventory')
    targets = {}
    for row in files['files']:
        if row['id'] in targets:
            raise ValueError('duplicate source path: ' + row['id'])
        targets[row['id']] = row['target']

    imports = []
    for module in IMPORT_MODULES:
        # Suppress Lean's implicit Init import, keeping the first ladder rung
        # distinct. Clean's handling of this header remains a correctness debt.
        source = 'prelude\nimport ' + module + '\n'
        path = 'src/' + module.replace('.', '/') + '.lean'
        mathlib = module.split('.')[0] == 'Mathlib'
        target = None if mathlib else targets.get(path)
        if not mathlib and not target:
            raise ValueError('missing import root source: ' + path)
        blockers = COMMON_BLOCKERS + [
            'explicit-prelude-header-equivalence-not-qualified',
            'v4.35.0-replay-world-selection-not-qualified',
            'unsafe-partial-and-other-replay-omissions-not-accounted',
        ]
        if mathlib:
            blockers += ['compatible-mathlib-revision-and-root-source-not-bound']
        imports.append(dict(
            id='P01:import:' + module, module=module, state='inventory',
            fixture=dict(utf8=source, sha256=sha256(source.encode())),
            root_source=None if mathlib else dict(path=path, **target),
            cache_modes=['cold', 'warm'],
            operations=['import-load', 'dependency-closed-replay'], blockers=blockers,
        ))

    selected, deferred = [], []
    root_ids, variant_ids = set(), set()
    for case in cases['cases']:
        if case['id'] in root_ids:
            raise ValueError('duplicate case ID: ' + case['id'])
        root_ids.add(case['id'])
        for variant in case['variants']:
            vid = variant['id']
            if vid in variant_ids or not vid.startswith(case['id'] + '#'):
                raise ValueError('duplicate or misbound variant ID: ' + vid)
            variant_ids.add(vid)
            if variant['phase'] != 'elaborate':
                deferred.append(dict(id=vid, phase=variant['phase'],
                                     reason='outside-elaborate-phase-seed; still owed by full workload inventory'))
                continue
            if variant['status'] != 'not-measured' or not variant.get('lean_options'):
                raise ValueError('changed elaborate contract: ' + vid)
            if variant.get('expected_exit') not in ('0', 'nonzero'):
                raise ValueError('unhandled exit contract: ' + vid)
            context = {key: value for key, value in case.items() if key != 'variants'}
            contract = dict(case=context, variant=variant)
            blockers = COMMON_BLOCKERS + ['inherited-setup-hooks-and-output-contract-not-replayed']
            if variant['output']['mode'] in ('ignored-by-upstream', 'performance-measurements-not-output-parity'):
                blockers += ['separate-correctness-control-required']
            selected.append(dict(id=vid, state='inventory', contract=contract,
                                 contract_sha256=sha256(encoded(contract)), blockers=blockers))
    if (len(root_ids) != cases['summary']['case_roots']
            or len(variant_ids) != cases['summary']['execution_variants']):
        raise ValueError('source denominator disagrees with manifest summary')
    if not selected:
        raise ValueError('empty elaborate-phase seed')
    selected.sort(key=lambda row: row['id'])
    deferred.sort(key=lambda row: row['id'])
    summary = dict(
        p01_seed_workloads=len(imports),
        p02_seed_roots=len({row['contract']['case']['id'] for row in selected}),
        p02_seed_variants=len(selected),
        p02_profiles=dict(sorted(Counter(row['contract']['variant']['profile'] for row in selected).items())),
        p02_expected_exit=dict(sorted(Counter(row['contract']['variant']['expected_exit'] for row in selected).items())),
        b01_variants_deferred=len(deferred),
        b01_deferred_phases=dict(sorted(Counter(row['phase'] for row in deferred).items())),
        ready=0, measured=0, qualified=0, full_workload_manifests_closed=0,
    )
    return dict(
        schema='clean-replacement-performance-inventory-v1',
        claim='Offline P01/P02 seed inventory only; no workload execution, readiness or performance qualification.',
        upstream_world='v4.35.0', upstream_revision=REVISION, inputs=provenance,
        oracle_identity=cases['oracle_identity'],
        command_templates={
            'status': 'unqualified templates; symbolic data, never shell commands to execute',
            'p01_lean': dict(cwd='{BOUND_PROJECT}', argv=['{LEAN}', '{FIXTURE}']),
            'p01_clean_candidate': dict(cwd='{BOUND_PROJECT}', argv=[
                '{CLEAN}', 'check', '--json', '--lean-world', 'v4.35.0',
                '--imports-prefer-olean', '{FIXTURE}']),
            'p01_lean_replay_candidate': dict(env={'LEAN_PATH': '{BOUND_LIBRARY_ROOTS}'},
                argv=['{SAME_WORLD_LEANCHECKER}', '--fresh', '{MODULE}']),
            'p01_clean_replay_candidate': dict(env={'LEAN_PATH': '{BOUND_LIBRARY_ROOTS}'},
                argv=['{CLEAN}', 'olean', 'replay', '--fresh', '--search-path',
                      '{BOUND_LIBRARY_ROOT}', '--json', '{MODULE}']),
            'p02_lean': dict(cwd='{UPSTREAM}/{case.directory}',
                             argv=['{LEAN}', '{*variant.lean_options}', '{*resolved.TEST_LEAN_ARGS}', '{basename(case.path)}']),
            'p02_clean_candidate': dict(cwd='{UPSTREAM}/{case.directory}', argv=[
                '{CLEAN}', 'check', '--json', '--lean-world', 'v4.35.0', '{case.path.absolute}']),
            'required': 'Resolve upstream setup/default variables, flags, hooks and output policies from each inherited contract; qualify Clean equivalence before timing.',
        },
        p01=imports, p02=selected, deferred_b01_variants=deferred,
        remaining_scope=[
            'P01 complete module/dependency and compatible-Mathlib scope, beyond the seed ladder',
            'P02 source operations inside drivers, aggregate scripts and non-elaborate phases',
            'P02 compatible full Mathlib corpus and generated declarations',
            'P03-P09 workload manifests',
            'All executable/platform/cache/budget bindings, correctness replays and paired measurements',
        ], summary=summary,
    )


def artifacts(manifest):
    return {
        'manifest.json.gz': gzip.compress(encoded(manifest), mtime=0),
        'summary.json': encoded(dict(schema=manifest['schema'], claim=manifest['claim'],
                                     inputs=manifest['inputs'], summary=manifest['summary'])),
    }


def check_artifacts(out_dir, outputs):
    for name, raw in outputs.items():
        if (out_dir / name).read_bytes() != raw:
            raise ValueError('artifact differs from offline regeneration: ' + name)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, default=ROOT / OUTPUT)
    parser.add_argument('--check', action='store_true', help='compare against offline regeneration without writing')
    args = parser.parse_args(argv)
    try:
        objects, provenance = load_inputs(ROOT)
        manifest = build_manifest(objects['cases'], objects['files'], provenance)
        outputs = artifacts(manifest)
        if args.check:
            check_artifacts(args.out_dir, outputs)
        else:
            args.out_dir.mkdir(parents=True, exist_ok=True)
            for name, raw in outputs.items():
                (args.out_dir / name).write_bytes(raw)
        print(json.dumps(manifest['summary'], sort_keys=True))
        print('PERFORMANCE_INVENTORY=consistent' if args.check else 'PERFORMANCE_INVENTORY=generated')
        return 0
    except (ValueError, KeyError, OSError) as error:
        print('PERFORMANCE_INVENTORY=error: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
