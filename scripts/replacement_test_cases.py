#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Expand pinned Lean CMake test roots and declared harness variants.

Reads archived data only: never configures CMake or executes upstream scripts.
Case roots, execution variants and supporting files are separate denominators.
A runnable upstream case is not evidence that Clean passes it.
"""
import argparse
import base64
from collections import Counter
import fnmatch
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shlex
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from replacement_driver_contracts import driver_contract

REVISION = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
CATALOG = 'tests/CMakeLists.txt'
INVENTORY_SHA256 = 'a5ecfaa3d5ac1e8be8969bbe345e730361751d383481d0e32066fd85a7f23d43'
CATALOG_BLOB = '92b9228b9a52edd6235f4343eee4d8e95636e12f'
STATUS = 'not-measured'
MARKERS = ('.no_test', '.no_bench', '.serial', '.do_compile', '.no_compile',
           '.do_interpret', '.no_interpret', '.do_compile_test', '.no_compile_test',
           '.do_interpret_test', '.no_interpret_test', '.do_compile_bench',
           '.no_compile_bench', '.do_interpret_bench', '.no_interpret_bench')


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def git_blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def read_json(path):
    raw = Path(path).read_bytes()
    return json.loads(gzip.decompress(raw) if str(path).endswith('.gz') else raw)


def load_inputs(inventory_path, bundle_path):
    inventory_raw = Path(inventory_path).read_bytes()
    if str(inventory_path).endswith('.gz'):
        inventory_raw = gzip.decompress(inventory_raw)
    if hashlib.sha256(inventory_raw).hexdigest() != INVENTORY_SHA256:
        raise ValueError('file inventory does not match the reviewed complete manifest')
    inventory = json.loads(inventory_raw)
    if inventory.get('worlds', {}).get('v4.35.0') != REVISION:
        raise ValueError('wrong upstream inventory revision')
    targets = {}
    seen = set()
    for row in inventory['files']:
        path = row['id']
        if path in seen or str(PurePosixPath(path)) != path or '..' in PurePosixPath(path).parts or path.startswith('/'):
            raise ValueError('duplicate or invalid upstream path: ' + path)
        seen.add(path)
        if row['target']:
            targets[path] = row['target']
    bundle = read_json(bundle_path)
    if bundle.get('upstream_revision') != REVISION:
        raise ValueError('wrong harness-source revision')
    sources = {}
    for row in bundle['files']:
        path = row['path']
        raw = base64.b64decode(row['content_base64'], validate=True)
        if (path in sources or path not in targets or git_blob(raw) != targets[path]['blob']
                or row['blob'] != targets[path]['blob'] or row['mode'] != targets[path]['mode']
                or hashlib.sha256(raw).hexdigest() != row['sha256'] or len(raw) != row['bytes']):
            raise ValueError('missing, duplicate or mismatched harness source: ' + path)
        sources[path] = raw.decode('utf-8')
    if targets.get(CATALOG, {}).get('blob') != CATALOG_BLOB:
        raise ValueError('unreviewed CMake catalog: update the parser contract before changing the pin')
    if not {CATALOG, 'tests/util.sh', 'tests/with_env.sh.in'} <= sources.keys():
        raise ValueError('missing pinned CMake catalog or common harness')
    return targets, sources


def normalize(path):
    parts = []
    for part in str(path).split('/'):
        if part in ('', '.'):
            continue
        if part == '..':
            if not parts:
                raise ValueError('path escapes upstream root')
            parts.pop()
        else:
            parts.append(part)
    return '/'.join(parts)


def catalog_entries(text):
    """Read top-level registrations, not similarly named calls inside functions."""
    entries = []
    pattern = r'^add_(test_pile|test_dir|dir_of_test_dirs)\((.*?)\)'
    for match in re.finditer(pattern, text, re.M | re.S):
        words = shlex.split(match.group(2), comments=True)
        kind = match.group(1)
        if not words or '$' in words[0]:
            raise ValueError('unresolved registration directory')
        directory = normalize('tests/' + words[0])
        glob = words[1] if kind == 'test_pile' else None
        rest = words[2:] if glob else words[1:]
        excludes = []
        index = 0
        while index < len(rest):
            word = rest[index]
            if word == 'EXCEPT':
                index += 1
                while index < len(rest) and rest[index] not in ('BENCH', 'FIXTURES_REQUIRED', '${ELAB_FIXTURES}'):
                    excludes.append(rest[index]); index += 1
            elif word in ('BENCH', 'FIXTURES_REQUIRED'):
                index += 2
            elif word == '${ELAB_FIXTURES}':
                index += 1
            else:
                raise ValueError('unresolved CMake registration option: ' + word)
        entries.append(dict(kind=kind, directory=directory, glob=glob, excludes=excludes,
                            catalog_lines=[text.count('\n', 0, match.start()) + 1,
                                           text.count('\n', 0, match.end()) + 1]))
    if not entries:
        raise ValueError('no case registrations found')
    return entries


def ref(path, targets):
    return dict(path=path, **targets[path])


def resolve_runner(path, targets, sources):
    seen = []
    while path in targets:
        if path in seen:
            raise ValueError('cyclic harness symlink: ' + path)
        seen.append(path)
        if path not in sources:
            raise ValueError('harness content not archived: ' + path)
        if targets[path]['mode'] != '120000':
            return path, seen
        path = normalize(str(PurePosixPath(path).parent) + '/' + sources[path].strip())
    raise ValueError('missing harness symlink target: ' + path)


def initial_settings(text):
    """Resolve only literal assignments; any shell computation keeps all unknown.

    Never source the script. Even an innocuous earlier assignment can be changed
    by a later conditional/function, so partial interpretation grants no credit.
    """
    settings = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        if re.fullmatch(r'unset [A-Za-z_][A-Za-z_0-9]*', line):
            settings[line.split()[1]] = None
            continue
        match = re.fullmatch(r'(?:export\s+)?([A-Za-z_][A-Za-z_0-9]*)=(.*)', line)
        if not match or any(char in match.group(2) for char in '$`;\\'):
            return {}, 'dynamic-shell'
        name, value = match.groups()
        array = value.startswith('(') and value.endswith(')')
        try:
            parsed = shlex.split(value[1:-1] if array else value, comments=True)
        except ValueError:
            return {}, 'dynamic-shell'
        if not array and len(parsed) > 1:
            return {}, 'dynamic-shell'
        settings[name] = parsed if array else (parsed[0] if parsed else '')
    return settings, 'literal-assignments'


def enabled_phase(path, phase, profile, targets, default):
    for suffix, value in [(f'.do_{phase}_{profile}', True), (f'.no_{phase}_{profile}', False),
                          (f'.do_{phase}', True), (f'.no_{phase}', False)]:
        if path + suffix in targets:
            return value
    return default


def packages(path):
    if '/server' in path:
        return ['B15']
    if path.startswith(('tests/lake/', 'tests/pkg/', 'tests/lake_bench/')):
        return ['B05', 'B13']
    if '/compile' in path:
        return ['B12', 'B16'] if '_bench/' in path else ['B12']
    if '/elab_fail/' in path:
        return ['B03']
    if '/docparse/' in path:
        return ['B04']
    if '/elab' in path or path.startswith('doc/examples/'):
        return ['B02']
    if '/bench/' in path or '_bench/' in path:
        return ['B16']
    return ['B01', 'B14']


def output_contract(path, targets):
    if path + '.out.ignored' in targets:
        return dict(mode='ignored-by-upstream', marker=ref(path + '.out.ignored', targets))
    if path + '.out.expected' in targets:
        return dict(mode='normalized-combined-stdout-stderr', expected=ref(path + '.out.expected', targets))
    return dict(mode='empty-combined-stdout-stderr')


def variants(path, runner, profile, targets, sources, aggregate):
    resolved, chain = resolve_runner(runner, targets, sources)
    base = dict(profile=profile, status=STATUS, harness=[ref(p, targets) for p in chain])
    init = path + '.init.sh'
    settings, init_state = ({}, 'absent')
    if init in targets and 'source_init' in sources[resolved]:
        if init not in sources:
            raise ValueError('setup hook content not archived: ' + init)
        settings, init_state = initial_settings(sources[init])
    extra = dict(settings=settings, setup_state=init_state,
                 shell_hooks='pinned before/after scripts are not executed by this producer',
                 setup=ref(init, targets) if init in targets else None)
    modes = []
    if resolved in ('tests/compile/run_test.sh', 'tests/compile_bench/run_bench.sh'):
        for phase in ['compile', 'interpret']:
            default = phase == 'compile' or profile == 'test'
            if enabled_phase(path, phase, profile, targets, default):
                modes.append(dict(base, id=profile + ':' + phase, phase=phase,
                    tools=['lean', 'leanc', 'native-executable'] if phase == 'compile' else ['lean'],
                    lean_options=['--c=<input>.c', '-Dcompiler.postponeCompile=false'] if phase == 'compile'
                                 else ['-Dlinter.all=false', '--run'],
                    leanc_options=['-O3', '-DNDEBUG'] if phase == 'compile' else [],
                    variable_options=extra, expected_exit=settings.get('TEST_EXIT', '0') if init_state != 'dynamic-shell' else 'unresolved:TEST_EXIT',
                    output=output_contract(path, targets) if profile == 'test' else dict(mode='performance-measurements-not-output-parity'),
                    normalization=['measurement-lines'], contract_state='dynamic-setup' if init_state == 'dynamic-shell' else 'declared'))
    elif resolved in ('tests/elab/run_test.sh', 'tests/elab_fail/run_test.sh', 'tests/elab_bench/run_bench.sh'):
        opts = ['--root=..', '-DprintMessageEndPos=true', '-Dlinter.all=false', '-DElab.inServer=true']
        if resolved == 'tests/elab/run_test.sh':
            opts += ['-Dcompiler.postponeCompile=false']
        modes.append(dict(base, id=profile + ':elaborate', phase='elaborate', tools=['lean'],
            lean_options=opts, variable_options=extra,
            expected_exit='nonzero' if resolved == 'tests/elab_fail/run_test.sh' else '0',
            output=output_contract(path, targets) if profile == 'test' else dict(mode='performance-measurements-not-output-parity'),
            normalization=['metavariable-suffixes', 'reference-URLs', 'measurement-lines'],
            header_snapshots=dict(used_by_runner='maybe_use_lean_header_snapshot' in sources[resolved],
                option='LEAN_HEADER_SNAPSHOTS', default='OFF', when_on='automatic exact-header eligibility only in runners calling the helper; source header not yet extracted'),
            contract_state='dynamic-setup' if init_state == 'dynamic-shell' else 'declared'))
    elif resolved in ('tests/server/run_test.sh', 'tests/server_interactive/run_test.sh', 'tests/docparse/run_test.sh'):
        modes.append(dict(base, id=profile + ':driver', phase='driver', tools=['lean'],
            lean_options=['-Dlinter.all=false', '--run'], variable_options=extra,
            expected_exit=settings.get('TEST_EXIT', '0') if resolved == 'tests/server_interactive/run_test.sh' and init_state != 'dynamic-shell' else ('unresolved:TEST_EXIT' if init_state == 'dynamic-shell' else '0'),
            output=output_contract(path, targets), driver='run_test.lean' if resolved != 'tests/server/run_test.sh' else '<input>',
            normalization=['metavariable-suffixes', 'reference-URLs'] if resolved.endswith('server_interactive/run_test.sh') else [],
            platform=dict(ASAN_OPTIONS='detect_leaks=0') if resolved != 'tests/server/run_test.sh' else {},
            driver_source=ref(str(PurePosixPath(resolved).parent) + '/run_test.lean', targets) if resolved != 'tests/server/run_test.sh' else None,
            contract_state='driver-subcases-not-enumerated' if resolved != 'tests/server/run_test.sh' else 'declared'))
    else:
        modes.append(dict(base, id=profile + ':aggregate', phase='aggregate-script', tools=['bash'],
            contract_state='subcases-options-imports-and-platform-conditions-unexpanded',
            script=ref(path, targets) if path in sources else ref(resolved, targets)))
    for mode in modes:
        mode['id'] = 'lean4:' + path + '#' + mode['id']
        mode['imports'] = dict(state='not-extracted', contract='actual source and package inputs pinned; no import-free assumption')
        mode['platform_contract'] = dict(build='configured upstream stage', compiler='stage toolchain',
                                        variables=['OSTYPE', 'CXX', 'LEANC_OPTS', 'LEAN_TEST_VARS'])
        mode['root_cause'] = None
        if mode['phase'] == 'compile':
            mode['option_arrays'] = dict(lean='TEST_LEAN_ARGS', leanc='TEST_LEANC_ARGS', executable='TEST_ARGS')
            mode['link_contract'] = dict(test='libleanshared; rpath except Windows', bench='stage static libraries; LEANC_OPTS')
        elif mode['phase'] == 'interpret':
            mode['option_arrays'] = dict(lean='TEST_LEANI_ARGS', main='TEST_ARGS')
        elif mode['phase'] == 'elaborate':
            mode['option_arrays'] = dict(lean='TEST_LEAN_ARGS')
    return modes


def build_manifest(targets, sources, tool):
    entries = catalog_entries(sources[CATALOG])
    roots = {}
    exclusions = []
    runner_paths = set()

    def add(path, directory, entry, aggregate=False, selection=None):
        if path in roots:
            raise ValueError('duplicate registered test root: ' + path)
        profiles = []
        expanded = []
        for profile, filename in [('test', 'run_test.sh'), ('bench', 'run_bench.sh')]:
            runner = directory + '/' + filename
            if runner not in targets:
                continue
            runner_paths.add(runner)
            marker = path + ('.no_test' if profile == 'test' else '.no_bench')
            if not aggregate and marker in targets:
                exclusions.append(dict(path=path, profile=profile, reason='sidecar', evidence=ref(marker, targets)))
                continue
            profiles.append(profile)
            expanded += variants(path, runner, profile, targets, sources, aggregate)
        for variant in expanded:
            runner_paths.update(item['path'] for item in variant['harness'])
            if variant.get('driver_source'):
                runner_paths.add(variant['driver_source']['path'])
        roots[path] = dict(id='lean4:' + path, path=path, directory=directory,
            input=ref(path, targets) if path in targets else None,
            input_scope='aggregate-directory' if aggregate else 'single-file',
            registration=entry, selection=selection or 'default', packages=packages(path),
            status=STATUS, profiles=profiles, variants=expanded,
            serial=path + '.serial' in targets,
            hooks=[ref(path + suffix, targets) for suffix in ('.init.sh', '.before.sh', '.after.sh') if path + suffix in targets],
            supporting_inputs=[ref(p, targets) for p in sorted(targets) if
                (p.startswith(directory + '/') if aggregate else p.startswith(path + '.'))],
            unresolved=['source-import-closure-not-enumerated'] + (['aggregate-script-subcases-not-enumerated'] if aggregate else []))

    for entry in entries:
        directory = entry['directory']
        if entry['kind'] == 'test_pile':
            for path in sorted(targets):
                if str(PurePosixPath(path).parent) != directory or not fnmatch.fnmatchcase(PurePosixPath(path).name, entry['glob']):
                    continue
                name = PurePosixPath(path).name
                if name in entry['excludes'] or name.startswith('_tmp_') or re.match(r'run_(test|bench)', name):
                    exclusions.append(dict(path=path, profile='all', reason='catalog-exclusion-or-runner', registration=entry))
                    continue
                add(path, directory, entry)
        elif entry['kind'] == 'test_dir':
            add(directory, directory, entry, aggregate=True)
        else:
            children = sorted({p[len(directory) + 1:].split('/')[0] for p in targets if p.startswith(directory + '/') and '/' in p[len(directory) + 1:]})
            for child in children:
                path = directory + '/' + child
                if child in entry['excludes'] or child.startswith('_tmp_'):
                    exclusions.append(dict(path=path, profile='all', reason='catalog-directory-exclusion', registration=entry))
                else:
                    add(path, path, entry, aggregate=True)

    # This special CMake block registers each recursively discovered test.sh,
    # excludes named online/bootstrap/toolchain trees, and gates extra on LAKE_CI.
    if '"${LEAN_SOURCE_DIR}/../tests/lake/examples/test.sh"' not in sources[CATALOG] or '"${LEAN_SOURCE_DIR}/../tests/lake/tests/test.sh"' not in sources[CATALOG]:
        raise ValueError('Lake discovery contract changed')
    for path in sorted(targets):
        if not path.endswith('/test.sh') or not path.startswith(('tests/lake/examples/', 'tests/lake/tests/', 'tests/lake/extra/')):
            continue
        if re.search(r'(lake-packages|bootstrap|toolchain|online)', path):
            exclusions.append(dict(path=path, profile='test', reason='Lake CMake name exclusion', evidence=ref(CATALOG, targets)))
            continue
        if path not in sources:
            raise ValueError('Lake test source not archived: ' + path)
        directory = str(PurePosixPath(path).parent)
        roots[path] = dict(id='lean4:' + path, path=path, directory=directory, input=ref(path, targets),
            input_scope='aggregate-directory', registration=dict(kind='lake-test-sh', catalog=ref(CATALOG, targets)),
            selection='LAKE_CI=ON' if path.startswith('tests/lake/extra/') else 'default',
            packages=['B13'], status=STATUS, profiles=['test'], serial=False, hooks=[],
            supporting_inputs=[ref(p, targets) for p in sorted(targets) if p.startswith(directory + '/')],
            unresolved=['aggregate-script-subcases-not-enumerated', 'source-import-closure-not-enumerated'],
            variants=[dict(id='lean4:' + path + '#test:aggregate', profile='test', phase='aggregate-script', status=STATUS,
                harness=[ref(path, targets)], tools=['bash', 'lake'], environment=dict(LAKE='lake', configured='TEST_VARS'),
                contract_state='subcases-options-imports-and-platform-conditions-unexpanded')])
        runner_paths.add(path)

    # lint.py is an actual CTest root; it is an upstream source-quality check,
    # not a Lean semantic parity case. Keep it visible, outside semantic totals.
    if 'tests/lint.py' in targets:
        roots['tests/lint.py'] = dict(id='lean4:tests/lint.py', path='tests/lint.py', packages=['B17'], status=STATUS,
            input=ref('tests/lint.py', targets), input_scope='source-quality-check', profiles=['test'], selection='default',
            variants=[dict(id='lean4:tests/lint.py#test:lint', profile='test', phase='source-quality', status=STATUS, tools=['python3'], harness=[ref('tests/lint.py', targets)])],
            supporting_inputs=[], unresolved=['source-quality-check-not-semantic-parity'])

    fixture = 'tests/build_lean_header_snapshots.sh'
    if fixture in targets:
        roots[fixture] = dict(id='lean4:' + fixture, path=fixture, directory='tests', input=ref(fixture, targets),
            packages=['B11', 'B16'], status=STATUS, input_scope='framework-fixture', profiles=['test'],
            selection='LEAN_HEADER_SNAPSHOTS=ON', supporting_inputs=[], unresolved=[],
            variants=[dict(id='lean4:' + fixture + '#test:fixture', profile='test', phase='fixture-setup',
                status=STATUS, tools=['bash', 'lean'], harness=[ref(fixture, targets)],
                contract_state='header-snapshot-build-fixture')])

    excluded_paths = {row['path'] for row in exclusions}
    files = []
    scope = [p for p in sorted(targets) if p.startswith(('tests/', 'doc/examples/'))]
    directories = [row['directory'] for row in roots.values() if row['input_scope'] == 'aggregate-directory']
    for path in scope:
        if path in roots:
            role = 'registered-case-input'
        elif path in runner_paths or path in (CATALOG, 'tests/util.sh', 'tests/with_env.sh.in'):
            role = 'harness'
        elif path in excluded_paths:
            role = 'excluded-case-input'
        elif path.endswith('.out.expected'):
            role = 'expected-output'
        elif path.endswith('.out.ignored'):
            role = 'output-policy-marker'
        elif path.endswith(MARKERS):
            role = 'selection-marker'
        elif path.endswith(('.init.sh', '.before.sh', '.after.sh')):
            role = 'setup-hook'
        elif path.endswith(('.md', '.rst')):
            role = 'documentation'
        elif any(path.startswith(d + '/') for d in directories):
            role = 'aggregate-case-input'
        elif path.endswith('.lean'):
            role = 'unregistered-or-input-only-source'
        elif path.endswith(('.sh', '.py', '.toml', '.in', '.nix')):
            role = 'support-or-unregistered-harness'
        else:
            role = 'support-input-unresolved'
        files.append(dict(path=path, blob=targets[path]['blob'], role=role, qualification=STATUS))
    cases = [roots[p] for p in sorted(roots)]
    for row in cases:
        row.setdefault('root_cause', None)
        for variant in row['variants']:
            variant.setdefault('imports', dict(state='not-extracted', contract='aggregate inputs and script are pinned'))
            variant.setdefault('platform_contract', dict(state='script-conditions-unexpanded', build='configured upstream stage'))
            variant.setdefault('expected_exit', 'aggregate-runner-success; internal command exits unexpanded')
            variant.setdefault('output', dict(mode='script-assertions-unexpanded'))
            variant.setdefault('option_arrays', dict(state='script-options-unexpanded'))
    for row in cases:
        for variant in row['variants']:
            if variant.get('contract_state') == 'driver-subcases-not-enumerated':
                contract = driver_contract(row['path'], variant['driver_source']['path'], sources, targets)
                contract['shell'] = [dict(ref(p, targets), source=sources[p]) for p in
                    [variant['harness'][-1]['path'], 'tests/util.sh', 'tests/with_env.sh.in']]
                contract['setup_hooks'] = [dict(hook, source=sources[hook['path']]) for hook in row['hooks']]
                contract['output_policy'] = variant['output']
                contract['expected_shell_exit'] = variant['expected_exit']
                variant['behavioral_contract'] = contract
                variant['imports'] = contract['imports']
                variant['contract_state'] = ('source-derived-driver-dynamic-expansion-required'
                    if contract['dynamic_expansion_required'] else 'source-derived-driver-static-expansion')
                variant['option_arrays'] = dict(state='fixed-driver-argv', argv=contract['invocation']['argv'])
    driver_source_records = {}
    def intern_driver_source(value):
        if isinstance(value, dict):
            if 'path' in value and 'source' in value:
                path = value['path']
                raw = sources[path].encode()
                driver_source_records[path] = dict(ref(path, targets),
                    sha256=hashlib.sha256(raw).hexdigest(), source=sources[path])
                value['source_slice_sha256'] = hashlib.sha256(value.pop('source').encode()).hexdigest()
                value['source_record'] = path
            for child in value.values():
                intern_driver_source(child)
        elif isinstance(value, list):
            for child in value:
                intern_driver_source(child)
    for row in cases:
        for variant in row['variants']:
            if 'behavioral_contract' in variant:
                intern_driver_source(variant['behavioral_contract'])
    all_variants = [v for row in cases for v in row['variants']]
    identifiers = [row['id'] for row in cases] + [v['id'] for v in all_variants]
    if len(identifiers) != len(set(identifiers)):
        raise ValueError('duplicate case/variant identity')
    return dict(schema='clean-upstream-test-case-manifest-v2', upstream_revision=REVISION,
        catalog=ref(CATALOG, targets), common_harness=[ref(p, targets) for p in ('tests/util.sh', 'tests/with_env.sh.in')], oracle_identity=tool,
        status=STATUS, claim='Pinned upstream case-root and harness-variant inventory only; no executed Clean or Lean parity verdict.',
        driver_source_records=driver_source_records, cases=cases, exclusions=exclusions, file_roles=files,
        summary=dict(case_roots=len(cases), test_roots=sum('test' in x['profiles'] for x in cases),
            benchmark_roots=sum('bench' in x['profiles'] for x in cases), roots_with_execution=sum(bool(x['variants']) for x in cases),
            case_roots_excluding_framework_checks=sum(x['input_scope'] not in ('source-quality-check', 'framework-fixture') for x in cases),
            execution_variants=len(all_variants), profiles=dict(sorted(Counter(v['profile'] for v in all_variants).items())),
            contract_states=dict(sorted(Counter(v.get('contract_state', 'source-quality') for v in all_variants).items())),
            case_selection=dict(sorted(Counter(x['selection'] for x in cases).items())),
            file_count=len(files), file_roles=dict(sorted(Counter(x['role'] for x in files).items())),
            excluded_registrations=len(exclusions), qualified_cases=0, qualified_variants=0),
        remaining_inventory=['imports and source-level subcases inside aggregate scripts',
            'dynamic setup and platform conditions', 'unregistered/input-only test surfaces',
            'runtime ABI and CLI/LSP contracts outside the CMake case catalog',
            'compatible Mathlib corpus', 'fresh execution and root-cause classification'])


def validate_driver_cohort(manifest, frozen):
    actual = sorted(v['id'] for c in manifest['cases'] for v in c['variants'] if 'behavioral_contract' in v)
    if (frozen['upstream_revision'] != REVISION or actual != frozen['variant_ids'] or len(actual) != 355
            or frozen['starting_manifest_sha256'] != 'bcb0f5a06fa9dc5959bc59bfc78e1ea4afaed91aaac8789876e48f11e20c3470'):
        raise ValueError('driver starting cohort changed: no denominator substitution permitted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', required=True)
    parser.add_argument('--harness-sources', required=True)
    parser.add_argument('--oracle', required=True)
    parser.add_argument('--out-dir', required=True)
    args = parser.parse_args()
    targets, sources = load_inputs(args.inventory, args.harness_sources)
    oracle = read_json(args.oracle)
    if oracle.get('githash') != REVISION:
        raise ValueError('wrong recorded oracle revision')
    tool = {key: oracle[key] for key in ('world', 'version', 'githash', 'executable_sha256', 'archive_sha256')}
    manifest = build_manifest(targets, sources, tool)
    frozen = read_json(Path(args.harness_sources).parent / 'driver-starting-ids.json')
    validate_driver_cohort(manifest, frozen)
    manifest['driver_starting_cohort'] = frozen
    raw = encoded(manifest)
    out = Path(args.out_dir); out.mkdir(parents=True, exist_ok=True)
    (out / 'manifest.json.gz').write_bytes(gzip.compress(raw, mtime=0))
    summary = dict(manifest['summary'],
        driver_contract_producer_sha256=hashlib.sha256(Path(__file__).with_name('replacement_driver_contracts.py').read_bytes()).hexdigest(), schema='clean-upstream-test-case-summary-v2',
        upstream_revision=REVISION, manifest_sha256=hashlib.sha256(raw).hexdigest(),
        input_sha256={Path(p).name: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in
                      (args.inventory, args.harness_sources, args.oracle)},
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        remaining_inventory=manifest['remaining_inventory'], claim=manifest['claim'])
    (out / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps(manifest['summary'], indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
