#!/usr/bin/env python3
"""Untrusted consistency checks for archived Q6 replay bytes; never executes them.

This binds the retained images and replay observations to strict nonlocal lineage
records. It is not a proof, independent compilation, a fresh execution, historical
OS-exit authentication, installed-image binding, or a Q6 completion gate.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import sys
import tempfile
import zlib

import check_ck0_lineage as lineage

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RUNS = ROOT / 'reports/self-proof-q6-capture-2026-11-14'
CAPTURE_REPORT_RELATIVE = PurePosixPath('reports/self-proof-q6-capture-2026-11-14')
CAPTURE_NAMESPACES = {CAPTURE_REPORT_RELATIVE,
                      PurePosixPath('reports/self-proof-q6-measurement-2026-11-14/captures'),
                      PurePosixPath('reports/self-proof-q6-recapture-2026-11-14/captures')}
ANSWERS_PINNED_INPUTS = True
LANES = ('stock', 'trust')
CASES = {'core': (0, 2, 2, {}), 'ill-typed': (1, 2, 1, {'type-check': 1}),
         'extra-axiom': (1, 3, 2, {'axiom-policy': 1}), 'seed': (0, 22, 22, {})}
MAX_FILE_BYTES = 64 * 1024 * 1024
MAX_IMAGE_BYTES = 128 * 1024 * 1024
_SOURCE_AUTHENTICATED = set()
IMAGE_FIELDS = {'lane', 'archive', 'archive_sha256', 'archive_bytes',
                'image_sha256', 'image_bytes', 'format', 'proof_claim', 'genesis_seed'}
ROW_FIELDS = {'name', 'lane', 'argv', 'binary_sha256', 'input_sha256', 'exit_code',
              'coverage', 'reasons', 'stdout_sha256', 'stderr_sha256'}


def need(value, message):
    if not value:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def decode(data):
    return json.loads(data, object_pairs_hook=unique_object)


def canonical_path(value, absolute=False):
    need(isinstance(value, str) and bool(value) and '\\' not in value and '\0' not in value,
         'invalid lexical path')
    path = PurePosixPath(value)
    need(path.is_absolute() == absolute and str(path) == value and value != '.' and
         '..' not in path.parts and not value.startswith('//'), 'escaped or noncanonical path')
    return path


def safe_file(base, relative):
    parts = canonical_path(relative).parts
    path = base
    for index, part in enumerate(parts):
        path = path / part
        mode = path.lstat().st_mode
        need(not stat.S_ISLNK(mode), 'symlink evidence path: ' + relative)
        need(stat.S_ISREG(mode) if index == len(parts) - 1 else stat.S_ISDIR(mode),
             'nonregular evidence path: ' + relative)
    need(path.stat().st_size <= MAX_FILE_BYTES, 'evidence file exceeds supported size bound')
    return path


def read_file(base, relative):
    path = safe_file(base, relative)
    with path.open('rb') as stream:
        data = stream.read(MAX_FILE_BYTES + 1)
    need(len(data) <= MAX_FILE_BYTES, 'evidence file exceeds supported size bound')
    return data


def load_file(base, relative):
    return decode(read_file(base, relative))


def file_hash(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def cargo_binary_owner(base, lane, record, artifact):
    """Bind the chosen bytes to one root-package normal Cargo binary event."""
    canonical_path(artifact['path'], absolute=True)
    events = []
    for line in read_file(base, lane + '/' + record['steps'][-1]['log']).splitlines():
        try:
            item = decode(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(item, dict) or item.get('reason') != 'compiler-artifact':
            continue
        target = item.get('target')
        filenames = item.get('filenames')
        need(isinstance(filenames, list) and all(isinstance(path, str) for path in filenames),
             'Cargo artifact filenames shape')
        for path in filenames:
            canonical_path(path, absolute=True)
        executable = item.get('executable')
        if executable is not None:
            canonical_path(executable, absolute=True)
        # Include executable-path collisions even when the owner/target was
        # forged. Unrelated dependency targets with other paths remain valid.
        if artifact['path'] in filenames or item.get('executable') == artifact['path'] or (
                item.get('package_id') == record['ck0_package_id'] and
                isinstance(target, dict) and target.get('name') == 'ck0-replay'):
            events.append(item)
    need(len(events) == 1, 'Cargo replay binary event census')
    item = events[0]
    need(item.get('package_id') == record['ck0_package_id'], 'Cargo replay binary owner')
    target = item.get('target')
    need(isinstance(target, dict) and target.get('name') == 'ck0-replay',
         'Cargo replay binary target name')
    need(target.get('kind') == ['bin'] and target.get('crate_types') == ['bin'],
         'Cargo replay binary target kind/crate types')
    need(item.get('executable') == artifact['path'], 'Cargo replay binary executable')
    need(isinstance(item.get('filenames'), list) and artifact['path'] in item['filenames'],
         'Cargo replay binary event filenames')
    # target.test describes the target's test capability; profile.test describes
    # this compilation. Honest retained Cargo targets have target.test=True.
    need(isinstance(item.get('profile'), dict) and item['profile'].get('test') is False,
         'Cargo replay binary normal profile')


def image_identity(base, image, artifact, host):
    need(isinstance(image, dict) and set(image) == IMAGE_FIELDS, 'manifest image shape')
    lane = image['lane']
    need(image['archive'] == f'binary-data/{lane}-ck0-replay.bin.gz', 'image archive lane/path')
    need(image['proof_claim'] is False and image['genesis_seed'] is False, 'image cannot promote claims')
    need(image['format'] == f'gzip of {host} debug executable', 'image format/host')
    need(type(image['image_bytes']) is int and 0 < image['image_bytes'] <= MAX_IMAGE_BYTES,
         'image size exceeds supported bound')
    need(image['image_sha256'] == artifact['sha256'] and image['image_bytes'] == artifact['bytes'],
         'lane image identity differs from binary artifact')
    need(type(image['archive_bytes']) is int and 0 < image['archive_bytes'] <= MAX_FILE_BYTES,
         'archive size bound')
    path = safe_file(base, image['archive'])
    need(path.stat().st_size == image['archive_bytes'], 'archive length mismatch')
    need(file_hash(path) == image['archive_sha256'], 'archive digest mismatch')
    value, total = hashlib.sha256(), 0
    try:
        with gzip.open(path, 'rb') as stream:
            while True:
                data = stream.read(min(1024 * 1024, image['image_bytes'] - total + 1))
                if not data:
                    break
                total += len(data)
                need(total <= image['image_bytes'], 'decompressed image exceeds expected size')
                value.update(data)
    except (OSError, EOFError, zlib.error) as error:
        raise ValueError('invalid gzip image: ' + str(error)) from error
    need(total == image['image_bytes'] and value.hexdigest() == image['image_sha256'],
         'decompressed image identity mismatch')


def name_shape(name):
    need(isinstance(name, list) and bool(name), 'declaration name shape')
    for part in name:
        need(isinstance(part, dict) and len(part) == 1, 'declaration name component')
        if set(part) == {'str'}:
            need(isinstance(part['str'], str) and bool(part['str']), 'declaration string component')
        else:
            need(set(part) == {'num'} and type(part['num']) is int and part['num'] >= 0,
                 'declaration numeric component')


def fixture_names(data):
    """Read only the pinned export's name/declaration subset, not CIC judgments."""
    names, declarations = {0: []}, []
    for line in data.decode('utf-8').splitlines():
        item = decode(line)
        need(isinstance(item, dict), 'fixture record shape')
        if 'in' in item:
            index = item['in']
            need(type(index) is int and index > 0 and index not in names, 'fixture name ID')
            kind = 'str' if 'str' in item else 'num'
            need(set(item) == {'in', kind} and isinstance(item[kind], dict), 'fixture name record')
            value = item[kind]
            need(set(value) == ({'pre', 'str'} if kind == 'str' else {'pre', 'i'}),
                 'fixture name component shape')
            pre = value['pre']
            need(type(pre) is int and pre in names, 'fixture name prefix')
            component = {'str': value['str']} if kind == 'str' else {'num': value['i']}
            name_shape([component])
            names[index] = names[pre] + [component]
        kinds = set(item) & {'def', 'thm', 'axiom', 'inductive'}
        need(len(kinds) <= 1, 'ambiguous fixture declaration')
        if kinds:
            kind = next(iter(kinds))
            need(set(item) == {kind}, 'unsupported top-level declaration tag')
            body = item[kind]
            need(isinstance(body, dict), 'fixture declaration body')
            entries = [body]
            if kind == 'inductive':
                entries = []
                for group in ('types', 'ctors', 'recs'):
                    need(isinstance(body[group], list), 'fixture inductive names')
                    entries.extend(body[group])
            for entry in entries:
                need(isinstance(entry, dict) and type(entry.get('name')) is int and
                     entry['name'] in names, 'fixture declaration name reference')
                name_shape(names[entry['name']])
                declarations.append(names[entry['name']])
        elif 'in' not in item:
            supported = {frozenset({'meta'}), frozenset({'il', 'param'}),
                         frozenset({'il', 'succ'}), frozenset({'ie', 'bvar'}),
                         frozenset({'ie', 'sort'}), frozenset({'ie', 'forallE'}),
                         frozenset({'ie', 'lam'}), frozenset({'ie', 'const'}),
                         frozenset({'ie', 'app'}), frozenset({'ie', 'proj'}),
                         frozenset({'ie', 'natVal'})}
            need(frozenset(item) in supported, 'unsupported fixture record tag')
    need(len({json.dumps(name, sort_keys=True) for name in declarations}) == len(declarations),
         'duplicate fixture declaration name')
    return declarations


def stdout_observation(data, names):
    need(data.endswith(b'\n'), 'stdout NDJSON final newline')
    items = [decode(line) for line in data.decode('utf-8').splitlines()]
    need(len(items) == len(names) + 1, 'stdout declaration/coverage census')
    declarations, coverage = items[:-1], items[-1]
    reasons, accepted = [], 0
    for item, expected_name in zip(declarations, names):
        need(isinstance(item, dict) and item.get('kind') == 'declaration' and
             type(item.get('accepted')) is bool, 'stdout declaration shape')
        name_shape(item.get('name'))
        need(item['name'] == expected_name, 'stdout declaration names/order differ from fixture')
        if item['accepted']:
            need(set(item) == {'kind', 'name', 'accepted'}, 'accepted declaration shape')
            accepted += 1
        else:
            need(set(item) == {'kind', 'name', 'accepted', 'reason', 'detail'} and
                 isinstance(item['reason'], str) and bool(item['reason']) and
                 isinstance(item['detail'], str), 'rejected declaration shape')
            reasons.append(item['reason'])
    refused = {reason: reasons.count(reason) for reason in sorted(set(reasons))}
    expected = {'kind': 'coverage', 'accepted': accepted, 'total': len(names),
                'axioms': [], 'refused': refused}
    need(isinstance(coverage, dict) and set(coverage) == set(expected) and
         type(coverage['accepted']) is int and type(coverage['total']) is int and
         isinstance(coverage['refused'], dict) and all(type(v) is int for v in coverage['refused'].values()) and
         coverage == expected, 'stdout coverage differs from declarations')
    return coverage, reasons, [item['accepted'] for item in declarations]


def capture_namespace(runs):
    try:
        relative = Path(runs).resolve(strict=True).relative_to(ROOT.resolve())
    except ValueError as error:
        raise ValueError('runs has no trusted repository-relative capture namespace') from error
    namespace = PurePosixPath(relative.as_posix())
    need(namespace in CAPTURE_NAMESPACES, 'unsupported capture namespace')
    return namespace


def committed_source(source):
    """Authenticate recorded Git blobs, not today's mutable source inventory."""
    need(isinstance(source, dict) and set(source) ==
         {'schema', 'kind', 'revision', 'files', 'proof_claim', 'genesis_promoted'} and
         source['schema'] == lineage.SCHEMA and source['kind'] == 'candidate-source' and
         source['proof_claim'] is False and source['genesis_promoted'] is False,
         'archived source record shape/claim')
    revision = source['revision']
    need(isinstance(revision, str) and len(revision) == 40 and
         set(revision) <= set('0123456789abcdef'), 'archived source revision')
    lineage.checked_inventory(source['files'], 'archived source file inventory')
    identity = digest(encoded(source))
    if identity in _SOURCE_AUTHENTICATED:
        return
    # Git object reads must not acquire missing objects from the network or apply
    # replacement refs to the reported immutable commit. Restore caller state.
    settings = {'GIT_NO_LAZY_FETCH': '1', 'GIT_TERMINAL_PROMPT': '0', 'GIT_NO_REPLACE_OBJECTS': '1'}
    previous = {key: os.environ.get(key) for key in settings}
    try:
        os.environ.update(settings)
        need(lineage.git(lineage.ROOT, 'cat-file', '-t', revision).strip() == 'commit',
             'archived source must name a commit')
        actual = lineage.git_files(lineage.ROOT, revision,
                                   [*lineage.BASE, lineage.CRATE, '.cargo'])
    finally:
        for key, value in previous.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
    lineage.same_inputs(source['files'], actual)
    _SOURCE_AUTHENTICATED.add(identity)


def validate(runs, source_path, expected_namespace=None):
    base = Path(runs).resolve(strict=True)
    namespace = capture_namespace(runs) if expected_namespace is None else expected_namespace
    need(namespace in CAPTURE_NAMESPACES, 'unsupported trusted capture namespace')
    need(base.is_dir(), 'runs directory')
    receipt = load_file(base, 'EVIDENCE.json')
    need(isinstance(receipt, dict) and isinstance(receipt.get('files'), dict), 'outer evidence census')
    required = {'binary-data/manifest.json', 'replay.json'} | {
        name + suffix for name in CASES for suffix in ('.ndjson',)} | {
        f'{name}-{lane}.{suffix}' for name in CASES for lane in LANES for suffix in ('stdout', 'stderr')}
    required |= {f'binary-data/{lane}-ck0-replay.bin.gz' for lane in LANES}
    need(required <= set(receipt['files']), 'missing replay-custody payload in outer seal')
    for relative in receipt['files']:
        safe_file(base, relative)
    source_path = Path(source_path)
    need(source_path.is_file() and source_path.stat().st_size <= MAX_FILE_BYTES, 'source record size/type')
    source = decode(source_path.read_bytes())
    committed_source(source)
    production = read_file(base, 'production.json')
    lineage.checked_production(decode(production))
    lineage.checked_receipt(base, source, production)
    records, artifacts, roots = {}, {}, {}
    for lane in LANES:
        record = load_file(base, lane + '/run.json')
        for phase in ('before', 'after-default', 'after-export', 'after-binary'):
            relative = lane + '/inputs-' + phase + '.json'
            need(relative in receipt['files'], 'snapshot missing from outer seal')
            load_file(base, relative)
        record = lineage.checked_run(base / lane / 'run.json', source,
                                     local=False, require_stability=True)
        need(record['label'] == lane, 'build lane label')
        candidates = [value for name, value in record['steps'][-1]['artifacts'].items()
                      if PurePosixPath(name).name == 'ck0-replay']
        need(len(candidates) == 1, 'lane binary-artifact census')
        cargo_binary_owner(base, lane, record, candidates[0])
        records[lane], artifacts[lane] = record, candidates[0]
        before = load_file(base, lane + '/inputs-before.json')
        roots[lane] = canonical_path(before['state']['source_root'], absolute=True)
    need(records['stock']['compiler']['sha256'] != records['trust']['compiler']['sha256'],
         'compiler images identical')
    for phase in ('default', 'export'):
        first = next(step for step in records['stock']['steps'] if step['name'] == phase)
        second = next(step for step in records['trust']['steps'] if step['name'] == phase)
        need(all(first[key] == second[key] for key in ('tests', 'test_names', 'test_targets')),
             'paired build test identities differ')
    manifest = load_file(base, 'binary-data/manifest.json')
    need(isinstance(manifest, dict) and set(manifest) == {'proof_claim', 'genesis_promoted', 'scope', 'images'} and
         manifest['proof_claim'] is False and manifest['genesis_promoted'] is False,
         'manifest cannot promote claims')
    need(isinstance(manifest['images'], list) and len(manifest['images']) == 2 and
         {image.get('lane') for image in manifest['images'] if isinstance(image, dict)} == set(LANES),
         'manifest lane census')
    for image in manifest['images']:
        lane = image['lane']
        targets = [line.removeprefix('host: ') for line in records[lane]['version'].splitlines()
                   if line.startswith('host: ')]
        need(len(targets) == 1 and bool(targets[0]), 'compiler target census')
        image_identity(base, image, artifacts[lane], targets[0])
    fixtures = {name: read_file(base, name + '.ndjson') for name in CASES}
    need(digest(fixtures['core']) == source['files']['crates/clean-ck0/tests/fixtures/q2-core.ndjson'],
         'core fixture differs from candidate source')
    need(digest(fixtures['seed']) == source['files']['reports/self-proof-q2-2026-11-12/seed.ndjson'],
         'seed fixture differs from candidate source')
    token = b'"type":8,"value":9'
    need(fixtures['core'].count(token) == 1 and fixtures['ill-typed'] ==
         fixtures['core'].replace(token, b'"type":8,"value":7'), 'ill-typed false-twin fixture')
    need(fixtures['extra-axiom'] == fixtures['core'] +
         b'{"axiom":{"name":1,"levelParams":[],"type":7,"isUnsafe":false}}\n',
         'extra-axiom false-twin fixture')
    names = {name: fixture_names(data) for name, data in fixtures.items()}
    replay = load_file(base, 'replay.json')
    need(isinstance(replay, dict) and set(replay) == {'proof_claim', 'rows'} and
         replay['proof_claim'] is False and isinstance(replay['rows'], list) and len(replay['rows']) == 8,
         'replay row census/claim')
    seen, outputs, relative_parents = set(), {}, set()
    for row in replay['rows']:
        need(isinstance(row, dict) and set(row) == ROW_FIELDS, 'replay row shape')
        key = (row['name'], row['lane'])
        need(key[0] in CASES and key[1] in LANES and key not in seen, 'duplicate/unknown replay row')  # gitleaks:allow
        seen.add(key)
        name, lane = key
        expected_exit, total, accepted, refused = CASES[name]
        need(type(row['exit_code']) is int and row['exit_code'] == expected_exit, 'replay exit mismatch')
        need(isinstance(row['argv'], list) and len(row['argv']) == 2 and
             row['argv'][0] == artifacts[lane]['path'], 'replay binary argv mismatch')
        input_path = canonical_path(row['argv'][1], absolute=True)
        need(input_path == roots[lane] / namespace / (name + '.ndjson'),
             'replay input argv mismatch')
        relative = input_path.parent.relative_to(roots[lane])
        need(len(relative.parts) >= 2 and relative.parts[0] == 'reports', 'replay input report namespace')
        relative_parents.add(str(relative))
        need(row['binary_sha256'] == artifacts[lane]['sha256'], 'replay binary identity mismatch')
        need(row['input_sha256'] == digest(fixtures[name]), 'replay input identity mismatch')
        out, err = (read_file(base, f'{name}-{lane}.{suffix}') for suffix in ('stdout', 'stderr'))
        need(digest(out) == row['stdout_sha256'] and digest(err) == row['stderr_sha256'],
             'replay output digest mismatch')
        need(not err, 'unexpected replay stderr')
        coverage, reasons, mask = stdout_observation(out, names[name])
        expected_mask = {'core': [True] * 2, 'seed': [True] * 22,
                         'ill-typed': [True, False], 'extra-axiom': [True, True, False]}[name]
        need(mask == expected_mask, 'expected declaration acceptance mask')
        need(encoded(row['coverage']) == encoded(coverage) and row['reasons'] == reasons,
             'replay observation differs from raw output')
        need(coverage == {'kind': 'coverage', 'accepted': accepted, 'total': total,
                          'axioms': [], 'refused': refused} and
             reasons == {'core': [], 'seed': [], 'ill-typed': ['type-check'],
                         'extra-axiom': ['axiom-policy']}[name], 'expected replay outcome mismatch')
        outputs[key] = out
    need(seen == {(name, lane) for name in CASES for lane in LANES} and len(relative_parents) == 1,
         'replay matrix/report-parent census')
    need(all(outputs[name, 'stock'] == outputs[name, 'trust'] for name in CASES),
         'paired replay outputs differ')
    return {'kind': 'archived-replay-custody-consistency', 'images': 2, 'replay_rows': 8,
            'proof_claim': False, 'q6_complete': False, 'binary_execution': False,
            'independent_DDC': False, 'production_image_binding': False,
            'capture_relative_namespace': str(namespace),
            'source_sha256': lineage.digest(lineage.encoded(source))}


def selftest(runs, source):
    """Isolated candidate copies only; never mutate the sealed report or execute images."""
    outcomes, legacy = [], []
    namespace = capture_namespace(runs)
    with tempfile.TemporaryDirectory(prefix='q6-replay-custody-') as temporary:
        base = Path(temporary) / 'runs'
        shutil.copytree(runs, base, symlinks=True)
        validate(base, source, namespace)

        # Owned JSON-only event fixtures exercise every path slot, including
        # unrelated dependencies. They create no executable or Rust source.
        toy = Path(temporary) / 'cargo-paths'
        (toy / 'stock').mkdir(parents=True)
        selected = '/synthetic with spaces/ck0-replay'
        toy_record = {'ck0_package_id': 'synthetic-root', 'steps': [{'log': 'binary.log'}]}
        toy_artifact = {'path': selected}
        root_event = {'reason': 'compiler-artifact', 'package_id': 'synthetic-root',
                      'target': {'name': 'ck0-replay', 'kind': ['bin'], 'crate_types': ['bin']},
                      'filenames': [selected], 'executable': selected, 'profile': {'test': False}}
        dependency = {'reason': 'compiler-artifact', 'package_id': 'synthetic-dependency',
                      'target': {'name': 'dependency', 'kind': ['lib'], 'crate_types': ['rlib']},
                      'filenames': ['/synthetic with spaces/libdependency.rlib'],
                      'executable': None, 'profile': {'test': False}}

        def toy_check(events, artifact):
            (toy / 'stock/binary.log').write_bytes(b''.join(json.dumps(event).encode() + b'\n'
                                                           for event in events))
            cargo_binary_owner(toy, 'stock', toy_record, artifact)

        toy_check([root_event, dependency], toy_artifact)
        other = decode(encoded(dependency))
        other['executable'] = '/synthetic with spaces/build-script-build'
        toy_check([root_event, other], toy_artifact)
        invalid_paths = (
            ('dot', '/synthetic with spaces/./ck0-replay', 'escaped or noncanonical path'),
            ('parent', '/synthetic with spaces/sub/../ck0-replay', 'escaped or noncanonical path'),
            ('separator', '/synthetic with spaces//ck0-replay', 'escaped or noncanonical path'),
            ('relative', 'synthetic/ck0-replay', 'escaped or noncanonical path'),
            ('empty', '', 'invalid lexical path'),
            ('backslash', '/synthetic\\ck0-replay', 'invalid lexical path'),
            ('nul', '/synthetic/ck0\0-replay', 'invalid lexical path'),
            ('nonstring', 0, 'invalid lexical path'),
        )
        for slot in ('selected', 'filename', 'executable'):
            for label, value, reason in invalid_paths:
                events = decode(encoded([root_event, dependency]))
                artifact = dict(toy_artifact)
                if slot == 'selected':
                    artifact['path'] = value
                elif slot == 'filename':
                    events[1]['filenames'].append(value)
                    if not isinstance(value, str):
                        reason = 'Cargo artifact filenames shape'
                else:
                    events[1]['executable'] = value
                try:
                    toy_check(events, artifact)
                except (ValueError, TypeError) as error:
                    need(reason in str(error), 'wrong Cargo path refusal: ' + str(error))
                    outcomes.append({'case': 'Cargo-path-' + slot + '-' + label,
                                     'refused': True, 'reason': str(error)})
                else:
                    raise ValueError('Cargo path negative accepted: ' + slot + '-' + label)

        original_source = decode(Path(source).read_bytes())
        source_copy = Path(temporary) / 'source.json'
        first_path = next(iter(original_source['files']))
        safe_env = {**os.environ, 'GIT_NO_LAZY_FETCH': '1', 'GIT_TERMINAL_PROMPT': '0',
                    'GIT_NO_REPLACE_OBJECTS': '1'}
        tree = subprocess.check_output(['git', '--no-replace-objects', '-C', str(ROOT),
                                        'rev-parse', '--verify', original_source['revision'] + '^{tree}'],
                                       text=True, env=safe_env).strip()
        for label, mutate, reason in (
            ('source-revision-option-injection', lambda value: value.__setitem__('revision', '--help'),
             'archived source revision'),
            ('source-tree-object-is-not-commit', lambda value: value.__setitem__('revision', tree),
             'archived source must name a commit'),
            ('source-boolean-hash', lambda value: value['files'].__setitem__(first_path, True),
             'archived source file inventory'),
            ('source-missing-committed-path', lambda value: value['files'].pop(first_path),
             'input inventory changed'),
            ('source-wrong-committed-hash', lambda value: value['files'].__setitem__(first_path, '0' * 64),
             'input digest changed'),
            ('source-proof-promotion', lambda value: value.__setitem__('proof_claim', True),
             'archived source record shape/claim'),
        ):
            value = decode(encoded(original_source))
            mutate(value)
            source_copy.write_bytes(encoded(value))
            try:
                validate(base, source_copy, namespace)
            except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
                need(reason in str(error), f'{label}: wrong refusal: {error}')
                outcomes.append({'case': label, 'refused': True, 'reason': str(error)})
            else:
                raise ValueError('source negative control accepted: ' + label)

        def replace(relative, data):
            path = base / relative
            path.write_bytes(data)

        def change(relative, edit):
            value = decode((base / relative).read_bytes())
            edit(value)
            replace(relative, encoded(value))

        def reseal(paths):
            receipt = decode((base / 'EVIDENCE.json').read_bytes())
            for relative in paths:
                path = base / relative
                if path.exists():
                    receipt['files'][relative] = digest(path.read_bytes())
                else:
                    receipt['files'].pop(relative, None)
            replace('EVIDENCE.json', encoded(receipt))

        def old_receiver():
            archived = decode(Path(source).read_bytes())
            lineage.checked_receipt(base, archived, (base / 'production.json').read_bytes())
            for lane in LANES:
                lineage.checked_run(base / lane / 'run.json', archived,
                                    local=False, require_stability=True)
            return 'strict nonlocal receipt/run validators accepted'

        def refuses(label, paths, mutate, reason, legacy_accepts=False):
            backups = {name: (base / name).read_bytes() for name in {*paths, 'EVIDENCE.json'}}
            cleanup = None
            try:
                cleanup = mutate()
                reseal(paths)
                if legacy_accepts:
                    text = old_receiver()
                    need('validators accepted' in text, 'legacy control did not accept')
                    legacy.append({'case': label, 'receipt_run_validators_accepted': True, 'stdout': text})
                try:
                    validate(base, source, namespace)
                except (ValueError, KeyError, TypeError, OSError, EOFError, UnicodeError) as error:
                    need(reason in str(error), f'{label}: wrong refusal: {error}')
                    outcomes.append({'case': label, 'refused': True, 'reason': str(error)})
                else:
                    raise ValueError('negative control accepted: ' + label)
            finally:
                if cleanup:
                    cleanup()
                for name, data in backups.items():
                    path = base / name
                    if path.is_symlink():
                        path.unlink()
                    path.write_bytes(data)

        manifest = 'binary-data/manifest.json'
        replay = 'replay.json'
        archive = 'binary-data/trust-ck0-replay.bin.gz'

        def cargo_event_change(edit):
            record = load_file(base, 'trust/run.json')
            step = record['steps'][-1]
            rows = []
            for line in read_file(base, 'trust/binary.log').splitlines():
                try:
                    item = decode(line)
                except json.JSONDecodeError:
                    item = None
                rows.append(item if isinstance(item, dict) else line)
            positions = [index for index, item in enumerate(rows) if isinstance(item, dict) and
                         item.get('reason') == 'compiler-artifact' and
                         item.get('package_id') == record['ck0_package_id'] and
                         item.get('target', {}).get('name') == 'ck0-replay']
            need(len(positions) == 1, 'Cargo control original event census')
            edit(rows, positions[0], record)
            data = b'\n'.join(json.dumps(item, separators=(',', ':')).encode()
                              if isinstance(item, dict) else item for item in rows) + b'\n'
            step['packages'] = sorted({item['package_id'] for item in rows if isinstance(item, dict) and
                                       item.get('reason') == 'compiler-artifact'})
            step['log_sha256'] = digest(data)
            replace('trust/binary.log', data)
            replace('trust/run.json', encoded(record))

        def wrong_cargo_owner(rows, index, record):
            rows[index]['package_id'] = next(value for value in record['steps'][-1]['packages']
                                              if value != record['ck0_package_id'])

        def duplicate_cargo_event(rows, index, record, conflicting=False):
            rows.append(decode(encoded(rows[index])))
            if conflicting:
                wrong_cargo_owner(rows, len(rows) - 1, record)

        def move_cargo_filenames(rows, index, record, remove=False, retain=False):
            other = next(item for item in rows if isinstance(item, dict) and
                         item.get('reason') == 'compiler-artifact' and
                         item['package_id'] != record['ck0_package_id'])
            other['filenames'].extend(rows[index]['filenames'])
            if remove:
                rows.pop(index)
            elif not retain:
                rows[index]['filenames'] = []

        def foreign_cargo_alias(rows, index, record, slot, component):
            other = next(item for item in rows if isinstance(item, dict) and
                         item.get('reason') == 'compiler-artifact' and
                         item['package_id'] != record['ck0_package_id'])
            parent, leaf = rows[index]['executable'].rsplit('/', 1)
            alias = parent + '/' + component + leaf
            if slot == 'filenames':
                other[slot].append(alias)
            else:
                other[slot] = alias

        for label, edit, reason in (
            ('wrong-owner', wrong_cargo_owner, 'Cargo replay binary owner'),
            ('wrong-target-name', lambda rows, i, r: rows[i]['target'].__setitem__('name', 'other-replay'),
             'Cargo replay binary target name'),
            ('wrong-target-kind', lambda rows, i, r: rows[i]['target'].__setitem__('kind', ['lib']),
             'Cargo replay binary target kind/crate types'),
            ('wrong-crate-types', lambda rows, i, r: rows[i]['target'].__setitem__('crate_types', ['rlib']),
             'Cargo replay binary target kind/crate types'),
            ('wrong-executable', lambda rows, i, r: rows[i].__setitem__('executable', '/tmp/other-replay'),
             'Cargo replay binary executable'),
            ('missing-executable', lambda rows, i, r: rows[i].pop('executable'),
             'Cargo replay binary executable'),
            ('test-profile', lambda rows, i, r: rows[i]['profile'].__setitem__('test', True),
             'Cargo replay binary normal profile'),
            ('integer-profile', lambda rows, i, r: rows[i]['profile'].__setitem__('test', 0),
             'Cargo replay binary normal profile'),
            ('duplicate-event', duplicate_cargo_event, 'Cargo replay binary event census'),
            ('conflicting-owner-duplicate', lambda rows, i, r: duplicate_cargo_event(rows, i, r, True),
             'Cargo replay binary event census'),
            ('missing-event-foreign-filenames', lambda rows, i, r: move_cargo_filenames(rows, i, r, True),
             'Cargo replay binary owner'),
            ('executable-foreign-filenames', move_cargo_filenames, 'Cargo replay binary event census'),
            ('retained-root-foreign-filenames', lambda rows, i, r: move_cargo_filenames(rows, i, r, retain=True),
             'Cargo replay binary event census'),
            ('foreign-dot-filename', lambda rows, i, r: foreign_cargo_alias(rows, i, r, 'filenames', './'),
             'escaped or noncanonical path'),
            ('foreign-parent-filename', lambda rows, i, r: foreign_cargo_alias(rows, i, r, 'filenames', 'sub/../'),
             'escaped or noncanonical path'),
            ('foreign-double-separator', lambda rows, i, r: foreign_cargo_alias(rows, i, r, 'filenames', '/'),
             'escaped or noncanonical path'),
            ('foreign-dot-executable', lambda rows, i, r: foreign_cargo_alias(rows, i, r, 'executable', './'),
             'escaped or noncanonical path'),
        ):
            refuses('Cargo-binary-' + label, ['trust/binary.log', 'trust/run.json'],
                    lambda edit=edit: cargo_event_change(edit), reason, legacy_accepts=True)

        def manifest_field(field, value):
            return lambda: change(manifest, lambda doc: doc['images'][1].__setitem__(field, value))

        def row_edit(edit):
            return lambda: change(replay, lambda doc: edit(next(row for row in doc['rows']
                                     if row['lane'] == 'trust' and row['name'] == 'ill-typed')))

        def wrong_image():
            def edit(doc):
                doc['images'][1] = {**doc['images'][0], 'lane': 'trust'}
            change(manifest, edit)

        def accepted_false():
            def edit(row):
                row['exit_code'] = 0
                row['reasons'] = []
                row['coverage']['refused'] = {}
                row['coverage']['accepted'] = row['coverage']['total']
            row_edit(edit)()

        refuses('wrong-real-stock-image-for-trust', [manifest], wrong_image,
                'image archive lane/path', legacy_accepts=True)
        refuses('false-twin-row-forged-accepted', [replay], accepted_false,
                'replay exit mismatch', legacy_accepts=True)
        refuses('missing-image', [manifest], lambda: change(manifest, lambda d: d['images'].pop()),
                'manifest lane census')
        refuses('extra-image', [manifest], lambda: change(manifest, lambda d: d['images'].append(d['images'][0])),
                'manifest lane census')
        refuses('duplicate-image-lane', [manifest], manifest_field('lane', 'stock'), 'manifest lane census')
        refuses('escaped-image-path', [manifest], manifest_field('archive', '../outside.gz'),
                'image archive lane/path')
        refuses('wrong-image-raw-hash', [manifest], manifest_field('image_sha256', '0' * 64),
                'lane image identity')
        refuses('wrong-image-raw-size', [manifest], manifest_field('image_bytes', 1), 'lane image identity')
        refuses('oversized-image-bound', [manifest], manifest_field('image_bytes', MAX_IMAGE_BYTES + 1),
                'image size exceeds supported bound')
        refuses('boolean-image-size', [manifest], manifest_field('image_bytes', True), 'image size')
        refuses('wrong-archive-size', [manifest], manifest_field('archive_bytes', 1), 'archive length')
        refuses('wrong-archive-hash', [manifest], manifest_field('archive_sha256', '0' * 64), 'archive digest')
        refuses('image-proof-promotion', [manifest], manifest_field('proof_claim', True), 'image cannot promote')

        def changed_archive(transform):
            data = transform((base / archive).read_bytes())
            replace(archive, data)
            change(manifest, lambda d: d['images'][1].update(
                archive_sha256=digest(data), archive_bytes=len(data)))

        refuses('truncated-gzip', [archive, manifest], lambda: changed_archive(lambda data: data[:-8]),
                'invalid gzip image')
        refuses('invalid-DEFLATE-block', [archive, manifest], lambda: changed_archive(
            lambda data: b'\x1f\x8b\x08\x00' + b'\0' * 6 + b'\x07' + b'\0' * 8),
            'invalid gzip image')
        refuses('different-decoded-image', [archive, manifest], lambda: changed_archive(
            lambda data: gzip.compress(bytes([gzip.decompress(data)[0] ^ 1]) + gzip.decompress(data)[1:], mtime=0)),
            'decompressed image identity')
        refuses('decoded-image-too-long', [archive, manifest], lambda: changed_archive(
            lambda data: gzip.compress(gzip.decompress(data) + b'x', mtime=0)),
            'decompressed image exceeds expected size')

        def same_path_wrong_image(update_raw):
            data = (base / 'binary-data/stock-ck0-replay.bin.gz').read_bytes()
            replace(archive, data)
            def edit(doc):
                doc['images'][1].update(archive_sha256=digest(data), archive_bytes=len(data))
                if update_raw:
                    doc['images'][1].update(image_sha256=doc['images'][0]['image_sha256'],
                                            image_bytes=doc['images'][0]['image_bytes'])
            change(manifest, edit)
        refuses('wrong-real-image-bytes-same-trust-path', [archive, manifest],
                lambda: same_path_wrong_image(False), 'decompressed image exceeds expected size')
        refuses('wrong-cohort-raw-identity-same-trust-path', [archive, manifest],
                lambda: same_path_wrong_image(True), 'lane image identity')
        refuses('missing-replay-row', [replay], lambda: change(replay, lambda d: d['rows'].pop()),
                'replay row census')
        refuses('extra-replay-row', [replay], lambda: change(replay, lambda d: d['rows'].append(d['rows'][0])),
                'replay row census')
        refuses('duplicate-replay-row', [replay], lambda: change(replay, lambda d: d['rows'].__setitem__(1, d['rows'][0])),
                'duplicate/unknown replay row')
        refuses('wrong-replay-lane', [replay], row_edit(lambda row: row.__setitem__('lane', 'other')),
                'duplicate/unknown replay row')
        refuses('boolean-replay-exit', [replay], row_edit(lambda row: row.__setitem__('exit_code', True)),
                'replay exit mismatch')
        refuses('wrong-binary-argv', [replay], row_edit(lambda row: row['argv'].__setitem__(0, '/bin/false')),
                'replay binary argv mismatch')
        refuses('escaped-input-argv', [replay], row_edit(lambda row: row['argv'].__setitem__(1, '/tmp/../ill-typed.ndjson')),
                'escaped or noncanonical path')
        refuses('wrong-input-argv-name', [replay], row_edit(lambda row: row['argv'].__setitem__(1, '/tmp/core.ndjson')),
                'replay input argv mismatch')
        def rerouted_inputs():
            def edit(doc):
                for row in doc['rows']:
                    path = PurePosixPath(row['argv'][1])
                    row['argv'][1] = str(path.parent.parent / 'other-report' / path.name)
            change(replay, edit)
        refuses('all-eight-argv-inputs-rerouted', [replay], rerouted_inputs, 'replay input argv mismatch')
        def relocated_inputs(destination):
            def edit(doc):
                for row in doc['rows']:
                    before = load_file(base, row['lane'] + '/inputs-before.json')
                    root = canonical_path(before['state']['source_root'], absolute=True)
                    row['argv'][1] = str(root / destination / (row['name'] + '.ndjson'))
            change(replay, edit)
        synthetic_namespaces = []
        for other_namespace in sorted(CAPTURE_NAMESPACES - {namespace}):
            refuses('candidate-cannot-choose-namespace-' + str(other_namespace), [replay],
                    lambda target=other_namespace: relocated_inputs(target),
                    'replay input argv mismatch')
            saved = {name: (base / name).read_bytes() for name in (replay, 'EVIDENCE.json')}
            try:
                relocated_inputs(other_namespace)
                reseal([replay])
                validate(base, source, other_namespace)
                synthetic_namespaces.append(str(other_namespace))
            finally:
                for name, data in saved.items():
                    replace(name, data)
        refuses('wrong-replay-binary-hash', [replay], row_edit(lambda row: row.__setitem__('binary_sha256', '0' * 64)),
                'replay binary identity')
        refuses('wrong-replay-input-hash', [replay], row_edit(lambda row: row.__setitem__('input_sha256', '0' * 64)),
                'replay input identity')
        refuses('wrong-replay-stdout-hash', [replay], row_edit(lambda row: row.__setitem__('stdout_sha256', '0' * 64)),
                'replay output digest')
        refuses('forged-replay-coverage', [replay], row_edit(lambda row: row['coverage'].__setitem__('accepted', 2)),
                'replay observation differs')
        refuses('boolean-replay-coverage', [replay], row_edit(lambda row: row['coverage'].__setitem__('accepted', True)),
                'replay observation differs')
        refuses('forged-replay-reason', [replay], row_edit(lambda row: row.__setitem__('reasons', ['axiom-policy'])),
                'replay observation differs')
        refuses('wrong-core-source-fixture', ['core.ndjson'], lambda: replace('core.ndjson', b'{}\n'),
                'core fixture differs')
        refuses('wrong-seed-source-fixture', ['seed.ndjson'], lambda: replace('seed.ndjson', b'{}\n'),
                'seed fixture differs')
        refuses('different-false-twin-fixture', ['ill-typed.ndjson'], lambda: replace('ill-typed.ndjson', b'{}\n'),
                'ill-typed false-twin fixture')
        refuses('different-extra-axiom-fixture', ['extra-axiom.ndjson'], lambda: replace('extra-axiom.ndjson', b'{}\n'),
                'extra-axiom false-twin fixture')

        def output_change(suffix, transform):
            relative = 'ill-typed-trust.' + suffix
            data = transform((base / relative).read_bytes())
            replace(relative, data)
            row_edit(lambda row: row.__setitem__(suffix + '_sha256', digest(data)))()

        def output_json(edit):
            def transform(data):
                rows = [decode(line) for line in data.decode().splitlines()]
                edit(rows)
                return b''.join(json.dumps(row).encode() + b'\n' for row in rows)
            output_change('stdout', transform)

        for label, edit, reason in [
            ('wrong-stdout-name', lambda rows: rows[0].__setitem__('name', [{'str': 'other'}]), 'names/order'),
            ('forged-stdout-coverage', lambda rows: rows[-1].__setitem__('accepted', 2), 'stdout coverage'),
            ('boolean-stdout-count', lambda rows: rows[-1].__setitem__('accepted', True), 'stdout coverage'),
            ('extra-coverage-object', lambda rows: rows.append(rows[-1]), 'stdout declaration/coverage census'),
        ]:
            refuses(label, ['ill-typed-trust.stdout', replay], lambda edit=edit: output_json(edit), reason)
        refuses('unexpected-stderr', ['ill-typed-trust.stderr', replay],
                lambda: output_change('stderr', lambda data: b'error\n'), 'unexpected replay stderr')
        refuses('duplicate-json-key', [replay], lambda: replace(replay,
                (base / replay).read_bytes().replace(b'"proof_claim": false,',
                                                   b'"proof_claim": false, "proof_claim": false,', 1)),
                'duplicate JSON key')

        def different_pair():
            output_json(lambda rows: rows[1].__setitem__('detail', rows[1]['detail'] + ' changed'))
        refuses('paired-output-drift', ['ill-typed-trust.stdout', replay], different_pair,
                'paired replay outputs differ')

        def wrong_rejection_target(case):
            for lane in LANES:
                relative = f'{case}-{lane}.stdout'
                rows = [decode(line) for line in (base / relative).read_bytes().decode().splitlines()]
                rejected = 1 if case == 'ill-typed' else 2
                wrong = 0 if case == 'ill-typed' else 1
                reason, detail = rows[rejected]['reason'], rows[rejected]['detail']
                rows[rejected] = {key: value for key, value in rows[rejected].items()
                                  if key not in {'reason', 'detail'}}
                rows[rejected]['accepted'] = True
                rows[wrong].update(accepted=False, reason=reason, detail=detail)
                data = b''.join(json.dumps(row).encode() + b'\n' for row in rows)
                replace(relative, data)
                change(replay, lambda doc, lane=lane, data=data: next(row for row in doc['rows']
                       if row['lane'] == lane and row['name'] == case).__setitem__('stdout_sha256', digest(data)))
        for case in ('ill-typed', 'extra-axiom'):
            refuses('wrong-rejected-declaration-' + case,
                    [f'{case}-{lane}.stdout' for lane in LANES] + [replay],
                    lambda case=case: wrong_rejection_target(case), 'expected declaration acceptance mask')
        refuses('missing-manifest-payload', [manifest], lambda: (base / manifest).unlink(),
                'missing replay-custody payload')

        def linked_archive():
            target = Path(temporary) / 'outside-archive.gz'
            target.write_bytes((base / archive).read_bytes())
            (base / archive).unlink()
            (base / archive).symlink_to(target)
        refuses('symlink-archive', [archive], linked_archive, 'symlink evidence path')

        def linked_directory():
            real = Path(temporary) / 'detached-binary-data'
            (base / 'binary-data').rename(real)
            (base / 'binary-data').symlink_to(real, target_is_directory=True)
            def cleanup():
                (base / 'binary-data').unlink()
                real.rename(base / 'binary-data')
            return cleanup
        refuses('symlink-evidence-directory', [], linked_directory, 'symlink evidence path')
        validate(base, source, namespace)

        try:
            fixture_names(b'{"unsupported-declaration": {"name": 1}}\n')
        except ValueError as error:
            need('unsupported fixture record tag' in str(error), 'unsupported-tag control wrong refusal')
            outcomes.append({'case': 'unsupported-fixture-record-tag', 'refused': True, 'reason': str(error)})
        else:
            raise ValueError('unsupported fixture record tag accepted')

        prefix = b'{"in":1,"str":{"pre":0,"str":"owned"}}\n'
        need(fixture_names(prefix + b'{"def":{"name":1}}\n') == [[{'str': 'owned'}]],
             'singleton declaration positive')
        try:
            fixture_names(prefix + b'{"def":{"name":1},"unsupported-declaration":{"name":1}}\n')
        except ValueError as error:
            need('unsupported top-level declaration tag' in str(error), 'extra declaration tag wrong refusal')
            outcomes.append({'case': 'extra-top-level-declaration-tag', 'refused': True, 'reason': str(error)})
        else:
            raise ValueError('extra top-level declaration tag accepted')

        missing = base / 'must-not-exist'
        for flags in (["--runs", str(missing), "--selftest"],
                      ["--runs", str(missing), "--pinned-inputs"],
                      ["--source", str(missing), "--selftest"],
                      ["--source", str(missing), "--pinned-inputs"],
                      ["--selftest", "--pinned-inputs"],
                      ["--runs", str(missing), "--selftest", "--pinned-inputs"]):
            result = subprocess.run([sys.executable, '-B', str(Path(__file__).resolve()), *flags],
                                    capture_output=True, text=True, timeout=30)
            need(result.returncode == 1 and 'conflicting action modes' in result.stderr and
                 not missing.exists(), 'CLI action skipped requested validation')
            outcomes.append({'case': 'CLI-' + '-'.join(flag for flag in flags if flag.startswith('--')),
                             'refused': True, 'reason': result.stderr.strip()})
    print(json.dumps({'negative_controls': len(outcomes), 'positive_accepted': True,
                      'synthetic_namespace_positives': synthetic_namespaces,
                      'controls': outcomes, 'legacy_receipt_run_acceptance_controls': legacy,
                      'persistent_original_payloads_modified': False, 'Rust_or_image_execution': False},
                     sort_keys=True))
    print(f'Q6 replay-custody selftest: {len(outcomes)} negative controls refused; positive accepted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path)
    parser.add_argument('--source', type=Path)
    parser.add_argument('--selftest', action='store_true')
    parser.add_argument('--pinned-inputs', action='store_true')
    args = parser.parse_args()
    need(not (args.selftest and args.pinned_inputs) and
         not ((args.selftest or args.pinned_inputs) and (args.runs or args.source)),
         'conflicting action modes: requested validation cannot be skipped')
    runs = args.runs or DEFAULT_RUNS
    source = args.source or ROOT / 'genesis/ck0/CANDIDATE.json'
    if args.pinned_inputs:
        print('\n'.join(sorted({'scripts/check_ck0_lineage.py', *lineage.PRODUCER_FILES})))
    elif args.selftest:
        selftest(DEFAULT_RUNS, DEFAULT_RUNS / 'source.json')
    else:
        print(json.dumps(validate(runs, source), sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, EOFError, UnicodeError,
            subprocess.CalledProcessError) as error:
        print('Q6 REPLAY CUSTODY REFUSED: ' + str(error), file=sys.stderr)
        sys.exit(1)
