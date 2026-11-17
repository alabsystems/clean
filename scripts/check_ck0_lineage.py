#!/usr/bin/env python3
"""Q6 evidence bookkeeping, NOT a proved checker or a compiler-correctness gate.

The candidate inventory and two rustc-family builds never promote a genesis seed.
--require-q6 deliberately refuses until independent compilation and the production
closure have been qualified. See README.md for that boundary.
"""
import argparse
import copy
import datetime
import platform
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import stat
try:
    import tomllib
except ImportError:
    import tomli as tomllib

ROOT = Path(__file__).resolve().parents[1]
RESOURCE_HELPER = 'scripts/resource_transport.py'
LEGACY_BASE = ('Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', '.cargo/config.toml',
        'reports/self-proof-q2-2026-11-12/seed.ndjson',
        'crates/clean-kernel/src/level/fixtures/lean_kernel_verdicts_v4.30.0-rc2.tsv')
BASE = (*LEGACY_BASE, RESOURCE_HELPER)
CRATE = 'crates/clean-ck0'
SCHEMA = 'clean.ck0-lineage/v1'
# Historical v1 source records did not bind the transport helper. Keep their
# immutable scope explicit; a new capture cannot select that weaker profile.
SOURCE_SCHEMA = 'clean.ck0-candidate-source/v2'
PRODUCTION_PATHS = {'trust_manifest': 'crates/trust-spec-temporal/Cargo.toml',
                    'trust_lock': 'crates/trust-spec-temporal/Cargo.lock',
                    'ty_manifest': 'crates/tla-check/Cargo.toml'}
RUN_TAILS = {'default': ['test', '--all-targets'],
             'export': ['test', '--all-targets', '--features', 'export'],
             'binary': ['build', '--bin', 'ck0-replay', '--features', 'export']}
ANSWERS_PINNED_INPUTS = True
PRODUCER_FILES = ('scripts/check_ck0_lineage.py', 'scripts/rust_modules.py',
                  'scripts/check_add_decl_ratchet.py', 'scripts/ck0_input_stability.py')
PRODUCTION_BATCH_TEST = 'scripts/test_ck0_production_batch.py'
CANDIDATE_CONTEXT_TEST = 'scripts/test_ck0_candidate_context.py'
TRANSPORT_TEST = 'scripts/test_ck0_transport.py'
SOURCE_PROFILE_TEST = 'scripts/test_ck0_source_profiles.py'
_RUST_MODULES = None


def need(ok, why):
    if not ok:
        raise ValueError(why)


class EvidenceJSONError(ValueError):
    """Ambiguous/non-finite evidence is not ignorable mixed-log text."""


def decode_evidence(data):
    violations = []
    def remember(reason):
        if not violations:
            violations.append(reason)

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                remember('duplicate JSON key: ' + repr(key))
            result[key] = value
        return result

    def nonfinite(word):
        remember('non-finite JSON number: ' + word)

    def finite_float(word):
        value = float(word)
        if not math.isfinite(value):
            nonfinite(word)
        return value

    # Mixed build logs contain prose beginning with JSON-looking tokens. Let
    # the complete syntax/trailing-data check reject those as non-JSON before
    # refusing semantic violations in an otherwise complete JSON record.
    value = json.loads(data, object_pairs_hook=unique_object,
                       parse_constant=nonfinite, parse_float=finite_float)
    if violations:
        raise EvidenceJSONError(violations[0])
    return value


def _source_module(name, path):
    """Execute the inventoried Python source; bytecode caches are not inputs."""
    spec = importlib.util.spec_from_file_location(name, path)
    need(spec is not None and spec.loader is not None, 'Python source helper unavailable')
    module = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module


inputs = _source_module('ck0_input_stability', ROOT / 'scripts/ck0_input_stability.py')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def identity(path):
    path = Path(path).resolve(strict=True)
    need(path.is_file(), f'not a regular file: {path}')
    return {'path': str(path), 'sha256': digest(path.read_bytes()), 'bytes': path.stat().st_size}


def checked_identity(value):
    need(isinstance(value, dict) and set(value) == {'path', 'sha256', 'bytes'} and
         isinstance(value['path'], str) and Path(value['path']).is_absolute() and
         isinstance(value['sha256'], str) and re.fullmatch('[0-9a-f]{64}', value['sha256']) and
         type(value['bytes']) is int and value['bytes'] >= 0, 'invalid file identity')


def checked_inventory(files, reason):
    need(isinstance(files, dict) and bool(files) and all(
        isinstance(path, str) and bool(path) and path != '.' and
        path == Path(path).as_posix() and not Path(path).is_absolute() and
        '..' not in Path(path).parts and isinstance(sha, str) and
        re.fullmatch('[0-9a-f]{64}', sha) for path, sha in files.items()), reason)


def command(argv, cwd=ROOT, env=None):
    inherited = os.environ if env is None else env
    return subprocess.check_output(argv, cwd=cwd, env=env, stderr=subprocess.PIPE,
                                   pass_fds=_resource_fds(inherited)).decode()


def _resource_fds(env):
    """Forward live advertised locators; native owners still authenticate them.

    The helper is a declared candidate input, so each physical source snapshot
    binds it. Load its current source per call, never an ignored bytecode cache.
    """
    try:
        return _source_module('ck0_resource_transport', ROOT / RESOURCE_HELPER).resource_fds(env)
    except (RuntimeError, AttributeError) as error:
        raise ValueError('Q6 inherited resource transport: ' + str(error)) from error


def git(repo, *args):
    return _production_git(repo, *args).decode()


def _rust_modules():
    """Reuse the module walk's repaired lexer, not its approximate reachability."""
    global _RUST_MODULES
    if _RUST_MODULES is None:
        _RUST_MODULES = _source_module('_ck0_rust_modules', ROOT / 'scripts/rust_modules.py')
    return _RUST_MODULES


def _meta_parts(lx, lo, hi):
    """Meta-arguments separated by code commas, skipping balanced groups."""
    parts, start, at = [], lo, lo
    while at < hi:
        if lx.code[at] in '([{':
            at = lx.pairs[at] + 1
            continue
        if lx.code[at] == ',':
            parts.append((start, at))
            start = at + 1
        at += 1
    if lx.code[start:hi].strip():
        parts.append((start, hi))
    return parts


def _meta_has_path(lx, lo, hi):
    """A path meta-item, including nested cfg_attr; its predicate is not an attribute."""
    ws = _rust_modules().WS
    head = re.match(rf'{ws}*(?:r#)?(?P<name>\w+){ws}*', lx.code[lo:hi])
    if head is None:
        return False
    if head['name'] == 'path':
        return True
    if head['name'] != 'cfg_attr':
        return False
    at = lo + head.end()
    need(at < hi and lx.code[at] == '(' and lx.pairs[at] < hi,
         'unsupported cfg_attr syntax in module-input scan')
    parts = _meta_parts(lx, at + 1, lx.pairs[at])
    need(len(parts) >= 2, 'unsupported cfg_attr syntax in module-input scan')
    return any(_meta_has_path(lx, start, end) for start, end in parts[1:])


def _embedded_path(root, source, value, paths, kind):
    need(value and not Path(value).is_absolute() and '\\' not in value and
         not any(ord(c) < 32 or 0xD800 <= ord(c) <= 0xDFFF for c in value),
         f'unsupported {kind} input: {source}')
    candidate = root.resolve() / Path(source).parent / value
    resolved = candidate.resolve()
    need(resolved == Path(os.path.abspath(candidate)), f'symlink {kind} input: {source}')
    try:
        relative = resolved.relative_to(root.resolve()).as_posix()
    except ValueError:
        raise ValueError(f'uninventoried {kind} input outside repository: {source}') from None
    need(relative in paths, f'uninventoried {kind} input: {relative}')
    if kind in ('module', 'Rust splice'):
        need(relative.endswith('.rs'), f'unsupported {kind} input extension: {relative}')


def _check_rust_inputs(root, path, paths, data):
    rm = _rust_modules()
    text = data.decode('utf-8-sig', errors='strict').replace('\r\n', '\n').replace('\r', '\n')
    lx = rm._lex(text)
    need(lx is not None, f'unlexable Rust input: {path}')
    # Match only CODE, then recover literal values at those same offsets.
    # Kept text alone still contains strings whose contents resemble attributes.
    attr = re.compile(rf'#{rm.WS}*(?P<inner>!)?{rm.WS}*\[')
    modules = set()
    for match in attr.finditer(lx.code):
        lo, hi = match.end(), lx.pairs[match.end() - 1]
        if not _meta_has_path(lx, lo, hi):
            continue
        head = re.match(rf'{rm.WS}*(?:r#)?(?P<name>\w+){rm.WS}*', lx.code[lo:hi])
        need(head['name'] == 'path', f'unsupported conditional module path: {path}')
        need(not match['inner'] and not any(start < match.start() < end
             for start, end in lx.pairs.items()), f'unsupported nested module path: {path}')
        after = hi + 1
        # The path belongs to the following item, not a nearby earlier declaration.
        while True:
            blank = re.match(rf'{rm.WS}*', lx.code[after:]).end()
            after += blank
            following = attr.match(lx.code, after)
            if following is None:
                break
            need(not following['inner'], f'unsupported module path owner: {path}')
            after = lx.pairs[following.end() - 1] + 1
        declaration = re.match(rf'(?:pub(?:{rm.WS}*\([^)]*\){rm.WS}*|{rm.WS}+))?(?:unsafe{rm.WS}+)?'
                               rf'mod{rm.WS}+(?:r#)?\w+{rm.WS}*;', lx.code[after:])
        need(declaration is not None, f'unsupported module path owner: {path}')
        need(after not in modules, f'unsupported multiple module paths: {path}')
        modules.add(after)
        rest = lx.kept[lo + head.end():hi].strip()
        literal = rm.LIT.fullmatch(rest[1:].strip()) if rest.startswith('=') else None
        need(literal is not None, f'unsupported module path literal: {path}')
        value = literal['raw'] if literal['raw'] is not None else literal['s']
        _embedded_path(root, path, value, paths, 'module')
    include = re.compile(rf'\b(?P<name>include(?:_str|_bytes)?){rm.WS}*!{rm.WS}*(?P<open>[([{{])')
    for match in include.finditer(lx.code):
        close = lx.pairs[match.end() - 1]
        literal = rm.INC_ONLY.fullmatch(lx.kept, match.end(), close)
        need(literal is not None, f'unsupported embedded input: {path}')
        value = literal['raw'] if literal['raw'] is not None else literal['s']
        kind = 'Rust splice' if match['name'] == 'include' else 'embedded'
        _embedded_path(root, path, value, paths, kind)


def collect_rust_source_files(paths):
    """The Rust source cohort in the already bounded input set, including fixtures."""
    return {path for path in paths if path.endswith('.rs')}


def inventory(root):
    root = Path(root).resolve(strict=True)
    paths = set(BASE)

    def traversal_error(error):
        raise error

    for name in (CRATE, '.cargo'):
        base = root
        for part in Path(name).parts:
            base /= part
            mode = base.lstat().st_mode
            need(not stat.S_ISLNK(mode), f'source directory symlink: {base}')
            need(stat.S_ISDIR(mode), f'non-directory source root: {base}')
        for directory, names, filenames in os.walk(base, followlinks=False, onerror=traversal_error):
            for name in names:
                path = Path(directory) / name
                mode = path.lstat().st_mode
                need(not stat.S_ISLNK(mode), f'source directory symlink: {path}')
                need(stat.S_ISDIR(mode), f'non-directory source input: {path}')
            paths.update((Path(directory) / name).relative_to(root).as_posix() for name in filenames)
    for path in paths:
        mode = (root / path).lstat().st_mode
        need(not stat.S_ISLNK(mode), f'symlink input: {path}')
        need(stat.S_ISREG(mode), f'non-regular source input: {path}')
    # The whole crate tree already contains ordinary modules. Literal top-level
    # path modules and includes must stay within that exact set; conditional,
    # nested and computed paths refuse rather than inventing Rust semantics.
    rust_files = collect_rust_source_files(paths)
    files = {}
    for path in sorted(paths):
        data = (root / path).read_bytes()
        if path in rust_files:
            _check_rust_inputs(root, path, paths, data)
        files[path] = digest(data)
    return files


def same_inputs(expected, actual):
    need(set(expected) == set(actual),
         f'input inventory changed: missing={sorted(set(expected)-set(actual))}, added={sorted(set(actual)-set(expected))}')
    changed = [p for p in expected if expected[p] != actual[p]]
    need(not changed, f'input digest changed: {changed}')


def source_record(root):
    revision = _production_commit(root, 'HEAD', label='candidate source')
    files = inventory(root)
    # Require every input to be a committed blob at this exact revision.
    for path, sha in files.items():
        need(digest(_production_git(root, 'show', f'{revision}:{path}')) == sha,
             f'input differs from committed source: {path}')
    return {'schema': SOURCE_SCHEMA, 'kind': 'candidate-source', 'revision': revision,
            'files': files, 'proof_claim': False, 'genesis_promoted': False}


def checked_source(root, record):
    need(record['schema'] == SOURCE_SCHEMA and record['kind'] == 'candidate-source', 'source schema')
    need(record['proof_claim'] is False and record['genesis_promoted'] is False, 'candidate cannot promote genesis or claim proof')
    need(re.fullmatch('[0-9a-f]{40}', record['revision']), 'source revision')
    need(_production_commit(root, record['revision'], label='candidate source') == record['revision'],
         'source commit identity')
    same_inputs(record['files'], inventory(root))
    for path, sha in record['files'].items():
        blob = _production_git(root, 'show', f"{record['revision']}:{path}")
        need(digest(blob) == sha, f'source commit mismatch: {path}')


PRODUCTION_GIT_LOCAL_ENV = frozenset({
    # Git's local-env vocabulary, namespace selector and pathspec selectors.
    # A caller's checkout (including an invoking Git hook) must not override
    # the repository passed to these committed-object reads. Config entry
    # siblings are removed below with their count/parameter advertisements.
    'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_CONFIG', 'GIT_CONFIG_PARAMETERS',
    'GIT_CONFIG_COUNT', 'GIT_OBJECT_DIRECTORY', 'GIT_DIR', 'GIT_WORK_TREE',
    'GIT_IMPLICIT_WORK_TREE', 'GIT_GRAFT_FILE', 'GIT_INDEX_FILE',
    'GIT_NO_REPLACE_OBJECTS', 'GIT_REPLACE_REF_BASE', 'GIT_PREFIX',
    'GIT_SHALLOW_FILE', 'GIT_COMMON_DIR', 'GIT_NAMESPACE',
    'GIT_LITERAL_PATHSPECS', 'GIT_GLOB_PATHSPECS', 'GIT_NOGLOB_PATHSPECS',
    'GIT_ICASE_PATHSPECS',
})


def _production_env():
    # Isolate Git repository/pathspec context; preserve native resource fields.
    env = {key: value for key, value in os.environ.items()
           if key not in PRODUCTION_GIT_LOCAL_ENV and
           not key.startswith(('GIT_CONFIG_KEY_', 'GIT_CONFIG_VALUE_'))}
    env.update(GIT_NO_REPLACE_OBJECTS='1', GIT_NO_LAZY_FETCH='1',
               GIT_TERMINAL_PROMPT='0')
    return env


def _production_git(repo, *args, reject_stderr=False):
    result = subprocess.run(['git', '-C', str(repo), *args], env=_production_env(),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    need(not reject_stderr or not result.stderr, 'production reference emitted Git diagnostics')
    return result.stdout


def _production_commit(repo, ref, label='production Trust'):
    """Resolve a caller's ref to one commit; warnings/ambiguous names refuse."""
    need(isinstance(ref, str) and bool(ref), label + ' reference')
    raw = _production_git(repo, '-c', 'core.warnAmbiguousRefs=true',
                          'rev-parse', '--verify', '--end-of-options',
                          ref + '^{commit}', reject_stderr=True)
    need(re.fullmatch(rb'[0-9a-f]{40}\n', raw), label + ' commit identity')
    return raw[:-1].decode('ascii')


def _batch_blob_hashes(stream, oids):
    """Read exactly the requested Git blob frames; trust no returned header."""
    need(len(oids) == len(set(oids)) and all(
        isinstance(oid, str) and re.fullmatch(r'[0-9a-f]{40}', oid)
        for oid in oids), 'production batch object requests')
    result = {}
    for oid in oids:
        header = stream.readline(128)
        fields = header.removesuffix(b'\n').split(b' ')
        need(header.endswith(b'\n') and len(fields) == 3 and
             fields[:2] == [oid.encode('ascii'), b'blob'] and
             re.fullmatch(rb'(?:0|[1-9][0-9]{0,19})', fields[2]),
             'production batch object header: ' + oid)
        size = int(fields[2])
        need(size <= sys.maxsize, 'production blob size out of range: ' + oid)
        content = hashlib.sha256()
        object_hash = hashlib.sha1(usedforsecurity=False)
        object_hash.update(b'blob ' + fields[2] + b'\0')
        remaining = size
        while remaining:
            chunk = stream.read(min(remaining, 1024 * 1024))
            need(bool(chunk), 'truncated production blob: ' + oid)
            content.update(chunk)
            object_hash.update(chunk)
            remaining -= len(chunk)
        need(stream.read(1) == b'\n', 'production blob frame terminator: ' + oid)
        need(object_hash.hexdigest() == oid, 'production Git blob identity: ' + oid)
        result[oid] = content.hexdigest()
    need(stream.read(1) == b'', 'extra production batch response')
    return result


def git_files(repo, revision, prefixes):
    """Hash committed blobs in one batch, never a sibling's mutable files.

    NUL records preserve literal paths. Only full object IDs enter batch input;
    duplicate content shares a request, never a path/census entry. Spool output
    to a private temporary file so total source size is not resident in memory.
    """
    raw = _production_git(repo, 'ls-tree', '-rz', '--full-tree', revision, '--', *prefixes)
    need(raw and raw.endswith(b'\0'), 'empty or malformed production inventory')
    paths = {}
    for row in raw[:-1].split(b'\0'):
        fields = row.split(b'\t', 1)
        need(len(fields) == 2, 'malformed production tree entry')
        meta, path = fields[0].split(b' '), fields[1].decode('utf-8')
        need(len(meta) == 3 and meta[0] in (b'100644', b'100755') and
             meta[1] == b'blob', f'non-regular production input: {path}')
        need(path and path not in paths, 'duplicate or empty production path')
        oid = meta[2].decode('ascii')
        need(re.fullmatch(r'[0-9a-f]{40}', oid),
             'production tree object identity: ' + path)
        paths[path] = oid
    oids = list(dict.fromkeys(paths.values()))
    with tempfile.TemporaryFile() as output:
        subprocess.run(['git', '-C', str(repo), 'cat-file', '--batch'],
                       input=''.join(oid + '\n' for oid in oids).encode('ascii'),
                       stdout=output, stderr=subprocess.PIPE, check=True,
                       env=_production_env())
        output.seek(0)
        hashes = _batch_blob_hashes(output, oids)
    result = {path: hashes[oid] for path, oid in paths.items()}
    checked_inventory(result, 'production source path census')
    return result


def production_route(documents):
    trust = tomllib.loads(documents['trust_manifest'])
    ty = tomllib.loads(documents['ty_manifest'])
    dep = trust['dependencies']['tla-check']
    need(dep['path'] == '../../first-party/ty/crates/tla-check', 'production tla-check path')
    need(dep['default-features'] is False and set(dep['features']) == {'im', 'bumpalo', 'clean-cic'}, 'production clean-cic feature route')
    need(trust['patch']['https://github.com/alabsystems/clean.git']['clean-ck0']['path'] == '../../first-party/clean/crates/clean-ck0', 'production ck0 patch')
    need(ty['dependencies']['clean-ck0'] == {'workspace': True, 'optional': True}, 'production ck0 dependency')
    need(set(ty['features']['clean-cic']) == {'dep:clean-kernel', 'dep:clean-ck0'}, 'production clean-cic dependencies')
    patches = trust['patch']['crates-io']
    for name, suffix in [('num-bigint', 'bigint'), ('num-integer', 'integer'), ('num-traits', 'traits')]:
        need(patches[name]['path'] == '../../first-party/ty/crates/tla-bignum/' + suffix, 'production arithmetic patch: ' + name)
    lock = tomllib.loads(documents['trust_lock'])
    ck0 = [p for p in lock['package'] if p['name'] == 'clean-ck0']
    tla = [p for p in lock['package'] if p['name'] == 'tla-check']
    need(len(ck0) == len(tla) == 1 and 'clean-ck0' in tla[0]['dependencies'], 'production lock ck0 edge')
    need('source' not in ck0[0], 'production ck0 must resolve through local patch')


def production_record(trust, ty, clean, ref):
    revision = _production_commit(trust, ref)
    links = {}
    for name in ('clean', 'ty'):
        path = ('first-party/' + name).encode('ascii')
        raw = _production_git(trust, 'ls-tree', '-z', revision, '--', path.decode('ascii'))
        fields = raw[:-1].split(b'\t', 1) if raw.endswith(b'\0') and raw.count(b'\0') == 1 else []
        meta = fields[0].split(b' ') if len(fields) == 2 else []
        need(len(meta) == 3 and meta[:2] == [b'160000', b'commit'] and
             fields[1] == path and re.fullmatch(rb'[0-9a-f]{40}', meta[2]),
             'missing or malformed production gitlink: ' + name)
        links[name] = meta[2].decode('ascii')
        need(_production_git(clean if name == 'clean' else ty,
                             'cat-file', '-t', links[name]) == b'commit\n',
             'production gitlink is not an exact commit: ' + name)
    paths = dict(PRODUCTION_PATHS)
    documents = {key: _production_git(ty if key == 'ty_manifest' else trust, 'show',
                          f"{links['ty'] if key == 'ty_manifest' else revision}:{path}").decode()
                 for key, path in paths.items()}
    production_route(documents)
    return {'schema': SCHEMA, 'kind': 'production-source-provenance', 'trust_revision': revision,
            'gitlinks': links, 'document_paths': paths, 'documents': documents,
            'document_sha256': {k: digest(v.encode()) for k, v in documents.items()},
            'trust_files': git_files(trust, revision, ['Cargo.toml', 'Cargo.lock', '.cargo', 'crates/trust-spec-temporal']),
            'clean_files': git_files(clean, links['clean'], [CRATE, *LEGACY_BASE, '.cargo']),
            'ty_files': git_files(ty, links['ty'], ['Cargo.toml', 'Cargo.lock', 'crates/tla-check',
                                                 'crates/tla-bignum', 'crates/tla-hash-fx']),
            'compiled_production_closure': False, 'proof_claim': False}


def checked_production(record):
    need(record['schema'] == SCHEMA and record['kind'] == 'production-source-provenance', 'production schema')
    need(record['compiled_production_closure'] is False and record['proof_claim'] is False, 'unmeasured production claim')
    need(set(record['gitlinks']) == {'clean', 'ty'}, 'production gitlink census')
    need(record['document_paths'] == PRODUCTION_PATHS and
         set(record['documents']) == set(PRODUCTION_PATHS), 'production document path census')
    anchors = {'trust_files': {'crates/trust-spec-temporal/src/lib.rs'},
               'ty_files': {'crates/tla-check/src/lib.rs', 'crates/tla-check/src/ck0_bridge.rs'},
               'clean_files': {CRATE + '/Cargo.toml', CRATE + '/src/lib.rs'}}
    for key, required in anchors.items():
        checked_inventory(record[key], 'production source inventory: ' + key)
        need(required <= set(record[key]), 'production source anchors: ' + key)
    need(all(re.fullmatch('[0-9a-f]{40}', v) for v in [record['trust_revision'], *record['gitlinks'].values()]), 'production revision')
    need(record['document_sha256'] == {k: digest(v.encode()) for k, v in record['documents'].items()}, 'production document digest')
    for key, path in record['document_paths'].items():
        files = record['ty_files'] if key == 'ty_manifest' else record['trust_files']
        need(files[path] == record['document_sha256'][key], 'production document inventory: ' + key)
    production_route(record['documents'])


def authenticate_production(record, trust, ty, clean):
    actual = production_record(trust, ty, clean, record['trust_revision'])
    need(actual == record, 'production Git provenance changed')


def test_names(log):
    return sorted(re.findall(r'^test (.+?) \.\.\. (ok|ignored)\s*$', log, re.M))


def summary(log):
    rows = re.findall(r'test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored;', log)
    need(rows, 'missing test summaries')
    need(all(int(failed) == 0 for _, failed, _ in rows), 'failed test summary')
    total = sum(int(passed) for passed, _, _ in rows)
    need(total > 0 and 'test result: FAILED' not in log, 'empty or failed suite')
    return {'passed': total, 'ignored': sum(int(ignored) for _, _, ignored in rows), 'targets': len(rows)}


def run_argv(driver, label, name):
    need(label in ('stock', 'trust'), 'compiler lane label')
    return [str(driver)] + (['--unverified'] if label == 'trust' else []) + RUN_TAILS[name] + [
        '--locked', '--offline', '-p', 'clean-ck0', '--message-format=json', '--verbose']


def metadata_argv(driver, context):
    need(context in ('default', 'export'), 'metadata context')
    return [str(driver), 'metadata', '--locked', '--offline', '--format-version=1'] + (
        ['--features', 'clean-ck0/export'] if context == 'export' else [])


def compiler_override_variable(name):
    return name in ('RUSTC', 'RUSTDOC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
        'RUSTFLAGS', 'RUSTDOCFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'CARGO_BUILD_RUSTC',
        'CARGO_BUILD_RUSTC_WRAPPER', 'CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER',
        'CARGO_BUILD_RUSTFLAGS', 'CC', 'CXX', 'AR') or name.startswith(('DYLD_', 'LD_PRELOAD')) or (
        name.startswith('CARGO_TARGET_') and name.endswith(('_RUSTFLAGS', '_LINKER', '_RUNNER')))


def validate_compiler_config(data):
    parsed = tomllib.loads(data.decode())
    build, environment = parsed.get('build', {}), parsed.get('env', {})
    need(isinstance(build, dict) and isinstance(environment, dict), 'Cargo compiler config table shape')
    need(not any(key in build for key in ('rustc-wrapper', 'rustc-workspace-wrapper', 'rustc')),
         'compiler override in config')
    need('include' not in parsed, 'unsupported Cargo configuration include')
    need(not any(compiler_override_variable(key) for key in environment),
         'compiler override in config environment')


def compile_record(driver, compiler, label, output, source):
    """Run only INSIDE machine admission. Caller supplies independent target dirs."""
    driver = driver.resolve(strict=True)
    compiler = compiler.resolve(strict=True)
    checked_source(ROOT, source)
    output.mkdir(parents=True, exist_ok=False)
    (output / 'producer.py').write_bytes(Path(__file__).read_bytes())
    env = _production_env()
    env['CARGO_TARGET_DIR'] = str(ROOT / '.q6' / ('target-' + label + '.noindex'))
    env['RUSTC'] = str(compiler)
    env['RUSTDOC'] = str(compiler.with_name('trustdoc' if label == 'trust' else 'rustdoc'))
    if label == 'stock':
        env['ATERM_STOCK_REASON'] = 'Q6 explicitly authorized stock compiler lineage qualification; no proof claim'
    forbidden = [name for name in os.environ if compiler_override_variable(name)]
    need(not forbidden, f'unrecorded compiler override environment: {forbidden}')
    need(Path(os.environ.get('CARGO_HOME', str(Path.home() / '.cargo'))).resolve() == (Path.home() / '.cargo').resolve(), 'custom CARGO_HOME not qualified')
    producer_sources = {}
    for name in PRODUCER_FILES:
        data = (ROOT / name).read_bytes()
        archive = output / 'producer-sources' / name
        archive.parent.mkdir(parents=True, exist_ok=True)
        archive.write_bytes(data)
        producer_sources[name] = digest(data)
    need(producer_sources['scripts/check_ck0_lineage.py'] == digest((output / 'producer.py').read_bytes()),
         'producer changed before capture')
    cargo_home = Path.home() / '.cargo'

    metadata_commands = {context: metadata_argv(driver, context)
                         for context in ('default', 'export')}

    def snapshot():
        resolution = {context: inputs.reachable_metadata(decode_evidence(command(argv, env=env)))
                      for context, argv in metadata_commands.items()}
        _root, specs = inputs.resolution_specs(resolution)
        target = Path(env['CARGO_TARGET_DIR']).resolve()
        need(all(not target.is_relative_to(Path(spec['manifest_path']).parent.resolve())
                 for spec in specs.values()), 'build output inside dependency package root')
        return inputs.capture_state(ROOT, inventory(ROOT), driver, compiler,
            command([str(compiler), '-Vv'], env=env),
            Path(command([str(compiler), '--print', 'sysroot'], env=env).strip()),
            resolution, cargo_home, PRODUCER_FILES, validate_compiler_config)

    before = snapshot()
    same_inputs(source['files'], before['source_files'])
    ck0_id, _specs = inputs.resolution_specs(before['resolution'])
    targets = before['resolution']['export']['targets']
    record = {'schema': inputs.RUN_SCHEMA, 'kind': 'rustc-family-qualification', 'label': label,
              'ck0_package_id': ck0_id, 'source_sha256': digest(encoded(source)),
              'compiler': before['compiler'], 'driver': before['driver'],
              'version': before['version'], 'sysroot': before['sysroot'],
              'sysroot_files': before['sysroot_files'],
              'ambient_configs': {name: value for name, value in before['config_candidates'].items()
                                  if value is not None},
              'family': 'rustc', 'independent_implementation': False, 'ddc': False, 'proof_claim': False,
              'environment': {key: env[key] for key in ('CARGO_TARGET_DIR', 'RUSTC', 'RUSTDOC')},
              'producer_sha256': producer_sources['scripts/check_ck0_lineage.py'],
              'producer_sources': producer_sources, 'metadata_commands': metadata_commands,
              'input_snapshots': {},
              'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'host': platform.node(), 'platform': platform.platform(), 'steps': []}

    def save_snapshot(phase, state):
        record['input_snapshots'][phase] = inputs.write_snapshot(output, phase, state,
            datetime.datetime.now(datetime.timezone.utc).isoformat())
        (output / 'run.json').write_bytes(encoded(record))

    save_snapshot('before', before)
    for name in RUN_TAILS:
        argv = run_argv(driver.resolve(), label, name)
        with (output / (name + '.log')).open('wb') as log:
            rc = subprocess.run(argv, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                                pass_fds=_resource_fds(env)).returncode
        data = (output / (name + '.log')).read_bytes()
        text = data.decode(errors='replace')
        artifacts = {}
        packages = set()
        test_targets = []
        for line in text.splitlines():
            try:
                item = decode_evidence(line)
            except json.JSONDecodeError:
                continue
            if item.get('reason') == 'compiler-artifact':
                packages.add(item['package_id'])
                if item['package_id'] == ck0_id and item['profile']['test']:
                    test_targets.append({'name': item['target']['name'], 'kind': item['target']['kind']})
                for path in item['filenames']:
                    if Path(path).is_file():
                        artifacts[path] = identity(path)
        step = {'name': name, 'argv': argv, 'exit_code': rc, 'log': name + '.log',
                'log_sha256': digest(data), 'artifacts': artifacts, 'packages': sorted(packages)}
        record['steps'].append(step)
        (output / 'run.json').write_bytes(encoded(record))
        try:
            after = snapshot()
            save_snapshot('after-' + name, after)
            inputs.same_state(before, after)
        except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
            record['input_stability_error'] = str(error)
            (output / 'run.json').write_bytes(encoded(record))
            raise
        need(any('ck0-replay' in Path(p).name for p in artifacts) if name == 'binary' and rc == 0 else True, 'missing ck0-replay binary')
        if rc == 0 and name != 'binary':
            expected = sorted([{'name': t['name'], 'kind': t['kind']} for t in targets
                               if set(t.get('required-features', [])) <= ({'export'} if name == 'export' else set())], key=lambda t: t['name'])
            actual = sorted(test_targets, key=lambda t: t['name'])
            need(actual == expected, f'test target set mismatch: {actual} vs {expected}')
            step['test_targets'] = actual
            step['test_names'] = test_names(text)
            step['tests'] = summary(text)
            need(len(step['test_names']) == step['tests']['passed'] + step['tests']['ignored'], 'test name census mismatch')
        (output / 'run.json').write_bytes(encoded(record))
        need(rc == 0, f'{label}/{name} exited {rc}: {output / step["log"]}')
    used = {package for step in record['steps'] for package in step['packages']}
    need(used - {ck0_id} <= set(before['dependency_sources']), 'unpreflighted dependency package')
    record['dependency_sources'] = {key: before['dependency_sources'][key]
                                    for key in sorted(used - {ck0_id})}
    checked_source(ROOT, source)
    record['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (output / 'run.json').write_bytes(encoded(record))
    print(label + ': ' + ', '.join(s['name'] + '=' + str(s.get('tests', {}).get('passed', 'built')) for s in record['steps']))


def checked_stability(base, record, source, used_packages, local=False):
    references = record['input_snapshots']
    need(isinstance(references, dict) and set(references) == set(inputs.PHASES),
         'input snapshot phase census')
    states = []
    for phase in inputs.PHASES:
        reference = references[phase]
        need(isinstance(reference, dict) and set(reference) == {'file', 'sha256'} and
             reference['file'] == 'inputs-' + phase + '.json' and
             isinstance(reference['sha256'], str) and re.fullmatch('[0-9a-f]{64}', reference['sha256']),
             'input snapshot reference')
        snapshot = decode_evidence(inputs.read_bound_file(base, reference['file'], reference['sha256']))
        need(set(snapshot) == {'schema', 'phase', 'observed_at', 'state'} and
             snapshot['schema'] == inputs.SNAPSHOT_SCHEMA and snapshot['phase'] == phase and
             isinstance(snapshot['observed_at'], str), 'input snapshot shape')
        datetime.datetime.fromisoformat(snapshot['observed_at'])
        states.append(snapshot['state'])
    before = states[0]
    expected_fields = {'source_root', 'cargo_home', 'source_files', 'compiler', 'driver',
                       'version', 'sysroot', 'sysroot_files', 'sysroot_links', 'config_candidates',
                       'resolution', 'dependency_sources', 'dependency_trees', 'producer_files'}
    need(isinstance(before, dict) and set(before) == expected_fields, 'input snapshot state shape')
    for after in states[1:]:
        inputs.same_state(before, after)
    same_inputs(source['files'], before['source_files'])
    for field in ('compiler', 'driver'):
        checked_identity(before[field])
    for field in ('source_root', 'cargo_home', 'sysroot'):
        need(isinstance(before[field], str) and Path(before[field]).is_absolute(), 'input snapshot root')
    checked_inventory(before['sysroot_files'], 'input snapshot sysroot inventory')
    need(all(name.startswith('lib/') for name in before['sysroot_files']), 'input snapshot sysroot scope')
    need(isinstance(before['version'], str) and bool(before['version']), 'input snapshot compiler version')
    for field in ('compiler', 'driver', 'version', 'sysroot', 'sysroot_files'):
        need(record[field] == before[field], 'run differs from input snapshot: ' + field)
    environment = record['environment']
    need(isinstance(environment, dict) and set(environment) == {'RUSTC', 'RUSTDOC', 'CARGO_TARGET_DIR'} and
         environment['RUSTC'] == record['compiler']['path'] and
         environment['RUSTDOC'] == str(Path(record['compiler']['path']).with_name(
             'trustdoc' if record['label'] == 'trust' else 'rustdoc')) and
         isinstance(environment['CARGO_TARGET_DIR'], str) and
         Path(environment['CARGO_TARGET_DIR']).is_absolute(), 'input snapshot compiler environment')
    configs = before['config_candidates']
    need(isinstance(configs, dict) and set(configs) == set(inputs.config_candidates(
        before['source_root'], before['cargo_home'])), 'input snapshot config candidate census')
    for value in configs.values():
        if value is not None:
            checked_identity(value)
    need(record['ambient_configs'] == {name: value for name, value in configs.items() if value is not None},
         'run differs from input snapshot: configs')
    root, specs = inputs.resolution_specs(before['resolution'])
    need(root == record['ck0_package_id'], 'input snapshot checker package')
    need(record['metadata_commands'] == {context: metadata_argv(record['driver']['path'], context)
                                        for context in ('default', 'export')}, 'input metadata commands')
    for context in before['resolution'].values():
        need(context['packages'][root]['manifest_path'] == str(Path(before['source_root']) / CRATE / 'Cargo.toml'),
             'input snapshot checker manifest')
    for step in record['steps']:
        if step['name'] != 'binary':
            expected = sorted([{'name': target['name'], 'kind': target['kind']}
                for target in before['resolution'][step['name']]['targets']
                if set(target.get('required-features', [])) <= (
                    {'export'} if step['name'] == 'export' else set())], key=lambda target: target['name'])
            need(step['test_targets'] == expected, 'input metadata target census')
    dependencies = before['dependency_sources']
    need(isinstance(dependencies, dict) and set(dependencies) == set(specs),
         'input snapshot dependency census')
    for key, dependency in dependencies.items():
        need(isinstance(dependency, dict) and set(dependency) == {'manifest_path', 'source', 'files'} and
             {name: dependency[name] for name in ('manifest_path', 'source')} == specs[key],
             'input snapshot dependency identity')
        checked_inventory(dependency['files'], 'input snapshot dependency files')
        need('Cargo.toml' in dependency['files'], 'input snapshot dependency manifest')
        need(not Path(environment['CARGO_TARGET_DIR']).is_relative_to(
             Path(dependency['manifest_path']).parent), 'input snapshot output inside dependency root')
    need(used_packages - {root} <= set(dependencies), 'unpreflighted dependency package')
    need(record['dependency_sources'] == {key: dependencies[key] for key in used_packages - {root}},
         'run differs from input snapshot: dependencies')
    trees = before['dependency_trees']
    need(isinstance(trees, dict) and set(trees) == set(dependencies), 'input snapshot tree census')
    for key, tree in trees.items():
        need(isinstance(tree, dict) and set(tree) == {'root', 'links'} and
             isinstance(tree['root'], str) and Path(tree['root']).is_absolute(), 'input snapshot tree shape')
        need(tree['root'] == str(Path(dependencies[key]['manifest_path']).parent),
             'dependency root differs from manifest')
        checked_links(tree['links'], dependencies[key]['files'])
    checked_links(before['sysroot_links'], before['sysroot_files'])
    checked_inventory(before['producer_files'], 'input snapshot producer inventory')
    need(set(before['producer_files']) == set(PRODUCER_FILES) and
         record['producer_sources'] == before['producer_files'], 'input snapshot producer census')
    need(record['producer_sha256'] == record['producer_sources']['scripts/check_ck0_lineage.py'],
         'input snapshot producer self identity')
    for name, sha in record['producer_sources'].items():
        inputs.read_bound_file(base, 'producer-sources/' + name, sha)
    if local:
        live = inputs.capture_state(Path(before['source_root']), inventory(Path(before['source_root'])),
            Path(record['driver']['path']), Path(record['compiler']['path']), before['version'],
            Path(before['sysroot']), before['resolution'], Path(before['cargo_home']), PRODUCER_FILES)
        inputs.same_state(before, live)


def checked_links(links, files):
    need(isinstance(links, dict) and set(links) <= set(files), 'input snapshot link census')
    for value in links.values():
        need(isinstance(value, dict) and set(value) == {'target', 'resolved'} and
             isinstance(value['target'], str) and bool(value['target']) and
             isinstance(value['resolved'], str) and Path(value['resolved']).is_absolute(),
             'input snapshot link identity')


def checked_run(path, source, local=False, require_stability=False):
    record = decode_evidence(path.read_text())
    need(record['schema'] in (SCHEMA, inputs.RUN_SCHEMA) and
         record['kind'] == 'rustc-family-qualification', 'run schema')
    need(not require_stability or record['schema'] == inputs.RUN_SCHEMA,
         'required input stability missing: v1 is historical')
    need(record['source_sha256'] == digest(encoded(source)), 'run source digest')
    for tool in ('compiler', 'driver'):
        checked_identity(record[tool])
    need(digest((path.parent / 'producer.py').read_bytes()) == record['producer_sha256'], 'run producer digest')
    need(record['family'] == 'rustc' and record['independent_implementation'] is False and record['ddc'] is False and record['proof_claim'] is False, 'rustc-family run cannot claim independence, DDC or proof')
    need([s['name'] for s in record['steps']] == ['default', 'export', 'binary'], 'incomplete run')
    latest_artifacts = {artifact['path']: artifact for step in record['steps'] for artifact in step['artifacts'].values()}
    used_packages = set()
    for step in record['steps']:
        need(type(step['exit_code']) is int and step['exit_code'] == 0, 'nonzero or invalid run exit')
        need(step['argv'] == run_argv(record['driver']['path'], record['label'], step['name']),
             'run command mismatch')
        need(Path(step['log']).name == step['log'], 'log path')
        data = (path.parent / step['log']).read_bytes()
        need(digest(data) == step['log_sha256'], 'run log digest')
        need(step['artifacts'] and step['packages'], 'missing build artifacts or package provenance')
        logged_targets, logged_packages, logged_files = [], set(), set()
        for line in data.decode().splitlines():
            try:
                item = decode_evidence(line)
            except json.JSONDecodeError:
                continue
            if item.get('reason') == 'compiler-artifact':
                logged_packages.add(item['package_id'])
                logged_files.update(item['filenames'])
                if item['package_id'] == record['ck0_package_id'] and item['profile']['test']:
                    logged_targets.append({'name': item['target']['name'], 'kind': item['target']['kind']})
        need(sorted(logged_packages) == step['packages'], 'logged package census')
        used_packages.update(logged_packages)
        need(set(step['artifacts']) <= logged_files, 'logged artifact census')
        for artifact_path, artifact in step['artifacts'].items():
            checked_identity(artifact)
            need(artifact_path == artifact['path'], 'artifact physical path mismatch')
        if step['name'] != 'binary':
            need(sorted(logged_targets, key=lambda t: t['name']) == step['test_targets'], 'logged test target census')
            need(step['tests'] == summary(data.decode()), 'test count mismatch')
            need(step['test_names'] == [list(row) for row in test_names(data.decode())] and
                 sum(status == 'ok' for _, status in step['test_names']) == step['tests']['passed'] and
                 sum(status == 'ignored' for _, status in step['test_names']) == step['tests']['ignored'],
                 'test name census mismatch')
            need(step['test_targets'], 'missing test target census')
        else:
            need(any(Path(p).name == 'ck0-replay' for p in step['artifacts']), 'missing ck0-replay binary')
        if local:
            for artifact in step['artifacts'].values():
                if artifact == latest_artifacts[artifact['path']]:
                    need(identity(artifact['path']) == artifact, 'local artifact identity')
    need(record['ck0_package_id'] in used_packages, 'missing checker package identity')
    need(set(record['dependency_sources']) == used_packages - {record['ck0_package_id']},
         'dependency source census mismatch')
    need(record['dependency_sources'], 'missing dependency source identities')
    checked_inventory(record['sysroot_files'], 'missing or invalid compiler sysroot identities')
    for dependency in record['dependency_sources'].values():
        need(isinstance(dependency, dict) and set(dependency) == {'manifest_path', 'source', 'files'} and
             isinstance(dependency['manifest_path'], str) and Path(dependency['manifest_path']).is_absolute() and
             (dependency['source'] is None or isinstance(dependency['source'], str) and bool(dependency['source'])),
             'dependency source record shape')
        checked_inventory(dependency['files'], 'dependency file inventory')
        need('Cargo.toml' in dependency['files'], 'dependency manifest identity missing')
    if record['schema'] == inputs.RUN_SCHEMA:
        checked_stability(path.parent, record, source, used_packages, local)
    if local and record['schema'] == SCHEMA:
        for tool in ('compiler', 'driver'):
            need(identity(record[tool]['path']) == record[tool], 'local tool identity')
        for dependency in record['dependency_sources'].values():
            base = Path(dependency['manifest_path']).parent
            actual = {p.relative_to(base).as_posix(): digest(p.read_bytes()) for p in sorted(base.rglob('*'))
                      if p.is_file() and '.git' not in p.relative_to(base).parts}
            same_inputs(dependency['files'], actual)
        for config in record['ambient_configs'].values():
            need(identity(config['path']) == config, 'local config identity')
        root = Path(record['sysroot'])
        actual = {p.relative_to(root).as_posix(): digest(p.read_bytes()) for p in sorted((root / 'lib').rglob('*')) if p.is_file()}
        same_inputs(record['sysroot_files'], actual)
    return record


def checked_receipt(base, source, production_data=None):
    receipt = decode_evidence((base / 'EVIDENCE.json').read_text())
    need(receipt['schema'] == 'clean.ck0-evidence/v1', 'evidence schema')
    need(receipt['proof_claim'] is False and receipt['q6_complete'] is False and receipt['genesis_promoted'] is False, 'evidence receipt cannot promote claims')
    need(receipt['source_sha256'] == digest(encoded(source)), 'evidence source pin')
    required = {'production.json'} | {lane + '/' + name for lane in ('stock', 'trust')
               for name in ('run.json', 'producer.py', 'default.log', 'export.log', 'binary.log')}
    need(required <= set(receipt['files']), 'incomplete evidence receipt')
    for path, sha in receipt['files'].items():
        need(not Path(path).is_absolute() and '..' not in Path(path).parts, 'receipt path')
        need(digest((base / path).read_bytes()) == sha, 'evidence file digest: ' + path)
    if production_data is not None:
        need(digest(production_data) == receipt['files']['production.json'],
             'production record differs from sealed receipt')


def stability_selftest():
    """Synthetic receiver evidence; no compiler, cargo, or Rust binary runs."""
    count = inputs.selftest()
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary).resolve()
        for name in (*BASE, CRATE + '/Cargo.toml', CRATE + '/src/lib.rs',
                     'dependency/Cargo.toml', 'dependency/src/lib.rs', 'sdk/lib/stdlib',
                     'compiler', 'driver', 'ck0-replay', 'dependency.rlib'):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'// synthetic input, not compiled\n')
        for name in PRODUCER_FILES:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
        context = {'root': 'synthetic-ck0', 'targets': [{'name': 'synthetic', 'kind': ['lib']}],
                   'packages': {key: {'manifest_path': str(root / directory / 'Cargo.toml'),
                                      'source': None, 'version': '1'}
                                for key, directory in [('synthetic-ck0', CRATE), ('dependency', 'dependency')]},
                   'nodes': {'synthetic-ck0': {'dependencies': ['dependency'], 'features': []},
                             'dependency': {'dependencies': [], 'features': []}}}
        source = {'files': inventory(root)}
        state = inputs.capture_state(root, source['files'], root / 'driver', root / 'compiler',
            'synthetic; not executed', root / 'sdk', {'default': context, 'export': context},
            root / '.cargo', PRODUCER_FILES)
        base = root / 'evidence'
        base.mkdir()
        producer_sources = state['producer_files']
        for name in PRODUCER_FILES:
            target = base / 'producer-sources' / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((root / name).read_bytes())
        (base / 'producer.py').write_bytes((ROOT / 'scripts/check_ck0_lineage.py').read_bytes())
        record = {'schema': inputs.RUN_SCHEMA, 'kind': 'rustc-family-qualification',
                  'label': 'stock', 'ck0_package_id': 'synthetic-ck0',
                  'source_sha256': digest(encoded(source)),
                  **{key: state[key] for key in ('compiler', 'driver', 'version', 'sysroot', 'sysroot_files')},
                  'ambient_configs': {key: value for key, value in state['config_candidates'].items()
                                      if value is not None},
                  'family': 'rustc', 'independent_implementation': False, 'ddc': False, 'proof_claim': False,
                  'producer_sha256': producer_sources['scripts/check_ck0_lineage.py'],
                  'producer_sources': producer_sources,
                  'environment': {'RUSTC': state['compiler']['path'],
                                  'RUSTDOC': str(Path(state['compiler']['path']).with_name('rustdoc')),
                                  'CARGO_TARGET_DIR': str(root / 'target')},
                  'metadata_commands': {key: metadata_argv(state['driver']['path'], key)
                                        for key in ('default', 'export')},
                  'dependency_sources': state['dependency_sources'], 'steps': [],
                  'input_snapshots': {phase: inputs.write_snapshot(base, phase, state,
                      datetime.datetime.now(datetime.timezone.utc).isoformat()) for phase in inputs.PHASES}}
        for name in RUN_TAILS:
            item = {'reason': 'compiler-artifact', 'package_id': 'synthetic-ck0',
                    'target': {'name': 'synthetic', 'kind': ['lib']},
                    'profile': {'test': name != 'binary'}, 'filenames': [str(root / 'ck0-replay')]}
            dependency = {**item, 'package_id': 'dependency', 'profile': {'test': False},
                          'filenames': [str(root / 'dependency.rlib')]}
            data = (json.dumps(item) + '\n' + json.dumps(dependency) +
                    '\ntest one ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored;\n').encode()
            (base / (name + '.log')).write_bytes(data)
            step = {'name': name, 'argv': run_argv(state['driver']['path'], 'stock', name),
                    'exit_code': 0, 'log': name + '.log', 'log_sha256': digest(data),
                    'packages': ['dependency', 'synthetic-ck0'],
                    'artifacts': {str(root / target): identity(root / target)
                                  for target in ('ck0-replay', 'dependency.rlib')}}
            if name != 'binary':
                step.update(tests=summary(data.decode()), test_names=[['one', 'ok']],
                            test_targets=[{'name': 'synthetic', 'kind': ['lib']}])
            record['steps'].append(step)

        def check(value, strict=True):
            (base / 'run.json').write_bytes(encoded(value))
            return checked_run(base / 'run.json', source, require_stability=strict)

        def refuses(value, reason):
            nonlocal count
            try:
                check(value)
            except (ValueError, KeyError) as error:
                need(reason in str(error), 'wrong stability receiver refusal: ' + str(error))
                count += 1
            else:
                raise ValueError('stability receiver accepted mutant: ' + reason)

        check(record)
        checked_run(base / 'run.json', source, local=True, require_stability=True)
        reference = record['input_snapshots']['before']
        snapshot_path = base / reference['file']
        original_snapshot = snapshot_path.read_bytes()
        needle = b'"state": {'
        need(original_snapshot.count(needle) == 1, 'snapshot duplicate control target')
        ambiguous_snapshot = original_snapshot.replace(needle, b'"state": {}, ' + needle)
        snapshot_path.write_bytes(ambiguous_snapshot)
        duplicate = copy.deepcopy(record)
        duplicate['input_snapshots']['before']['sha256'] = digest(ambiguous_snapshot)
        refuses(duplicate, 'duplicate JSON key')
        snapshot_path.write_bytes(original_snapshot)
        check(record)
        legacy = copy.deepcopy(record)
        legacy['schema'] = SCHEMA
        check(legacy, strict=False)
        refuses(legacy, 'v1 is historical')
        for phase in inputs.PHASES:
            mutant = copy.deepcopy(record)
            del mutant['input_snapshots'][phase]
            refuses(mutant, 'snapshot phase census')
        mutant = copy.deepcopy(record)
        mutant['input_snapshots']['after-default']['sha256'] = '0' * 64
        refuses(mutant, 'snapshot digest')
        mutant = copy.deepcopy(record)
        mutant['dependency_sources']['dependency']['files']['src/lib.rs'] = '0' * 64
        refuses(mutant, 'run differs from input snapshot: dependencies')
        mutant = copy.deepcopy(record)
        mutant['sysroot_files']['lib/stdlib'] = '0' * 64
        refuses(mutant, 'run differs from input snapshot: sysroot_files')
        for key in ('RUSTC', 'RUSTDOC'):
            mutant = copy.deepcopy(record)
            mutant['environment'][key] = str(root / 'unrelated-compiler')
            refuses(mutant, 'input snapshot compiler environment')
        changed = copy.deepcopy(state)
        changed['dependency_trees']['dependency']['root'] = str(root / 'unrelated')
        mutant = copy.deepcopy(record)
        for phase in inputs.PHASES:
            mutant['input_snapshots'][phase] = inputs.write_snapshot(base, phase, changed,
                datetime.datetime.now(datetime.timezone.utc).isoformat())
        refuses(mutant, 'dependency root differs from manifest')
        for phase in inputs.PHASES:
            record['input_snapshots'][phase] = inputs.write_snapshot(base, phase, state,
                datetime.datetime.now(datetime.timezone.utc).isoformat())
        changed = copy.deepcopy(state)
        changed['compiler']['sha256'] = '0' * 64
        mutant = copy.deepcopy(record)
        mutant['input_snapshots']['after-export'] = inputs.write_snapshot(base, 'after-export', changed,
            datetime.datetime.now(datetime.timezone.utc).isoformat())
        refuses(mutant, 'input snapshot changed')
        record['input_snapshots']['after-export'] = inputs.write_snapshot(base, 'after-export', state,
            datetime.datetime.now(datetime.timezone.utc).isoformat())
        producer = base / 'producer-sources' / PRODUCER_FILES[-1]
        original = producer.read_bytes()
        producer.write_bytes(b'changed producer helper')
        refuses(record, 'snapshot digest')
        producer.write_bytes(original)
        check(record)
    return count


def selftest():
    count = 0
    def refuses(action, reason):
        nonlocal count
        try:
            action()
        except (ValueError, KeyError, OSError) as err:
            need(reason in str(err), f'wrong refusal: {err}, expected {reason}')
            count += 1
            return
        raise ValueError('negative control accepted: ' + reason)
    same_inputs({'a': '1'}, {'a': '1'})
    refuses(lambda: same_inputs({'a': '1'}, {'a': '2'}), 'digest changed')
    refuses(lambda: same_inputs({'a': '1'}, {}), 'inventory changed')
    refuses(lambda: same_inputs({'a': '1'}, {'a': '1', 'b': '2'}), 'inventory changed')
    refuses(lambda: summary('test result: ok. 0 passed; 0 failed; 0 ignored;'), 'empty')
    refuses(lambda: summary('test result: ok. 1 passed; 1 failed; 0 ignored;'), 'failed')
    refuses(lambda: summary('no test output'), 'missing')
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        for path in BASE:
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text('test')
        (root / CRATE / 'tests').mkdir(parents=True)
        fixture = root / CRATE / 'tests' / 'fixture.ndjson'
        fixture.write_text('honest')
        before = inventory(root)
        fixture.write_text('forged')
        refuses(lambda: same_inputs(before, inventory(root)), 'digest changed')
        fixture.write_text('honest')
        added = root / CRATE / 'build.rs'
        added.write_text('new build input')
        refuses(lambda: same_inputs(before, inventory(root)), 'inventory changed')
        # Ordinary module lookup must not escape through an unwalked directory.
        from unittest import mock
        ordinary = root / CRATE / 'src/ordinary'
        ordinary.mkdir(parents=True)
        (ordinary / 'mod.rs').write_text('// owned ordinary module\n')
        (ordinary.parent / 'lib.rs').write_text('mod ordinary;\n')
        honest = inventory(root)
        need(CRATE + '/src/ordinary/mod.rs' in honest, 'ordinary module input missing')
        saved = root / 'saved-ordinary'
        ordinary.rename(saved)
        ordinary.symlink_to(saved, target_is_directory=True)
        refuses(lambda: inventory(root), 'source directory symlink')
        ordinary.unlink()
        saved.rename(ordinary)
        need(inventory(root) == honest, 'ordinary module inventory changed')
        crate = root / CRATE
        saved = root / 'saved-crate'
        crate.rename(saved)
        crate.symlink_to(saved, target_is_directory=True)
        refuses(lambda: inventory(root), 'source directory symlink')
        crate.unlink()
        saved.rename(crate)
        scandir = os.scandir

        def denied_source(path):
            if Path(path) == ordinary:
                raise PermissionError('fixture nested source EACCES')
            return scandir(path)

        with mock.patch.object(os, 'scandir', denied_source):
            refuses(lambda: inventory(root), 'fixture nested source EACCES')
        fifo = ordinary / 'nonregular'
        os.mkfifo(fifo)
        read_bytes = Path.read_bytes

        def never_read_fifo(path):
            if path == fifo:
                raise AssertionError('non-regular source must refuse before reading')
            return read_bytes(path)

        with mock.patch.object(Path, 'read_bytes', never_read_fifo):
            refuses(lambda: inventory(root), 'non-regular source input')
        fifo.unlink()
        need(inventory(root) == honest, 'source error controls changed inventory')
        # The exact raw bytes hashed must also supply the lexical observation.
        original_read = Path.read_bytes
        lib = ordinary.parent / 'lib.rs'
        def substituted_bytes(path):
            if path == lib:
                return b'#[path = "../../unobserved.rs"] mod injected;\n'
            return original_read(path)
        with mock.patch.object(Path, 'read_bytes', substituted_bytes):
            refuses(lambda: inventory(root), 'uninventoried module input')
        need(inventory(root) == honest, 'single-buffer control changed source')

    # Lexical module/input closure only, not a Rust parser or macro-expansion
    # completeness claim. The two live #[path] test modules remain supported.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        for path in BASE:
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text('test')
        source = root / CRATE / 'src/lib.rs'
        source.parent.mkdir(parents=True)
        inside = source.parent / 'inside.rs'
        inside.write_text('pub const VALUE: u8 = 1;')
        fixture = root / CRATE / 'tests/fixture.ndjson'
        fixture.parent.mkdir(parents=True)
        fixture.write_text('honest')
        for text in ('mod inside;', '#[path = "inside.rs"]\nmod alias;',
                     '#[path = r###"inside.rs"###]\nmod alias;',
                     '#[path = "inside.rs"]\n#[cfg(test)]\npub(crate) mod alias;',
                     'const S: &str = include_str!("../tests/fixture.ndjson");',
                     'include!{"inside.rs"}',
                     '#[cfg_attr(feature = "path", inline)] fn f() {}',
                     '#[cfg_attr(path = "condition", inline)] fn f() {}',
                     r'''// #[path = "../../../external.rs"] mod absent;
/* nested /* #[path = "missing.rs"] mod absent; */ comment */
const S: &str = "#[path = \"missing.rs\"] mod absent;";
const R: &str = r###"#[cfg_attr(test, path = "missing.rs")] mod absent;
include_str!(concat!("missing", ".rs"))"###;
const C: char = '\"';
'''):
            source.write_text(text)
            need(CRATE + '/src/inside.rs' in inventory(root), 'positive module inventory')
        source.write_text('#[path = "inside.rs"]\nmod alias;')
        before = inventory(root)
        inside.write_text('pub const VALUE: u8 = 2;')
        refuses(lambda: same_inputs(before, inventory(root)), 'digest changed')
        (root / 'external.rs').write_text('pub const OUTSIDE: u8 = 0;')
        for text, reason in (
                ('#[path = "../../../external.rs"] mod external;', 'uninventoried module input'),
                ('#[path = "../../../../outside.rs"] mod external;', 'outside repository'),
                ('#[cfg_attr(feature = "x", path = "inside.rs")] mod conditional;', 'conditional module path'),
                ('#[cfg_attr(all(), cfg_attr(test, path = "inside.rs"))] mod conditional;', 'conditional module path'),
                ('#![path = "inside.rs"] mod inner;', 'nested module path'),
                ('mod nested { #[path = "inside.rs"] mod child; }', 'nested module path'),
                ('#[path = concat!("inside", ".rs")] mod computed;', 'module path literal'),
                ('#[path = "inside\\x2ers"] mod escaped;', 'module path literal'),
                ('#[path = "inside.rs"] mod inline {}', 'module path owner'),
                ('#[path = "inside.rs"] #[path = "inside.rs"] mod duplicate;', 'multiple module paths'),
                ('#[\u200epath = "../../../external.rs"] mod external;', 'uninventoried module input'),
                ('const S: &str = include_str!(concat!("a", "b"));', 'unsupported embedded input'),
                ('include!["../../../external.rs"];', 'uninventoried Rust splice input'),
                ('include!["../tests/fixture.ndjson"];', 'Rust splice input extension'),
                ('fn broken() {', 'unlexable Rust input')):
            source.write_text(text)
            refuses(lambda: inventory(root), reason)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for name in BASE:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'fixture\n')
        source = root / CRATE / 'src/lib.rs'
        source.parent.mkdir(parents=True)
        (source.parent / 'inside.rs').write_bytes(b'pub const V: u8 = 0;\n')
        for visibility in ('pub ', 'pub(crate)', 'pub(crate) ', 'pub(in crate)', ''):
            for newline in ('\n', '\r\n', '\r'):
                source.write_text('#[path = "inside.rs"] ' + visibility + 'mod inner;' + newline)
                need(CRATE + '/src/inside.rs' in inventory(root), 'supported module owner missing')
        source.write_text('#[path = "inside.rs"] pubmod inner;\n')
        refuses(lambda: inventory(root), 'unsupported module path owner')
        source.write_text("const C: char = '\\u{0_0_0_0_0_0}';\n")
        inventory(root)
    validate_compiler_config(b'[env]\nRUST_MIN_STACK = { value = "67108864", force = false }\n')
    with tempfile.TemporaryDirectory() as temporary:
        config = Path(temporary) / 'config.toml'
        for variable in ('CARGO_BUILD_RUSTC', 'CC', 'CARGO_TARGET_EXAMPLE_RUNNER'):
            config.write_text('[env]\n' + variable + ' = { value = "unqualified-tool", force = true }\n')
            refuses(lambda: validate_compiler_config(config.read_bytes()), 'config environment')
    # The real captured production documents are test fixtures, not an oracle:
    # each control changes precisely one edge while preserving all other bytes.
    production_path = ROOT / 'reports/self-proof-q6-2026-11-13/production.json'
    if production_path.exists():
        production = decode_evidence(production_path.read_text())
        checked_production(production)
        for key in ('trust_files', 'ty_files', 'clean_files'):
            mutant = copy.deepcopy(production)
            mutant[key] = {}
            refuses(lambda: checked_production(mutant), 'production source inventory')
        mutant = copy.deepcopy(production)
        mutant['clean_files'] = {'unrelated.txt': '0' * 64}
        refuses(lambda: checked_production(mutant), 'production source anchors')
        mutant = copy.deepcopy(production)
        mutant['document_paths'] = {}
        refuses(lambda: checked_production(mutant), 'production document path census')
        mutant = copy.deepcopy(production)
        del mutant['gitlinks']['clean']
        refuses(lambda: checked_production(mutant), 'production gitlink census')
        for key in ('compiled_production_closure', 'proof_claim'):
            mutant = copy.deepcopy(production)
            mutant[key] = True
            refuses(lambda: checked_production(mutant), 'unmeasured production claim')
        for old, new, reason in [
            ('"clean-cic"', '"missing-cic"', 'clean-cic feature route'),
            ('../../first-party/clean/crates/clean-ck0', '../../shadow/clean-ck0', 'ck0 patch'),
            ('../../first-party/ty/crates/tla-bignum/bigint', '../../shadow/bigint', 'arithmetic patch')]:
            mutant = copy.deepcopy(production['documents'])
            need(old in mutant['trust_manifest'], 'control is a no-op')
            mutant['trust_manifest'] = mutant['trust_manifest'].replace(old, new, 1)
            refuses(lambda: production_route(mutant), reason)
        mutant = copy.deepcopy(production)
        mutant['documents']['trust_manifest'] += '# tampered\n'
        refuses(lambda: checked_production(mutant), 'document digest')
        mutant = copy.deepcopy(production)
        mutant['trust_files'][mutant['document_paths']['trust_manifest']] = '0' * 64
        refuses(lambda: checked_production(mutant), 'document inventory')
    else:
        raise ValueError('production fixture required for selftest')
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        source = {'candidate': 'synthetic; tests do not compile'}
        artifact = root / 'ck0-replay'
        artifact.write_bytes(b'synthetic artifact')
        (root / 'producer.py').write_bytes(b'synthetic producer')
        (root / 'lib').mkdir()
        (root / 'lib' / 'stdlib').write_bytes(b'synthetic stdlib')
        (root / 'dependency').mkdir()
        (root / 'dependency' / 'Cargo.toml').write_bytes(b'synthetic dependency')
        record = {'schema': SCHEMA, 'kind': 'rustc-family-qualification',
                  'label': 'stock', 'compiler': identity(artifact), 'driver': identity(artifact),
                  'producer_sha256': digest(b'synthetic producer'), 'ck0_package_id': 'synthetic',
                  'ambient_configs': {}, 'sysroot': str(root),
                  'sysroot_files': {'lib/stdlib': digest(b'synthetic stdlib')},
                  'source_sha256': digest(encoded(source)), 'family': 'rustc',
                  'independent_implementation': False, 'ddc': False, 'proof_claim': False,
                  'dependency_sources': {'dependency': {'manifest_path': str(root / 'dependency' / 'Cargo.toml'), 'source': None, 'files': {'Cargo.toml': digest(b'synthetic dependency')}}}, 'steps': []}
        log = b'test one ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored;\n'
        for name in ('default', 'export', 'binary'):
            item = {'reason': 'compiler-artifact', 'package_id': 'synthetic',
                    'target': {'name': 'synthetic', 'kind': ['test']},
                    'profile': {'test': name != 'binary'}, 'filenames': [str(artifact)]}
            dependency_item = {**item, 'package_id': 'dependency', 'profile': {'test': False}}
            log = json.dumps(dependency_item).encode() + b'\n' + json.dumps(item).encode() + b'\n' + b'test one ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored;\n'
            (root / (name + '.log')).write_bytes(log)
            step = {'name': name, 'argv': run_argv(str(artifact), 'stock', name), 'exit_code': 0, 'log': name + '.log', 'log_sha256': digest(log),
                    'artifacts': {str(artifact): identity(artifact)}, 'packages': ['dependency', 'synthetic']}
            if name != 'binary':
                step.update(tests=summary(log.decode()), test_names=[['one', 'ok']],
                            test_targets=[{'name': 'synthetic', 'kind': ['test']}])
            record['steps'].append(step)
        path = root / 'run.json'
        def check(value):
            path.write_bytes(encoded(value))
            checked_run(path, source)
        check(record)
        checked_run(path, source, local=True)
        mutant = copy.deepcopy(record)
        mutant['dependency_sources'].clear()
        refuses(lambda: check(mutant), 'dependency source census mismatch')
        mutant = copy.deepcopy(record)
        mutant['dependency_sources']['unlogged'] = copy.deepcopy(mutant['dependency_sources']['dependency'])
        refuses(lambda: check(mutant), 'dependency source census mismatch')
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['artifacts'][str(artifact)]['path'] = str(root / 'unrelated-image')
        refuses(lambda: check(mutant), 'artifact physical path mismatch')
        for tool in ('compiler', 'driver'):
            mutant = copy.deepcopy(record)
            mutant[tool]['sha256'] = '0' * 64
            def local_tool():
                path.write_bytes(encoded(mutant))
                checked_run(path, source, local=True)
            refuses(local_tool, 'local tool identity')
        mutant = copy.deepcopy(record)
        mutant['steps'][2]['artifacts'][str(artifact)]['sha256'] = '0' * 64
        def local_artifact():
            path.write_bytes(encoded(mutant))
            checked_run(path, source, local=True)
        refuses(local_artifact, 'local artifact identity')
        for key in ('independent_implementation', 'ddc', 'proof_claim'):
            mutant = copy.deepcopy(record)
            mutant[key] = True
            refuses(lambda: check(mutant), 'cannot claim')
        for value, reason in [({}, 'dependency source record shape'),
                              ({'manifest_path': '/dependency/Cargo.toml', 'source': None, 'files': {}}, 'dependency file inventory'),
                              ({'manifest_path': '/dependency/Cargo.toml', 'source': None, 'files': {'other': '0' * 64}}, 'dependency manifest identity missing')]:
            mutant = copy.deepcopy(record)
            mutant['dependency_sources']['dependency'] = value
            refuses(lambda: check(mutant), reason)
        mutant = copy.deepcopy(record)
        mutant['sysroot_files'] = {}
        refuses(lambda: check(mutant), 'compiler sysroot identities')
        for location in ('compiler', 'artifact'):
            mutant = copy.deepcopy(record)
            value = mutant['compiler'] if location == 'compiler' else next(iter(mutant['steps'][0]['artifacts'].values()))
            value['sha256'] = 'not-a-sha256'
            refuses(lambda: check(mutant), 'invalid file identity')
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['argv'] = ['/usr/bin/false']
        refuses(lambda: check(mutant), 'run command mismatch')
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['exit_code'] = False
        refuses(lambda: check(mutant), 'run exit')
        original_default_log = (root / 'default.log').read_bytes()
        inconsistent_log = (root / 'default.log').read_bytes().replace(b'1 passed;', b'2 passed;')
        (root / 'default.log').write_bytes(inconsistent_log)
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['log_sha256'] = digest(inconsistent_log)
        mutant['steps'][0]['tests']['passed'] = 2
        refuses(lambda: check(mutant), 'test name census mismatch')
        (root / 'default.log').write_bytes(original_default_log)
        ignored_log = original_default_log.replace(b'test one ... ok', b'test one ... ignored')
        (root / 'default.log').write_bytes(ignored_log)
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['log_sha256'] = digest(ignored_log)
        mutant['steps'][0]['test_names'] = [['one', 'ignored']]
        refuses(lambda: check(mutant), 'test name census mismatch')
        (root / 'default.log').write_bytes(original_default_log)
        mutant = copy.deepcopy(record)
        mutant['steps'].pop()
        refuses(lambda: check(mutant), 'incomplete run')
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['exit_code'] = 1
        refuses(lambda: check(mutant), 'run exit')
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['tests']['passed'] += 1
        refuses(lambda: check(mutant), 'test count mismatch')
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['test_names'] = [['other', 'ok']]
        refuses(lambda: check(mutant), 'test name census mismatch')
        mutant = copy.deepcopy(record)
        mutant['steps'][0]['artifacts'] = {}
        refuses(lambda: check(mutant), 'missing build artifacts')
        mutant = copy.deepcopy(record)
        mutant['steps'][2]['artifacts'] = {'other': identity(artifact)}
        refuses(lambda: check(mutant), 'logged artifact census')
        (root / 'default.log').write_bytes(log + b'tampered')
        refuses(lambda: check(record), 'run log digest')
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        source = {'synthetic': 'source'}
        names = {'production.json'} | {lane + '/' + name for lane in ('stock', 'trust')
                 for name in ('run.json', 'producer.py', 'default.log', 'export.log', 'binary.log')}
        for name in names:
            (base / name).parent.mkdir(parents=True, exist_ok=True)
            (base / name).write_bytes(b'synthetic evidence')
        receipt = {'schema': 'clean.ck0-evidence/v1', 'proof_claim': False, 'q6_complete': False,
                   'genesis_promoted': False, 'source_sha256': digest(encoded(source)),
                   'files': {name: digest(b'synthetic evidence') for name in names}}
        def check_receipt(value):
            (base / 'EVIDENCE.json').write_bytes(encoded(value))
            checked_receipt(base, source)
        check_receipt(receipt)
        alternate_production = base / 'alternate-production.json'
        alternate_production.write_bytes((base / 'production.json').read_bytes())
        checked_receipt(base, source, alternate_production.read_bytes())
        alternate_production.write_bytes(b'different production record')
        refuses(lambda: checked_receipt(base, source, alternate_production.read_bytes()),
                'production record differs from sealed receipt')
        for key in ('proof_claim', 'q6_complete', 'genesis_promoted'):
            mutant = copy.deepcopy(receipt)
            mutant[key] = True
            refuses(lambda: check_receipt(mutant), 'cannot promote claims')
        mutant = copy.deepcopy(receipt)
        del mutant['files']['stock/run.json']
        refuses(lambda: check_receipt(mutant), 'incomplete evidence receipt')
        (base / 'stock/run.json').write_bytes(b'substituted compiler identity or binary digest')
        refuses(lambda: check_receipt(receipt), 'evidence file digest')
    # These combinations must refuse before a capture write or compiler launch.
    with tempfile.TemporaryDirectory() as tmp:
        output = Path(tmp) / 'must-not-exist'
        for mode in ([], ['--selftest'], ['--capture-source', '--source', str(output)],
                     ['--capture-production', '--production', str(output)],
                     ['--compile', 'stock', '--output', str(output)],
                     ['--compile', 'trust', '--output', str(output)]):
            result = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                                     '--require-q6', *mode], capture_output=True, text=True,
                                    pass_fds=_resource_fds(os.environ))
            need(result.returncode == 1 and 'Q6 incomplete:' in result.stderr and
                 not output.exists(), 'Q6 completion flag bypassed by early mode')
            count += 1
    count += stability_selftest()
    with tempfile.TemporaryDirectory() as temporary:
        output = Path(temporary) / 'must-not-exist'
        for mode in ([], ['--selftest'], ['--pinned-inputs'],
                     ['--capture-source', '--source', str(output)],
                     ['--capture-production', '--production', str(output)],
                     ['--compile', 'stock', '--output', str(output)],
                     ['--compile', 'trust', '--output', str(output)]):
            receiver = ['--runs', str(output)] if mode else []
            result = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                                     '--require-stability', *receiver, *mode],
                                    capture_output=True, text=True, timeout=10,
                                    pass_fds=_resource_fds(os.environ))
            need(result.returncode == 1 and '--require-stability requires' in result.stderr and
                 not output.exists(), 'stability receiver flag bypassed by early mode')
            count += 1
    for controls in (PRODUCTION_BATCH_TEST, CANDIDATE_CONTEXT_TEST, TRANSPORT_TEST, SOURCE_PROFILE_TEST):
        batch = subprocess.run([sys.executable, '-B', str(ROOT / controls)],
                               capture_output=True, text=True, check=False,
                               pass_fds=_resource_fds(os.environ))
        need(batch.returncode == 0, controls + ' controls failed: ' + batch.stderr[-2000:])
        print(batch.stdout + batch.stderr, end='')
    print(f'Q6 selftest: {count} negative controls refused; positive inventory, production route and run accepted')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    action = ap.add_mutually_exclusive_group()
    action.add_argument('--selftest', action='store_true')
    action.add_argument('--pinned-inputs', action='store_true')
    ap.add_argument('--require-stability', action='store_true')
    ap.add_argument('--source', type=Path, default=ROOT / 'genesis/ck0/CANDIDATE.json')
    action.add_argument('--capture-source', action='store_true')
    action.add_argument('--capture-production', action='store_true')
    ap.add_argument('--production', type=Path)
    ap.add_argument('--trust-repo', type=Path)
    ap.add_argument('--ty-repo', type=Path)
    ap.add_argument('--clean-repo', type=Path, default=ROOT)
    ap.add_argument('--trust-ref', default='origin/main')
    action.add_argument('--compile', choices=['trust', 'stock'])
    ap.add_argument('--driver', type=Path)
    ap.add_argument('--compiler', type=Path)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--runs', type=Path)
    ap.add_argument('--local', action='store_true')
    action.add_argument('--authenticate-production', action='store_true')
    ap.add_argument('--require-q6', action='store_true')
    args = ap.parse_args()
    if args.require_q6:
        raise ValueError('Q6 incomplete: no independent compiler implementation/DDC or installed production-image binding; genesis NOT promoted')
    if args.require_stability:
        need(args.runs is not None and not any((args.selftest, args.pinned_inputs,
             args.capture_source, args.capture_production, args.compile)),
             '--require-stability requires --runs without early action modes')
    if args.pinned_inputs:
        print('\n'.join(sorted({PRODUCTION_BATCH_TEST, CANDIDATE_CONTEXT_TEST, TRANSPORT_TEST, SOURCE_PROFILE_TEST,
                          'reports/self-proof-q6-2026-11-13/production.json',
                          'scripts/check_ck0_replay_custody.py', RESOURCE_HELPER, *(name for name in PRODUCER_FILES
                          if name != 'scripts/check_ck0_lineage.py')})))
        return
    if args.capture_production:
        need(all((args.production, args.trust_repo, args.ty_repo)), '--capture-production requires --production, --trust-repo and --ty-repo')
    if args.compile:
        need(all((args.driver, args.compiler, args.output)), '--compile requires --driver, --compiler and --output')
    if args.authenticate_production:
        need(all((args.production, args.trust_repo, args.ty_repo)), '--authenticate-production requires --production, --trust-repo and --ty-repo')
    if args.selftest:
        selftest()
        return
    if args.capture_source:
        args.source.write_bytes(encoded(source_record(ROOT)))
        print(f'wrote candidate inventory {args.source}; genesis NOT promoted')
        return
    if args.capture_production:
        args.production.write_bytes(encoded(production_record(args.trust_repo, args.ty_repo, args.clean_repo, args.trust_ref)))
        print(f'wrote production source provenance {args.production}; production NOT compiled')
        return
    source = decode_evidence(args.source.read_text())
    checked_source(ROOT, source)
    if args.compile:
        compile_record(args.driver, args.compiler, args.compile, args.output, source)
        return
    production_data = args.production.read_bytes() if args.production else None
    if production_data is not None:
        production = decode_evidence(production_data)
        checked_production(production)
        if args.authenticate_production:
            authenticate_production(production, args.trust_repo, args.ty_repo, args.clean_repo)
    if args.runs:
        checked_receipt(args.runs, source, production_data)
        records = [checked_run(args.runs / label / 'run.json', source, args.local, args.require_stability) for label in ('stock', 'trust')]
        need(records[0]['label'] == 'stock' and records[1]['label'] == 'trust', 'compiler lane labels')
        need(records[0]['compiler']['sha256'] != records[1]['compiler']['sha256'], 'compiler binaries identical')
        for name in ('default', 'export'):
            totals = [next(s['tests'] for s in r['steps'] if s['name'] == name) for r in records]
            need(totals[0] == totals[1], f'{name} suite coverage differs')
            steps = [next(s for s in r['steps'] if s['name'] == name) for r in records]
            need(steps[0]['test_names'] == steps[1]['test_names'] and steps[0]['test_targets'] == steps[1]['test_targets'], f'{name} test identities differ')
    if not args.require_q6:
        need(args.production is not None and args.runs is not None, 'full candidate check requires --production and --runs')
    history = 'v1 historical; ' if any(record['schema'] == SCHEMA for record in records) else 'observed input endpoints; '
    print('Q6 candidate evidence consistent (' + history +
          'no proof, independent DDC, production-build or seed-promotion claim)')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f'Q6 REFUSED: {error}', file=sys.stderr)
        sys.exit(1)
