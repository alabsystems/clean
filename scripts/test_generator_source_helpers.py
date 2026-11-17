#!/usr/bin/env python3
"""Real helper-cache controls; no Rust compiler, Cargo or proof image runs."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import importlib._bootstrap_external as bytecode
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import types
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SELF = 'scripts/test_generator_source_helpers.py'
TRANSPORT = 'scripts/resource_transport.py'
BASE = 'crates/clean-verify/src/spec/core_spec/'
CASES = {
    'gen_lzb_activation.py': (('scripts/explicit_prefix.py',), (BASE+'eval_ir_lzb_activation.rs',)),
    'gen_lzd_activation.py': (('scripts/explicit_prefix.py',),
        (BASE+'eval_ir_lzd_activation.rs', BASE+'eval_ir_lzd_correct.rs')),
    'gen_slot_lemmas.py': (('scripts/explicit_prefix.py',), (BASE+'eval_ir_slot_lemmas.rs',)),
    'gen_lzd_sctr.py': (('scripts/gen_lzd_activation.py', 'scripts/explicit_prefix.py'),
        (BASE+'eval_ir_lzd_sctr.rs', BASE+'eval_ir_lzd_pc.rs')),
}
CACHED = b'CONTROL_CACHED_HELPER_EXECUTED\n'
FRESH = b'CONTROL_CURRENT_HELPER_SOURCE_EXECUTED\n'
MODE = b'CONTROL_PYTHON_MODE='
PRINT_CONSTS = {
    'gen_lzb_activation.py': 'SRC_IR_LZB_DEREF_ACTIVATION',
    'gen_lzd_activation.py': 'SRC_IR_LZD_DEREF_ACTIVATION',
    'gen_slot_lemmas.py': 'SRC_EXEC_LOAD_IS_VIEW',
    'gen_lzd_sctr.py': 'SRC_IR_LZD_PC',
}


def require(condition, detail):
    """These predicates must remain enforced when Python removes assertions."""
    if not condition:
        raise AssertionError(detail)


def python_flags():
    level = sys.flags.optimize
    require(level in (0, 1, 2), ('unsupported Python optimization level', level))
    return (['-E'] if sys.flags.ignore_environment else []) + (['-'+'O'*level] if level else [])


def sources(name):
    helpers, rust = CASES[name]
    subject = 'scripts/'+name
    files = (subject, SELF, TRANSPORT, *helpers, *rust)
    return helpers, rust, subject, {p: (ROOT / p).read_bytes() for p in files}


def capsule(root, originals):
    for relative, data in originals.items():
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    return root


def payload(source, marker):
    return (source+b'\nprint('+repr(marker.decode().rstrip()).encode()+b', file=sys.stderr)\n'
            b'print("CONTROL_PYTHON_MODE="+str(sys.flags.optimize)+":"+'
            b'str(sys.flags.ignore_environment), file=sys.stderr)\n')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def lzd_emission_cases(originals, rust):
    """Private canonical-template fixtures, independent of the producer's map."""
    keys = ('SRC_IR_LZD_FRAME_AGREE', 'SRC_IR_LZD_DEREF_ACTIVATION',
            'SRC_IR_LZD_MAX_TRUE_SEG', 'SRC_IR_LZD_MAX_FALSE_SEG', 'SRC_IR_LZD_IMAX_SEG',
            'SRC_IR_LZD_ACTIVATION', 'SRC_IR_LZD_CORRECT', 'SRC_IR_LZD_MACHINE_SOUND',
            'SRC_IR_LZD_NEVER_FAULTS')
    patterns = {key: re.compile(rb'const '+key.encode()+rb': &str = ".*?";\n', re.S) for key in keys}
    bindings = {}
    for key, pattern in patterns.items():
        matches = [(path, match) for path in rust for match in pattern.finditer(originals[path])]
        require(len(matches) == 1, ('emission fixture binding', key, len(matches)))
        bindings[key] = matches[0]
    first = next(key for key in keys if bindings[key][0] == rust[0])
    second = next(key for key in keys if bindings[key][0] == rust[1])
    stale = dict(originals)
    stale[rust[0]] = patterns[first].sub(b'const '+first.encode()+b': &str = "CONTROL_STALE";\n', stale[rust[0]])
    cases = [('pristine', dict(originals), None), ('stale-body', stale, None)]
    empty = dict(stale)
    for path in rust:
        for pattern in patterns.values():
            empty[path] = pattern.sub(b'', empty[path])
    cases.append(('empty-roster', empty, b'--emit requires exactly one binding'))
    for label, key in (('missing-first', first), ('missing-second', second)):
        fixture = dict(stale); path = bindings[key][0]
        fixture[path] = patterns[key].sub(b'', fixture[path])
        cases.append((label, fixture, b'--emit requires exactly one binding'))
    for label, path in (('duplicate-within', rust[0]), ('duplicate-cross', rust[1])):
        fixture = dict(stale)
        fixture[path] += b'\n'+bindings[first][1].group()
        cases.append((label, fixture, b'--emit requires exactly one binding'))
    balanced = dict(stale)
    balanced[rust[1]] = patterns[second].sub(b'', balanced[rust[1]])+b'\n'+bindings[first][1].group()
    cases.append(('balanced-cross', balanced, b'--emit requires exactly one binding'))
    overlap = dict(stale)
    overlap[rust[1]] = patterns[second].sub(b'', overlap[rust[1]])
    overlap[rust[0]] = patterns[first].sub(
        lambda _m: b'const '+first.encode()+b': &str = "CONTROL_PREFIX\n'+bindings[second][1].group(),
        overlap[rust[0]])
    cases.append(('overlap', overlap, b'--emit bindings overlap'))
    missing = dict(stale); del missing[rust[1]]
    cases.append(('missing-second-file', missing, b'FileNotFoundError'))
    return cases


def run_generator_controls(name, *, expect_cache=False, artifacts=None):
    helpers, rust, subject, originals = sources(name)
    transport = types.ModuleType('generator_control_transport')
    transport.__file__ = str(ROOT / TRANSPORT)
    exec(compile(originals[TRANSPORT], transport.__file__, 'exec', dont_inherit=True), transport.__dict__)
    archive = Path(artifacts).resolve() / name if artifacts is not None else None
    if archive is not None:
        archive.mkdir(parents=True, exist_ok=False)
    records = []
    def save():
        if archive is not None:
            (archive / 'records.json').write_text(json.dumps(records, indent=2)+'\n')
    with tempfile.TemporaryDirectory(prefix='generator-source-control-') as temporary:
        base = Path(temporary).resolve()
        def invoke(root, label, args):
            cache = root / 'cache'
            command = [sys.executable, *python_flags(), '-B', '-X', 'pycache_prefix='+str(cache),
                       str(root / subject), *args]
            result = subprocess.run(command, cwd=root, env=os.environ.copy(),
                pass_fds=transport.resource_fds(os.environ), capture_output=True, timeout=60)
            row = dict(case=label, command=command, direct_exit=result.returncode,
                       stdout_hex=result.stdout.hex(), stderr_hex=result.stderr.hex())
            records.append(row)
            save()
            return result, row
        golden_root = capsule(base / 'golden', originals)
        golden,_ = invoke(golden_root, 'golden-check', ['--check'])
        require(golden.returncode == 0, golden.stderr)
        require(CACHED not in golden.stderr and FRESH not in golden.stderr, 'golden helper marker')
        for helper in helpers:
            for mode in ('timestamp', 'checked-hash'):
                label = Path(helper).stem+'-'+mode
                root = capsule(base / label, originals)
                path = root / helper
                fresh = payload(originals[helper], FRESH)
                path.write_bytes(fresh)
                poison = payload(originals[helper], CACHED)
                code = compile(poison, str(path), 'exec', dont_inherit=True)
                if mode == 'timestamp':
                    cache_data = bytecode._code_to_timestamp_pyc(code, int(path.stat().st_mtime), len(fresh))
                else:
                    cache_data = bytecode._code_to_hash_pyc(code, importlib.util.source_hash(fresh), checked=True)
                # The fixture's own cache prefix is the child's actual prefix;
                # no shared cache or native resource advertisement is changed.
                with patch.object(sys, 'pycache_prefix', str(root / 'cache')):
                    cache_path = Path(importlib.util.cache_from_source(str(path)))
                cache_path.parent.mkdir(parents=True, exist_ok=True)
                cache_path.write_bytes(cache_data)
                if archive is not None:
                    (archive / (label+'.pyc.data')).write_bytes(cache_data)
                    (archive / (label+'.source.data')).write_bytes(fresh)
                result,row = invoke(root, label, ['--check'])
                row.update(helper=helper, source_sha256=digest(fresh), cached_code_sha256=digest(cache_data),
                           cache_header_hex=bytes(cache_data[:16]).hex(),
                           actual_cached_marker=CACHED in result.stderr, actual_fresh_marker=FRESH in result.stderr,
                           python_mode=[line[len(MODE):].decode() for line in result.stderr.splitlines()
                                        if line.startswith(MODE)])
                save()
                require(result.returncode == 0 and result.stdout == golden.stdout, (label, result.stderr))
                require(row['python_mode'] == [str(sys.flags.optimize)+':'+str(sys.flags.ignore_environment)],
                        ('child Python mode differs from its cache fixture', row))
                if expect_cache:
                    require(CACHED in result.stderr and FRESH not in result.stderr, ('baseline cache not executed', row))
                else:
                    require(CACHED not in result.stderr, ('cached helper bytecode executed', row))
                    require(FRESH in result.stderr, ('current helper source was not executed', row))
                require(path.read_bytes() == fresh and cache_path.read_bytes() == cache_data, ('fixture moved', label))
            for error, detail in (('missing', b'FileNotFoundError'), ('syntax', b'SyntaxError')):
                label = Path(helper).stem+'-'+error
                error_root = capsule(base / label, originals)
                path = error_root / helper
                source = originals[helper] + (b'\nif:\n' if error == 'syntax' else b'')
                path.write_bytes(source)
                code = compile(payload(originals[helper], CACHED), str(path), 'exec', dont_inherit=True)
                cached = bytecode._code_to_hash_pyc(code, importlib.util.source_hash(source), checked=True)
                with patch.object(sys, 'pycache_prefix', str(error_root / 'cache')):
                    cache = Path(importlib.util.cache_from_source(str(path)))
                cache.parent.mkdir(parents=True, exist_ok=True)
                cache.write_bytes(cached)
                if error == 'missing':
                    path.unlink()
                if archive is not None:
                    (archive / (label+'.pyc.data')).write_bytes(cached)
                    (archive / (label+'.source.data')).write_bytes(source)
                result, row = invoke(error_root, label, ['--check'])
                row.update(helper=helper, source_sha256=digest(source), cached_code_sha256=digest(cached),
                           cache_header_hex=bytes(cached[:16]).hex(), actual_cached_marker=CACHED in result.stderr,
                           actual_fresh_marker=FRESH in result.stderr)
                mode_lines = [line[len(MODE):].decode() for line in result.stderr.splitlines() if line.startswith(MODE)]
                if mode_lines:
                    row['python_mode'] = mode_lines
                save()
                if error == 'syntax' and expect_cache:
                    require(result.returncode == 0 and result.stdout == golden.stdout,
                            ('baseline syntax cache refused', row))
                    require(CACHED in result.stderr and FRESH not in result.stderr,
                            ('baseline syntax cache not executed', row))
                    require(mode_lines == [str(sys.flags.optimize)+':'+str(sys.flags.ignore_environment)],
                            ('baseline syntax cache mode', row))
                else:
                    require(result.returncode != 0 and CACHED not in result.stderr, ('source error accepted cache', row))
                    require(detail in result.stderr, ('wrong source error', row))
                require(cache.read_bytes() == cached, ('error cache moved', row))
                require(not path.exists() if error == 'missing' else path.read_bytes() == source,
                        ('error source moved', row))
        if not expect_cache:
            declared,_ = invoke(golden_root, 'declared-helper-inputs', ['--pinned-inputs'])
            require(declared.returncode == 0, declared.stderr)
            require(set(declared.stdout.decode().splitlines()) == {SELF, TRANSPORT, *helpers, *rust}, 'declared input roster')
            original_stats = {p: (golden_root / p).stat().st_mtime_ns for p in originals}
            def unchanged(label):
                for relative, data in originals.items():
                    path = golden_root / relative
                    require(path.read_bytes() == data and path.stat().st_mtime_ns == original_stats[relative],
                            ('empty action wrote source or Rust', label, relative))
            # An explicit empty value is still an action. Run this first so
            # either parser omission refuses here before any self-test can recurse.
            empty, _ = invoke(golden_root, 'mixed-empty-print-and-query', ['--pinned-inputs', '--print', ''])
            require(empty.returncode == 2 and not empty.stdout and b'cannot be combined' in empty.stderr,
                    ('mixed primary actions accepted', 'empty print and query', empty.returncode))
            unchanged('mixed empty print and query')
            sole, row = invoke(golden_root, 'sole-empty-print', ['--print', ''])
            require(sole.returncode == 2 and not sole.stdout and b'--print requires a nonempty const name' in sole.stderr,
                    ('empty print was not refused', name, row))
            unchanged('sole empty print')
            actions = [('--check',), ('--print', PRINT_CONSTS[name]), ('--emit',), ('--self-test',), ('--pinned-inputs',)]
            if name in ('gen_lzd_activation.py', 'gen_lzd_sctr.py'):
                actions.append(('--pin',))
            if name == 'gen_lzd_activation.py':
                actions.append(('--digests',))
            for left, right in itertools.combinations(actions, 2):
                for args in (left+right, right+left):
                    result, _ = invoke(golden_root, 'mixed-primary-actions', list(args))
                    require(result.returncode == 2 and not result.stdout and b'cannot be combined' in result.stderr,
                            ('mixed primary actions accepted', args, result.returncode))
                    unchanged(args)
            mixed,_ = invoke(golden_root, 'mixed-input-and-check-actions', ['--pinned-inputs', '--check'])
            require(mixed.returncode == 2 and b'cannot be combined' in mixed.stderr, 'mixed input/check actions')
            if name == 'gen_lzd_activation.py':
                for label, fixture, error in lzd_emission_cases(originals, rust):
                    root = capsule(base / ('emit-'+label), fixture)
                    before = {p: ((root/p).read_bytes(), (root/p).stat().st_mtime_ns)
                              if (root/p).exists() else None for p in rust}
                    result, row = invoke(root, 'emit-'+label, ['--emit'])
                    after = {p: ((root/p).read_bytes(), (root/p).stat().st_mtime_ns)
                             if (root/p).exists() else None for p in rust}
                    row['targets'] = {p: {phase: dict(sha256=digest(value[p][0]), mtime_ns=value[p][1])
                                                if value[p] is not None else None
                                         for phase, value in (('before', before), ('after', after))} for p in rust}
                    save()
                    if error is None:
                        require(result.returncode == 0 and result.stdout == b'emitted 9 terms\n',
                                ('valid emission refused', label, row))
                        require(all(after[p][0] == originals[p] for p in rust), ('emitted bytes differ', label))
                        checked, _ = invoke(root, 'emit-'+label+'-check', ['--check'])
                        require(checked.returncode == 0 and checked.stdout == golden.stdout, ('emitted check', label))
                    else:
                        expected = 1 if label == 'missing-second-file' else 2
                        require(result.returncode == expected and not result.stdout and error in result.stderr,
                                ('invalid emission was not refused', label, row))
                        require(before == after, ('invalid emission wrote targets', label, row))
        for relative,data in originals.items():
            require((ROOT / relative).read_bytes() == data, ('source moved', relative))
        for relative in rust:
            require((golden_root / relative).read_bytes() == originals[relative], ('Rust witness moved', relative))
    save()
    return records


def optimization_controls(name, *, artifacts=None):
    """Six modes with intact, source-loader and action-input omissions."""
    helpers, _, subject, originals = sources(name)
    transport = types.ModuleType('optimization_transport')
    transport.__file__ = str(ROOT / TRANSPORT)
    exec(compile(originals[TRANSPORT], transport.__file__, 'exec', dont_inherit=True), transport.__dict__)
    archive = Path(artifacts).resolve() / name if artifacts is not None else None
    if archive is not None:
        archive.mkdir(parents=True, exist_ok=False)
    modes = [('ordinary', [], '0', '0:0'), ('explicit-O', ['-O'], '0', '1:0'),
             ('explicit-OO', ['-OO'], '0', '2:0'), ('inherited-O', [], '1', '1:0'),
             ('inherited-OO', [], '2', '2:0'), ('ignored-environment', ['-E'], '2', '0:1')]
    records = []
    with tempfile.TemporaryDirectory(prefix='generator-optimization-control-') as temporary:
        base = Path(temporary).resolve()
        for mode, flags, optimize, expected_mode in modes:
            for disposition in ('intact', 'omitted', 'baseline', 'action-omitted', 'action-empty', 'sole-empty-omitted'):
                label = mode+'-'+disposition
                root = capsule(base / label, originals)
                target = root / subject
                omitted_sources = {}
                if disposition in ('omitted', 'baseline'):
                    needle = "exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)"
                    # The refusal mutates one site. The diagnostic baseline
                    # restores every old loader along the controlled helper chain.
                    for relative in (subject, *helpers) if disposition == 'baseline' else (subject,):
                        path = root / relative
                        text = path.read_text()
                        count = text.count(needle)
                        require(count == 1 if relative == subject else count in (0, 1), 'loader omission target')
                        if count:
                            path.write_text(text.replace(needle, 'spec.loader.exec_module(module)'))
                            omitted_sources[relative] = path.read_bytes()
                if disposition in ('action-omitted', 'action-empty'):
                    text = target.read_text()
                    needle = 'if sum(actions) > 1:' if disposition == 'action-omitted' else (
                        'args.show is not None' if name in ('gen_lzb_activation.py', 'gen_slot_lemmas.py') else 'a.name is not None')
                    replacement = 'if False:' if disposition == 'action-omitted' else (
                        'bool(args.show)' if needle.startswith('args') else 'bool(a.name)')
                    require(text.count(needle) == 1, ('action omission target', disposition))
                    target.write_text(text.replace(needle, replacement))
                    omitted_sources[subject] = target.read_bytes()
                if disposition == 'sole-empty-omitted':
                    text = target.read_text()
                    needle = 'if args.show == "":' if name in ('gen_lzb_activation.py', 'gen_slot_lemmas.py') else 'if a.name == "":'
                    require(text.count(needle) == 1, 'sole empty-name omission target')
                    target.write_text(text.replace(needle, 'if False:'))
                    omitted_sources[subject] = target.read_bytes()
                out = archive / label if archive is not None else root / 'observations'
                out.mkdir(parents=True, exist_ok=False)
                if archive is not None:
                    (out / 'subject.py.data').write_bytes(target.read_bytes())
                    for relative, data in omitted_sources.items():
                        saved = out / 'omitted-loaders' / (relative+'.data')
                        saved.parent.mkdir(parents=True, exist_ok=True)
                        saved.write_bytes(data)
                command = [sys.executable, *flags, '-B', str(root / SELF), '--generator', name,
                           '--artifacts', str(out / 'assets')]
                if disposition == 'baseline':
                    command.append('--baseline')
                env = os.environ.copy()
                env['PYTHONOPTIMIZE'] = optimize
                result = subprocess.run(command, cwd=root, env=env, pass_fds=transport.resource_fds(env),
                                        capture_output=True, timeout=60)
                (out / 'stdout').write_bytes(result.stdout)
                (out / 'stderr').write_bytes(result.stderr)
                receipt = out / 'assets' / name / 'records.json'
                require(receipt.is_file(), ('leaf produced no custody observations', command,
                                             result.returncode, result.stderr))
                observations = json.loads(receipt.read_bytes())
                marked = [r for r in observations if 'python_mode' in r]
                row = dict(case=label, command=command, pythonoptimize=optimize,
                           direct_exit=result.returncode, expected_mode=expected_mode,
                           omitted_loaders={p: digest(data) for p, data in omitted_sources.items()},
                           marked_observations=len(marked),
                           actual_cached_executions=sum(r.get('actual_cached_marker', False) for r in marked),
                           actual_fresh_executions=sum(r.get('actual_fresh_marker', False) for r in marked),
                           stdout_hex=result.stdout.hex(), stderr_hex=result.stderr.hex())
                records.append(row)
                if archive is not None:
                    (archive / 'records.json').write_text(json.dumps(records, indent=2)+'\n')
                summary = {k: v for k, v in row.items() if k not in ('stdout_hex', 'stderr_hex')}
                require(marked and all(r['python_mode'] == [expected_mode] for r in marked), ('Python mode', summary))
                if disposition == 'sole-empty-omitted':
                    require(result.returncode != 0 and b'empty print was not refused' in result.stderr,
                            ('empty-name omission did not hit its guard', summary, result.stderr[-2000:]))
                    require(row['actual_cached_executions'] == 0 and row['actual_fresh_executions'] > 0,
                            ('empty-name omission changed helper custody', summary))
                elif disposition in ('action-omitted', 'action-empty'):
                    require(result.returncode != 0 and b'mixed primary actions accepted' in result.stderr,
                            ('action omission did not hit its guard', summary, result.stderr[-2000:]))
                    require(row['actual_cached_executions'] == 0 and row['actual_fresh_executions'] > 0,
                            ('action omission changed helper custody', summary))
                elif disposition == 'omitted':
                    require(result.returncode != 0 and b'cached helper bytecode executed' in result.stderr,
                            ('omission did not hit the custody guard', summary, result.stderr[-2000:]))
                    require(row['actual_cached_executions'] > 0 and row['actual_fresh_executions'] == 0,
                            ('omission did not execute the actual cached helper', summary))
                elif disposition == 'baseline':
                    require(result.returncode == 0, ('explicit baseline measure refused', summary, result.stderr[-2000:]))
                    require(row['actual_cached_executions'] > 0 and row['actual_fresh_executions'] == 0,
                            ('explicit baseline did not measure cached execution', summary))
                else:
                    require(result.returncode == 0, ('intact optimized control refused', summary, result.stderr[-2000:]))
                    require(row['actual_cached_executions'] == 0 and row['actual_fresh_executions'] > 0,
                            ('intact source did not run', summary))
        for relative, data in originals.items():
            require((ROOT / relative).read_bytes() == data, ('source moved', relative))
    return records


def self_test_generator(name, *, artifacts=None):
    root = Path(artifacts).resolve() if artifacts is not None else None
    return dict(direct=run_generator_controls(name, artifacts=root / 'direct' if root is not None else None),
                optimization=optimization_controls(name, artifacts=root / 'optimization' if root is not None else None))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generator', choices=sorted(CASES))
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--baseline', action='store_true', help='measure the old cache-accepting implementation')
    mode.add_argument('--self-test', action='store_true', help='include optimized intact/omission pairs')
    parser.add_argument('--artifacts', type=Path)
    args = parser.parse_args()
    records = {}
    for name in ([args.generator] if args.generator else CASES):
        records[name] = (self_test_generator(name, artifacts=args.artifacts) if args.self_test else
                         run_generator_controls(name, expect_cache=args.baseline, artifacts=args.artifacts))
    print(json.dumps(dict(baseline=args.baseline, records=records, compiler_execution=False,
                         python_mode=str(sys.flags.optimize)+':'+str(sys.flags.ignore_environment),
                         proof_claim=False, q6_complete=False)), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
