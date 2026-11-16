#!/usr/bin/env python3
"""Real helper-cache controls; no Rust compiler, Cargo or proof image runs."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import importlib._bootstrap_external as bytecode
import json
import os
from pathlib import Path
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


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run_generator_controls(name, *, expect_cache=False, artifacts=None):
    helpers, rust = CASES[name]
    subject = 'scripts/'+name
    files = (subject, SELF, TRANSPORT, *helpers, *rust)
    originals = {p: (ROOT / p).read_bytes() for p in files}
    transport = types.ModuleType('generator_control_transport')
    transport.__file__ = str(ROOT / TRANSPORT)
    exec(compile(originals[TRANSPORT], transport.__file__, 'exec', dont_inherit=True), transport.__dict__)
    archive = Path(artifacts) / name if artifacts is not None else None
    if archive is not None:
        archive.mkdir(parents=True, exist_ok=False)
    records = []
    def save():
        if archive is not None:
            (archive / 'records.json').write_text(json.dumps(records, indent=2)+'\n')
    with tempfile.TemporaryDirectory(prefix='generator-source-control-') as temporary:
        base = Path(temporary).resolve()
        def capsule(label):
            root = base / label
            for relative,data in originals.items():
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            return root
        def invoke(root, label, args):
            cache = root / 'cache'
            command = [sys.executable, '-B', '-X', 'pycache_prefix='+str(cache),
                       str(root / subject), *args]
            result = subprocess.run(command, cwd=root, env=os.environ.copy(),
                pass_fds=transport.resource_fds(os.environ), capture_output=True, timeout=60)
            row = dict(case=label, command=command, direct_exit=result.returncode,
                       stdout_hex=result.stdout.hex(), stderr_hex=result.stderr.hex())
            records.append(row)
            save()
            return result, row
        golden_root = capsule('golden')
        golden,_ = invoke(golden_root, 'golden-check', ['--check'])
        assert golden.returncode == 0, golden.stderr
        assert CACHED not in golden.stderr and FRESH not in golden.stderr
        for helper in helpers:
            for mode in ('timestamp', 'checked-hash'):
                label = Path(helper).stem+'-'+mode
                root = capsule(label)
                path = root / helper
                fresh = originals[helper]+b'\nprint('+repr(FRESH.decode().rstrip()).encode()+b', file=sys.stderr)\n'
                path.write_bytes(fresh)
                poison = originals[helper]+b'\nprint('+repr(CACHED.decode().rstrip()).encode()+b', file=sys.stderr)\n'
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
                           actual_cached_marker=CACHED in result.stderr, actual_fresh_marker=FRESH in result.stderr)
                save()
                assert result.returncode == 0 and result.stdout == golden.stdout, (label, result.stderr)
                if expect_cache:
                    assert CACHED in result.stderr and FRESH not in result.stderr, ('baseline cache not executed', row)
                else:
                    assert CACHED not in result.stderr, ('cached helper bytecode executed', row)
                    assert FRESH in result.stderr, ('current helper source was not executed', row)
                assert path.read_bytes() == fresh and cache_path.read_bytes() == cache_data
            missing_root = capsule(Path(helper).stem+'-missing')
            missing_path = missing_root / helper
            old = originals[helper]
            code = compile(old+b'\nprint('+repr(CACHED.decode().rstrip()).encode()+b', file=sys.stderr)\n',
                           str(missing_path), 'exec', dont_inherit=True)
            cached = bytecode._code_to_hash_pyc(code, importlib.util.source_hash(old), checked=True)
            with patch.object(sys, 'pycache_prefix', str(missing_root / 'cache')):
                missing_cache = Path(importlib.util.cache_from_source(str(missing_path)))
            missing_cache.parent.mkdir(parents=True, exist_ok=True)
            missing_cache.write_bytes(cached)
            missing_path.unlink()
            missing,_ = invoke(missing_root, Path(helper).stem+'-missing', ['--check'])
            assert missing.returncode != 0 and CACHED not in missing.stderr
            assert b'FileNotFoundError' in missing.stderr and missing_cache.read_bytes() == cached
        if not expect_cache:
            declared,_ = invoke(golden_root, 'declared-helper-inputs', ['--pinned-inputs'])
            assert declared.returncode == 0, declared.stderr
            assert set(declared.stdout.decode().splitlines()) == {SELF, TRANSPORT, *helpers, *rust}
            mixed,_ = invoke(golden_root, 'mixed-input-and-check-actions', ['--pinned-inputs', '--check'])
            assert mixed.returncode == 2 and b'cannot be combined' in mixed.stderr
        for relative,data in originals.items():
            assert (ROOT / relative).read_bytes() == data, relative
        for relative in rust:
            assert (golden_root / relative).read_bytes() == originals[relative], relative
    save()
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generator', choices=sorted(CASES))
    parser.add_argument('--baseline', action='store_true', help='measure the old cache-accepting implementation')
    parser.add_argument('--artifacts', type=Path)
    args = parser.parse_args()
    records = {}
    for name in ([args.generator] if args.generator else CASES):
        records[name] = run_generator_controls(name, expect_cache=args.baseline, artifacts=args.artifacts)
    print(json.dumps(dict(baseline=args.baseline, records=records, compiler_execution=False,
                         proof_claim=False, q6_complete=False)), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
