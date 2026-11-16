#!/usr/bin/env python3
"""Actual custody CLI source/cache controls on private copied Python modules.

Matching timestamp/hash headers are genuine. Only cached code is replaced by a
harmless RuntimeError. No Rust, recorded image, native tool or proof is executed.
"""
import importlib.util
import marshal
import os
from pathlib import Path
import py_compile
import struct
import subprocess
import sys
import tempfile
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
PRODUCERS = ('scripts/check_ck0_lineage.py', 'scripts/rust_modules.py',
             'scripts/check_add_decl_ratchet.py', 'scripts/ck0_input_stability.py')
CUSTODY = 'scripts/check_ck0_replay_custody.py'
RESOURCE = 'scripts/resource_transport.py'
CACHE_MARKER = 'Q6_MATCHING_CUSTODY_CACHE_POISON'
SOURCE_MARKER = 'Q6_CHANGED_LINEAGE_SOURCE'


def source_module(path):
    module = types.ModuleType('ck0_custody_test_resource_transport')
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module


class CustodySourceLoader(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='ck0-custody-loader-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name in (CUSTODY, *PRODUCERS, RESOURCE):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
        self.lineage = self.root / PRODUCERS[0]
        self.custody = self.root / CUSTODY
        self.transport = source_module(ROOT / RESOURCE)
        # This is the exact public result of clean copied sources, before any
        # cache exists. Later source-owned pin additions remain part of this
        # full byte-for-byte reference, not an expected set chosen by a cache.
        reference = self.cli()
        self.assertEqual(reference.returncode, 0, reference.stderr)
        self.assertEqual(reference.stderr, b'')
        rows = reference.stdout.decode().splitlines()
        self.assertEqual(rows, sorted(set(rows)))
        self.assertTrue(set(PRODUCERS) <= set(rows))
        self.expected_stdout = reference.stdout

    def run_child(self, argv, cwd=None):
        # Preserve the caller environment and its live advertised descriptors;
        # the helper grants no authority, and these children are Python only.
        return subprocess.run(argv, cwd=cwd or self.root, env=os.environ.copy(),
                              pass_fds=self.transport.resource_fds(os.environ),
                              capture_output=True, timeout=60, check=False)

    def cli(self):
        return self.run_child([sys.executable, '-B', str(self.custody), '--pinned-inputs'])

    def poisoned_cache(self, mode):
        source = self.lineage.read_bytes()
        path = Path(py_compile.compile(str(self.lineage), doraise=True,
                                       invalidation_mode=mode))
        header = path.read_bytes()[:16]
        self.assertEqual(header[:4], importlib.util.MAGIC_NUMBER)
        if mode == py_compile.PycInvalidationMode.TIMESTAMP:
            self.assertEqual(struct.unpack('<I', header[4:8])[0], 0)
            self.assertEqual(struct.unpack('<II', header[8:16]),
                             (int(self.lineage.stat().st_mtime) & 0xffffffff, len(source)))
        else:
            self.assertEqual(struct.unpack('<I', header[4:8])[0], 3)
            self.assertEqual(header[8:16], importlib.util.source_hash(source))
        code = compile('raise RuntimeError(' + repr(CACHE_MARKER) + ')\n',
                       str(self.lineage), 'exec', dont_inherit=True)
        path.write_bytes(header + marshal.dumps(code))
        cached = path.read_bytes()
        # -B prevents cache writes, but deliberately retains ordinary import's
        # cache reads. This proves the matching cache is usable and selected.
        probe = self.run_child([sys.executable, '-B', '-c', 'import check_ck0_lineage'],
                               cwd=self.lineage.parent)
        self.assertNotEqual(probe.returncode, 0)
        # Tracebacks display the current source line even for cached code.
        # The actual final exception, rather than that display, is the oracle.
        self.assertEqual(probe.stderr.splitlines()[-1],
                         b'RuntimeError: ' + CACHE_MARKER.encode())
        self.assertEqual(path.read_bytes(), cached)
        return path, cached, source

    def assert_cache_ignored(self, mode):
        path, cached, source = self.poisoned_cache(mode)
        result = self.cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, self.expected_stdout)
        self.assertEqual(result.stderr, b'')
        self.assertEqual(self.lineage.read_bytes(), source)
        self.assertEqual(path.read_bytes(), cached)

    def assert_changed_source_used(self, mode):
        self.lineage.write_text('raise RuntimeError(' + repr(SOURCE_MARKER) + ')\n')
        path, cached, source = self.poisoned_cache(mode)
        result = self.cli()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b'')
        self.assertIn(SOURCE_MARKER.encode(), result.stderr)
        self.assertNotIn(CACHE_MARKER.encode(), result.stderr)
        self.assertEqual(self.lineage.read_bytes(), source)
        self.assertEqual(path.read_bytes(), cached)

    def test_actual_copied_sources_cli_positive(self):
        result = self.cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, self.expected_stdout)
        self.assertEqual(result.stderr, b'')

    def test_matching_timestamp_cache_cannot_replace_lineage_source(self):
        self.assert_cache_ignored(py_compile.PycInvalidationMode.TIMESTAMP)

    def test_matching_checked_hash_cache_cannot_replace_lineage_source(self):
        self.assert_cache_ignored(py_compile.PycInvalidationMode.CHECKED_HASH)

    def test_changed_source_wins_over_matching_timestamp_cache(self):
        self.assert_changed_source_used(py_compile.PycInvalidationMode.TIMESTAMP)

    def test_changed_source_wins_over_matching_checked_hash_cache(self):
        self.assert_changed_source_used(py_compile.PycInvalidationMode.CHECKED_HASH)


if __name__ == '__main__':
    program = unittest.main(exit=False, verbosity=2)
    raise SystemExit(0 if program.result.testsRun > 0 and program.result.wasSuccessful() else 1)
