#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Actual lineage loader controls over harmless private Python source/cache fixtures.

No Rust, compiler, libtest or proof is executed. Cache headers genuinely match
the fixture source; only their harmless VALUE assignment differs.
"""
import importlib.util
import json
import marshal
from pathlib import Path
import py_compile
import struct
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
SUBJECT_PATH = SCRIPTS / 'check_ck0_lineage.py'
SOURCE = b"VALUE = 'source'\n"
CACHE_SOURCE = "VALUE = 'cache'\n"


def load_subject(path=SUBJECT_PATH):
    """Read the actual subject source, without importing a subject cache."""
    module = types.ModuleType('ck0_source_loader_test_subject')
    module.__file__ = str(path)
    prior = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        with mock.patch.object(sys, 'path', [str(path.parent), *sys.path]), mock.patch.dict(sys.modules):
            sys.modules.pop('ck0_input_stability', None)
            exec(compile(path.read_bytes(), str(path), 'exec',
                         dont_inherit=True), module.__dict__)
    finally:
        sys.dont_write_bytecode = prior
    return module


class SourceLoaderTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='ck0-source-loader-test-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.path = self.root / 'scripts/rust_modules.py'
        self.path.parent.mkdir()
        self.path.write_bytes(SOURCE)
        self.subject = load_subject()
        self.child_subject = SUBJECT_PATH
        self.child_kind = 'lineage'
        self.patch = mock.patch.multiple(self.subject, ROOT=self.root, _RUST_MODULES=None)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def loaded(self):
        return self.subject._rust_modules()

    def assert_not_cached(self):
        self.assertIsNone(self.subject._RUST_MODULES)

    def cache(self, mode):
        """Preserve a real valid header, substitute only harmless code bytes."""
        cache = Path(py_compile.compile(str(self.path), doraise=True,
                                        invalidation_mode=mode))
        header = cache.read_bytes()[:16]
        if mode == py_compile.PycInvalidationMode.TIMESTAMP:
            self.assertEqual(struct.unpack('<II', header[8:16]),
                             (int(self.path.stat().st_mtime) & 0xffffffff, len(SOURCE)))
        else:
            self.assertEqual(struct.unpack('<I', header[4:8])[0], 3)
            self.assertEqual(header[8:16], importlib.util.source_hash(SOURCE))
        code = compile(CACHE_SOURCE, str(self.path), 'exec', dont_inherit=True)
        cache.write_bytes(header + marshal.dumps(code))
        return cache

    def test_source_positive(self):
        module = self.loaded()
        self.assertEqual(module.VALUE, 'source')
        self.assertEqual(Path(module.__file__).resolve(), self.path.resolve())
        self.assertIs(self.loaded(), module)

    def test_matching_timestamp_cache_cannot_replace_source(self):
        cache = self.cache(py_compile.PycInvalidationMode.TIMESTAMP)
        cached = cache.read_bytes()
        self.assertEqual(self.loaded().VALUE, 'source')
        self.assertEqual(self.path.read_bytes(), SOURCE)
        self.assertEqual(cache.read_bytes(), cached)

    def test_checked_hash_cache_cannot_replace_source(self):
        cache = self.cache(py_compile.PycInvalidationMode.CHECKED_HASH)
        cached = cache.read_bytes()
        self.assertEqual(self.loaded().VALUE, 'source')
        self.assertEqual(self.path.read_bytes(), SOURCE)
        self.assertEqual(cache.read_bytes(), cached)

    def test_corrupt_cache_is_ignored(self):
        cache = Path(importlib.util.cache_from_source(str(self.path)))
        cache.parent.mkdir()
        raw = b'not a Python cache\x00'
        cache.write_bytes(raw)
        with mock.patch.object(sys, 'dont_write_bytecode', True):
            self.assertEqual(self.loaded().VALUE, 'source')
        self.assertEqual(cache.read_bytes(), raw)

    def test_invalid_source_is_refused_despite_matching_cache(self):
        cache = self.cache(py_compile.PycInvalidationMode.TIMESTAMP)
        invalid = b'VALUE = (\n'
        self.path.write_bytes(invalid)
        raw = cache.read_bytes()
        cache.write_bytes(raw[:8] + struct.pack('<II',
                          int(self.path.stat().st_mtime) & 0xffffffff, len(invalid)) + raw[16:])
        with self.assertRaises(SyntaxError):
            self.loaded()
        self.assert_not_cached()
        self.assertEqual(self.path.read_bytes(), invalid)

    def test_no_cache_write_with_B(self):
        code = '''import json,sys,types
from pathlib import Path
subject=Path(sys.argv[1]);sys.path.insert(0,str(subject.parent))
module=types.ModuleType("ck0_source_loader_child");module.__file__=str(subject)
exec(compile(subject.read_bytes(),str(subject),"exec",dont_inherit=True),module.__dict__)
root=Path(sys.argv[2]);kind=sys.argv[3]
if kind=="observer":
    loaded=module.inputs
elif kind=="shared":
    module.REPO=root;module._LOADED={};loaded=module._load(module.LEXER)
else:
    module.ROOT=root;module._RUST_MODULES=None;loaded=module._rust_modules()
print(json.dumps({"dont_write_bytecode":sys.dont_write_bytecode,"value":loaded.VALUE}))
'''
        result = subprocess.run([sys.executable, '-B', '-c', code, str(self.child_subject),
                                 str(self.root), self.child_kind],
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), {'dont_write_bytecode': True, 'value': 'source'})
        self.assertFalse(list(self.root.rglob('*.pyc')))
        self.assertFalse(list(self.root.rglob('__pycache__')))


class ObserverImportTests(SourceLoaderTests):
    """The actual observer import in a copied actual lineage producer."""
    def setUp(self):
        super().setUp()
        self.path = self.root / 'scripts/ck0_input_stability.py'
        self.path.write_bytes(SOURCE)
        self.child_subject = self.root / 'scripts/check_ck0_lineage.py'
        self.child_subject.write_bytes(SUBJECT_PATH.read_bytes())
        self.child_kind = 'observer'
        self.observer_subject = None

    def loaded(self):
        if self.observer_subject is None:
            self.observer_subject = load_subject(self.child_subject)
        return self.observer_subject.inputs

    def assert_not_cached(self):
        self.assertIsNone(self.observer_subject)


class SharedLexerLoaderTests(SourceLoaderTests):
    """The actual generic shared loader, selecting its actual LEXER entry."""
    def setUp(self):
        super().setUp()
        self.path = self.root / 'scripts/check_add_decl_ratchet.py'
        self.path.write_bytes(SOURCE)
        self.child_subject = SCRIPTS / 'rust_modules.py'
        self.child_kind = 'shared'
        self.shared = types.ModuleType('q6_shared_lexer_test_subject')
        self.shared.__file__ = str(self.child_subject)
        exec(compile(self.child_subject.read_bytes(), str(self.child_subject), 'exec',
                     dont_inherit=True), self.shared.__dict__)
        self.shared.REPO = self.root
        self.shared._LOADED = {}

    def loaded(self):
        return self.shared._load(self.shared.LEXER)

    def assert_not_cached(self):
        self.assertNotIn(self.shared.LEXER, self.shared._LOADED)


LEXICAL_CORPUS = [
    ('ordinary', 'mod visible; fn f() { let x = (1, [2]); }', True),
    ('line-comment', '// mod hidden; #[path="bad.rs"]\nmod visible;', True),
    ('nested-comment', '/* mod hidden; /* [nested] */ } */ mod visible;', True),
    ('string', 'const S: &str = "mod hidden; } include!(x)"; mod visible;', True),
    ('raw-string', 'const S: &str = r###"mod hidden; } "##"###; mod visible;', True),
    ('byte-string', 'const S: &[u8] = b"mod hidden; }"; mod visible;', True),
    ('escaped-character', r"const A: char = '\x7b'; const B: char = '\u{7d}'; mod visible;", True),
    ('lifetime', "fn f<'a>(x: &'a str) -> &'a str { x } mod visible;", True),
    ('module-attributes', '#[path="child.rs"] mod visible; #[cfg_attr(unix, path="a.rs")] mod other;', True),
    ('include-macro', 'include!("item.rs"); macro_rules! m { () => { mod visible; } }', True),
    ('pattern-white-space', 'mod\u200evisible; fn f() { [()] }', True),
    ('unbalanced', 'mod visible; fn broken() { [()]', False),
]


def lexical_outputs(shared_source=None, lexer_source=None):
    """Run the actual repaired lexer with a fresh, real source helper copy."""
    shared_source = shared_source or SCRIPTS / 'rust_modules.py'
    lexer_source = lexer_source or SCRIPTS / 'check_add_decl_ratchet.py'
    module = types.ModuleType('q6_lexical_corpus_subject')
    module.__file__ = str(shared_source)
    exec(compile(shared_source.read_bytes(), str(shared_source), 'exec', dont_inherit=True),
         module.__dict__)
    with tempfile.TemporaryDirectory(prefix='ck0-source-loader-lexical-') as temporary:
        root = Path(temporary)
        (root / 'scripts').mkdir()
        (root / module.LEXER).write_bytes(lexer_source.read_bytes())
        module.REPO = root
        rows = []
        for name, raw, valid in LEXICAL_CORPUS:
            result = module._lex(raw)
            if valid:
                if result is None or 'visible' not in result.code or 'hidden' in result.code:
                    raise AssertionError('lexical visibility mismatch: ' + name)
            elif result is not None:
                raise AssertionError('unbalanced fixture accepted: ' + name)
            rows.append(dict(case=name, source=raw, valid=valid, code=result.code if result else None,
                             kept=result.kept if result else None,
                             pairs=sorted(result.pairs.items()) if result else None))
        return rows


class ReferenceLexerCompatibilityTests(unittest.TestCase):
    def test_reference_lexer_corpus(self):
        self.assertEqual(len(lexical_outputs()), 12)


if __name__ == '__main__':
    unittest.main()
