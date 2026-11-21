#!/usr/bin/env python3
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
"""Local controls for Q4's orchestration rules. No stub ever becomes a vote.

`kstar_recheck.py --selftest` runs every check; so does running this file, which
exits 1 at the first check that does not hold. `kstar_inputs.py --selftest` runs
the input controls alone."""
import contextlib
import copy
import io
import json
import os
import shutil
import subprocess
import tempfile
import threading
import time
import sys
from pathlib import Path
from unittest.mock import patch
import kstar_inputs as ki
import kstar_recheck as k
import lean4lean_selftest
from kstar_subjects_selftest import restriction_controls


# A tree with one file of each kind a member's build can read. `expected` must be
# inputs and `unnamed` must not; each `refusals` edit [(path, text appended)] must
# make the input rule refuse, for the reason named, rather than name fewer files.
# crates/m/src/lib.rs compiles: `rustc --emit=dep-info` reads what EXPECTED names
# of it (with CARGO_MANIFEST_DIR and an OUT_DIR holding generated.rs).
SOURCE_TREE = {
    'Cargo.toml': '[workspace]\nmembers = ["crates/m"]\n', '.cargo/config.toml': '[build]\n',
    'crates/m/Cargo.toml': '[package]\nname = "m"\n\n[dependencies]\nv = { path = "../../vendor/v" }\n',
    'crates/m/build.rs': 'fn main() { let _ = std::fs::read_to_string("table.tsv"); let _ = "lean-toolchain"; }\n',
    'crates/m/table.tsv': '# world\tfixture\nw\tfixtures/w.bin\n',
    'crates/m/notes.md': 'tracked under crates/ and named by nothing\n',
    'crates/m/src/lib.rs': (
        'pub const T: &str = include_str!("../../../data/t.json");\n'
        'pub const G: &[u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/g.json"));\n'
        '// include_str!("../../../data/mentioned.json"), include_str!("absent.json")\n'
        'pub const S: &str = r#"include_str!("../../../data/quoted.json")"#;\n'
        '#[path = "../../../island/model.clean"]\nmod model;\n'
        'include!(concat!(env!("OUT_DIR"), "/generated.rs"));\n'
        # Each form below once escaped the literal prefix the scanner read as a wildcard.
        'macro_rules! embed { ($p:literal) => { include_str!(concat!($p)) } }\n'
        'pub const A: &str = embed!("../../../data/a.json");\n'
        'pub(crate) use embed;\n'
        'macro_rules! fx { ($n:literal) => { include_str!(concat!("../../../data/fx/", $n)) }; }\n'
        'pub const B: &str = fx!("../b.json");\n'
        'macro_rules! lean { ($n:literal) => { include_str!(concat!("../../../fx/", $n)) }; }\n'
        'pub const L: [&str; 2] = [lean!("a.lean"), lean!("sub/b.lean")];\n'),
    'data/t.json': '{}', 'data/g.json': '{}', 'data/mentioned.json': '{}', 'data/quoted.json': '{}',
    'data/a.json': '{}', 'data/b.json': '{}', 'data/e.json': '{}',
    'data/fx/unnamed.json': '{}',
    'data/unnamed.json': '{}', 'data/c.bin': 'c', 'fx/a.lean': 'a', 'fx/sub/b.lean': 'b', 'fx/unnamed.lean': 'u',
    'island/model.clean': 'mod child;\n',
    'island/child.rs': ('pub const C: &[u8] = include_bytes!("../data/c.bin");\n'
                        # rustc reads a macro's include against the invoking file: data/e.json.
                        'pub const E: &str = crate::embed!("../data/e.json");\n'),
    'lean-toolchain': 'leanprover/lean4:v0\n', 'fixtures/w.bin': 'w',
    'vendor/v/Cargo.toml': '[package]\nname = "v"\n', 'vendor/v/README': 'r',
    'vendor/v/src/lib.rs': 'pub const D: &str = include_str!("../data.txt");\n', 'vendor/v/data.txt': 'd',
}
EXPECTED = ['data/t.json', 'data/g.json', 'fx/a.lean', 'fx/sub/b.lean', 'data/mentioned.json',
            'data/quoted.json', 'island/model.clean', 'island/child.rs', 'data/c.bin',
            'data/a.json', 'data/b.json', 'data/e.json',
            'crates/m/table.tsv', 'crates/m/notes.md', 'lean-toolchain', 'fixtures/w.bin',
            'vendor/v/Cargo.toml', 'vendor/v/README', 'vendor/v/src/lib.rs', 'vendor/v/data.txt']
UNNAMED = ['data/unnamed.json', 'data/fx/unnamed.json', 'fx/unnamed.lean']
LIB = 'crates/m/src/lib.rs'
REFUSALS = [
    ('an include_str! in code naming no file', 'names no repository file',
     [(LIB, 'pub const X: &str = include_str!("absent.json");\n')]),
    ('a macro include whose invocation names no file', 'names no repository file',
     [(LIB, 'macro_rules! y { ($n:literal) => { include_str!(concat!("../../../none/", $n)) }; }\n'
            'pub const Y: &str = y!("a");\n')]),
    ('a macro include nothing invokes', 'names no repository file',
     [(LIB, 'macro_rules! z { ($n:literal) => { include_str!(concat!($n)) }; }\n')]),
    ('a path-qualified concat!', 'cannot evaluate',
     [(LIB, 'pub const Q: &str = include_str!(crate::concat!("../../../data/t.json"));\n')]),
    ('an env! other than CARGO_MANIFEST_DIR and OUT_DIR', 'cannot evaluate',
     [(LIB, 'pub const E: &str = include_str!(concat!(env!("HOME"), "/x"));\n')]),
    ('a stringify! of more than one token', 'cannot evaluate',
     [(LIB, 'pub const R: &str = include_str!(concat!("../../../data/", stringify!(t . json)));\n')]),
    ('an exported macro include', 'may be invoked from another crate',
     [(LIB, '#[macro_export]\nmacro_rules! e { () => { include_str!("../../../data/t.json") }; }\n')]),
    ('a macro include renamed by a use', 'is renamed by a use',
     [('island/child.rs', 'use crate::embed as other;\n')]),
    ('a macro include defined inside another macro', 'defined inside another macro',
     [(LIB, 'macro_rules! gen { () => { macro_rules! g { () => { include_str!("../../../data/t.json") } } } }\n')]),
    ('an include! in a macro body', 'an include! in a macro body',
     [(LIB, 'macro_rules! inc { () => { include!("../../../island/child.rs") }; }\n')]),
    ('a macro include invoked inside another macro', 'invoked inside another macro',
     [(LIB, 'macro_rules! outer { () => { embed!("../../../data/t.json") }; }\npub const O: &str = outer!();\n')]),
    ('a literal metavariable bound to more than one token', 'cannot evaluate',
     [(LIB, 'pub const P: &str = embed!(concat!("../../../data/", "t.json"));\n')]),
    ('a #[path] naming no file', '#[path] names no repository file',
     [('vendor/v/src/lib.rs', '#[path = "absent.rs"]\nmod absent;\n')]),
    ('OUT_DIR without a build script', 'OUT_DIR in a package without a build script',
     [('vendor/v/src/lib.rs', 'include!(concat!(env!("OUT_DIR"), "/generated.rs"));\n')]),
    ('a path dependency outside the repository', 'a path dependency outside the repository',
     [('crates/m/Cargo.toml', 'w = { path = "../../../elsewhere" }\n')]),
    ('a build script changed since its declaration', 'has no reviewed declaration of its reads',
     [('crates/m/build.rs', '// a comment moves the closure\n')]),
]


def declare(root, scripts):
    """A build-read declaration of `scripts` ({script: (reads, data[, other keys])}) for their closures as they stand."""
    rows = {script: dict(closure=ki.closure_digest(root, [script], {}), reads=row[0], data=row[1], **dict(row[2:]))
            for script, row in scripts.items()}
    (root / ki.BUILD_DECLARATIONS).parent.mkdir(parents=True, exist_ok=True)
    (root / ki.BUILD_DECLARATIONS).write_text(json.dumps(dict(scripts=rows)))


def write_tree(root, files, links=None):
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text)
    for rel, target in (links or {}).items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        os.symlink(target, root / rel)


def git_add(root):
    for argv in (['init', '-q'], ['add', '-A']):
        subprocess.run(['git', '-C', str(root), *argv], check=True, capture_output=True)


def source_tree(root):
    write_tree(root, {**{p: p for p in k.FIXED_INPUTS}, **SOURCE_TREE,
                      '../elsewhere/Cargo.toml': '[package]\nname = "w"\n'})
    declare(root, {'crates/m/build.rs': (['crates/m/table.tsv'], ['crates/m/table.tsv'],
                                         ('rustc_env', []), ('out_dir', ['generated.rs']))})
    git_add(root)


# One arm per form the input rule lists, or group sharing one branch (docs/DECISIONS.md,
# 2026-11-19, and its corrections): a synthetic tree (crates/k plus files outside
# crates/), scanned by `kstar_inputs.inputs`. `want` are inputs the scan must name;
# `refuses` is the reason it must refuse with. `stock` builds the tree with stock
# rustc (`--emit=dep-info` of crates/k/src/lib.rs) or stock cargo, and
# `stock_reads` are the repository files that build reads: from dep-info, for a
# build script from its exit status (it unwraps every read), and `stock_marker`, a
# file a program the build runs writes (`stock_cwd` is where cargo runs). Set KSTAR_STOCK_RUSTC (and
# KSTAR_STOCK_CARGO) to re-measure them; None marks a form no stock build reads (a
# guard, or a nightly-only feature).
K, KM = 'crates/k/src/lib.rs', 'crates/k/Cargo.toml'
ARM_BASE = {'Cargo.toml': '[workspace]\nmembers = ["crates/k"]\nresolver = "2"\n',
            KM: '[package]\nname = "k"\nversion = "0.0.0"\nedition = "2021"\n', K: ''}
X, Y, M = {'data/x.json': '{}'}, {'data/y.json': '{}'}, {'data/m.rs': ''}
S = '#[path = "../../../shared/s.rs"]\nmod s;\n'
FIX = 'macro_rules! fixture { ($p:literal) => { include_str!(concat!($p)) }; }\n'
READ = 'fn main() { std::fs::read(%s).unwrap(); }\n'
FEATURES = ', '.join(f'feature = "f{i:03}"' for i in range(40))
PKG = '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2021"\n'
MDIR = 'include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "%s"))'
ODIR = 'include!(concat!(env!("OUT_DIR"), "%s"));\n'
SPELLED = 'an include spelled other than `include_str!(` unqualified'
PATH_ATTR = 'a #[path] attribute other than `#[path = "..."]`'
UNFOLLOWED = 'cannot evaluate the include_str! argument'
BINDS = 'of fx! can bind what this rule cannot evaluate'
MEMBERS = 'a workspace members entry other than a plain path'
NO_ROW = 'has no reviewed declaration of its reads and the cargo:rustc-env keys it can print'
FA = '../../../data/a'
NUM = 'macro_rules! fx { ($n:literal) => { include_str!(concat!("%s", $n, %%s, ".json")) }; }\n' % FA
FX_LIT = 'macro_rules! fx { ($n:literal) => { include_str!(concat!("%s", $n, ".json")) }; }\n' % FA
FORM_ARMS = [
    dict(name='1 a comment before the bang of an include', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'pub const X: &str = include_str /* c */ !("../../../data/x.json");\n', **X}, refuses=SPELLED),
    dict(name='1b a comment before the bang of a macro invocation and inside a mod', stock='rustc', files={
        K: FIX + 'pub const Y: &str = fixture /* c */ !("../../../data/y.json");\n' + S,
        'shared/s.rs': 'mod /* c */ inner;\n', 'shared/inner.rs': '', **Y},
        want=['data/y.json', 'shared/s.rs', 'shared/inner.rs']),
    dict(name='a path-qualified include', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'pub const X: &str = std:: /* c */ include_str!("../../../data/x.json");\n', **X}, refuses=SPELLED),
    dict(name='a raw identifier include', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'pub const X: &str = r#include_str!("../../../data/x.json");\n', **X}, refuses=SPELLED),
    dict(name='2 a builtin include renamed by a use', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'use std::include_str as inc;\npub const X: &str = inc!("../../../data/x.json");\n', **X},
        refuses='a builtin include, concat!, stringify! or env! renamed by a use'),
    dict(name='3 an include macro renamed where it is never invoked by name', stock='rustc', stock_reads=['data/y.json'],
         files={K: FIX + 'pub(crate) use fixture;\npub const X: &str = fixture!("../../../data/x.json");\nmod other;\n',
                'crates/k/src/other.rs': 'use crate::fixture as fx;\npub const Y: &str = fx!("../../../data/y.json");\n',
                **X, **Y},
         refuses='fixture! is renamed by a use in crates/k/src/other.rs'),
    dict(name='4 a macro invoked through a metavariable', stock='rustc', stock_reads=['data/y.json'], files={
        K: FIX + 'macro_rules! call { ($m:ident) => { $m!("../../../data/y.json") }; }\n'
           'pub const X: &str = fixture!("../../../data/x.json");\npub const Y: &str = call!(fixture);\n', **X, **Y},
        refuses='a macro invoked through a metavariable'),
    dict(name='5 a negative literal bound to a literal fragment', stock='rustc', stock_reads=['data/a-1.json'], files={
        K: FX_LIT + 'pub const A: &str = fx!(2);\npub const B: &str = fx!(-1);\n', 'data/a2.json': '{}', 'data/a-1.json': '{}'},
        refuses=BINDS),
    dict(name='a decimal with leading zeros bound to a literal fragment', stock='rustc', stock_reads=['data/a7.json'],
         files={K: FX_LIT + 'pub const A: &str = fx!(007);\n', 'data/a7.json': '{}', 'data/a007.json': '"decoy"'},
         refuses=BINDS),
    dict(name='a number that is not plain decimal bound to a literal fragment', stock='rustc',
         stock_reads=['data/a1.json'], files={
             K: FX_LIT + 'pub const A: &str = fx!("2");\npub const B: &str = fx!(0x1);\n', 'data/a2.json': '{}',
             'data/a1.json': '{}'}, refuses=BINDS),
    dict(name='a fragment other than literal under concat!', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'macro_rules! fx { ($p:expr) => { include_str!(concat!($p)) }; }\n'
           'pub const A: &str = fx!("../../../data/x.json");\n', **X}, refuses=BINDS),
    dict(name='a decimal with leading zeros written directly', stock='rustc', stock_reads=['data/a7.json'], files={
        K: f'pub const A: &str = include_str!(concat!("{FA}", 007, ".json"));\n', 'data/a7.json': '{}',
        'data/a007.json': '"decoy"'}, refuses=UNFOLLOWED),
    dict(name='a number that is not decimal written directly', stock='rustc', stock_reads=['data/a1.json'], files={
        K: f'pub const A: &str = include_str!(concat!("{FA}", 0x1, ".json"));\n', 'data/a1.json': '{}'},
        refuses=UNFOLLOWED),
    dict(name='a concat! of plain literals only', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'pub const X: &str = include_str!(concat!("../../../data/", "x.json"));\n', **X}, refuses=UNFOLLOWED),
    dict(name='a decimal with leading zeros beside a metavariable', stock='rustc', stock_reads=['data/ax7.json'], files={
        K: NUM % '007' + 'pub const A: &str = fx!("x");\n', 'data/ax7.json': '{}', 'data/ax007.json': '"decoy"'},
        refuses='cannot evaluate the include_str! argument'),
    dict(name='a number that is not decimal beside a metavariable', stock='rustc', stock_reads=['data/ax1.json'], files={
        K: NUM % '0x1' + 'pub const A: &str = fx!("x");\n', 'data/ax1.json': '{}'},
        refuses='cannot evaluate the include_str! argument'),
    dict(name='a canonical decimal beside a metavariable', stock='rustc', stock_reads=['data/ax2.json'], files={
        K: NUM % '2' + 'pub const A: &str = fx!("x");\n', 'data/ax2.json': '{}'},
        refuses='cannot evaluate the include_str! argument'),
    dict(name='a boolean and stringify! of one token beside a metavariable', stock='rustc',
         stock_reads=['data/axtrue-k.json'], files={
             K: NUM % 'true, "-", stringify!(k)' + 'pub const A: &str = fx!("x");\n', 'data/axtrue-k.json': '{}'},
         refuses='cannot evaluate the include_str! argument'),
    dict(name='6 a comment inside #[path]', stock='rustc', stock_reads=['data/m.rs'], files={
        K: '#[/* c */ path = "../../../data/m.rs"]\nmod m;\n', **M}, refuses=PATH_ATTR),
    dict(name='a raw identifier path attribute', stock='rustc', stock_reads=['data/m.rs'], files={
        K: '#[r#path = "../../../data/m.rs"]\nmod m;\n', **M}, refuses=PATH_ATTR),
    dict(name='7 a path in cfg_attr, its predicate longer than 400 characters', stock='rustc', stock_reads=['data/m.rs'],
         files={K: f'#[cfg_attr(any({FEATURES}, not(feature = "zzz")), path = "../../../data/m.rs")]\nmod m;\n', **M},
         refuses='a #[path] inside cfg_attr'),
    dict(name='8 #[path = $p] in a macro body', stock='rustc', stock_reads=['data/m.rs'], files={
        K: 'macro_rules! pm { ($p:literal) => { #[path = $p] mod m; }; }\npm!("../../../data/m.rs");\n', **M},
        refuses=PATH_ATTR),
    dict(name='a #[path] on an item the rule does not read as mod x;', stock='rustc', stock_reads=['data/m.rs'], files={
        K: '#[path = "../../../data/m.rs"]\npub(crate)mod m;\n', **M},
        refuses='a #[path] on an item other than `mod x;`'),
    dict(name='a #[path] inside an inline module', stock='rustc', stock_reads=['data/m.rs'], files={
        K: 'mod outer {\n#[path = "../../../../data/m.rs"]\nmod m;\n}\n', 'crates/k/src/outer/README': '', **M},
        refuses='a #[path] inside an inline module'),
    dict(name='8b a module declared in a macro body', stock='rustc', stock_reads=['shared/deep.rs'], files={
        K: 'macro_rules! mm { () => { mod deep; }; }\n' + S, 'shared/s.rs': 'mm!();\n', 'shared/deep.rs': ''},
        refuses='a module declared in the body of mm!'),
    dict(name='9 a module in an inline module of a file reached by #[path]', stock='rustc',
         stock_reads=['shared/inner/deep.rs', 'data/x.json'], files={
             K: S, 'shared/s.rs': 'mod inner { mod deep; }\n',
             'shared/inner/deep.rs': 'pub const X: &str = include_str!("../../data/x.json");\n', **X},
         refuses='mod deep; inside an inline module'),
    dict(name='10 a symbolic link before ..', stock='rustc', stock_reads=['data/y.json'], files={
        K: S, 'shared/s.rs': 'pub const Y: &str = include_str!("lnk/../y.json");\n', 'shared/y.json': '"decoy"',
        'data/sub/z.json': '{}', **Y}, links={'shared/lnk': '../data/sub'},
        refuses='shared/y.json: read through a symbolic link'),
    dict(name='10b a directory link under crates/', stock='rustc', stock_reads=['gen/mod.rs'], files={
        K: 'mod gen;\n', 'gen/mod.rs': ''}, links={'crates/k/src/gen': '../../../gen'},
        refuses='crates/k/src/gen: a symbolic link under crates/'),
    dict(name='11 a single-quoted path dependency', stock='cargo', stock_reads=['ext/foo/src/lib.rs', 'data/x.json'], files={
        KM: ARM_BASE[KM] + "\n[dependencies]\nfoo = { path = '../../ext/foo' }\n", K: 'pub use foo::X;\n',
        'ext/foo/Cargo.toml': PKG % 'foo',
        'ext/foo/src/lib.rs': 'pub const X: &str = include_str!("../../../data/x.json");\n', **X},
        want=['ext/foo/Cargo.toml', 'ext/foo/src/lib.rs', 'data/x.json']),
    dict(name='11b a build key', stock='cargo', script=True, stock_reads=['data/x.json'], files={
        KM: ARM_BASE[KM] + "build = 'gen.rs'\n", 'crates/k/gen.rs': READ % '"../../data/x.json"', **X},
        refuses='crates/k/Cargo.toml: a `build` key in [package]'),
    dict(name='12 read_dir in a build script', stock='cargo', script=True, stock_reads=['data/dir/a.txt', 'data/dir/b.txt'], files={
        'crates/k/build.rs': 'fn main() { for e in std::fs::read_dir("../../data/dir").unwrap() '
                             '{ std::fs::read(e.unwrap().path()).unwrap(); } }\n',
        'data/dir/a.txt': 'a', 'data/dir/b.txt': 'b'},
        refuses='crates/k/build.rs: a build script (`fs`'),
    dict(name='12b format! in a build script', stock='cargo', script=True, stock_reads=['data/x.json'], files={
        'crates/k/build.rs': READ % 'format!("{}{}", "../../da", "ta/x.json")', **X},
        refuses='crates/k/build.rs: a build script (`fs`'),
    dict(name='12c a Path::join chain in a build script', stock='cargo', script=True, stock_reads=['data/x.json'], files={
        'crates/k/build.rs': READ % 'std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..")'
                                    '.join("data").join("x.json")', **X},
        refuses='crates/k/build.rs: a build script (`fs`'),
    dict(name='12d a declared build script, its reads named only by its row', stock='cargo', script=True,
         want=['data/list.txt', 'data/y.json'], declare={'crates/k/build.rs': (['data/list.txt'], ['data/list.txt'])},
         files={'crates/k/build.rs': 'fn main() { let l = std::fs::read_to_string(concat!("../../da", "ta/list.txt"))'
                                     '.unwrap(); for p in l.lines() { std::fs::read(format!("../../{p}")).unwrap(); } }\n',
                'data/list.txt': 'data/y.json\n', **Y}),
    dict(name='12e a build script that names no file capability', stock='cargo', script=True, want=[], files={
        'crates/k/build.rs': 'fn main() { println!("cargo:rustc-cfg=k"); }\n'}),
    dict(name='an OUT_DIR include reaching out of OUT_DIR', stock='cargo', stock_reads=['data/x.json'], files={
        'crates/k/build.rs': 'fn main() {}\n',
        K: 'pub const X: &str = include_str!(concat!(env!("OUT_DIR"), "/../../../../../repository/data/x.json"));\n',
        **X}, refuses='an OUT_DIR include other than'),
    dict(name='OUT_DIR set by cargo:rustc-env in a build script without a row', stock='cargo', stock_reads=['data/x.rs'],
         files={'crates/k/build.rs': 'fn main() { println!("cargo:rustc-env=OUT_DIR={}/../../data", '
                                     'std::env::var("CARGO_MANIFEST_DIR").unwrap()); }\n',
                K: ODIR % '/x.rs', 'data/x.rs': 'pub const X: u8 = 1;\n'}, refuses=NO_ROW),
    dict(name='an OUT_DIR file its row declares', stock='cargo', want=[],
         declare={'crates/k/build.rs': ([], [], ('rustc_env', []), ('out_dir', ['gen.rs']))},
         files={'crates/k/build.rs': 'fn main() { let d = std::env::var("OUT_DIR").unwrap(); '
                                     'std::fs::write(format!("{d}/gen.rs"), "pub const G: u8 = 1;\\n").unwrap(); }\n',
                K: ODIR % '/gen.rs'}),
    dict(name='an OUT_DIR file its row does not declare', stock='cargo', stock_reads=['data/x.json'],
         declare={'crates/k/build.rs': ([], [], ('rustc_env', []), ('out_dir', []))},
         files={'crates/k/build.rs': 'fn main() { let d = std::env::var("OUT_DIR").unwrap(); '
                                     'std::fs::write(format!("{d}/gen.rs"), concat!("pub const X: &str = include_str!(\\"", '
                                     'env!("CARGO_MANIFEST_DIR"), "/../../data/x.json\\");\\n")).unwrap(); }\n',
                K: ODIR % '/gen.rs', **X}, refuses='gen.rs is not a file crates/k/build.rs declares under out_dir'),
    dict(name='CARGO_MANIFEST_DIR set by cargo:rustc-env, listed in the row', stock='cargo', stock_reads=['data/x.json'],
         declare={'crates/k/build.rs': ([], [], ('rustc_env', ['CARGO_MANIFEST_DIR']), ('out_dir', []))},
         files={'crates/k/build.rs': 'fn main() { println!("cargo:rustc-env=CARGO_MANIFEST_DIR={}/../../data", '
                                     'std::env::var("CARGO_MANIFEST_DIR").unwrap()); }\n',
                K: f'pub const X: &str = {MDIR % "/x.json"};\n', 'crates/k/x.json': '"decoy"', **X},
         refuses='crates/k/build.rs can print cargo:rustc-env=CARGO_MANIFEST_DIR'),
    dict(name='a [lib] path outside the package directory', stock='cargo', stock_reads=['crates/k/data/x.json'], files={
        KM: ARM_BASE[KM] + '\n[lib]\npath = "../../shared/lib.rs"\n',
        'shared/lib.rs': f'pub const X: &str = {MDIR % "/data/x.json"};\n', 'crates/k/data/x.json': '{}',
        'data/x.json': '"decoy"', '.gitignore': 'crates/k/data/\n'},
        refuses='a target path outside its package directory'),
    dict(name='a CARGO_MANIFEST_DIR include in a package inside another package directory', stock='cargo',
         stock_reads=['data/x.json'], files={
             K: 'pub mod n;\n', 'crates/k/src/n/Cargo.toml': PKG % 'n',
             'crates/k/src/n/mod.rs': f'pub const X: &str = {MDIR % "/../../data/x.json"};\n',
             'crates/k/data/x.json': '"decoy"', **X},
         refuses='an env!("CARGO_MANIFEST_DIR") include in a package inside another package directory'),
    dict(name='a ** glob in workspace members', stock='cargo', stock_reads=['ext/a/b/p/src/lib.rs', 'data/x.json'], files={
        'Cargo.toml': '[workspace]\nmembers = ["crates/k", "ext/**/p"]\nresolver = "2"\n', 'ext/a/b/p/Cargo.toml': PKG % 'p',
        'ext/a/b/p/src/lib.rs': 'pub const X: &str = include_str!("../../../../../data/x.json");\n', **X},
        refuses=MEMBERS),
    dict(name='a * glob in workspace members matching a dot directory', stock='cargo',
         stock_reads=['ext/.p/src/lib.rs', 'data/x.json'], files={
             'Cargo.toml': '[workspace]\nmembers = ["crates/k", "ext/*"]\nresolver = "2"\n', 'ext/.p/Cargo.toml': PKG % 'p',
             'ext/.p/src/lib.rs': 'pub const X: &str = include_str!("../../../data/x.json");\n', **X},
         refuses=MEMBERS),
    dict(name='build.rustc-wrapper in .cargo/config.toml', stock='cargo', stock_marker='tools/ran.log',
         stock_reads=['tools/ran.log'], modes={'tools/w.sh': 0o755}, files={
             '.cargo/config.toml': '[build]\nrustc-wrapper = "tools/w.sh"\n',
             'tools/w.sh': '#!/bin/sh\necho ran >> "$(dirname "$0")/ran.log"\nexec "$@"\n'},
         refuses='.cargo/config.toml: `build.rustc-wrapper` in Cargo configuration'),
    dict(name="build.rustc-wrapper in a member's .cargo/config.toml", stock='cargo', stock_cwd='crates/k',
         stock_marker='tools/ran.log', stock_reads=['tools/ran.log'], modes={'tools/w.sh': 0o755}, files={
             'crates/k/.cargo/config.toml': '[build]\nrustc-wrapper = "../../tools/w.sh"\n',
             'tools/w.sh': '#!/bin/sh\necho ran >> "$(dirname "$0")/ran.log"\nexec "$@"\n'},
         refuses='crates/k/.cargo/config.toml: `build.rustc-wrapper` in Cargo configuration'),
    dict(name='the Cargo configuration keys the rule hashes', stock='cargo', want=['.cargo/config.toml'], stock_reads=[],
         files={
        '.cargo/config.toml': '[build]\njobs = 4\nrustflags = ["-C", "target-cpu=native"]\n\n'
                              '[target.aarch64-apple-darwin]\nrustflags = ["-C", "target-cpu=native"]\n\n'
                              '[env]\nRUST_MIN_STACK = { value = "67108864", force = false }\n\n'
                              '[alias]\nbuild = ["run", "--bogus"]\nx = "check"\n'}),
    dict(name='[patch] in .cargo/config.toml', stock=None, files={
        '.cargo/config.toml': '[patch.crates-io]\nfoo = { path = "ext/foo" }\n'},
        refuses='.cargo/config.toml: `patch.crates-io` in Cargo configuration'),
    dict(name='13a more than one metavariable in an include', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'macro_rules! two { ($a:literal, $b:literal) => { include_str!(concat!($a, $b)) }; }\n'
           'pub const A: &str = two!("../../../data/", "x.json");\n', **X}, refuses=UNFOLLOWED),
    dict(name='13b CARGO_MANIFEST_DIR after another piece', stock=None, files={
        K: 'pub const X: &str = include_str!(concat!("x", env!("CARGO_MANIFEST_DIR"), "/../../data/x.json"));\n', **X},
        refuses=UNFOLLOWED),
    dict(name='13c a file only a recursive invocation names', stock='rustc', want=['data/rec.json'], files={
        K: 'macro_rules! r { () => { r!("../../../data/rec.json") }; ($p:literal) => { include_str!(concat!($p)) }; }\n'
           'pub const R: &str = r!();\n', 'data/rec.json': '{}'}),
    dict(name='stringify! of an ident metavariable', stock='rustc', want=['data/case.json'], files={
        K: 'macro_rules! case { ($c:ident, $n:literal) => { pub const C: &str = '
           'include_str!(concat!("../../../data/", stringify!($c), ".json")); }; }\ncase!(case, 1);\n',
        'data/case.json': '{}'}),
    dict(name='a macro invoked by a computed name in a macro body', stock='rustc', stock_reads=['data/y.json'], files={
        K: FIX + 'macro_rules! call { ($($m:ident)*) => { $($m)*!("../../../data/y.json") }; }\n'
           'pub const X: &str = fixture!("../../../data/x.json");\npub const Y: &str = call!(fixture);\n', **X, **Y},
        refuses='a macro invoked by a computed name in the body of call!'),
    dict(name='an input reached through a symbolic link', stock=None, files={'data/t.lean': ''},
         links={'theories/cic_l/T.lean': '../../data/t.lean'},
         refuses='theories/cic_l/T.lean: an input reached through a symbolic link'),
    dict(name='a manifest tomllib cannot read', stock=None, files={KM: ARM_BASE[KM] + 'path = \n'},
         refuses='crates/k/Cargo.toml: a manifest this rule cannot read'),
    dict(name='a character outside ASCII in code', stock='rustc', stock_reads=['data/x.json'], files={
        K: 'pub const X: &str = include_str‎!("../../../data/x.json");\n', **X},
        refuses='a character outside ASCII in code'),
    dict(name='concat! shadowed by a macro_rules!', stock='rustc', stock_reads=['data/y.json'], files={
        K: 'macro_rules! concat { ($a:literal) => { "../../../data/y.json" }; }\n'
           'pub const X: &str = include_str!(concat!("../../../data/x.json"));\n', **X, **Y},
        refuses='a builtin include, concat!, stringify! or env! shadowed'),
    dict(name='#[path] on an inline module', stock='rustc', stock_reads=['shared/deep.rs'], files={
        K: '#[path = "../../../shared"]\nmod inl { mod deep; }\n', 'shared/deep.rs': ''},
        refuses='a #[path] on an inline module'),
    dict(name='a mod declaration in a file reached by #[path] naming no file', stock=None, files={
        K: S, 'shared/s.rs': 'mod absent;\n'}, refuses='mod absent; names no repository file'),
    dict(name='the macro keyword (nightly decl_macro)', stock=None, files={
        K: '#![feature(decl_macro)]\nmacro m($p:literal) { include_str!($p) }\n'
           'pub const X: &str = m!("../../../data/x.json");\n', **X},
        refuses='the `macro` keyword'),
    dict(name='a package at the workspace root', stock=None, files={
        'Cargo.toml': '[package]\nname = "r"\nversion = "0.0.0"\n\n[workspace]\nmembers = ["crates/k"]\n'},
        refuses='a package at the workspace root'),
]


def stock_build(root, arm, rustc, cargo):
    """(exit status, repository files the stock build reads) of an arm's tree: its dep-info, and its marker."""
    env = dict(os.environ, CARGO_MANIFEST_DIR=str(root / 'crates/k'), RUSTC=rustc)
    target = root.parent / 'target'
    if arm['stock'] == 'rustc':
        argv = [rustc, '--edition', '2021', '--crate-type', 'lib', '--crate-name', 'k',
                f'--emit=dep-info={target}/k.d', K]
        target.mkdir(exist_ok=True)
    else:
        argv, env['CARGO_TARGET_DIR'] = [cargo, 'build', '--offline', '--quiet'], str(target)
    done = subprocess.run(argv, cwd=root / arm.get('stock_cwd', ''), env=env, capture_output=True, text=True)
    reads = {arm['stock_marker']} if arm.get('stock_marker') and (root / arm['stock_marker']).is_file() else set()
    for d in target.rglob('*.d'):
        for line in d.read_text().splitlines():
            for dep in (line.partition(': ')[2] if ': ' in line else '').replace('\\ ', '\0').split():
                real = Path(os.path.realpath(dep.replace('\0', ' ') if os.path.isabs(dep) else root / dep))
                if real.is_file() and real.is_relative_to(root) and '.git' not in real.relative_to(root).parts:
                    reads.add(real.relative_to(root).as_posix())
    return done.returncode, reads


def form_controls(check):
    """Each listed form: evaluated (its stock reads are inputs) or refused for its reason."""
    rustc, cargo = os.environ.get('KSTAR_STOCK_RUSTC'), os.environ.get('KSTAR_STOCK_CARGO')
    for arm in FORM_ARMS:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve() / 'repository'
            write_tree(root, {**ARM_BASE, **arm['files']}, arm.get('links'))
            for rel, mode in arm.get('modes', {}).items():
                os.chmod(root / rel, mode)
            declare(root, arm.get('declare', {}))
            git_add(root)
            try:
                found, refused = set(ki.inputs(root, ())), ''
            except Exception as e:  # a crash is no refusal: its message names no reason
                found, refused = set(), f'{type(e).__name__}: {e}'
            if 'refuses' in arm:
                check(f'form {arm["name"]}: refused', arm['refuses'] in refused and refused.startswith('ValueError'))
            else:
                check(f'form {arm["name"]}: evaluated', not refused and set(arm['want']) <= found)
            if rustc and arm['stock'] and (arm['stock'] == 'rustc' or cargo):
                code, reads = stock_build(root, arm, rustc, cargo)
                expected = set(arm.get('stock_reads', arm.get('want', [])))
                reads |= expected if code == 0 and arm.get('script') else set()  # it unwraps each read
                check(f'form {arm["name"]}: stock {arm["stock"]} builds it', code == 0)
                check(f'form {arm["name"]}: stock reads', expected <= reads)
                if 'want' in arm:
                    check(f'form {arm["name"]}: every stock read is an input', reads <= found)


def input_controls(check):
    """The input rule: a file a member's build reads moves the record; a use it cannot name refuses."""
    def verdict(path):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = k.check_record(path)
        return code, out.getvalue()
    with tempfile.TemporaryDirectory() as td:
        root = Path(td).resolve() / 'repository'
        source_tree(root)
        record = root / 'record.json'
        with patch.object(k, 'ROOT', root):
            inputs = k.source_inputs()
            (root / 'read.txt').write_text('read by both builds\n')  # a build read no edit below moves
            reads = {m: {'read.txt': k.digest(root / 'read.txt')} for m in k.RUST_MEMBERS}
            record.write_text(json.dumps(dict(source_inputs=inputs, success=False, build_reads=reads)))
            code, before = verdict(record)
            (root / 'data/t.json').write_text('{"moved": true}')
            code_after, after = verdict(record)
            check('an include_str! target outside crates/ makes the record stale',
                  'stale source inputs' not in before and code_after == 1 and 'stale source inputs' in after)
            for rel in EXPECTED:
                check('input: ' + rel, rel in inputs)
            for rel in UNNAMED:
                check('a file nothing names is no input: ' + rel, rel not in inputs)
            old_rule = set(k.FIXED_INPUTS) | {p.relative_to(root).as_posix() for p in (root / 'crates').rglob('*')
                                               if p.suffix in ('.rs', '.toml')}
            check('no input of the 2026-11-13 rule is dropped', old_rule <= set(inputs))
            for name, reason, edits in REFUSALS:
                originals = {rel: (root / rel).read_text() for rel, _ in edits}
                for rel, text in edits:
                    (root / rel).write_text((root / rel).read_text() + text)
                try:
                    k.source_inputs()
                    refused = ''
                except Exception as e:  # a crash is no refusal: its message names no reason
                    refused = f'{type(e).__name__}: {e}'
                code, out = verdict(record)
                check('refuses ' + name, reason in refused and code == 1 and 'not knowable here' in out)
                for rel, text in originals.items():
                    (root / rel).write_text(text)
    form_controls(check)


def verdict(path):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        code = k.check_record(path)
    return code, out.getvalue()


def green_record(td):
    """A record every conjunct but the build read set accepts (stub executables, never a vote)."""
    rows = {m: dict(accepted=True, axioms=['propext']) for m in k.MEMBERS}
    said = {'extra-axiom': 'q3_extra_axiom: axiom outside Ax0', 'ill-typed-body': 'type mismatch',
            'forged-recursor': ("while replaying declaration 'forged_rec_false' application type mismatch @FRT.rec; "
                                'FRT.rec: the structural tier refused it: file (0, 0, 1, 0), kernel generates '
                                '(0, 0, 1, 2); malformed: recursor numMinors')}
    controls = {n: dict(sha256=k.nano.CONTROLS[n]['sha256'], members={
        m: dict(accepted=False, failure=k.LEAN4LEAN_CONTROLS[n]) if m == 'lean4lean'
        else dict(accepted=False, exit_code=1, stderr=said[n]) for m in k.MEMBERS}) for n in k.CONTROL_NAMES}
    ids = {}
    for m in k.MEMBERS:
        (Path(td) / m).write_text('#!/bin/sh\n')
        os.chmod(Path(td) / m, 0o755)
        ids[m] = dict(binary=k.identity(Path(td) / m))
    return dict(source_inputs={}, success=True, qualified_lean4lean=True, identities=ids, controls=controls,
                subjects=[dict(sha256=h, source_sha256=s, members=rows)
                          for h, s in zip(sorted(k.SUBJECT_PINS), sorted(k.SOURCE_PINS))])


# Cargo's dep-info escapes only a space (`\ `): the names below hold a space, a
# colon, a lone backslash, a backslash before a space, `#` and `$`.
DEP_INFO = ('/w/t\\ d/debug/k: /w/a\\ b.rs /w/c:d.rs /w/e\\f.rs /w/g\\\\ h.rs /w/i#$.rs\n',
            ['/w/a b.rs', '/w/c:d.rs', '/w/e\\f.rs', '/w/g\\ h.rs', '/w/i#$.rs'])
DEP_INFO_REFUSALS = [('a second line', '/w/t\\ d/debug/k: /w/a.rs\n/w/b.rs:\n', 'is not one rule'),
                     ('no final newline', '/w/t\\ d/debug/k: /w/a.rs', 'is not one rule'),
                     ('another target', '/w/t\\ d/debug/j: /w/a.rs\n', 'is not one rule'),
                     ('two spaces', '/w/t\\ d/debug/k:  /w/a.rs\n', 'is malformed'),
                     ('a relative path', '/w/t\\ d/debug/k: a.rs\n', 'names a relative path')]


GIT_IDENT = ['-c', 'user.name=k', '-c', 'user.email=k@k', '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null']
GIT_ENV = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}


def git_commit(root):
    """Commit every file of a synthetic repository, a new one included, as it stands."""
    for argv in (['init', '-q'], ['add', '-A'], [*GIT_IDENT, 'commit', '-q', '--no-verify', '--allow-empty', '-m', 'c']):
        subprocess.run(['git', '-C', str(root), *argv], check=True, capture_output=True, env=GIT_ENV)


def fake_build(td, inside=False):
    """A committed repository, a target directory with one member binary, its dep-info and its
    build-start record, and the entry naming it. HEAD~1 holds other bytes of data/x.txt."""
    root = Path(td).resolve() / 'repository'
    target = root / 'target-x' if inside else Path(td).resolve() / 'target'
    write_tree(root, {'crates/p/Cargo.toml': PKG % 'p', 'crates/p/build.rs': 'fn main() {}\n',
                      'crates/p/src/main.rs': 'fn main() {}\n', 'data/x.txt': 'earlier\n', 'data/y.txt': 'y\n'})
    git_commit(root)
    (root / 'data/x.txt').write_text('x\n')
    git_commit(root)
    out = target / 'debug/build/p-0123456789abcdef'
    write_tree(target, {'debug/k': 'binary', 'debug/build/p-0123456789abcdef/output': 'cargo:rerun-if-changed=build.rs\n',
                        'debug/build/p-0123456789abcdef/out/gen.rs': ''})
    deps = [root / 'crates/p/src/main.rs', root / 'crates/p/build.rs', root / 'data/x.txt', out / 'out/gen.rs']
    (target / 'debug/k.d').write_text(f'{target}/debug/k:' + ''.join(f' {d}' for d in deps) + '\n')
    entry = dict(binary=dict(path=str(target / 'debug/k'), sha256=k.digest(target / 'debug/k')),
                 built_at=str(target / 'debug/k'))
    head = k.git(root, 'rev-parse', 'HEAD').strip()
    (target / ('debug/k' + k.BUILD_RECORD)).write_text(json.dumps(dict(
        member='m', started_ns=25 * 10**17, head_before=head, head_after=head, dirty_before=[], dirty_after=[],
        exit_code=0, binary_sha256=entry['binary']['sha256'])))
    return root, target, entry


def stamp(path, ns):
    os.utime(path, ns=(ns, ns))


def attempt(fn, *args):
    """(value, '') or (None, the refusal); a crash is no refusal: its message names no reason."""
    try:
        return fn(*args), ''
    except Exception as e:
        return None, f'{type(e).__name__}: {e}'


def refusals_of_build(check):
    """Item 1's fail-closed cases on a fake target directory: each refused for its reason, or admitted."""
    def append_dep(t, *paths):
        (t / 'debug/k.d').write_text((t / 'debug/k.d').read_text()[:-1] + ''.join(f' {x}' for x in paths) + '\n')

    def new_layout(t, text):  # the build-dir layout Trust's targo writes
        (t / 'debug/build/p-0123456789abcdef/output').unlink()
        write_tree(t, {'debug/build/p/0123456789abcdef/run/stdout': text})

    def toolchain(r, t, e):  # a compiler whose printed sysroot is not its grandparent, as for Trust's store
        write_tree(t.parent, {'tc/bin/rustc': f'#!/bin/sh\necho {t.parent}/store\n', 'tc/lib/a.rlib': '', 'store/lib/b.rlib': ''})
        os.chmod(t.parent / 'tc/bin/rustc', 0o755)
        e['compiler_path'] = str(t.parent / 'tc/bin/rustc')
        append_dep(t, t.parent / 'tc/lib/a.rlib', t.parent / 'store/lib/b.rlib')

    def started(t, **changes):  # an edit of the build-start record
        path = t / ('debug/k' + k.BUILD_RECORD)
        path.write_text(json.dumps(dict(json.loads(path.read_text()), **changes)))

    def detour(r, t, e):  # out of the repository through a link, back in by `..`, to other bytes
        write_tree(r.parent, {'other/deep/.keep': '', 'other/repository/data/x.txt': 'elsewhere\n'})
        os.symlink(r.parent / 'other/deep', r.parent / 'away')
        append_dep(t, f'{r.parent}/away/../repository/data/x.txt')

    def head1(r):
        return k.git(r, 'rev-parse', 'HEAD~1').strip()
    out = 'debug/build/p-0123456789abcdef/out'
    honest = {'crates/p/src/main.rs', 'crates/p/build.rs', 'data/x.txt'}
    cases = [
        ('an honest dep-info', lambda r, t, e: None, honest),
        ('the build-dir layout', lambda r, t, e: new_layout(t, 'cargo:rerun-if-changed=build.rs\n'), honest),
        ('toolchain files', toolchain, honest),
        ('a target directory inside the repository', lambda r, t, e: None, honest, dict(inside=True)),
        ('an unnormalized path, keyed as listed and normalized', lambda r, t, e: append_dep(t, f'{r}/crates/p/../../data/y.txt'),
         honest | {'data/y.txt'}),
        ('no dep-info', lambda r, t, e: (t / 'debug/k.d').unlink(), 'no dep-info beside'),
        ('another binary at built_at', lambda r, t, e: (t / 'debug/k').write_text('rebuilt'), 'is not the member binary'),
        ('a dep-info older than the binary', lambda r, t, e: stamp(t / 'debug/k.d', 10**18), 'older than the binary'),
        ('a listed path that is missing', lambda r, t, e: (r / 'data/x.txt').unlink(), 'cannot be read as a file'),
        ('a listed directory', lambda r, t, e: ((r / 'data/x.txt').unlink(), (r / 'data/x.txt').mkdir()),
         'cannot be read as a file'),
        ('a path outside every known root', lambda r, t, e: append_dep(t, '/elsewhere/x.rs'), 'outside the repository'),
        ('a toolchain file with no compiler named', lambda r, t, e: (toolchain(r, t, e), e.pop('compiler_path')),
         'outside the repository'),
        ('no repository file', lambda r, t, e: (t / 'debug/k.d').write_text(
            f'{t}/debug/k: {t}/debug/build/p-0123456789abcdef/out/gen.rs\n'), 'names no repository file'),
        ('a build script without rerun-if-changed',
         lambda r, t, e: (t / 'debug/build/p-0123456789abcdef/output').write_text('cargo:rerun-if-env-changed=X\n'),
         'printed no rerun-if-changed'),
        ('a build script without rerun-if-changed (the build-dir layout)',
         lambda r, t, e: new_layout(t, 'cargo:rerun-if-env-changed=X\n'), 'printed no rerun-if-changed'),
        ('no build-script output', lambda r, t, e: (t / 'debug/build/p-0123456789abcdef/output').unlink(),
         'no build-script output of p'),
        ('no build-script output of a `[project]` package',
         lambda r, t, e: ((r / 'crates/p/Cargo.toml').write_text(PKG.replace('package', 'project') % 'p'),
                          (t / 'debug/build/p-0123456789abcdef/output').unlink()), 'no build-script output of p'),
        # D1: the build-start stamp and the git state, as `build_member` records them.
        ('no build-start record', lambda r, t, e: (t / ('debug/k' + k.BUILD_RECORD)).unlink(), 'no build-start record'),
        ('a malformed build-start record', lambda r, t, e: started(t, started_ns='0'), 'malformed build-start record'),
        ('a build-start record of another binary', lambda r, t, e: started(t, binary_sha256='0' * 64), 'is of another build'),
        ('a build-start record of another member', lambda r, t, e: started(t, member='n'), 'is of another build'),
        ('a stamped build that exited nonzero', lambda r, t, e: started(t, exit_code=101), 'the stamped build exited 101'),
        ('HEAD moving during the build', lambda r, t, e: started(t, head_after=head1(r)), 'HEAD moved during the build'),
        ('a listed file changed at the start of the build', lambda r, t, e: stamp(r / 'data/x.txt', 25 * 10**17),
         'data/x.txt, which changed at or after the start of the build'),
        ('a listed file changed after the build', lambda r, t, e: stamp(r / 'data/x.txt', 4 * 10**18),
         'data/x.txt, which changed at or after the start of the build'),
        ('a listed file not clean before the build', lambda r, t, e: started(t, dirty_before=['data/x.txt']),
         'tracked paths were not clean before or after the build (data/x.txt)'),
        ('a listed file not clean after the build', lambda r, t, e: started(t, dirty_after=['data/x.txt']),
         'tracked paths were not clean before or after the build (data/x.txt)'),
        # K1: a dirty path the dep-info never lists (a manifest, Cargo.lock) refuses as well.
        ('an unlisted manifest not clean before the build', lambda r, t, e: started(t, dirty_before=['crates/p/Cargo.toml']),
         'tracked paths were not clean before or after the build (crates/p/Cargo.toml)'),
        ('an unlisted Cargo.lock not clean after the build', lambda r, t, e: started(t, dirty_after=['Cargo.lock']),
         'tracked paths were not clean before or after the build (Cargo.lock)'),
        ('a listed file edited, its mtime reset (cp -p)',
         lambda r, t, e: ((r / 'data/x.txt').write_text('z\n'), stamp(r / 'data/x.txt', 2 * 10**18)),
         'data/x.txt, whose bytes differ from its blob at'),
        ('an untracked listed file', lambda r, t, e: ((r / 'data/u.txt').write_text('u\n'), stamp(r / 'data/u.txt', 10**18),
                                                      append_dep(t, r / 'data/u.txt')), 'does not track'),
        ("a listed file whose blob differs at the record's HEAD", lambda r, t, e: e.update(record_head=head1(r)),
         'data/x.txt, whose bytes differ from its blob at'),
        # D2: a path is keyed as listed, never through a link.
        ('a listed symbolic link', lambda r, t, e: (os.symlink('x.txt', r / 'data/link.txt'), append_dep(t, r / 'data/link.txt')),
         'data/link.txt, which is a symbolic link'),
        ('a listed path through a directory link', lambda r, t, e: (os.symlink('data', r / 'alias'), append_dep(t, r / 'alias/x.txt')),
         'alias/x.txt, which passes through a symbolic link'),
        ('a path that leaves through a link and returns by ..', detour, 'which passes through a symbolic link'),
        ('the repository named through a link outside it',
         lambda r, t, e: (os.symlink(r, r.parent / 'alias'), append_dep(t, r.parent / 'alias/data/x.txt')),
         'reaches the repository through a symbolic link'),
        ('a target-directory path that resolves into the repository',
         lambda r, t, e: (os.symlink(r / 'data/x.txt', t / out / 'x.rs'), append_dep(t, t / out / 'x.rs')),
         'reaches the repository through a symbolic link'),
    ]
    for label, edit, reason, *options in cases:
        with tempfile.TemporaryDirectory() as td:
            root, target, entry = fake_build(td, **(options[0] if options else {}))
            for p in [*root.rglob('*'), *target.rglob('*')]:
                stamp(p, 2 * 10**18)
            edit(root, target, entry)
            if label != 'a dep-info older than the binary' and (target / 'debug/k.d').exists():
                stamp(target / 'debug/k.d', 3 * 10**18)
            got, refused = attempt(k.build_reads, 'm', entry, root, entry.pop('record_head', None))
            if isinstance(reason, set):
                check('build reads: admitted ' + label, set(got or ()) == reason and not refused)
            else:
                check('build reads refuse ' + label, refused.startswith('ValueError') and reason in refused)


def exit_status(fn):
    """fn()'s value, or the status an argparse refusal exits with."""
    try:
        return fn()
    except SystemExit as e:
        return e.code


def builder_controls(check):
    """build_member stamps the start before the command and records HEAD, dirty paths, exit and binary."""
    with tempfile.TemporaryDirectory() as td:
        root, target, _ = fake_build(td)
        built, sh = target / 'debug/k', Path(__file__).with_name('kstar_recheck.sh')
        record = built.with_name('k' + k.BUILD_RECORD)
        (root / 'data/y.txt').write_text('dirty before the build\n')
        command = [sys.executable, '-c', 'import pathlib, sys; pathlib.Path(sys.argv[1]).write_text("rebuilt"); '
                   'pathlib.Path(sys.argv[2]).write_text("edited during the build\\n"); sys.exit(3)',
                   built, root / 'data/x.txt']
        code = k.build_member('m', built, command, root)
        b = json.loads(record.read_text())
        head = k.git(root, 'rev-parse', 'HEAD').strip()
        check('builder: returns and records the exit status', code == 3 and b['exit_code'] == 3)
        check('builder: stamps the start before the command runs', b['started_ns'] < built.stat().st_mtime_ns)
        check('builder: records the binary the command left', b['binary_sha256'] == k.digest(built))
        check('builder: records HEAD before and after', b['head_before'] == b['head_after'] == head)
        check('builder: records a path not clean before the build', b['dirty_before'] == ['data/y.txt'])
        check('builder: records a path the build left not clean', b['dirty_after'] == ['data/x.txt', 'data/y.txt'])
        k.build_member('m', built, ['git', '-C', root, *GIT_IDENT, 'commit', '-qam', 'during'], root, GIT_ENV)
        b = json.loads(record.read_text())
        check('builder: records HEAD moving during the build', b['head_before'] == head != b['head_after'])
        argv = ['kstar', '--build-member', 'ck0-stock', '--built-at', str(built), '--', sys.executable, '-c', 'pass']
        with patch.object(k, 'ROOT', root), patch.object(sys, 'argv', argv), contextlib.redirect_stderr(io.StringIO()):
            code = exit_status(k.main)
        check('builder: --build-member runs the command after --', code == 0 and json.loads(record.read_text())['command']
              == [sys.executable, '-c', 'pass'])
        with patch.object(sys, 'argv', argv[:5]), contextlib.redirect_stdout(io.StringIO()):
            check('builder: --build-member without a command refuses', exit_status(k.main) == 2)
        record.unlink()
        # The shell driver, copied beside a stub gate: no reservation is ever taken here.
        driver = Path(td) / 'driver/scripts'
        write_tree(driver, {'heavy_gate.sh': '#!/bin/sh\necho stub gate reached\nexit 99\n'})
        shutil.copy2(sh, driver / sh.name)
        os.chmod(driver / 'heavy_gate.sh', 0o755)
        env = {n: v for n, v in os.environ.items() if n != 'HEAVY_GATE_HELD'}
        done = subprocess.run([driver / sh.name, *argv[1:]],
                              env=dict(env, KSTAR_PYTHON=sys.executable), capture_output=True, text=True)
        check('builder: the shell driver refuses a build outside a reservation',
              done.returncode == 2 and 'heavy_gate' in done.stderr and not record.exists())


# A workspace whose binary k depends on library a, which includes data/x.txt. k's build
# script waits for the file KSTAR_GO names, so an arm can edit a's inputs after rustc read
# them and before cargo finishes (and writes the dep-info).
RACE = {'Cargo.toml': '[workspace]\nmembers = ["a", "k"]\nresolver = "2"\n', 'a/Cargo.toml': PKG % 'a',
        'a/src/lib.rs': 'pub const S: &str = "OLD";\npub const X: &str = include_str!("../../data/x.txt");\n',
        'k/Cargo.toml': PKG % 'k' + '\n[dependencies]\na = { path = "../a" }\n',
        'k/build.rs': ('fn main() {\n    println!("cargo:rerun-if-changed=build.rs");\n'
                       '    let go = std::path::PathBuf::from(std::env::var("KSTAR_GO").unwrap());\n'
                       '    let start = std::time::Instant::now();\n'
                       '    while !go.exists() && start.elapsed().as_secs() < 120 {\n'
                       '        std::thread::sleep(std::time::Duration::from_millis(20));\n    }\n}\n'),
        'k/src/main.rs': 'fn main() { println!("{} {}", a::S, a::X.trim()); }\n', 'data/x.txt': 'x1\n'}


def stock_race(check, cargo):
    """D1 and D2 with stock cargo: an edit during the build, an edit whose mtime is reset, a listed link."""
    with tempfile.TemporaryDirectory() as td:
        root, target, go = Path(td).resolve() / 'ws', Path(td).resolve() / 'target', Path(td).resolve() / 'go'
        write_tree(root, RACE)
        git_commit(root)
        rustc = os.environ.get('KSTAR_STOCK_RUSTC') or str(Path(cargo).with_name('rustc'))
        env = dict(os.environ, CARGO_TARGET_DIR=str(target), RUSTC=rustc, KSTAR_GO=str(go))
        built, x = target / 'debug/k', root / 'data/x.txt'

        def reads():
            entry = dict(binary=dict(path=str(built), sha256=k.digest(built)), built_at=str(built), compiler_path=rustc)
            return attempt(k.build_reads, 'ck0-stock', entry, root)

        def output():
            return subprocess.run([built], capture_output=True, text=True).stdout.strip()

        def stamped(during):
            """A build_member build; `during` runs once a's rlib is rewritten, then k's build script goes on."""
            go.unlink(missing_ok=True)
            began, box = time.time(), {}
            worker = threading.Thread(target=lambda: box.update(code=k.build_member(
                'ck0-stock', built, [cargo, 'build', '--offline', '--quiet'], root, env)))
            worker.start()
            def rebuilt():
                try:
                    return any(p.stat().st_mtime > began for p in (target / 'debug/deps').glob('liba-*.rlib'))
                except OSError:
                    return False
            while worker.is_alive() and time.time() < began + 120 and not rebuilt():
                time.sleep(0.02)
            during()
            go.touch()
            worker.join()
            return box.get('code')

        def plain():
            go.touch()
            return subprocess.run([cargo, 'build', '--offline', '--quiet'], cwd=root, env=env, capture_output=True).returncode
        lib = root / 'a/src/lib.rs'
        code = stamped(lambda: lib.write_text(RACE['a/src/lib.rs'].replace('OLD', 'NEW')))
        check('stock race: stock cargo builds the arm, its binary from the bytes read before the edit',
              code == 0 and output() == 'OLD x1')
        check('stock race: a file edited during the build refuses (the start stamp, not the dep-info mtime)',
              'a/src/lib.rs, which changed at or after the start of the build' in reads()[1])
        check('stock race: stock cargo, stamping its start, rebuilds the edit', plain() == 0 and output() == 'NEW x1')
        x.write_text('x2\n')
        (root / 'k/build.rs').write_text(RACE['k/build.rs'] + '// rerun\n')
        git_commit(root)

        def reset_edit():  # what cp -p, rsync -t or tar -x leave
            before = x.stat()
            x.write_text('x3, longer\n')
            os.utime(x, ns=(before.st_atime_ns, before.st_mtime_ns))
        code = stamped(reset_edit)
        check('stock race: the binary holds the bytes read before an edit whose mtime was reset',
              code == 0 and output() == 'NEW x2')
        check('stock race: an edit during the build with its mtime reset refuses',
              'tracked paths were not clean before or after the build (data/x.txt)' in reads()[1])
        check('stock race: stock cargo misses an edit whose mtime was reset', plain() == 0 and output() == 'NEW x2')
        x.write_text('x2\n')
        write_tree(root, {'data/vis.py': 'print(1)\n',
                          'k/src/main.rs': '#![debugger_visualizer(gdb_script_file = "../../data/link.py")]\n'
                                           + RACE['k/src/main.rs']}, {'data/link.py': 'vis.py'})
        git_commit(root)
        code = stamped(lambda: None)
        listed = {os.path.normpath(p) for p in k.parse_dep_info((target / 'debug/k.d').read_text(), built)}
        check('stock link: stock cargo lists the link the build named, not its target',
              code == 0 and str(root / 'data/link.py') in listed and str(root / 'data/vis.py') not in listed)
        check('stock link: a listed symbolic link refuses', 'data/link.py, which is a symbolic link' in reads()[1])


# K1: k/Cargo.toml selects which file main.rs includes; no dep-info lists a manifest.
DIRTY = {'Cargo.toml': '[workspace]\nmembers = ["k"]\nresolver = "2"\n',
         'k/Cargo.toml': PKG % 'k' + '\n[features]\ndefault = []\nalt = []\n',
         'k/src/main.rs': ('#[cfg(feature = "alt")]\nconst M: &str = include_str!("alt.txt");\n'
                           '#[cfg(not(feature = "alt"))]\nconst M: &str = include_str!("m.txt");\n'
                           'fn main() { println!("{}", M.trim()); }\n'),
         'k/src/alt.txt': 'alt\n', 'k/src/m.txt': 'm\n'}


def stock_dirty_manifest(check, cargo):
    """K1 with stock cargo: an uncommitted k/Cargo.toml selects a feature, and `git checkout` reverts it."""
    with tempfile.TemporaryDirectory() as td:
        root, target = Path(td).resolve() / 'ws', Path(td).resolve() / 'target'
        write_tree(root, DIRTY)
        git_commit(root)
        rustc = os.environ.get('KSTAR_STOCK_RUSTC') or str(Path(cargo).with_name('rustc'))
        env = dict(os.environ, CARGO_TARGET_DIR=str(target), RUSTC=rustc)
        built, argv = target / 'debug/k', [cargo, 'build', '--offline', '--quiet']

        def output():
            return subprocess.run([built], capture_output=True, text=True).stdout.strip()
        (root / 'k/Cargo.toml').write_text(DIRTY['k/Cargo.toml'].replace('default = []', 'default = ["alt"]'))
        code = k.build_member('ck0-stock', built, argv, root, env)
        b = json.loads(built.with_name('k' + k.BUILD_RECORD).read_text())
        check('stock dirty manifest: stock cargo builds the feature the uncommitted manifest selects',
              code == 0 and output() == 'alt' and b['dirty_before'] == b['dirty_after'] == ['k/Cargo.toml'])
        listed = {os.path.relpath(p, root) for p in k.parse_dep_info((target / 'debug/k.d').read_text(), built)}
        check('stock dirty manifest: the dep-info lists the selected file and no manifest',
              {'k/src/main.rs', 'k/src/alt.txt'} <= listed and not any(p.endswith('Cargo.toml') for p in listed))
        subprocess.run(['git', '-C', str(root), 'checkout', '--', 'k/Cargo.toml'], check=True, capture_output=True,
                       env=GIT_ENV)
        entry = dict(binary=dict(path=str(built), sha256=k.digest(built)), built_at=str(built), compiler_path=rustc)
        refused = attempt(k.build_reads, 'ck0-stock', entry, root)[1]
        check('stock dirty manifest: a manifest dirty at the build, reverted before the receipt, refuses',
              refused.startswith('ValueError') and 'not clean before or after the build (k/Cargo.toml)' in refused)
        code = subprocess.run(argv, cwd=root, env=env, capture_output=True).returncode
        check('stock dirty manifest: the committed tree builds other bytes', code == 0 and output() == 'm')


def stock_cargo_build(check, cargo):
    """A stock cargo build's dep-info, parsed and compared with what the arm expects."""
    files = {'Cargo.toml': '[workspace]\nmembers = ["k"]\nresolver = "2"\n', 'k/Cargo.toml': PKG % 'k',
             'k/build.rs': 'fn main() {\n    println!("cargo:rerun-if-changed=build.rs");\n'
                           '    println!("cargo:rerun-if-changed=data/w.txt");\n}\n',
             'k/src/main.rs': ('#![debugger_visualizer(gdb_script_file = "../vis/k.py")]\n'
                               '#[path = "other/p.rs"]\nmod p;\nmod m;\ninclude!("../gen/i.rs");\n'
                               'const A: &str = include_str!("../data/sp ace.txt");\n'
                               'const B: &[u8] = include_bytes!("../data/c:d\\\\e.bin");\n'
                               'fn main() { println!("{} {} {} {} {}", A, B.len(), p::P, m::M, I); }\n'),
             'k/src/m.rs': 'pub const M: u8 = 1;\n', 'k/src/other/p.rs': 'pub const P: u8 = 2;\n',
             'k/gen/i.rs': 'const I: u8 = 3;\n', 'k/data/w.txt': 'w\n', 'k/data/sp ace.txt': 's\n',
             'k/data/c:d\\e.bin': 'b', 'k/data/unread.txt': 'u\n', 'k/vis/k.py': 'print(1)\n'}
    want = {'k/build.rs', 'k/src/main.rs', 'k/src/m.rs', 'k/src/other/p.rs', 'k/gen/i.rs', 'k/vis/k.py',
            'k/data/w.txt', 'k/data/sp ace.txt', 'k/data/c:d\\e.bin'}
    with tempfile.TemporaryDirectory() as td:
        root, target = Path(td).resolve() / 'ws dir', Path(td).resolve() / 'target dir'
        write_tree(root, files)
        git_commit(root)
        rustc = os.environ.get('KSTAR_STOCK_RUSTC') or str(Path(cargo).with_name('rustc'))
        env = dict(os.environ, CARGO_TARGET_DIR=str(target), RUSTC=rustc)
        built = target / 'debug/k'

        def build():
            code = k.build_member('ck0-stock', built, [cargo, 'build', '--offline', '--quiet'], root, env)
            return code == 0 and dict(binary=dict(path=str(built), sha256=k.digest(built)),
                                      built_at=str(built), compiler_path=rustc)
        entry = build()
        check('build reads: stock cargo builds the arm', bool(entry))
        check('build reads: the stock dep-info lists exactly the files the arm expects',
              set(attempt(k.build_reads, 'ck0-stock', entry, root)[0] or ()) == want)
        (root / 'k/build.rs').write_text('fn main() {}\n')  # no rerun-if-changed: cargo watches the package
        git_commit(root)
        (target / 'debug/k.d').unlink()  # cargo rewrites a dep-info only when its list changes
        entry = build()
        refused = attempt(k.build_reads, 'ck0-stock', entry, root)[1]
        check('build reads: a stock build script without rerun-if-changed refuses',
              refused.startswith('ValueError') and 'printed no rerun-if-changed' in refused)


def main_controls(check):
    """The replay's own use of the set: recorded after the identities, checked again at the end of the run."""
    with tempfile.TemporaryDirectory() as td:
        root = Path(td).resolve() / 'repository'
        listed = root / 'crates/m/src/lib.rs'
        own = {'clean-reference': 'crates/r/src/lib.rs', 'ck0-stock': 'crates/c/src/lib.rs'}
        write_tree(root, {'crates/m/src/lib.rs': 'pub fn f() {}\n', **{p: f'// {m}\n' for m, p in own.items()}})
        for name in k.CONTROL_NAMES:  # the committed controls, byte for byte
            control = k.nano.CONTROLS[name]['path']
            (root / control).parent.mkdir(parents=True, exist_ok=True)
            (root / control).write_bytes((k.ROOT / control).read_bytes())
        git_commit(root)
        # K2: each member's set holds a file the other's does not, and the stub answers by the entry it is given.
        reads = {m: {'crates/m/src/lib.rs': k.digest(listed), own[m]: k.digest(root / own[m])} for m in k.RUST_MEMBERS}
        heads = []
        (Path(td) / 'subject.ndjson').write_text('{}\n')

        def replay_run(label, during):
            out = Path(td) / label
            argv = ['kstar', '--members', str(Path(td) / 'members.json'), '--subject', str(Path(td) / 'subject.ndjson'),
                    '--out', str(out)]

            def replay(*args):
                during()
                return dict(accepted=True, members={m: {} for m in k.MEMBERS})
            printed = io.StringIO()
            with patch.object(k, 'ROOT', root), patch.object(sys, 'argv', argv), \
                    patch.object(k, 'source_inputs', return_value={}), \
                    patch.object(k, 'prepare', return_value={m: dict(binary=dict(path=m)) for m in k.MEMBERS}), \
                    patch.object(k, 'build_reads',
                                 side_effect=lambda n, e, head: heads.append(head) or reads[e['binary']['path']]), \
                    patch.object(k.l4l, 'main', return_value=0), \
                    patch.object(k.subj, 'restrict', return_value=(b'{}\n', [], {})), \
                    patch.object(k, 'replay', side_effect=replay), patch.object(k, 'control_refused', return_value=True), \
                    contextlib.redirect_stdout(printed):
                code = attempt(k.main)[0]
            return code, printed.getvalue(), json.loads((out / 'replay.json').read_text())
        code, out, record = replay_run('steady', lambda: None)
        check("main: the replay records each Rust member's build read set, from that member's own entry",
              code == 0 and record['build_reads'] == reads and record['success'] is True)
        check("main: each set is checked against the blobs at the record's HEAD",
              len(heads) == 2 and set(heads) == {record['source_commit']} and len(record['source_commit']) == 40)
        code, out, record = replay_run('moved', lambda: listed.write_text('pub fn moved() {}\n'))
        check('main: a build read file changed during the replay makes the run not knowable',
              code == 1 and 'build reads changed during replay' in out and record['success'] is False)


def build_read_controls(check):
    """The build read set: required, compared byte for byte, parsed exactly, measured, fail-closed."""
    with tempfile.TemporaryDirectory() as td:
        root = Path(td).resolve() / 'repository'
        # K2: each member's set holds a file the other's does not, so checking one member alone fails.
        own = {'clean-reference': 'crates/r/src/lib.rs', 'ck0-stock': 'crates/c/src/lib.rs'}
        write_tree(root, {'crates/m/src/lib.rs': 'pub fn f() {}\n', **{p: f'// {m}\n' for m, p in own.items()}})
        record, path = green_record(td), Path(td) / 'record.json'
        reads = {m: {p: k.digest(root / p) for p in ('crates/m/src/lib.rs', own[m])} for m in k.RUST_MEMBERS}
        with patch.object(k, 'ROOT', root), patch.object(k, 'source_inputs', return_value={}):
            path.write_text(json.dumps(dict(record, build_reads=reads)))
            code, out = verdict(path)
            check('build reads: a record fresh in every conjunct is accepted', code == 0 and 'accepted' in out)
            path.write_text(json.dumps(record))
            code, out = verdict(path)
            check('build reads: a record without build_reads is never fresh',
                  code == 1 and 'not knowable here: record carries no build read set' in out)
            for m in k.RUST_MEMBERS:
                path.write_text(json.dumps(dict(record, build_reads={n: v for n, v in reads.items() if n != m})))
                code, out = verdict(path)
                check(f'build reads: a record without the reads of {m} is never fresh',
                      code == 1 and f'no build read set for {m}' in out)
            path.write_text(json.dumps(dict(record, build_reads=reads)))
            for m, rel in own.items():
                text = (root / rel).read_text()
                (root / rel).write_text(text + '// moved\n')
                code, out = verdict(path)
                check(f'build reads: a changed file only {m} reads makes the record stale',
                      code == 1 and f'stale build reads: {rel}' in out)
                (root / rel).write_text(text)
            # D3: a set of any other shape says not knowable, never a traceback.
            one, sha = reads['ck0-stock'], reads['ck0-stock']['crates/m/src/lib.rs']
            other = 'names a member other than'
            for label, shape, reason in [
                    ('a list', [reads], 'carries no build read set'),
                    ('an extra member holding a number', dict(reads, extra=5), other),
                    ('an extra member holding a set', dict(reads, extra=one), other),
                    ('a member set that is a number', dict(reads, **{'ck0-stock': 5}), 'no build read set for ck0-stock'),
                    ('a digest that is a number', dict(reads, **{'ck0-stock': {'crates/m/src/lib.rs': 5}}), 'holds no sha256'),
                    ('a digest that is not sha256', dict(reads, **{'ck0-stock': {'crates/m/src/lib.rs': 'zz'}}), 'holds no sha256'),
                    ('a path that is not normalized', dict(reads, **{'ck0-stock': {'crates/m/./src/lib.rs': sha}}),
                     'not a normalized path'),
                    ('a path above the repository', dict(reads, **{'ck0-stock': {'../x': sha}}), 'not a normalized path')]:
                path.write_text(json.dumps(dict(record, build_reads=shape)))
                got, crash = attempt(verdict, path)
                code, out = got or (None, '')
                check('build reads: a malformed set is not knowable: ' + label,
                      not crash and code == 1 and out.startswith('KSTAR_RECHECK=not knowable here: ') and reason in out)
            path.write_text('[]')
            got, crash = attempt(verdict, path)
            code, out = got or (None, '')
            check('build reads: a record that is no JSON object is not knowable',
                  not crash and code == 1 and out.startswith('KSTAR_RECHECK=not knowable here: '))
            path.write_text(json.dumps(dict(record, build_reads=reads)))
            (root / 'crates/m/src/lib.rs').write_text('pub fn g() {}\n')
            code, out = verdict(path)
            check('build reads: a changed build_reads file makes the record stale',
                  code == 1 and 'stale build reads: crates/m/src/lib.rs' in out)
            (root / 'crates/m/src/lib.rs').unlink()
            code, out = verdict(path)
            check('build reads: a deleted build_reads file makes the record stale',
                  code == 1 and 'stale build reads: crates/m/src/lib.rs' in out)
    text, want = DEP_INFO
    check('build reads: the dep-info parser reads escaped paths',
          attempt(k.parse_dep_info, text, Path('/w/t d/debug/k'))[0] == want)
    for label, text, reason in DEP_INFO_REFUSALS:
        refused = attempt(k.parse_dep_info, text, Path('/w/t d/debug/k'))[1]
        check('build reads: the dep-info parser refuses ' + label, refused.startswith('ValueError') and reason in refused)
    refusals_of_build(check)
    builder_controls(check)
    main_controls(check)
    if os.environ.get('KSTAR_STOCK_CARGO'):
        stock_cargo_build(check, os.environ['KSTAR_STOCK_CARGO'])
        stock_race(check, os.environ['KSTAR_STOCK_CARGO'])
        stock_dirty_manifest(check, os.environ['KSTAR_STOCK_CARGO'])


def run(controls, label, limits):
    """Run `controls(check)`; 0 only when every check held, 1 at the first that did not."""
    checks = []

    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        checks.append(name)
        print('ok:', name)
    try:
        controls(check)
    except AssertionError as e:
        print(f'{label}=FAILED at {e}; checks={len(checks)}; {limits}')
        return 1
    print(f'{label}=ok checks={len(checks)}; {limits}')
    return 0


def selftest():
    """Every orchestration and input control, each in the run's count."""
    return run(controls, 'KSTAR_SELFTEST', 'no quorum vote')


def controls(check):
    for member, obj in [
        ('lean', dict(verdict='accepted', declarations=1, axioms=['propext'])),
        ('clean-reference', dict(accepted=True, admitted=1, declarations=1,
                                axioms=['propext'], refusals=[], unpermitted_axioms=[], reader_error=None)),
        ('ck0-stock', dict(kind='coverage', accepted=1, total=1, refused={}, axioms=[[{'str':'propext'}]])),
    ]:
        raw = dict(exit_code=0, stdout=json.dumps(obj), stderr='')
        good = k.evaluate(member, raw, 1, ['propext'])
        check(member + ' honest report', good['accepted'])
        for label, bad, count, axioms in [
            ('missing report', dict(raw, stdout=''), 1, ['propext']),
            ('count drift', raw, 2, ['propext']),
            ('axiom drift', raw, 1, []),
            ('timeout', dict(raw, exit_code=None), 1, ['propext']),
            ('crash', dict(raw, exit_code=-6), 1, ['propext']),
        ]:
            check(member + ' refuses ' + label, not k.evaluate(member, bad, count, axioms)['accepted'])
        mutated = copy.deepcopy(obj)
        mutated['axioms'] = ['evil'] if member != 'ck0-stock' else [[{'str':'evil'}]]
        check(member + ' Ax0 boundary', not k.evaluate(member, dict(raw, stdout=json.dumps(mutated)), 1, ['evil'])['accepted'])
    restriction_controls(check)
    rows = {m: dict(accepted=True, axioms=['propext']) for m in k.MEMBERS}
    check('all four required', k.agreed(rows))
    for member in k.MEMBERS:
        missing = dict(rows); missing.pop(member)
        check('missing ' + member, not k.agreed(missing))
        bad = copy.deepcopy(rows); bad[member]['axioms'] = []
        check('axiom mismatch ' + member, not k.agreed(bad))
        bad[member]['accepted'] = False
        check('disagreement ' + member, not k.agreed(bad))
        for name in k.CONTROL_NAMES:
            check(member + ' control acceptance ' + name, not k.control_refused(member, name, dict(accepted=True, exit_code=0)))
            check(member + ' control timeout ' + name, not k.control_refused(member, name, dict(accepted=False, exit_code=None)))
            check(member + ' incidental failure ' + name, not k.control_refused(member, name, dict(accepted=False, exit_code=1, stderr='unrelated IO failure')))
    for name, failure in k.LEAN4LEAN_CONTROLS.items():
        row = dict(accepted=False, exit_code=0 if failure['kind'] == 'runner' else 1, failure=failure)
        check('lean4lean pinned refusal ' + name, k.control_refused('lean4lean', name, row))
        panic = dict(accepted=False, exit_code=134, verdict='panic',
                     failure=dict(kind='panic', location='x', reason=failure['reason']))
        check('lean4lean panic is no refusal ' + name, not k.control_refused('lean4lean', name, panic))
        other = dict(row, failure=dict(failure, reason='unrelated'))
        check('lean4lean other refusal ' + name, not k.control_refused('lean4lean', name, other))
    # Every record below carries a current build read set, so each check reaches its own conjunct.
    reads = {m: {'rust-toolchain.toml': k.digest(k.ROOT / 'rust-toolchain.toml')} for m in k.RUST_MEMBERS}
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / 'record.json'
        check('missing record', k.check_record(p) == 1)
        p.write_text(json.dumps(dict(success=False, source_inputs={}, build_reads=reads)))
        with patch.object(k, 'source_inputs', return_value={}):
            check('red record never green', k.check_record(p) == 1)
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / 'new-run'
        argv = ['kstar', '--members', str(Path(td) / 'absent.json'),
                '--subject', str(Path(td) / 'absent.ndjson'), '--out', str(out)]
        with patch.object(k, 'source_inputs', return_value={}), patch.object(sys, 'argv', argv):
            check('missing build receipt cannot vote', k.main() == 1)
        check('unavailable run records failure', not json.loads((out / 'replay.json').read_text())['success'])
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / 'record.json'
        candidate = dict(source_inputs={}, success=True, qualified_lean4lean=True, build_reads=reads,
                         subjects=[dict(sha256='seed', source_sha256='seed', members=rows)], controls={})
        p.write_text(json.dumps(candidate))
        with patch.object(k, 'source_inputs', return_value={}):
            check('seed cannot replace the pinned full subjects', k.check_record(p) == 1)
            candidate['subjects'] = [dict(sha256=h, source_sha256='seed', members=rows) for h in k.SUBJECT_PINS]
            candidate['identities'] = {m: {} for m in k.MEMBERS}
            p.write_text(json.dumps(candidate))
            check('an unpinned source cannot green the standing record', k.check_record(p) == 1)
            candidate['subjects'] = [dict(sha256=h, source_sha256=s, members=rows)
                                     for h, s in zip(sorted(k.SUBJECT_PINS), sorted(k.SOURCE_PINS))]
            candidate['identities'] = {}
            p.write_text(json.dumps(candidate))
            check('missing member identity cannot green the standing record', k.check_record(p) == 1)
    build_read_controls(check)
    input_controls(check)
    l4l_checks = []
    lean4lean_selftest.selftest(l4l_checks)
    for name in l4l_checks:
        check(name, True)


if __name__ == '__main__':
    sys.exit(selftest())
