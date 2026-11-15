# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The module walk's own arms (scripts/rust_modules.py): module paths, include!
splices and the `fn` items libtest can name.

Both gates that import the walk run these on every invocation, inside their
own self-tests (milliseconds; synthetic crates in a temporary directory, no
repo file read). Each arm is a crate rooted at agg.rs with EXACT expectations:
the CERTAIN and POSSIBLE (file, module path) sets, and the libtest paths of the
`#[test]` fns CERTAIN finds. Each was checked on 2026-11-01 against rustc on
the same tree: CERTAIN's files within `trustc --edition 2021 --test
--emit=dep-info`, its test paths within the built binary's `--list
--format=terse` (equal to it unless a macro writes the test), POSSIBLE's files
covering the dep-info. Where rustc refuses the crate (E0761, E0753, E0754) the
arm says so. MAYBE_ARMS pin MAYBE the same way: its files and test paths
cover rustc's with the undecided cfgs set (`--cfg 'feature="x"'`), and none
that a cfg decides false; each macro group that holds a `#[test]` is named.

Notation: a file is `rel` (body: one `#[test] fn t() {}`) or `rel=body`; a
set is `file=path ...`, `-` for a path libtest cannot name, `=` for "the
CERTAIN set". The arms decide platform cfgs from FACTS, the host they were
checked on (aarch64-apple-darwin), never from the host they run on.
"""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

T = "#[test] fn t() {}\n"
FACTS = {"unix": True, "windows": False, "target_os": frozenset({"macos"}), "target_family": frozenset({"unix"})}
# `cfg(pred)` -> the evaluator's answer under FACTS and the harness (None: undecided, so CERTAIN is unsure).
CFG_ARMS = [("(all())", True), ("(any())", False), ("(not(any()))", True), ("(test)", True), ("(not(test))", False),
            ('(feature = "x")', None), ('(any(test, feature = "x"))', True), ('(all(test, feature = "x"))', None),
            ('(all(windows, feature = "x"))', False), ('(target_os = "macos")', True), ('(target_os = "linux")', False),
            ("(debug_assertions)", None), ("(not(unix, windows))", None), ('(feature = "a\\"b")', None),
            ("(unix)(windows)", None)]

ARMS = [  # (label, files, CERTAIN, POSSIBLE, CERTAIN's test paths)
    ("underscores do not count toward Unicode escape hex width",
     ("agg.rs=const C: char = '\\u{0_0_0_0_0_0}';\nmod real;\n", "real.rs"),
     "agg.rs= real.rs=real", "=", "real::t"),
    ("seven Unicode hex digits remain unreadable (compiler refuses)",
     ("agg.rs=const C: char = '\\u{0000000}';\nmod real;\n", "real.rs"),
     "agg.rs=", "agg.rs= real.rs=-", ""),
    ("the root is \"\"; a by-name file, its by-name child and a mod.rs child append their names",
     ("agg.rs=mod h;\nmod d;\n#[test] fn top() {}\n", "h.rs=mod x;\n", "h/x.rs", "d/mod.rs=mod y;\n", "d/y.rs"),
     "agg.rs= h.rs=h h/x.rs=h::x d/mod.rs=d d/y.rs=d::y", "=", "top h::x::t d::y::t"),
    ("a #[path] file takes its DECLARED name; an inline module appends its own",
     ('agg.rs=#[path = "impl/p.rs"]\nmod placed;\nmod outer {\n    mod inner;\n    #[test] fn o() {}\n}\n',
      "impl/p.rs", "outer/inner.rs"),
     "agg.rs= impl/p.rs=placed outer/inner.rs=outer::inner", "=", "placed::t outer::inner::t outer::o"),
    ("a raw keyword keeps r#, a raw non-keyword does not (as --list prints them)",
     ("agg.rs=mod r#type { #[test] fn r#match() {} }\nmod r#loop;\nmod r#foo { #[test] fn r#bar() {} }\n", "loop.rs"),
     "agg.rs= loop.rs=r#loop", "=", "r#type::r#match r#loop::t foo::bar"),
    ("comments between a file module's tokens: rustc loads both", ("agg.rs=mod /* c */ x;\nmod y // d\n;\n", "x.rs",
     "y.rs"), "agg.rs= x.rs=x y.rs=y", "=", "x::t y::t"),
    ("one file at two module paths", ('agg.rs=#[path = "h.rs"]\nmod a;\n#[path = "h.rs"]\nmod b;\n', "h.rs"),
     "agg.rs= h.rs=a h.rs=b", "=", "a::t b::t"),
    ("a `mod` in a macro body never invoked: CERTAIN does not follow it, POSSIBLE widens",
     ("agg.rs=macro_rules! m { () => { mod x; } }\n#[test] fn top() {}\n", "x.rs"),
     "agg.rs=", "agg.rs= x.rs=-", "top"),
    ("a macro's `mod` lands where it is invoked (rustc: i/x.rs as i::x): CERTAIN takes none, POSSIBLE every dir",
     ("agg.rs=macro_rules! m { () => { mod x; } }\nmod i { m!(); }\n#[test] fn top() {}\n", "x.rs", "i/x.rs"),
     "agg.rs=", "agg.rs= x.rs=- i/x.rs=-", "top"),
    ("a cfg_attr(all(), path): rustc loads y.rs as x; CERTAIN takes neither, POSSIBLE both",
     ('agg.rs=#[cfg_attr(all(), path = "y.rs")]\nmod x;\n', "x.rs", "y.rs"), "agg.rs=", "agg.rs= x.rs=x y.rs=x", ""),
    ("a #[path] mod in a fn body is compiled, and libtest can name nothing in it",
     ('agg.rs=fn f() {\n    #[path = "x.rs"]\n    mod x;\n}\n#[test] fn top() {}\n', "x.rs=mod y;\n#[test] fn xt() {}\n",
      "y.rs"), "agg.rs= x.rs=- y.rs=-", "=", "top"),
    ("E0761: x.rs beside x/mod.rs (rustc refuses the crate)", ("agg.rs=mod x;\n", "x.rs", "x/mod.rs"),
     "agg.rs=", "agg.rs= x.rs=x x/mod.rs=x", ""),
    ("inline modules and tests in blocks, impls and macros are not nameable",
     ("agg.rs=fn f() { mod b { #[test] fn t() {} } #[test] fn u() {} }\nconst _: () = { mod c { #[test] fn t() {} } };\n"
      "macro_rules! m { () => { #[test] fn mt() {} } }\nstruct S;\nimpl S { fn m() {} }\n#[test] fn top() {}\n",),
     "agg.rs=", "=", "top"),
    ("a #[cfg(any())] test or module is gone, a #[cfg(all())] one stays",
     ("agg.rs=#[cfg(any())]\nmod a { #[test] fn t() {} }\n#[cfg(any())]\n#[test] fn gone() {}\n"
      "#[cfg(all())]\nmod b { #[test] fn t() {} }\n#[cfg(test)]\n#[test] fn kept() {}\n",), "agg.rs=", "=", "b::t kept"),
    ("include! at the root splices at \"\"; the mods it declares resolve beside it",
     ('agg.rs=include!("inc.rs");\n', "inc.rs=#[test] fn inc_t() {}\nmod y;\n", "y.rs", "agg/y.rs"),
     "agg.rs= inc.rs= y.rs=y", "=", "inc_t y::t"),
    ("include! in an inline module: the path in force is h, the file is beside the invoker",
     ('agg.rs=mod h {\n    include!("inc.rs");\n}\n', "inc.rs=#[test] fn inc_t() {}\nmod y;\n", "y.rs", "h/y.rs",
      "h/inc.rs"), "agg.rs= inc.rs=h y.rs=h::y", "=", "h::inc_t h::y::t"),
    ("include! in a by-name h.rs resolves beside h.rs, not in h/; its mods beside the included file",
     ("agg.rs=mod h;\n", 'h.rs=include!("sub/inc.rs");\n', "sub/inc.rs=#[test] fn inc_t() {}\nmod y;\n", "sub/y.rs",
      "h/y.rs", "y.rs", "h/sub/inc.rs"), "agg.rs= h.rs=h sub/inc.rs=h sub/y.rs=h::y", "=", "h::inc_t h::y::t"),
    ("an included file's inline module and #[path] resolve beside it; nested include! beside the includer",
     ('agg.rs=include!("d/inc.rs");\n', 'd/inc.rs=mod z {\n    mod w;\n    #[test] fn zt() {}\n}\n#[path = "p.rs"]\n'
      'mod q;\ninclude!("e/two.rs");\n', "d/z/w.rs", "d/p.rs", "z/w.rs", "p.rs", "d/e/two.rs=#[test] fn two() {}\n"),
     "agg.rs= d/inc.rs= d/z/w.rs=z::w d/p.rs=q d/e/two.rs=", "=", "z::w::t z::zt q::t two"),
    ("brackets, braces, a trailing comma and ::std::include! all splice",
     ('agg.rs=include!["a.rs"];\ninclude!{"b.rs"}\ninclude!("c.rs",);\n::std::include!("d.rs");\n',
      "a.rs=#[test] fn ta() {}\n", "b.rs=#[test] fn tb() {}\n", "c.rs=#[test] fn tc() {}\n", "d.rs=#[test] fn td() {}\n"),
     "agg.rs= a.rs= b.rs= c.rs= d.rs=", "=", "ta tb tc td"),
    ("include! in an inline module inside a fn: compiled, nothing nameable; its by-name mod is owned",
     ('agg.rs=fn f() {\n    mod z {\n        include!("inc.rs");\n    }\n}\n#[test] fn top() {}\n',
      "inc.rs=#[test] fn it() {}\nmod y;\n", "y.rs"), "agg.rs= inc.rs=- y.rs=-", "=", "top"),
    ("CERTAIN does not follow an include! that is cfg'd, in a macro body, not one literal, or in a #![cfg]'d file",
     ('agg.rs=#[cfg(feature = "x")]\ninclude!("a.rs");\nmacro_rules! m { () => { include!("b.rs"); } }\n'
      'mod h;\n', 'h.rs=#![cfg(any())]\ninclude!("c.rs");\n', "a.rs", "b.rs", "c.rs"),
     "agg.rs= h.rs=h", "agg.rs= h.rs=h a.rs= b.rs=- c.rs=h", ""),
    ("platform cfgs are decided by the host's facts, `feature` never, `test` by the harness",
     ('agg.rs=mod a;\n#[cfg(windows)]\nmod w;\n#[cfg(any(test, feature = "nope"))]\nmod t;\n#[cfg(not(test))]\nmod n;\n'
      '#[cfg(all(unix, target_os = "macos"))]\nmod m;\n#[cfg(feature = "nope")]\nmod f;\n',
      "a.rs=#![cfg(unix)]\n#[test] fn ta() {}\n", "w.rs", "t.rs", "n.rs", "m.rs", "f.rs"),
     "agg.rs= a.rs=a t.rs=t m.rs=m", "agg.rs= a.rs=a w.rs=w t.rs=t n.rs=n m.rs=m f.rs=f", "a::ta t::t m::t"),
    ("an included file opening with an inner attribute or doc comment (rustc refuses it) is not followed",
     ('agg.rs=include!("a.rs");\ninclude!("b.rs");\n', "a.rs=//! doc\n#[test] fn ta() {}\n",
      "b.rs=#![allow(unused)]\n#[test] fn tb() {}\n"), "agg.rs=", "agg.rs= a.rs= b.rs=", ""),
    # 2026-11-01 review. rustc: dep-info agg.rs k.rs; --list top.
    ("the item that owns a block decides it: a cfg'd fn, impl, const or statement block, cfg_attr(.., cfg), "
     "a body's #![cfg], cfg(not(test))",
     ('agg.rs=#[cfg(feature = "slow")]\nfn a() {\n    #[path = "a.rs"]\n    mod a;\n}\n#[cfg(feature = "slow")]\n'
      'fn b() {\n    mod z {\n        include!("b.rs");\n    }\n}\nstruct S;\n#[cfg(any())]\nimpl S {\n    fn f() {\n'
      '        #[path = "c.rs"]\n        mod c;\n    }\n}\n#[cfg(any())]\nconst _: () = {\n    mod z {\n'
      '        include!("d.rs");\n    }\n};\nfn g() {\n    #[cfg(any())]\n    {\n        #[path = "e.rs"]\n'
      '        mod e;\n    }\n}\n#[cfg_attr(all(), cfg(any()))]\nfn h() {\n    #[path = "f.rs"]\n    mod f;\n}\n'
      'fn i() {\n    #![cfg(any())]\n    #[path = "g.rs"]\n    mod g;\n}\n#[cfg(not(test))]\nfn j() {\n'
      '    #[path = "h.rs"]\n    mod h;\n}\n#[cfg(all())]\nfn k() {\n    #[path = "k.rs"]\n    mod k;\n}\n'
      "#[test] fn top() {}\n", "a.rs", "b.rs", "c.rs", "d.rs", "e.rs", "f.rs", "g.rs", "h.rs", "k.rs"),
     "agg.rs= k.rs=-", "agg.rs= a.rs=- b.rs=- c.rs=- d.rs=- e.rs=- f.rs=- g.rs=- h.rs=- k.rs=-", "top"),
    ("an include! in a macro body lands where the macro is invoked (rustc: sub/gen.rs as sub): POSSIBLE widens",
     ("agg.rs=#[macro_use]\nmod macros;\nmod sub;\n#[test] fn top() {}\n",
      'macros.rs=macro_rules! inc { () => { include!("gen.rs"); } }\n', "sub/mod.rs=inc!();\n",
      "sub/gen.rs=#[test] fn generated() {}\n"),
     "agg.rs= macros.rs=macros sub/mod.rs=sub", "agg.rs= macros.rs=macros sub/mod.rs=sub sub/gen.rs=-", "top"),
    ("a #![cfg] opening a test fn's body strips the test (rustc --list: kept plain top)",
     ('agg.rs=#[test]\nfn gone() -> Result<(), [u8; 1]> {\n    #![cfg(feature = "x")]\n    Ok(())\n}\n#[test]\n'
      "fn kept() {\n    #![cfg(test)]\n}\n#[test]\nfn plain() where u8: Copy {\n    #![allow(unused)]\n}\n#[test]\n"
      "fn off() {\n    #![cfg(any())]\n}\n#[test] fn top() {}\n",), "agg.rs=", "=", "kept plain top"),
    ("E0754: a by-name `mod café;` (rustc refuses the crate)", ("agg.rs=mod café;\n#[test] fn top() {}\n", "café.rs"),
     "agg.rs=", "agg.rs= café.rs=café", "top"),
    ("... a #[path] one loads (rustc --list: café::t top)",
     ('agg.rs=#[path = "café.rs"]\nmod café;\n#[test] fn top() {}\n', "café.rs"), "agg.rs= café.rs=café", "=",
     "café::t top"),
    ("weak keywords and gen print bare, strict and 2018 ones keep r# (rustc --list, as given)",
     ("agg.rs=mod r#union {\n    #[test] fn r#gen() {}\n    #[test] fn r#match() {}\n}\nmod r#dyn {\n"
      "    #[test] fn r#macro_rules() {}\n}\nmod r#safe;\n", "safe.rs"), "agg.rs= safe.rs=safe", "=",
     "union::gen union::r#match r#dyn::macro_rules safe::t"),
]

# (label, files, MAYBE set, the files it could not place, MAYBE's test paths, the macro groups holding a
# `#[test]` (`rm._macro`'s answer: the name a macro_rules! defines, "!name" an invocation), the macros called)
MAYBE_ARMS = [
    ("a #![cfg(feature)] root's tests are MAYBE's, a #[cfg(any())] or #[cfg(windows)] item is not "
     "(rustc: none; with --cfg feature=x/y: m::t t)",
     ('agg.rs=#![cfg(feature = "x")]\n#[test] fn t() {}\n#[cfg(any())]\n#[test] fn gone() {}\n'
      '#[cfg(feature = "y")]\nmod m;\n#[cfg(windows)]\nmod w;\n', "m.rs", "w.rs"),
     "agg.rs= m.rs=m", "", "t m::t", "", ""),
    ("a macro's tokens or an invoked macro_rules! body may write a test, an uninvoked one may not "
     "(rustc --list: made passed)",
     ("agg.rs=macro_rules! gen { ($n:ident) => { #[test] fn $n() {} }; }\ngen!(made);\n"
      "macro_rules! parked { () => { #[test] fn p() {} }; }\nmacro_rules! pass { ($($t:tt)*) => { $($t)* }; }\n"
      "pass! { #[test] fn passed() {} }\nfn f() { #[test] fn inner() {} }\n",),
     "agg.rs=", "", "", "!pass gen parked", "gen pass"),
    ("a one-letter macro_rules! name is a macro group; a #![..] is none (rustc --list: t)",
     ("agg.rs=#![allow(unused)]\nmacro_rules! m { () => { #[test] fn t() {} }; }\nm!();\n"
      "macro_rules! q { () => { #[test] fn u() {} }; }\n",), "agg.rs=", "", "", "m q", "m"),
    ("an uninvoked macro_rules! body's include! places nothing (rustc dep-info: agg.rs)",
     ('agg.rs=macro_rules! m { () => { include!("x.rs"); } }\n#[test] fn top() {}\n', "x.rs"),
     "agg.rs=", "", "top", "", "include"),
    ("... once invoked, MAYBE cannot place it (rustc dep-info: agg.rs x.rs)",
     ('agg.rs=macro_rules! m { () => { include!("x.rs"); } }\nm!();\n#[test] fn top() {}\n', "x.rs"),
     "agg.rs= x.rs=-", "agg.rs", "top", "", "include m"),
]
# The facts a run falls back to when no compiler answers `--print cfg` (rust_cfg.python_facts).
PY_FACTS = [("darwin", True, "macos"), ("linux", True, None), ("win32", False, "windows"), ("cygwin", None, None)]


def _pairs(spec: str) -> set[tuple[str, str | None]]:
    out = set()
    for item in spec.split():
        rel, _, path = item.partition("=")
        out.add((rel, None if path == "-" else path))
    return out


def _tree(base: Path, files: tuple[str, ...]) -> Path:
    for f in files:
        rel, eq, body = f.partition("=")
        (base / rel).parent.mkdir(parents=True, exist_ok=True)
        (base / rel).write_text(body if eq else T)
    return base.resolve()


def _fail(label: str, what: str, got, want) -> None:
    if got != want:
        raise SystemExit(f"rust_modules SELFTEST FAILED: {label} -> {what} {sorted(got, key=str)}, "
                         f"expected {sorted(want, key=str)}")


def run(rm) -> int:
    """Each cfg predicate through `rm.cfg`, the fallback facts, each arm through `rm.walk` (CERTAIN
    and POSSIBLE) and `rm.fn_items`, each MAYBE arm also through `rm.macro_items`: the arm count,
    or SystemExit on the first wrong answer."""
    for pred, want in CFG_ARMS:
        if rm.cfg(pred, dict(FACTS, test=True)) is not want:
            raise SystemExit(f"rust_modules SELFTEST FAILED: cfg{pred} -> {rm.cfg(pred, dict(FACTS, test=True))}, "
                             f"expected {want}")
    for platform, unix, os_name in PY_FACTS:
        facts = rm.rust_cfg.python_facts(platform)
        got = (facts.get("unix"), next(iter(facts.get("target_os", ())), None), rm.cfg("(unix)", facts))
        _fail(f"python_facts({platform!r})", "unix, target_os, cfg(unix)", {got}, {(unix, os_name, unix)})
    # No compiler answering `--print cfg` falls back to those, and says so (2026-11-01 review: it fell
    # back to NO facts, so `#![cfg(unix)]` went undecided and an honest selector read as VACUOUS).
    gone = ("rust-modules-selftest-no-such-compiler",)
    got = (rm.rust_cfg.host_facts(gone) == rm.rust_cfg.python_facts(sys.platform), rm.rust_cfg.host_source(gone))
    _fail("host_facts with no compiler", "(equals python_facts, source)", {got},
          {(True, f"python sys.platform={sys.platform}")})
    for label, files, want_m, want_u, want_t, want_w, want_calls in MAYBE_ARMS:
        with tempfile.TemporaryDirectory() as tmp:
            real, unplaced = _tree(Path(tmp), files), set()
            walked = rm.walk(Path(tmp) / "agg.rs", rm.Reach.MAYBE, unplaced, facts=FACTS)
            _fail(label, "MAYBE", {(str(f.relative_to(real)), p) for f, p in walked}, _pairs(want_m))
            _fail(label, "unplaced", {str(f.relative_to(real)) for f in unplaced}, set(want_u.split()))
            tests = {p for f, m in walked for p, a in rm.fn_items(f, m, rm.Reach.MAYBE, facts=FACTS)
                     if any(x.strip() == "test" for x in a)}
            _fail(label, "MAYBE test paths", tests, set(want_t.split()))
            items = [rm.macro_items(f, m, facts=FACTS) for f, m in walked]
            _fail(label, "macro groups holding a #[test]", {k for macs, _ in items for k, a in macs
                                                            if any(x.strip() == "test" for x in a)}, set(want_w.split()))
            _fail(label, "macros called", {c for _, calls in items for c in calls}, set(want_calls.split()))
    for label, files, want_c, want_p, want_t in ARMS:
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            real = _tree(base, files)
            for mode, want in ((rm.Reach.CERTAIN, want_c), (rm.Reach.POSSIBLE, want_c if want_p == "=" else want_p)):
                walked = rm.walk(base / "agg.rs", mode, facts=FACTS)
                got = {(str(f.relative_to(real)), p) for f, p in walked}
                if got != _pairs(want):
                    raise SystemExit(f"rust_modules SELFTEST FAILED: {label} -> {mode.name} {sorted(got, key=str)}, "
                                     f"expected {sorted(_pairs(want), key=str)}")
                if mode is rm.Reach.CERTAIN:
                    tests = {p for f, m in walked for p, attrs in rm.fn_items(f, m, facts=FACTS)
                             if any(a.strip() == "test" for a in attrs)}
            if tests != set(want_t.split()):
                raise SystemExit(f"rust_modules SELFTEST FAILED: {label} -> test paths {sorted(tests)}, "
                                 f"expected {sorted(want_t.split())}")
    return len(ARMS) + len(CFG_ARMS) + len(MAYBE_ARMS) + len(PY_FACTS) + 1
