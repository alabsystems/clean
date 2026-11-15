#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Refuse an integration-test file that nothing builds.

WHY THIS EXISTS
---------------
Cargo compiles one test binary per ``tests/*.rs``. `clean-verify` turns that
off (``autotests = false``) because the per-binary rule was paying for
``Specification::new()`` -- about fifteen minutes -- once per FILE rather than
once per process: of the 56 aggregated targets, 47 reach ``FULL_SPEC`` and 7
reach ``SUBSTITUTION_SPEC``, and together they cost at least 12.59 measured
hours of rebuilding two immutable objects (a floor -- six of the 56 carry no
recorded duration).  ``tests/spec_suite.rs`` aggregates them into ONE binary.

The price of that switch is a hazard this repo has a name for: **a test nobody
runs cannot fail.**  With auto-discovery off, a new ``tests/foo.rs`` is simply
never compiled, and it reads exactly like a passing test -- no error, no
warning, no row anywhere.  So the switch does not land without the gate that
refuses it.

WHAT IT CHECKS
--------------
For every workspace crate that sets ``autotests = false``: every top-level
``tests/*.rs`` must be REACHABLE -- declared as its own ``[[test]]`` target, or
reached from one by module items and item-level ``include!`` as rustc resolves
them, by the walk ``scripts/rust_modules.py`` (shared with
``check_cargo_test_selectors.py`` and ``verify_runner.py``), over code whose
comments and literals R9's reference lexer blanked: a ``mod`` inside a comment
or a string is not code.  Where rustc's answer depends on more than the walk
reads, the gate refuses rather than guesses (``Reach.CERTAIN``; a ``cfg`` is
decided only by ``test`` and the host target's platform cfgs, ``scripts/rust_cfg.py``,
and one on the item that owns a block -- a ``fn``, ``impl`` or ``const`` -- decides
every ``mod`` and ``include!`` in it).  It also refuses
a ``[[test]]`` whose ``path`` does not exist, which fails at build time with a
message about the wrong thing.  Exit 0, or 1 naming each orphan.  Every
invocation first runs the walk's own arms (``scripts/rust_modules_arms.py``) and
this gate's.
"""

from __future__ import annotations

import importlib.util
import re
import sys
import tomllib
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
# check_gate_registry.py R7 pins what `--pinned-inputs` prints: the module walk this gate imports, its
# arms, its cfg evaluator and the lexer it imports (this gate runs no other gate).
ANSWERS_PINNED_INPUTS = True
_RM = None


def _rust_modules():
    """scripts/rust_modules.py, the module walk this gate, check_cargo_test_selectors and
    verify_runner share: imported, never copied, so a fix to it lands once."""
    global _RM
    if _RM is None:
        src = Path(__file__).resolve().parent / "rust_modules.py"
        spec = importlib.util.spec_from_file_location("_clean_rust_modules", src)
        if not src.is_file() or spec is None or spec.loader is None:
            raise SystemExit(f"cannot load the module walk at {src}")
        _RM = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(_RM)
    return _RM


def crate_dirs(root: Path) -> list[Path]:
    members = tomllib.loads((root / "Cargo.toml").read_text()).get("workspace", {}).get("members", [])
    return [p for m in members for p in (sorted(root.glob(m)) if "*" in m else [root / m]) if (p / "Cargo.toml").is_file()]


def check(root: Path) -> tuple[list[str], int]:
    """Return (problems, files_checked) for the workspace rooted at `root`."""
    failures: list[str] = []
    checked = 0
    rm = _rust_modules()
    for crate in crate_dirs(root):
        manifest = tomllib.loads((crate / "Cargo.toml").read_text())
        pkg = manifest.get("package", {})
        declared = manifest.get("test", [])
        rel = crate.relative_to(root)
        for entry in declared:
            if entry.get("path") and not (crate / entry["path"]).is_file():
                failures.append(f"{rel}: [[test]] name = \"{entry.get('name')}\" points at "
                                f"{entry['path']}, which does not exist")
        tests_dir = crate / "tests"
        if pkg.get("autotests") is not False or not tests_dir.is_dir():
            continue
        reached, unreadable = set[Path](), set[Path]()
        for entry in declared:
            if entry.get("path"):
                reached |= rm.reachable_from(crate / entry["path"], rm.Reach.CERTAIN, unreadable,
                                          test_cfg=entry.get("harness") is not False)
        orphans = 0
        for f in sorted(tests_dir.glob("*.rs")):
            checked += 1
            if f.resolve() not in reached:
                orphans += 1
                failures.append(
                    f"{rel}/tests/{f.name}: NOTHING BUILDS THIS FILE. The crate sets "
                    f"autotests = false, so a tests/*.rs is compiled only when it is a "
                    f"[[test]] target or is reached from one by a `mod` declaration. "
                    f"Add it to the aggregating target's `mod` list, or declare it as "
                    f"its own [[test]] in {rel}/Cargo.toml."
                )
        for u in sorted(unreadable) if orphans else ():
            failures.append(
                f"{u.relative_to(root.resolve()) if root.resolve() in u.parents else u}: UNREAD -- this "
                f"walk cannot lex it as rustc does (an unterminated block comment, a char literal it does "
                f"not know, or brackets that do not balance), so the `mod` items in it were not followed."
            )
    return failures, checked


def _selftest() -> tuple[int, int]:
    """Prove the gate can say no -- and that it does not just say no to everything.

    Each arm is a synthetic workspace (milliseconds, run on EVERY invocation;
    the only repo files read are the walk, its arms, its cfg evaluator and the
    reference lexer; the one platform cfg an arm holds, the cfg_attr pair, is
    one CERTAIN follows on no host and POSSIBLE ignores, so the host's facts move
    no expectation) with an EXACT expectation:
    the files the gate refuses, and for a resolution arm the CERTAIN and
    POSSIBLE sets from tests/agg.rs ("*" = every .rs there), the gate refusing
    exactly the top-level files CERTAIN leaves out. Silent arms are here too.
    """
    import tempfile

    rm = _rust_modules()
    # tests/agg.rs = `agg`; an extra is `p` (a test), `p=body`, `p/` (a directory) or `p->target` (a
    # symlink) under tests/; a [[test]] name ending in `!` is `harness = false`.
    def tree(tmp: Path, agg: str | None, extra: tuple[str, ...], tests: tuple[str, ...] = ("agg",)) -> Path:
        (tmp / "Cargo.toml").write_text('[workspace]\nmembers = ["crates/c"]\n')
        crate = tmp / "crates" / "c"
        crate.mkdir(parents=True)
        manifest = '[package]\nname = "c"\nautotests = false\n'
        for t in tests:
            manifest += f'\n[[test]]\nname = "{t}"\npath = "tests/{t.rstrip("!")}.rs"\n'
            manifest += "harness = false\n" if t.endswith("!") else ""
        (crate / "Cargo.toml").write_text(manifest)
        for e in (() if agg is None else (f"agg.rs={agg}",)) + extra:
            rel, eq, body = e.partition("=")
            rel, _, link = (rel, "", "") if eq else rel.partition("->")
            f = crate / "tests" / rel.rstrip("/")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.symlink_to(link) if link else f.mkdir() if rel.endswith("/") else f.write_text(body if eq else T)
        return crate / "tests"

    def refused(problems: list[str]) -> set[str]:
        hits = [(re.search(r"tests/([^/:]+\.rs): NOTHING|points at (\S+), which", p), p) for p in problems]
        return {m.group(1) or m.group(2) if m else "UNREAD" if ": UNREAD" in p else p for m, p in hits}

    def fail(label: str, what: str, got: set[str], want: set[str]) -> None:
        if got != want:
            raise SystemExit(f"check_test_target_coverage SELFTEST FAILED: {label} -> {what} {sorted(got)}, expected "
                             f"{sorted(want)}. A gate that cannot say no, or says no to everything, proves nothing.")

    T, A = "#[test] fn t() {}\n", ("agg",)
    B = '// #[path = "orphan.rs"] mod commented_out;\n#[path = "sub/real.rs"]\nmod real;\n'
    R = ("sub/real.rs", "orphan.rs")
    manifest_arms = [  # (label, tests/agg.rs, other files, [[test]] targets, the exact set refused)
        ("an undeclared tests/*.rs under autotests = false (its #[path] only in a comment)", B, R, A, "orphan.rs"),
        ("the same file declared as its own [[test]]", B, R, ("agg", "orphan"), ""),
        ("the same file reached by a #[path] mod", B + '#[path = "orphan.rs"]\nmod orphan;\n', R, A, ""),
        ("a [[test]] path that does not exist", B, R, ("agg", "orphan", "gone"), "tests/gone.rs"),
        ("under `harness = false` there is no cfg(test)", "#[cfg(test)]\nmod x;\nfn main() {}\n", ("x.rs",), ("agg!",),
         "x.rs"),
        ("a symlinked root resolves beside the link, not beside its target", None,
         ("agg_impl.rs=mod x;\n", "suite/agg.rs->../agg_impl.rs", "suite/x.rs", "x.rs"), ("suite/agg",), "x.rs"),
    ]
    for label, agg, extra, tests, want in manifest_arms:
        with tempfile.TemporaryDirectory() as tmp:
            tree(Path(tmp), agg, extra, tests)
            fail(label, "refused", refused(check(Path(tmp))[0]), set(want.split()))
    resolution_arms = [  # (label, tests/agg.rs, other files, CERTAIN, POSSIBLE; "=" = the CERTAIN set)
        ("`mod x;` at the root is x.rs; `mod r#y;` is y.rs", "mod x;\nmod r#y;\n", ("x.rs", "y.rs"), "x.rs y.rs", "="),
        ("in a by-name h.rs it is h/x.rs", "mod h;\n", ("h.rs=mod x;\n", "h/x.rs", "x.rs"), "h.rs h/x.rs", "="),
        ("in a #[path] file it is a SIBLING (rustc: #[path] files are mod.rs files)", '#[path = "h.rs"]\nmod h;\n',
         ("h.rs=mod x;\n", "h/x.rs", "x.rs"), "h.rs x.rs", "="),
        ("a non-root mod.rs's children live beside it", "mod c;\n",
         ("c/mod.rs=mod s;\n", 'c/s.rs=#[path = "../x.rs"]\nmod x;\n', "x.rs"), "c/mod.rs c/s.rs x.rs", "="),
        ("an inline `mod i {}` puts i/ in force; a #[path] on it replaces it",
         'mod i {\n    mod x;\n}\n#[path = "."]\nmod h {\n    mod y;\n}\n', ("i/x.rs", "x.rs", "y.rs"), "i/x.rs y.rs", "="),
        ("a #[path] belongs to its own item", '#[path = "impl_x.rs"]\nmod x;\n', ("impl_x.rs", "x.rs"), "impl_x.rs", "="),
        ("a `mod` in a string, or in a comment after a char quote, is not code",
         "const S: &str = \"mod x;\";\nconst Q: char = '\"';\n// mod y;\nconst R: char = '\"';\n", ("x.rs", "y.rs"), "", ""),
        ("a macro's `mod` lands where it is invoked", "macro_rules! m { () => { mod x; } }\nmod i { m!(); }\n",
         ("i/x.rs", "x.rs"), "", "*"),
        ("`mod $n;`, and a #[path] in a macro never invoked", "macro_rules! m { ($n:ident) => { mod $n; } }\nm!(x);\n"
         'macro_rules! u { () => { #[path = "y.rs"] mod y; } }\n', ("x.rs", "y.rs"), "", "*"),
        ("a cfg_attr path: CERTAIN takes neither", '#[cfg_attr(all(), path = "x.rs")]\nmod y;\n', ("x.rs", "y.rs"),
         "", "x.rs y.rs"),
        ("a cfg_attr platform pair", '#[cfg_attr(unix, path = "u.rs")]\n#[cfg_attr(windows, path = "w.rs")]\nmod p;\n',
         ("u.rs", "w.rs", "p.rs"), "", "u.rs w.rs p.rs"),
        ("a cfg_attr path before a plain one", '#[cfg_attr(test, path = "a.rs")]\n#[path = "b.rs"]\nmod x;\n',
         ("a.rs", "b.rs", "x.rs"), "", "a.rs b.rs"),
        ("a raw-string path", '#[path = r"impl_x.rs"]\nmod x;\n', ("impl_x.rs", "x.rs"), "impl_x.rs", "="),
        ("an escaped path", '#[path = "impl\\x5fx.rs"]\nmod x;\n', ("impl_x.rs", "x.rs"), "", "*"),
        ("a cfg_attr path on an inline module", '#[cfg_attr(all(), path = "p")]\nmod i { mod x; }\n',
         ("p/x.rs", "i/x.rs"), "", "p/x.rs i/x.rs"),
        ("an inline module's #![path]", 'mod z {\n    #![path = "p"]\n    use std::fmt as _f;\n    mod x;\n}\n',
         ("z/x.rs", "p/x.rs"), "p/x.rs", "="),
        ("a loaded file's #![path]", "mod h;\n", ('h.rs=#![path = "sub/dummy.rs"]\nmod x;\n', "sub/x.rs", "h/x.rs"),
         "h.rs sub/x.rs", "="),
        ("E0761 (x.rs beside x/mod.rs)", "mod x;\n", ("x.rs", "x/mod.rs"), "", "x.rs x/mod.rs"),
        ("E0761 with a directory named x.rs", "mod x;\n", ("x.rs/", "x/mod.rs"), "", "x/mod.rs"),
        ("a nested block comment ends where rustc ends it", "/* a /* b */ { */\nmod x;\n", ("x.rs",), "x.rs", "="),
        ("... so a `mod` after one, with no bracket in sight, is not code",
         "mod y;\n/*\n * /* see the flake log */\n * mod x;\n */\n", ("x.rs", "y.rs"), "y.rs", "="),
        ("... nor do the brackets after one move a directory",
         "mod a {\n    /* x /* y */ } */\n    mod x;\n    /* x /* y */ { */\n}\n", ("a/x.rs", "x.rs"), "a/x.rs", "="),
        ("an unterminated nested comment (E0758) is UNREAD", "/* a /* b */\nmod x;\n", ("x.rs",), "", "*"),
        ("#[cfg(test)] holds under the harness; #[cfg(any())] strips its item",
         "#[cfg(test)]\nmod y;\n#[cfg(any())]\nmod x;\n", ("x.rs", "y.rs"), "y.rs", "x.rs y.rs"),
        ("a loaded file's #![cfg(feature = ..)] strips its children, not itself", '#[path = "c/h.rs"]\nmod h;\n',
         ('c/h.rs=#![cfg(feature = "slow")]\n#[path = "../x.rs"]\nmod x;\n', "x.rs"), "c/h.rs", "c/h.rs x.rs"),
        ("a brace inside an attribute keeps the item's #[path]", '#[path = "y.rs"]\n#[doc = stringify!({})]\nmod x;\n',
         ("x.rs", "y.rs"), "y.rs", "="),
        ("a `#[path]` inside a raw string is not an attribute",
         '#[doc = r#"#[path = "x.rs"]"#]\n#[cfg_attr(all(), path = "y.rs")]\nmod m;\n', ("x.rs", "y.rs"), "", "y.rs"),
        ("'\\u{7b}' is one char", "const A: [char; 2] = ['\\u{7b}','\"'];\nconst S: &str = \"]; mod x;\";\n",
         ("x.rs",), "", ""),
        ("'\\x7b' is one char", "const A: [char; 2] = ['\\x7b','\"'];\nmod y;\nconst S: &str = \"]\";\n",
         ("y.rs",), "y.rs", "="),
        ("`clean mod u;` loads u.clean, a leaf, never u.rs", "clean mod u;\n",
         ("u.clean=theorem t : True := True.intro\n", "u.rs"), "", "u.clean"),
        ("one file, two directory contexts", 'mod h;\n#[path = "h.rs"]\nmod h2;\n', ("h.rs=mod x;\n", "h/x.rs", "x.rs"),
         "h.rs h/x.rs x.rs", "="),
        ("include! beside the invoking file, and the mods of an included file beside it", 'mod h;\ninclude!("x.rs");\n',
         ('h.rs=include!("inc.rs");\n', "inc.rs=mod y;\n", "x.rs", "y.rs", "h/y.rs"), "h.rs inc.rs x.rs y.rs", "="),
        ("an include! in a macro body, under an undecided cfg, or in a block: CERTAIN follows none",
         'macro_rules! m { () => { include!("a.rs"); } }\n#[cfg(feature = "slow")]\ninclude!("b.rs");\n'
         'fn f() -> u32 { include!("c.rs") }\n', ("a.rs", "b.rs", "c.rs=1\n"), "", "a.rs b.rs c.rs"),
        ("an included file opening with an inner doc comment (E0753) is not followed", 'include!("inc.rs");\n',
         ("inc.rs=//! inner doc\nmod y;\n", "y.rs"), "", "inc.rs y.rs"),
        # 2026-11-01 review; rustc dep-info: agg.rs (with --cfg 'feature="slow"': agg.rs a.rs)
        ("a cfg on the fn that owns a block, or a #![cfg] opening its body, decides the mods in it",
         '#[cfg(feature = "slow")]\nfn a() {\n    #[path = "a.rs"]\n    mod a;\n}\nfn b() {\n    #![cfg(any())]\n'
         '    mod z {\n        include!("b.rs");\n    }\n}\n', ("a.rs", "b.rs"), "", "a.rs b.rs"),
        ("blocks drop y/ and keep #[path]", 'mod h;\nconst _: () = {\n    #[path = "y.rs"]\n    mod y;\n};\n',
         ('h.rs=fn f() {\n    mod a {\n        #[path = "x.rs"]\n        mod x;\n    }\n}\n', "a/x.rs", "h/a/x.rs", "y.rs"),
         "h.rs a/x.rs y.rs", "="),
        ("a non-ASCII inline module, and U+200E as whitespace", "mod π { mod x; }\nmod\u200ey;\n", ("π/x.rs", "y.rs"),
         "π/x.rs y.rs", "="),
    ]
    for label, agg, extra, want_c, want_p in resolution_arms:
        with tempfile.TemporaryDirectory() as tmp:
            tests, unread = tree(Path(tmp), agg, extra), set()
            every = {str(p.relative_to(tests)) for p in tests.rglob("*.rs") if p.is_file()}
            for mode, want in ((rm.Reach.CERTAIN, want_c), (rm.Reach.POSSIBLE, want_c if want_p == "=" else want_p)):
                got = {str(p.relative_to(tests.resolve())) for p in rm.reachable_from(tests / "agg.rs", mode, unread)}
                fail(label, f"{mode.name} reaches", got, every if want == "*" else {"agg.rs", *want.split()})
            top = {p.name for p in tests.glob("*.rs")} - {"agg.rs", *want_c.split()}
            fail(label, "refused", refused(check(Path(tmp))[0]), top | ({"UNREAD"} if top and unread else set()))
    return len(manifest_arms), len(resolution_arms)


def main(argv: list[str]) -> int:
    if "--pinned-inputs" in argv:  # runs nothing; this script is the row's script_sha256
        print(*(p.as_posix() for p in _rust_modules().PINNED_INPUTS), sep="\n")
        return 0
    walk_arms = _rust_modules().selftest()
    manifest_arms, resolution_arms = _selftest()
    if "--selftest" in argv:
        print(f"TEST_TARGET_COVERAGE selftest ok: {manifest_arms} manifest arms + {resolution_arms} resolution "
              f"arms, each an exact refused set (the resolution arms also exact CERTAIN/POSSIBLE sets); "
              f"{walk_arms} module-walk arms (scripts/rust_modules_arms.py)")
        return 0
    if not (source := _rust_modules().rust_cfg().host_source()).endswith("--print cfg"):
        print(f"note: no trustc/rustc answered `--print cfg`; platform cfgs decided from {source}", file=sys.stderr)
    failures, checked = check(REPO)
    if failures:
        print("TEST_TARGET_COVERAGE FAIL", *(f"  {f}" for f in failures), sep="\n", file=sys.stderr)
        return 1
    print(f"TEST_TARGET_COVERAGE ok: {checked} explicitly-declared test file(s) all reachable")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
