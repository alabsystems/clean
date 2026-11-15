#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""A `targo --unverified test` filter that selects ZERO tests must never be a green gate.

WHY THIS EXISTS
---------------
Measured 2026-08-26. `cargo test --locked -p clean-kernel axiom_refutation_gate`
exits 0, verbatim:

    test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 10412 filtered out

There is no `axiom_refutation_gate` in `clean-kernel`. The real gate is
`crates/clean-verify/tests/axiom_refutation_gate.rs`, run as
`cargo test --locked -p clean-verify --test axiom_refutation_gate` -- a 28.91 GB
peak / 6571 s OVERSIZE job that must be admitted at its measured weight (~44),
never at 8. So the invocation that "passed" was the one that ran nothing, and the
one that measures the property was never started.

That is `docs/GATE_REGISTRY.md`'s central class in its purest form: *a gate
nobody has seen fail is indistinguishable from `exit 0`*. A filter that matches
nothing is a gate that CANNOT fail, and libtest reports it as a pass.

`scripts/verify_runner.py` already knows this -- `shard_count_mismatch()` demotes
a shard that exits 0 having run fewer tests than its plan declares -- but that
guard is scoped to SHARDS. Nothing checked the filters written into gate scripts,
into `local_gate.sh`'s legs, or into the registry's own `demonstrated.ref`
citations, and nothing checked them without paying a cargo build.

WHAT THIS MEASURES
------------------
Every `targo --unverified test` invocation on the ENFORCEMENT SURFACE -- the four runner
roots, every `gate`-row script the registry names, and every `demonstrated.ref`
the registry cites -- is resolved statically against the workspace source. An
invocation is REFUSED when it provably selects nothing:

  * `-p <pkg>` names a package that is not in this workspace;
  * `--test <target>` (or `--test=<target>`) names an integration target
    that NO selected package has -- as cargo counts targets: declared ones,
    plus autodiscovered `tests/` files unless `autotests = false` -- or is a
    quoted glob that matches no target of any;
  * a `--test` target that exists -- or any target a glob matches --
    declares zero `#[test]` functions libtest could run: none in a file
    rustc may compile for it at a path libtest names, nor in a macro it may
    expand (`integration_target_declares_a_test`);
  * a positional filter fails the every-package rule (some `::` segment
    matches no module name and no `#[test]` function name in some selected
    package's own source) and matches, as libtest matches, the path of no
    `#[test]` fn in a test binary the run executes.

SEVERAL `-p` PACKAGES, AND GLOBS (2026-10-28)
---------------------------------------------
Until 2026-10-28 every `-p` was judged alone, and a `--test` value was always
a target NAME. Both were wrong, and the hook leg went red on two honest
Justfile recipes for it: `test-int-division` (six packages; each `--test` and
each filter lives in one of them) and `test-olean-pinned` (`--test '*'`).
Measured 2026-10-28 with `targo --unverified test` (targo 0.11.0+g20565c325)
on a two-crate throwaway workspace: `a` owns `tests/alpha.rs`, `b` owns
`tests/beta.rs` and `tests/blank.rs` (no test), and each lib has one test.
Each line is the command's own exit code:

  -p a -p b --test beta                exit 0    ran b's beta_works
  -p a -p b --test gamma               exit 101  no test target named `gamma`
                                                 in `a`, ... packages
  -p a --test '*'                      exit 0    ran alpha_works
  -p a --test 'al*'                    exit 0    ran alpha_works
  -p a --test 'zz*'                    exit 101  no test target matches pattern
                                                 `zz*` in `a` package
  -p a -p b --test 'be*'               exit 0    ran b's beta_works
  -p a -p b --test 'zz*'               exit 101  (same refusal, both packages)
  -p b --test 'bl*'                    exit 0    `0 passed` -- the vacuous green
  -p a -p b --lib -- a_lib_test        exit 0    a: 1 passed; b: 0 passed
  -p a -p b --lib -- no_such_test      exit 0    0 passed in both -- vacuous
  -p a -p b --test alpha --test beta   exit 0    ran both
  -p a -p b --test alpha --test 'zz*'  exit 101  one unmatched glob refuses all

So a `--test` name or glob needs ONE match among the selected packages, a
glob matching nothing is refused by cargo itself, a glob matching only an
empty target is the same vacuous green as an emptied name, and libtest's
filters go to every binary that runs. The rules above are written to that. Two choices in
them are deliberately the stricter reading: EVERY target a selector reaches --
each existing owner of a name, each match of a glob -- is held to the
emptiness rule (an emptied target is refused although another still runs),
and a glob left UNQUOTED in shell text is judged as the literal name it is
spelled as, because the shell, not cargo, expands it.

THE REVIEW OF THAT CHANGE (2026-11-01). Its first cut relaxed the filter rule
to "some running package has it anywhere in its source", which accepted
filters the old every-package rule refused and libtest would match nowhere: a
lib's test under `--test` only, an integration test's under `--lib` only, a
module of a bin, an undeclared file, a substring under `--exact`. It also
held a glob to a looser emptiness rule than a name, and counted `tests/` files
cargo builds into no target. So the old filter rule stands, with ONE
exemption: a filter only some of the packages hold is accepted when libtest
would match it -- a substring of, or under `--exact` equal to, a test's path
-- to a `#[test]` fn of one test binary this run executes: a selected
package's lib under `--lib`, a selected `--test` target, each read through the
module tree rustc compiles (`module_tree`). Any other selection keeps the old
rule; with one package the exemption cannot fire, so every single-package
FILTER verdict is the old one.

ONE MODULE WALK (2026-11-01). That module tree, and the `#[test]` fns read in
each of its files, come from `scripts/rust_modules.py`, the walk
`check_test_target_coverage.py` and `verify_runner.py` share, in CERTAIN mode:
a file or test path rustc does not compile is a false acceptance here. This
gate's own walk before it followed a `mod` in an unused macro body, took x.rs
for `#[cfg_attr(all(), path = "y.rs")] mod x;`, named a `#[path]` module in a
fn body and took x.rs beside x/mod.rs (E0761); and its test scan named a test
in a fn body or a macro body. `_MODULE_TREE_ARMS` and two guards pin those, and
the walk's own arms run inside this gate's self-test, which every invocation
runs before it reports. A `cfg` is decided by `test` and the host target's
platform cfgs (`#![cfg(unix)]` holds on this box), from the compiler's
`--print cfg`, or from Python's `sys.platform` when no compiler answers (a
stderr note says so; 2026-11-01 review: with none, an empty fact set turned
`test-int-division` VACUOUS); a `feature` never is, so a module behind one
gives the exemption nothing. The emptiness rule reads the same walk
(`integration_target_declares_a_test`).

LEXED, NOT RAW -- AND THE HONEST SIZE OF THAT
---------------------------------------------
Identifiers are harvested by SHAPE (`mod X`, `#[test] fn X`) over code with
comments and string literals blanked, using the shared stripper in
`scripts/check_add_decl_ratchet.py` -- R9's reference implementation -- rather
than a fourth private copy of a Rust lexer.

Two measurements, 2026-08-26, and they say different things. Do not read the
second as the first:

  * On TODAY's surface the lexer changes NO verdict. Re-running every site with
    the stripper replaced by the identity gives byte-identical results. In
    particular the motivating bug does not need it: `axiom_refutation_gate`
    occurs twice in `crates/clean-kernel/` -- a `//!` doc in
    `tc/tests2/iota_one_step_wide_major.rs` and an `assert!` message -- and
    neither is shaped like `mod X` or `#[test] fn X`, so the SHAPE requirement
    alone already refuses it. An earlier draft of this docstring claimed the
    lexing was what caught it. That was false and is recorded here rather than
    quietly deleted.
  * The guard is still real, and its size is 80. Harvesting the same shapes from
    RAW text invents **80 identifiers tree-wide** that exist only inside
    comments and literals -- `sorry_bypass_lines_in_production`,
    `collect_registry_line_sets`, `detects_marker`, `add_kexpr_beq` among them.
    Those are test-shaped names, which is exactly what a stale filter points at:
    a deleted test still named in the comment that explains its deletion would
    resolve under a raw harvest and select nothing at run time.

So: lexed because a raw scan would have 80 ways to be wrong here, not because it
has been wrong yet.

WHAT IT DOES *NOT* CLAIM
------------------------
Resolution is per PACKAGE, not per target, whenever every selected package
resolves the filter: a filter naming a module that exists in the crate's
`tests/` while the invocation says `--lib` still resolves. That is deliberate
-- an over-approximation inside the right crate cannot produce a false RED,
and the class this gate exists for is the filter aimed at the WRONG CRATE
ENTIRELY. (Only the several-package exemption above is judged per test
binary, because there an over-approximation would have ACCEPTED what the old
rule refused.) It is also static: a filter whose tests are all behind an
inactive `#[cfg(feature = ...)]` resolves here and still selects nothing at run
time. The runtime half of the property belongs to whoever runs the command;
`verify_runner.py`'s count check is that half for the suite. Which binaries
run is modelled for `--lib` and `--test` selections only, the two shapes
measured against cargo: with no target flag, a broad flag (`--tests`,
`--all-targets`, `--bins`, `--doc`, ...) or a `--bin`/`--example`/`--bench`,
every selected package must resolve every filter, which is the rule this
checker applied before 2026-10-28 and can be a false red with several
packages. `--exact` narrows only the exemption, never the old rule. The
every-package rule harvests names from EVERY `.rs` file of the package, lexed
(`resolve_segments`), whatever compiles it -- the deliberate over-approximation
above; the exemption and the emptiness rule read the module walk instead. Test
paths are the `#[test]` (and `#[x::test]`) fns the walk names (CERTAIN): a test
a macro generates has no path here, so a filter aimed only at one gets no
exemption, and a target such a test may be written into is never called empty.

Exit codes: 0 all resolvable, 1 a vacuous invocation, 2 self-test failure.

Usage:
    python3 scripts/check_cargo_test_selectors.py
    python3 scripts/check_cargo_test_selectors.py --list
    python3 scripts/check_cargo_test_selectors.py --selftest
"""

from __future__ import annotations

import ast
import fnmatch
import importlib.util
import json
import re
import shlex
import sys
import tempfile
import tomllib
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
REGISTRY_REL = "data/gate_registry.json"
# check_gate_registry.py R7 pins what `--pinned-inputs` prints: every repo file this gate's verdict
# executes -- the module walk (scripts/rust_modules.py), its arms, its cfg evaluator, the lexer it
# reads Rust with, and scripts/check_gate_registry.py, whose `script_code_only` and RUNNER_ROOTS it
# loads (2026-11-01 review: a change there moved this gate's verdicts with no pin moving). It is
# spelled in parts, as everywhere here: a whole `scripts/<x>.py` literal reads to R3 as a CALL, and
# this gate imports that file, it never runs it (see the runner-roots note below).
ANSWERS_PINNED_INPUTS = True
_REGISTRY_SCRIPT = Path("scripts") / "check_gate_registry.py"

# The four runner roots come from check_gate_registry.py's own RUNNER_ROOTS --
# `_runner_roots()` below reads them out of that module rather than repeating
# the four paths here. Two reasons, and the second was measured:
#
#   * one definition of "what is a runner root", so the two meta-gates cannot
#     drift into scanning different surfaces;
#   * a bare `scripts/<x>.sh` STRING LITERAL in this file is indistinguishable
#     from a call to R3's invocation scan. Writing the paths out made
#     check_gate_registry.py report "local_gate is invoked by
#     scripts/check_cargo_test_selectors.py", an edge that does not exist -- the
#     mirror image of the prose-is-not-an-invocation lesson in its own
#     docstring. A path this file never spells cannot be misread as a call.

# THERE IS NO ALLOWLIST, and that is a measurement, not an omission. The scan
# was written with one -- a per-command sanction for the single `cargo test`
# string on the surface that is a FIXTURE rather than a call
# (check_gate_registry.py's --selftest builds a synthetic registry citing a
# synthetic package `x`). Measured over the real tree, the entry never fired:
# that text is an unterminated JSON fragment, so it is SKIPped as unlexable
# like every other prose hit. An exemption no run exercises is an untested code
# path guarding nothing, so it was deleted rather than kept "in case". If a
# future false positive needs one, it arrives with the case that justifies it.

# ---------------------------------------------------------------------------
# the shared lexer -- R9's reference implementation, imported not re-typed
# ---------------------------------------------------------------------------


def _load_lexer():
    """`strip_noncode` from scripts/check_add_decl_ratchet.py, as the module walk
    (`rust_modules.py`) imported it: one import of the reference lexer serves both.

    Importing it is the point: the registry's own notes record a lane spent
    consolidating clean-auto onto ONE lexer copy after two duplicates drifted
    apart. A gate that lexes Rust in this repo uses the reference stripper.
    """
    return _rust_modules().strip_noncode


def _load_script_code_only(root: Path):
    """`script_code_only` from scripts/check_gate_registry.py.

    Same reason. It blanks `#` comments and Python docstrings, which is what
    keeps a `targo --unverified test` line in a usage banner from being read as a call --
    the mention-is-not-an-invocation rule R3 already learned the hard way.
    """
    ref = root / _REGISTRY_SCRIPT
    spec = importlib.util.spec_from_file_location("_clean_gate_registry", ref)
    if spec is None or spec.loader is None:  # pragma: no cover - unreachable
        raise SystemExit(f"cannot load the code-only helper at {ref}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.script_code_only


# ---------------------------------------------------------------------------
# workspace model
# ---------------------------------------------------------------------------

NAME_RE = re.compile(r'^\s*name\s*=\s*"([^"]+)"', re.M)
MOD_RE = re.compile(r"\bmod\s+([A-Za-z_][A-Za-z0-9_]*)")
FN_RE = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)")
ATTR_TEST_RE = re.compile(r"#\[[^]]*\btest\b[^]]*\]")
TEST_NAME_RE = re.compile(r'^\s*name\s*=\s*"([^"]+)"', re.M)


def crate_dirs(root: Path) -> list[Path]:
    out = []
    for parent in (root / "crates", root):
        if not parent.is_dir():
            continue
        for d in sorted(parent.iterdir()):
            if (d / "Cargo.toml").is_file() and (d / "src").is_dir():
                out.append(d)
    return out


def package_map(root: Path) -> dict[str, Path]:
    """package name -> crate directory, read from each member manifest."""
    out: dict[str, Path] = {}
    for d in crate_dirs(root):
        m = NAME_RE.search((d / "Cargo.toml").read_text(errors="replace"))
        if m:
            out.setdefault(m.group(1), d)
    return out


def libtest_names(code: str) -> set[str]:
    """The libtest path parts one file's CODE declares: module names and `#[test]` fns."""
    names = {m.group(1) for m in MOD_RE.finditer(code)}
    for m in ATTR_TEST_RE.finditer(code):
        fm = FN_RE.search(code, m.end(), m.end() + 400)
        if fm:
            names.add(fm.group(1))
    return names


def resolve_segments(crate: Path, segments: set[str], strip_noncode) -> set[str]:
    """Which of `segments` occur in this crate's CODE as a libtest path part.

    A libtest path is `mod::mod::test_fn`, so the harvest is module names plus
    `#[test]`-annotated function names -- and file stems, because a `tests/x.rs`
    integration target contributes its own name to nothing else.

    Two passes, and the cheap one comes first for a measured reason: stripping
    comments and literals is a regex over the whole file, and running it over
    all ~7,000 `.rs` files of the big crates costs seconds. A segment that does
    not occur in a file's RAW text cannot occur in its code, so the raw
    substring test is a sound prefilter -- it can only ever skip files that
    could not have matched. The expensive lex runs on the handful of files that
    survive it. This is a speed decision ONLY: the verdict is still decided on
    lexed code, never on the raw hit.
    """
    found: set[str] = set()
    todo = set(segments)
    for f in sorted(crate.rglob("*.rs")):
        if not todo:
            break
        if "target" in f.parts:
            continue
        try:
            raw = f.read_text(errors="replace")
        except OSError:  # pragma: no cover - unreadable file
            continue
        for seg in list(todo):
            if seg in f.stem:
                found.add(seg)
                todo.discard(seg)
        candidates = {seg for seg in todo if seg in raw}
        if not candidates:
            continue
        names = libtest_names(strip_noncode(raw))
        for seg in candidates:
            if any(seg in n for n in names):
                found.add(seg)
                todo.discard(seg)
    return found


def manifest_of(crate: Path) -> dict | None:
    """The crate's Cargo.toml, parsed by tomllib; None when it does not parse."""
    try:
        return tomllib.loads((crate / "Cargo.toml").read_text(errors="replace"))
    except (OSError, tomllib.TOMLDecodeError):
        return None


def _declared_tests(manifest: dict) -> dict[str, str | None]:
    """`[[test]]` name -> its `path` (None when it has none), from a parsed manifest."""
    out: dict[str, str | None] = {}
    tables = manifest.get("test")
    for t in tables if isinstance(tables, list) else []:
        if isinstance(t, dict) and isinstance(t.get("name"), str):
            path = t.get("path")
            out[t["name"]] = path if isinstance(path, str) else None
    return out


def _inferred_tests(crate: Path) -> dict[str, Path]:
    """Target name -> root file for each `tests/` entry cargo's autodiscovery sees."""
    out: dict[str, Path] = {}
    tests = crate / "tests"
    if tests.is_dir():
        for entry in tests.iterdir():
            if entry.is_file() and entry.suffix == ".rs":
                out[entry.stem] = entry
            elif entry.is_dir() and (entry / "main.rs").is_file():
                out[entry.name] = entry / "main.rs"
    return out


def integration_targets(crate: Path) -> set[str]:
    """Names cargo will accept for `--test <name>` in this crate.

    cargo's own rule (`toml_targets_and_inferred`), since 2026-11-01: every
    declared `[[test]]`, plus each autodiscovered `tests/<x>.rs` and
    `tests/<x>/main.rs` -- unless the package says `autotests = false`, and
    minus any whose NAME or PATH a declared target already took. Before, every
    `tests/` file counted, so a glob could match a file cargo builds into no
    target (`clean-verify` is `autotests = false`) and let it stand in for an
    emptied one. Edition 2015's implicit `autotests = false` beside explicit
    targets is not modelled; this workspace is not on 2015.

    A manifest that does not parse falls back to the reading this checker had
    before: every `tests/` entry plus every declared name.
    """
    inferred = _inferred_tests(crate)
    manifest = manifest_of(crate)
    if manifest is None:
        text = (crate / "Cargo.toml").read_text(errors="replace")
        declared_by_text = set()
        for block in re.split(r"^\[\[test\]\]\s*$", text, flags=re.M)[1:]:
            m = TEST_NAME_RE.search(re.split(r"^\[", block, flags=re.M)[0])
            if m:
                declared_by_text.add(m.group(1))
        return set(inferred) | declared_by_text
    declared = _declared_tests(manifest)
    names = set(declared)
    package = manifest.get("package")
    autotests = package.get("autotests", True) if isinstance(package, dict) else True
    if autotests is not False:
        claimed = {(crate / p).resolve() for p in declared.values() if p}
        names.update(
            n for n, root in inferred.items()
            if n not in declared and root.resolve() not in claimed
        )
    return names


def integration_target_root(crate: Path, name: str) -> Path | None:
    """The crate-root file cargo compiles for `--test <name>`, or None if unknown."""
    manifest = manifest_of(crate)
    if manifest is not None:
        path = _declared_tests(manifest).get(name)
        if path:
            root = crate / path
            return root if root.is_file() else None
    for root in (crate / "tests" / f"{name}.rs", crate / "tests" / name / "main.rs"):
        if root.is_file():
            return root
    return None


def lib_root(crate: Path) -> Path | None:
    """The crate-root file of this package's library, or None when it has none."""
    manifest = manifest_of(crate)
    lib = manifest.get("lib") if manifest is not None else None
    path = lib.get("path") if isinstance(lib, dict) else None
    root = crate / path if isinstance(path, str) else crate / "src" / "lib.rs"
    return root if root.is_file() else None


HARNESS_FALSE_RE = re.compile(r"^\s*harness\s*=\s*false", re.M)


def integration_target_has_harness(crate: Path, name: str) -> bool:
    """False when the manifest declares `harness = false` for this target.

    Such a target has a `main` and legitimately declares no `#[test]`, so the
    emptiness rule must not fire on it.
    """
    manifest_path = crate / "Cargo.toml"
    if not manifest_path.is_file():
        return True
    manifest = manifest_path.read_text(errors="replace")
    for block in re.split(r"^\[\[test\]\]\s*$", manifest, flags=re.M)[1:]:
        head = re.split(r"^\[", block, flags=re.M)[0]
        m = TEST_NAME_RE.search(head)
        if m and m.group(1) == name and HARNESS_FALSE_RE.search(head):
            return False
    return True


# ---------------------------------------------------------------------------
# what one test binary compiles (2026-11-01): scripts/rust_modules.py
# ---------------------------------------------------------------------------

# An attribute BODY (what `#[` .. `]` holds, as `rust_modules.fn_items` hands them) whose LAST path
# segment is `test`, bare or called: `test`, `tokio::test`, `async_std::test(..)`. Deliberately not
# `test_case(..)` -- a different attribute, and counting it would make these rules guess.
TEST_BODY_RE = re.compile(r"\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*test\s*(?:\(.*)?", re.S)
_RM = None


def _rust_modules():
    """scripts/rust_modules.py, the module walk this gate, check_test_target_coverage and
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


def module_tree(crate: Path, root: Path) -> list[tuple[Path, str | None]]:
    """(file, module path) for every file of this package that rustc surely
    compiles into the crate rooted at `root`; the root's module path is "", and
    a file whose module libtest cannot name (one in a fn body or const block)
    has None.

    It is `rust_modules.walk` in CERTAIN mode, whose docstring is the
    resolution rule, include!d files included. CERTAIN because here a file or
    path rustc does not compile is a FALSE ACCEPTANCE (a filter "matched" a test
    no binary has); a file missed only sends a filter back to the every-package
    rule this checker has always applied. Until 2026-11-01 this walk was its
    own, and it followed a `mod` in an unused macro body, took x.rs for
    `#[cfg_attr(all(), path = "y.rs")] mod x;` (rustc loads y.rs), named a
    `#[path]` module in a fn body (libtest names nothing there) and took x.rs
    beside x/mod.rs (E0761: the crate does not build); `_MODULE_TREE_ARMS` pins
    each. Files outside the package, or under its `target/`, are dropped, so
    this tree never holds a file `resolve_segments` cannot see.
    """
    rm = _rust_modules()
    pkg = crate.resolve()
    return sorted(
        ((f, path) for f, path in rm.walk(root, rm.Reach.CERTAIN)
         if pkg in f.parents and "target" not in f.relative_to(pkg).parts),
        key=lambda fp: (str(fp[0]), fp[1] or ""),
    )


def file_test_paths(path: Path, modpath: str) -> list[str]:
    """The libtest path of each `#[test]` fn in this file, as libtest prints it:
    `rust_modules.fn_items` (CERTAIN), so a test in a block or a macro body has
    none (libtest lists neither), and nor has one under a `cfg` -- its own, its
    body's `#![cfg]` or its module's -- the host facts do not decide true:
    rustc may well compile that one, and it is left out because this is the
    side a filter's acceptance is read from (2026-11-01)."""
    rm = _rust_modules()
    return [p for p, attrs in rm.fn_items(path, modpath) if any(TEST_BODY_RE.fullmatch(a) for a in attrs)]


def integration_target_declares_a_test(crate: Path, name: str) -> bool | None:
    """Does `--test <name>` declare a test libtest runs? True, False, or None: cannot say.

    The gap this closes: the target-NAME check asks only whether a source file
    exists. A target that exists and declares zero tests compiles, runs, prints
    `running 0 tests` and exits 0 -- the same vacuous green the missing name
    produces, from the other direction.

    Read through `rust_modules.py` since 2026-11-01. True: the CERTAIN walk
    names a `#[test]` fn libtest lists (`file_test_paths`). False only when
    MAYBE -- every file rustc may compile for it, less what a host cfg decides
    false -- holds no `#[test]` fn at a path libtest can name, no file it could
    not place, no `#[test]` in the tokens of an item-level macro call, and none
    in a `macro_rules!` body whose name is invoked; anything else is None, and
    the caller does not refuse on it. Before, this rule had its own scan: any
    `#[test]` in code, `include!`s followed by a private lexer, and every .rs
    under a directory target. It named a test in a fn body, in a macro nobody
    invokes, under `#[cfg(any())]`, in a file an uninvoked macro includes and
    in a stray file beside a `main.rs` (each an empty target accepted), and it
    never followed a `mod`, so 7 aggregating targets here (`spec_suite` among
    them), which hold every test through `#[path] mod`, read as empty (2026-11-01
    review). Not seen: a macro from another crate that writes a test from tokens
    holding no `#[test]` -- refused, as it was before.
    """
    root = integration_target_root(crate, name)
    if root is None:
        return None
    rm = _rust_modules()
    if any(file_test_paths(f, m) for f, m in rm.walk(root, rm.Reach.CERTAIN) if m is not None):
        return True
    unplaced: set[Path] = set()
    maybe = rm.walk(root, rm.Reach.MAYBE, unplaced)
    if unplaced or any(any(TEST_BODY_RE.fullmatch(a) for a in attrs)
                       for f, m in maybe for _, attrs in rm.fn_items(f, m, rm.Reach.MAYBE)):
        return None
    groups, calls = [], set()
    for f, m in maybe:
        held, called = rm.macro_items(f, m)
        groups += held
        calls |= called
    tests_in = {mac for mac, attrs in groups if any(TEST_BODY_RE.fullmatch(a) for a in attrs)}
    return None if any(mac.startswith("!") or mac in calls for mac in tests_in) else False


def may_hold_match(filt: str, modpath: str, raw: str) -> bool:
    """False only when no test in this file can have a path containing `filt`.

    A SPEED prefilter, sound by construction: a test path here is `modpath`
    followed by names written in this file. So a match lies inside the module
    path (then any test here matches), or some tail of `filt` starts in this
    file's own names -- whose first piece then occurs in its raw text.
    """
    if "test" not in raw:
        return False
    prefix = modpath + "::" if modpath else ""
    for j in range(len(filt)):
        if prefix.endswith(filt[:j]):
            piece = filt[j:].split("::")[0]
            if not piece or piece in raw:
                return True
    return filt in prefix


# ---------------------------------------------------------------------------
# invocation parsing
# ---------------------------------------------------------------------------

CARGO_VALUE_FLAGS = {
    "-p",
    "--package",
    "--exclude",
    "--features",
    "-F",
    "--target",
    "--target-dir",
    "--manifest-path",
    "-j",
    "--jobs",
    "--message-format",
    "--profile",
    "--config",
    "--color",
    "-Z",
}
TARGET_FLAGS = {"--test", "--bin", "--example", "--bench"}
BROAD_FLAGS = {
    "--workspace",
    "--all",
    "--all-targets",
    "--tests",
    "--bins",
    "--benches",
    "--examples",
    "--doc",
}
LIBTEST_VALUE_FLAGS = {"--skip", "--test-threads", "--format", "--logfile", "-Z"}
# A cargo/libtest token that is a filter looks like a Rust path. Prose does not.
FILTER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_:]*$")
PKG_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.-]*$")
DYNAMIC_RE = re.compile(r"[$`*?]")
# cargo's own test for "this target selector is a pattern, not a name": a
# `--test`/`--bin`/`--example`/`--bench` value containing any of these is
# matched as a Unix glob against the selected packages' target names. `cargo
# help test` ("Target Selection") documents it, and adds that the pattern must
# be QUOTED or the shell expands it first. Measured against targo 2026-10-28;
# see the module docstring. (`-p` takes globs too; a `-p` pattern fails
# PKG_RE and is SKIPped, never judged.)
CARGO_GLOB_RE = re.compile(r"[*?\[\]]")
# The characters that make the SHELL expand a bare word. `]` alone does not.
SHELL_GLOB_CHARS = "*?["
# Exactly shlex's POSIX word separators, so word counts agree with shlex.split.
SHELL_BLANKS = " \t\r\n"


def bare_glob_words(cmd: str) -> list[bool]:
    """For each shell word of `cmd`, whether it carries an UNQUOTED glob character.

    `shlex.split` drops quotes, so `--test '*'` and `--test *` reach the parser
    as the same token -- and they are different commands. Quoted, cargo
    receives the pattern and matches it against target names. Bare, the SHELL
    expands it against the working directory first (or, matching no file,
    passes it on), so what cargo receives is not decidable from the text. An
    argv list has no shell; `argv_commands` re-quotes its items, so they land
    here quoted, which is what they are.

    Word boundaries follow `shlex.split` in POSIX mode; `resolve` refuses to
    trust this when the two disagree on the word count.
    """
    flags: list[bool] = []
    word: bool | None = None
    quote = ""
    i, n = 0, len(cmd)
    while i < n:
        c = cmd[i]
        if quote:
            if c == quote:
                quote = ""
            elif c == "\\" and quote == '"':
                i += 1
            i += 1
            continue
        if c in SHELL_BLANKS:
            if word is not None:
                flags.append(word)
                word = None
            i += 1
            continue
        if word is None:
            word = False
        if c == "\\":
            i += 2
            continue
        if c in "'\"":
            quote = c
        elif c in SHELL_GLOB_CHARS:
            word = True
        i += 1
    if word is not None:
        flags.append(word)
    return flags


class NotACommand(Exception):
    """The text matched `targo --unverified test` but is prose, not an invocation."""


class Unresolvable(Exception):
    """A real invocation whose selection cannot be decided statically."""


def parse_invocation(tokens: list[str], bare_globs: list[bool] | None = None) -> dict:
    """Model `targo --unverified test <cargo-args> [-- <libtest-args>]` selection.

    Each target selector is `(kind, value, form)`: `form` is "name" (an exact
    target name), "glob" (a pattern cargo itself matches) or "shell-glob" (a
    pattern left UNQUOTED, which the shell expands before cargo sees it, so it
    is judged as the literal name it is spelled as -- the verdict it had before
    globs were modelled). `bare_globs[i]` says whether token `i` carries an
    unquoted glob character; with no information every pattern is "shell-glob",
    the fail-closed reading.
    """
    packages: list[str] = []
    targets: list[tuple[str, str, str]] = []
    filters: list[str] = []
    lib = False
    broad = False
    exact = False
    after_dd = False

    def selector(kind: str, value: str, word: int) -> None:
        if not CARGO_GLOB_RE.search(value):
            form = "name"
        elif bare_globs is not None and not bare_globs[word]:
            form = "glob"
        else:
            form = "shell-glob"
        targets.append((kind, value, form))

    i = 0
    while i < len(tokens):
        tok = tokens[i]
        # `--test=NAME` is the same selector in one word (2026-11-01). It used
        # to fall through to "a flag" below and be skipped, so `--test=gone`
        # read as "selects whole targets" and was never judged. Read before the
        # dynamic-token test, which would take its glob for a shell variable.
        flag, eq, value = tok.partition("=")
        if not after_dd and eq and flag in TARGET_FLAGS:
            if not value:
                raise NotACommand(f"{flag}= with no value")
            if "$" in value or "`" in value:
                raise Unresolvable(f"dynamic token {tok!r}")
            selector(flag[2:], value, i)
            i += 1
            continue
        if DYNAMIC_RE.search(tok):
            raise Unresolvable(f"dynamic token {tok!r}")
        if tok == "--":
            after_dd, i = True, i + 1
            continue
        if not after_dd:
            if tok in ("-p", "--package"):
                if i + 1 >= len(tokens):
                    raise NotACommand("-p with no value")
                packages.append(tokens[i + 1])
                i += 2
                continue
            if tok.startswith("--package=") or tok.startswith("-p="):
                packages.append(tok.split("=", 1)[1])
                i += 1
                continue
            if tok in TARGET_FLAGS:
                if i + 1 >= len(tokens):
                    raise NotACommand(f"{tok} with no value")
                selector(tok[2:], tokens[i + 1], i + 1)
                i += 2
                continue
            if tok == "--lib":
                lib, i = True, i + 1
                continue
            if tok in BROAD_FLAGS:
                broad, i = True, i + 1
                continue
            if tok in CARGO_VALUE_FLAGS:
                i += 2
                continue
            if tok.startswith("-"):
                i += 1
                continue
            filters.append(tok)
            i += 1
            continue
        if tok in LIBTEST_VALUE_FLAGS:
            i += 2
            continue
        if tok == "--exact":
            exact = True
        if tok.startswith("-"):
            i += 1
            continue
        filters.append(tok)
        i += 1
    for f in filters:
        if not FILTER_RE.match(f):
            raise NotACommand(f"positional {f!r} is not a test path")
    for p in packages:
        if not PKG_RE.match(p):
            raise NotACommand(f"package {p!r} is not a package name")
    return {
        "packages": packages,
        "targets": targets,
        "filters": filters,
        "lib": lib,
        "broad": broad,
        "exact": exact,
    }


# Where a shell command ends. `)` closes a subshell or a function body and
# terminates; `(` does NOT, deliberately -- an opening paren mid-command is prose
# ("cargo test -p x --lib AND (if a native shard exists"), and cutting there
# would leave behind a tail of identifier-shaped English that parses as a filter
# list and reads as vacuous. Keeping the paren keeps the token that gives the
# prose away.
CMD_TERMINATOR = re.compile(r"\|\||&&|[|;&><`)]")
# The driver is targo (owner directive 2026-09-28): `targo --unverified test`
# or `targo trust test`. A stock `cargo [+chan] test` is still recognised, so a
# stale spelling on the enforcement surface is judged rather than skipped.
SHELL_CARGO_RE = re.compile(
    r"\b(?:targo\s+(?:--unverified|trust)|cargo(?:\s+\+\S+)?)\s+test\b"
)
ARGV_CARGO_RE = re.compile(
    r"""["'](?:targo["']\s*,\s*["'](?:--unverified|trust)|cargo)["']\s*,\s*["']test["']"""
)


def test_args(tokens: list[str]) -> list[str]:
    """The arguments after the `test` subcommand of a matched invocation."""
    if "test" in tokens[:4]:
        return tokens[tokens.index("test") + 1 :]
    return tokens[2:]


def _join_continuations(text: str) -> list[tuple[int, str]]:
    out: list[tuple[int, str]] = []
    buf = ""
    start = 0
    for lineno, line in enumerate(text.splitlines(), 1):
        if not buf:
            start = lineno
        if line.rstrip().endswith("\\"):
            buf += line.rstrip()[:-1] + " "
            continue
        out.append((start, buf + line))
        buf = ""
    if buf:
        out.append((start, buf))
    return out


def shell_commands(text: str):
    """(lineno, command text) for each shell-form `targo --unverified test` in `text`."""
    for lineno, line in _join_continuations(text):
        for m in SHELL_CARGO_RE.finditer(line):
            rest = line[m.start() :]
            end = CMD_TERMINATOR.search(rest, len(m.group(0)))
            cmd = rest[: end.start()] if end else rest
            cmd = re.split(r"\s#", cmd)[0].strip()
            yield lineno, cmd


def argv_commands(text: str):
    """(lineno, command text) for each Python `["targo", "--unverified", "test", ...]` list."""
    for m in ARGV_CARGO_RE.finditer(text):
        open_at = text.rfind("[", 0, m.start())
        if open_at < 0:
            continue
        depth = 0
        close_at = -1
        for idx in range(open_at, len(text)):
            if text[idx] == "[":
                depth += 1
            elif text[idx] == "]":
                depth -= 1
                if depth == 0:
                    close_at = idx
                    break
        if close_at < 0:
            continue
        try:
            argv = ast.literal_eval(text[open_at : close_at + 1])
        except (ValueError, SyntaxError):
            continue
        if not isinstance(argv, list) or not all(isinstance(a, str) for a in argv):
            continue
        lineno = text.count("\n", 0, open_at) + 1
        yield lineno, " ".join(shlex.quote(a) for a in argv)


# ---------------------------------------------------------------------------
# the check
# ---------------------------------------------------------------------------


def _runner_roots(root: Path) -> tuple[str, ...]:
    """The runner roots, read from check_gate_registry.py -- never re-typed."""
    ref = root / _REGISTRY_SCRIPT
    spec = importlib.util.spec_from_file_location("_clean_gate_registry_roots", ref)
    if spec is None or spec.loader is None:  # pragma: no cover - unreachable
        raise SystemExit(f"cannot load the runner roots from {ref}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return tuple(mod.RUNNER_ROOTS)


def surface(root: Path) -> list[tuple[str, str]]:
    """(kind, path) for every file scanned, re-derived from the registry.

    Deduplicated: `scripts/local_gate.sh` is both a runner root and a `gate`
    row, and scanning it twice would double-count every leg it declares.
    """
    seen: dict[str, str] = {r: "runner" for r in _runner_roots(REPO_ROOT)}
    reg = json.loads((root / REGISTRY_REL).read_text())
    for row in reg["rows"]:
        path = row.get("path") or ""
        if row.get("kind") == "gate" and path.endswith((".sh", ".py")):
            seen.setdefault(path, "gate-script")
    return [(kind, rel) for rel, kind in seen.items()]


def registry_refs(root: Path) -> list[tuple[str, str]]:
    """(row id, command) for every `demonstrated.ref` that is a cargo command."""
    reg = json.loads((root / REGISTRY_REL).read_text())
    out = []
    for row in reg["rows"]:
        ref = (row.get("demonstrated") or {}).get("ref", "")
        if isinstance(ref, str) and ref.strip().startswith(
            ("targo --unverified test", "targo trust test", "cargo test")
        ):
            out.append((row["id"], ref.strip()))
    return out


# THIS FILE IS EXEMPT FROM ITS OWN SCAN, and the exemption is named here rather
# than hidden in a pattern -- the same way check_gate_registry.py names its own
# READS_SOURCE exemption instead of encoding it in a regex.
#
# The reason is that a checker's corpus is FIXTURES. `--selftest` builds a
# synthetic crate called `demo` and drives a dozen commands against it, every
# one of them a string literal in code (not a docstring), and every one of them
# deliberately unresolvable against this workspace -- that is what makes them
# arms. Scanning them would report the checker's own negative controls as the
# defect it looks for. Nothing is lost: this file runs no cargo, so it has no
# invocation for the scan to protect.
SELF_REL = "scripts/" + Path(__file__).name


def collect(root: Path, script_code_only) -> list[dict]:
    """Every invocation on the surface, before resolution."""
    found: list[dict] = []
    for kind, rel in surface(root):
        path = root / rel
        if not path.is_file() or rel == SELF_REL:
            continue
        raw = path.read_text(errors="replace")
        # Every runner root and gate script is `#`-commented shell, Python or a
        # Justfile, so the code-only pass is unconditional. It used to be
        # `.py`/`.sh`-only -- which silently exempted `scripts/githooks/pre-push`,
        # a shell script with no extension, and read its comments as commands.
        # Found by this gate on its own wiring commit.
        code = script_code_only(rel, raw)
        for lineno, cmd in shell_commands(code):
            found.append({"site": f"{rel}:{lineno}", "file": rel, "cmd": cmd, "kind": kind})
        if rel.endswith(".py"):
            for lineno, cmd in argv_commands(code):
                found.append(
                    {"site": f"{rel}:{lineno}", "file": rel, "cmd": cmd, "kind": "argv"}
                )
    for rid, cmd in registry_refs(root):
        found.append(
            {
                "site": f"{REGISTRY_REL}#{rid}",
                "file": REGISTRY_REL,
                "cmd": cmd,
                "kind": "registry-ref",
            }
        )
    return found


def _selects_nothing(crate: Path, name: str) -> bool:
    """`--test <name>` of this crate provably runs zero tests.

    It has the libtest harness and `integration_target_declares_a_test` says
    False. A `harness = false` target and a target it cannot say about are
    never refused: neither is evidence of emptiness.
    """
    if not integration_target_has_harness(crate, name):
        return False
    return integration_target_declares_a_test(crate, name) is False


class _Workspace:
    """The packages of one tree, and what has been read of them, for one `resolve`."""

    def __init__(self, root: Path) -> None:
        self.strip = _load_lexer()
        self.packages = package_map(root)
        self._targets: dict[str, set[str]] = {}
        self._segments: dict[tuple[str, str], bool] = {}
        self._trees: dict[Path, list[tuple[Path, str | None]]] = {}
        self._paths: dict[tuple[Path, str], list[str]] = {}
        self._selects: dict[tuple[Path, str, bool], bool] = {}
        self._empty: dict[tuple[Path, str], bool] = {}

    def selects_nothing(self, crate: Path, name: str) -> bool:
        """`_selects_nothing`, read once per target for one `resolve`."""
        if (crate, name) not in self._empty:
            self._empty[(crate, name)] = _selects_nothing(crate, name)
        return self._empty[(crate, name)]

    def targets(self, pkg: str, crate: Path) -> set[str]:
        if pkg not in self._targets:
            self._targets[pkg] = integration_targets(crate)
        return self._targets[pkg]

    def resolves(self, pkg: str, crate: Path, segments: set[str]) -> dict[str, bool]:
        """Segment -> whether it occurs anywhere in the package's code (resolve_segments)."""
        unknown = {s for s in segments if (pkg, s) not in self._segments}
        if unknown:
            hit = resolve_segments(crate, unknown, self.strip)
            for seg in unknown:
                self._segments[(pkg, seg)] = seg in hit
        return {s: self._segments[(pkg, s)] for s in segments}

    def selected_by(self, crate: Path, root: Path, filters: list[str], exact: bool) -> set[str]:
        """Which of `filters` libtest would match to a `#[test]` of the binary rooted at `root`.

        libtest's own rule: the filter is a substring of the test's path, or
        equal to it under `--exact`. Paths come from `module_tree` and
        `file_test_paths` (both `rust_modules.py`); `may_hold_match` decides
        only which files to lex.
        """
        key = root.resolve()
        if key not in self._trees:
            self._trees[key] = module_tree(crate, root)
        todo = [f for f in filters if (key, f, exact) not in self._selects]
        hits: set[str] = set()
        for path, modpath in self._trees[key]:
            if not todo:
                break
            if modpath is None:  # libtest can name no test in this file
                continue
            raw = path.read_text(errors="replace")
            for filt in [f for f in todo if may_hold_match(f, modpath, raw)]:
                tests = self._paths.get((path, modpath))
                if tests is None:
                    tests = self._paths[(path, modpath)] = file_test_paths(path, modpath)
                if any(t == filt if exact else filt in t for t in tests):
                    hits.add(filt)
                    todo.remove(filt)
        for filt in filters:
            self._selects.setdefault((key, filt, exact), filt in hits)
        return {f for f in filters if self._selects[(key, f, exact)]}


def _judge_targets(
    inv: dict, existing: list[tuple[str, Path]], ws: _Workspace
) -> tuple[list[str], list[tuple[str, Path, str]]]:
    """Why the `--test` selectors select nothing, and each (package, crate, target) that runs.

    SEVERAL `-p` PACKAGES ARE ONE SELECTION, measured 2026-10-28 (module
    docstring): cargo resolves a `--test` name or glob against every selected
    package together and refuses the run only when NONE has a match. So an
    exact `--test NAME` needs ONE owner among them, and a quoted `--test GLOB`
    one match. Every target either selects -- each owner of a name, each match
    of a glob -- is held to the emptiness rule: an emptied target is refused
    although another target still runs (2026-11-01: a glob was first refused
    only when EVERY match was empty, so `'[ep]*_target'` passed where the same
    two targets spelled out did not). With one package each rule is the rule
    this checker always had; the messages are the ones it always printed.
    """
    problems: list[str] = []
    running: list[tuple[str, Path, str]] = []
    for kind, name, form in inv["targets"]:
        if kind != "test":
            continue
        if form == "glob":
            matched = [
                (pkg, crate, t)
                for pkg, crate in existing
                for t in sorted(ws.targets(pkg, crate))
                if fnmatch.fnmatchcase(t, name)
            ]
            running.extend(matched)
            if not matched:
                problems.append(
                    f"--test {name!r} is a glob that matches no integration target of "
                    f"{', '.join(pkg for pkg, _ in existing)} -- cargo matches it against "
                    f"target names and refuses a pattern that matches none"
                )
                continue
            empty = [f"{pkg}/{t}" for pkg, crate, t in matched if ws.selects_nothing(crate, t)]
            if empty:
                problems.append(
                    f"--test {name!r} selects {', '.join(empty)}, which declare"
                    f"{'s' if len(empty) == 1 else ''} ZERO #[test] functions libtest could run "
                    f"(none at a path it names in a file rustc may compile, nor in a macro it "
                    f"may expand) -- a glob holds every target it matches to the rule an exact "
                    f"name is held to (a `harness = false` target is exempt)"
                )
            continue
        owners = [(pkg, crate) for pkg, crate in existing if name in ws.targets(pkg, crate)]
        running.extend((pkg, crate, name) for pkg, crate in owners)
        if not owners:
            hint = (
                " -- an UNQUOTED glob, which the shell expands before cargo sees it; "
                "quote it to hand cargo the pattern"
                if form == "shell-glob"
                else ""
            )
            for pkg, crate in existing:
                where = (
                    f"crates/{crate.name}/tests/{name}.rs exists, but cargo builds it into "
                    f"no target: `autotests = false`, or a declared [[test]] took its path"
                    if name in _inferred_tests(crate)
                    else f"no crates/{crate.name}/tests/{name}.rs"
                )
                problems.append(
                    f"--test {name} is not an integration target of {pkg} ({where}){hint}"
                )
            continue
        # The target EXISTS. Does it declare anything to run? A target emptied
        # of its tests exits 0 having measured nothing, which is the same
        # vacuous green as a missing name.
        for pkg, crate in owners:
            if ws.selects_nothing(crate, name):
                problems.append(
                    f"--test {name} of {pkg} exists but declares ZERO #[test] "
                    f"functions libtest could run (none at a path it names in a file "
                    f"rustc may compile, nor in a macro it may expand), so it exits 0 "
                    f"having run nothing (a `harness = false` target is exempt and this "
                    f"one is not)"
                )
    return problems, running


def _running_binaries(
    inv: dict, existing: list[tuple[str, Path]], running: list[tuple[str, Path, str]]
) -> list[tuple[str, str, Path, Path]] | None:
    """(package, label, crate, crate root) of each libtest binary this run executes.

    Modelled only for a selection made of `--lib` and `--test` selectors -- the
    shapes measured against cargo (module docstring). Any other selection (no
    target flag, a broad flag, `--bin`/`--example`/`--bench`) is None, and the
    caller keeps the every-package rule. `--lib` runs the lib of each selected
    package that has one; `--test` runs each target it selected; a `harness =
    false` target runs no libtest, so no filter can select a test there.
    """
    if inv["broad"] or any(kind != "test" for kind, _, _ in inv["targets"]):
        return None
    if not inv["lib"] and not inv["targets"]:
        return None
    out: list[tuple[str, str, Path, Path]] = []
    if inv["lib"]:
        for pkg, crate in existing:
            root = lib_root(crate)
            if root is not None:
                out.append((pkg, "its lib", crate, root))
    seen: set[tuple[str, str]] = set()
    for pkg, crate, t in running:
        if (pkg, t) in seen or not integration_target_has_harness(crate, t):
            continue
        seen.add((pkg, t))
        root = integration_target_root(crate, t)
        if root is not None:
            out.append((pkg, f"--test {t}", crate, root))
    return out


def _judge_filters(
    inv: dict,
    existing: list[tuple[str, Path]],
    running: list[tuple[str, Path, str]],
    ws: _Workspace,
) -> list[str]:
    """Why a positional filter selects nothing.

    THE RULE THIS CHECKER HAS ALWAYS APPLIED comes first: every selected
    package resolves every `::` segment of the filter somewhere in its code. A
    filter that passes it is accepted, as it always was -- including the
    per-package over-approximation the module docstring owns to.

    ONE EXEMPTION, from the cargo measurement of 2026-10-28: libtest hands the
    filters to every binary that runs, so with several packages a filter only
    one of them holds is honest IF it lives in a test binary this run executes.
    The evidence must be positive and inside ONE binary, judged by libtest's
    own rule: the filter is a substring of -- under `--exact`, equal to -- the
    path of a `#[test]` fn that binary compiles, its module path read through
    the crate root's module tree (`module_tree`). A filter found only in a
    target this run does not build -- a lib under `--test`, an integration
    target under `--lib`, a bin's module, an undeclared file -- or whose
    segments exist but form no test's path, gets no exemption (2026-11-01: the
    first cut searched each package's whole source tree and accepted all of
    those). Only packages that resolve the whole filter are searched.

    With one package the exemption can never fire: a filter matching a test
    path in one of its binaries has every segment among that package's module
    and `#[test]` fn names, so it passes the old rule first. Every
    single-package filter verdict is therefore the old one.
    """
    problems: list[str] = []
    wanted = {seg for filt in inv["filters"] for seg in filt.split("::") if seg}
    resolved = {pkg: ws.resolves(pkg, crate, wanted) for pkg, crate in existing}
    binaries = _running_binaries(inv, existing, running)
    pending: list[tuple[str, dict[str, list[str]], list[str]]] = []
    for filt in inv["filters"]:
        segs = [s for s in filt.split("::") if s]
        misses = {pkg: [s for s in segs if not resolved[pkg][s]] for pkg, _ in existing}
        if any(misses.values()):
            pending.append((filt, misses, [pkg for pkg, _ in existing if not misses[pkg]]))
    proven: set[str] = set()
    for pkg, _, crate, root in binaries or []:
        want = [f for f, _, holders in pending if pkg in holders and f not in proven]
        if want:
            proven |= ws.selected_by(crate, root, want, inv["exact"])
    for filt, misses, holders in pending:
        if filt in proven:
            continue
        for pkg, _ in existing:
            for seg in misses[pkg]:
                problems.append(
                    f"filter {filt!r}: segment {seg!r} matches no module and no "
                    f"#[test] fn in {pkg}'s CODE -- this run selects zero tests "
                    f"and libtest reports `0 passed` as ok"
                )
        if binaries is not None:
            for pkg in holders:
                ran = [label for p, label, _, _ in binaries if p == pkg]
                problems.append(
                    f"filter {filt!r} occurs in {pkg}'s code, but matches no test path "
                    f"in a test binary this run executes there "
                    f"({'it runs ' + ', '.join(ran) if ran else 'it runs none'}"
                    f"{', matched --exact' if inv['exact'] else ''})"
                )
    return problems


def _judge_selection(inv: dict, existing: list[tuple[str, Path]], ws: _Workspace) -> list[str]:
    """Why this invocation's `--test` selectors and filters select nothing."""
    problems, running = _judge_targets(inv, existing, ws)
    if inv["filters"]:
        problems.extend(_judge_filters(inv, existing, running, ws))
    return problems


def resolve(root: Path, entries: list[dict]) -> list[dict]:
    ws = _Workspace(root)
    results: list[dict] = []
    for entry in entries:
        cmd = entry["cmd"]
        try:
            tokens = shlex.split(cmd)
        except ValueError as exc:
            results.append({**entry, "verdict": "SKIP", "why": f"unlexable: {exc}"})
            continue
        if len(tokens) < 2:
            results.append({**entry, "verdict": "SKIP", "why": "truncated"})
            continue
        args = test_args(tokens)
        bare = bare_glob_words(cmd)
        # A disagreement with shlex leaves the quoting unknown; `None` makes
        # every pattern a "shell-glob", judged by name as before (fail-closed).
        bare_args = bare[len(tokens) - len(args) :] if len(bare) == len(tokens) else None
        try:
            inv = parse_invocation(args, bare_args)
        except NotACommand as exc:
            results.append({**entry, "verdict": "SKIP", "why": f"prose: {exc}"})
            continue
        except Unresolvable as exc:
            results.append({**entry, "verdict": "SKIP", "why": str(exc)})
            continue
        if not inv["filters"] and not inv["targets"]:
            results.append({**entry, "verdict": "OK", "why": "selects whole targets"})
            continue
        if not inv["packages"]:
            results.append({**entry, "verdict": "SKIP", "why": "no -p: package set is the workspace default"})
            continue
        problems: list[str] = []
        existing: list[tuple[str, Path]] = []
        for pkg in inv["packages"]:
            crate = ws.packages.get(pkg)
            if crate is None:
                problems.append(
                    f"-p {pkg} is not a package in this workspace "
                    f"(nothing would build, let alone run)"
                )
                continue
            existing.append((pkg, crate))
        if existing:
            problems.extend(_judge_selection(inv, existing, ws))
        if problems:
            results.append({**entry, "verdict": "VACUOUS", "why": "; ".join(problems)})
        else:
            results.append({**entry, "verdict": "OK", "why": "resolves"})
    return results


def run(root: Path, listing: bool = False) -> int:
    source = _rust_modules().rust_cfg().host_source()
    if not source.endswith("--print cfg"):  # no compiler answered: say what decided `cfg(unix)` here
        print(f"note: no trustc/rustc answered `--print cfg`; platform cfgs decided from {source}", file=sys.stderr)
    script_code_only = _load_script_code_only(root)
    results = resolve(root, collect(root, script_code_only))
    bad = [r for r in results if r["verdict"] == "VACUOUS"]
    counts: dict[str, int] = {}
    for r in results:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    if listing:
        for r in sorted(results, key=lambda r: (r["verdict"], r["site"])):
            print(f"{r['verdict']:<11} {r['site']}")
            print(f"            {r['cmd'][:140]}")
            print(f"            {r['why'][:200]}")
    for r in bad:
        print(f"VACUOUS CARGO TEST: {r['site']}", file=sys.stderr)
        print(f"  {r['cmd'][:200]}", file=sys.stderr)
        print(f"  {r['why']}", file=sys.stderr)
    summary = " ".join(f"{k.lower()}={v}" for k, v in sorted(counts.items()))
    print(f"CARGO_TEST_SELECTORS={'fail' if bad else 'ok'} sites={len(results)} {summary}")
    if bad:
        print(
            "A zero-match `targo --unverified test` exits 0. Point the filter at the crate that "
            "owns the test, or delete the invocation.",
            file=sys.stderr,
        )
    return 1 if bad else 0


# ---------------------------------------------------------------------------
# self-test
# ---------------------------------------------------------------------------

_MANIFEST = 'name = "{name}"\nversion = "0.1.0"\n'
_LIB = """
//! axiom_refutation_gate lives in another crate entirely.
mod real_module {
    #[test]
    fn real_test_fn() {
        assert_eq!("axiom_refutation_gate", "axiom_refutation_gate");
    }
}
"""


def _mktree(tmp: Path, commands: list[str], py_commands: list[str] | None = None) -> Path:
    """A synthetic repo: one crate, one gate script, the real runner roots.

    The root FILENAMES come from `_runner_roots()`, not from literals here, for
    the reason the module header gives: a `scripts/<x>.sh` string in this file's
    code is read as a CALL by check_gate_registry.py's R3 scan, and a fixture
    that writes a fake local_gate.sh would mint a runner edge that does not
    exist. Deriving them also keeps the fixture honest -- if the set of runner
    roots changes, the fixture changes with it instead of testing a stale shape.
    """
    roots = _runner_roots(REPO_ROOT)
    root = tmp / "tree"
    (root / "scripts").mkdir(parents=True, exist_ok=True)
    (root / "data").mkdir(parents=True, exist_ok=True)
    crate = root / "crates" / "demo"
    (crate / "src").mkdir(parents=True, exist_ok=True)
    (crate / "tests").mkdir(parents=True, exist_ok=True)
    (crate / "Cargo.toml").write_text(
        _MANIFEST.format(name="demo")
        + '\n[[test]]\nname = "harnessless_target"\nharness = false\n'
    )
    (crate / "src" / "lib.rs").write_text(_LIB)
    (crate / "tests" / "present_target.rs").write_text("#[test]\nfn t() {}\n")
    # 2026-09-15 fixtures for the EMPTINESS rule. A target that exists and
    # declares nothing exits 0 having run nothing, which the name check above
    # cannot see; the other three pin the cases where refusing would be wrong.
    (crate / "tests" / "empty_target.rs").write_text(
        "// a target whose tests were all deleted\nfn helper() {}\n"
    )
    (crate / "tests" / "commented_target.rs").write_text(
        '// #[test]\n// fn gone() {}\nconst S: &str = "#[test]";\nfn helper() {}\n'
    )
    (crate / "tests" / "harnessless_target.rs").write_text("fn main() {}\n")
    (crate / "tests" / "spliced_target.rs").write_text('include!("spliced_cases.rs");\n')
    (crate / "tests" / "spliced_cases.rs").write_text("#[test]\nfn spliced() {}\n")
    # 2026-10-28: a SECOND package, for the several-`-p` rules. It owns a target
    # and a test fn `demo` lacks, and an `empty_target` namesake that does run a
    # test -- so `demo`'s empty one is refused on its own account, not rescued.
    other = root / "crates" / "other"
    (other / "src").mkdir(parents=True, exist_ok=True)
    (other / "tests").mkdir(parents=True, exist_ok=True)
    (other / "Cargo.toml").write_text(_MANIFEST.format(name="other"))
    (other / "tests" / "other_target.rs").write_text("#[test]\nfn other_target_works() {}\n")
    (other / "tests" / "empty_target.rs").write_text("#[test]\nfn not_empty_here() {}\n")
    # 2026-11-01: what ONE test binary compiles. `other`'s lib reaches a test
    # through each module form rustc resolves -- a file module, one declared
    # inside an inline module, a `#[path]` and a `mod.rs` -- and its src/ also
    # holds files the lib does NOT compile: an undeclared one, a module of the
    # bin, and two decoys at the paths a resolver that ignored the inline
    # module or the `#[path]` would load instead.
    for rel, body in {
        "src/lib.rs": "mod other_module {\n    #[test]\n    fn other_test_fn() {}\n}\n"
        "mod deep;\nmod outer {\n    mod inner;\n}\n"
        '#[path = "custom/place.rs"]\nmod placed;\nmod dirmod;\n'
        'mod incl_host {\n    include!("incl_body.rs");\n}\n'
        "fn block_host() {\n    #[test]\n    fn block_test_fn() {}\n}\n"
        "macro_rules! never_invoked {\n    () => {\n        #[test]\n        fn macro_test_fn() {}\n    };\n}\n",
        "src/deep.rs": "#[test]\nfn deep_test_fn() {}\n",
        "src/outer/inner.rs": "#[test]\nfn inner_test_fn() {}\n",
        "src/custom/place.rs": "#[test]\nfn placed_test_fn() {}\n",
        "src/dirmod/mod.rs": "mod leaf;\n",
        "src/dirmod/leaf.rs": "#[test]\nfn leaf_test_fn() {}\n",
        "src/orphan.rs": "#[test]\nfn orphan_test_fn() {}\n",
        "src/main.rs": "mod cli;\nfn main() {}\n",
        "src/cli.rs": "#[test]\nfn cli_test_fn() {}\n",
        "src/inner.rs": "#[test]\nfn misplaced_test_fn() {}\n",
        "src/placed.rs": "#[test]\nfn decoy_placed_test_fn() {}\n",
        "tests/stemmed.rs": "#[test]\nfn unrelated_name() {}\n",
        "src/incl_body.rs": "#[test]\nfn included_test_fn() {}\n",
    }.items():
        (other / rel).parent.mkdir(parents=True, exist_ok=True)
        (other / rel).write_text(body)
    # A package with no lib; one that is `autotests = false` with a test file it
    # never declares; one whose declared target takes another file's path.
    pkg_files = {
        "binonly": (_MANIFEST.format(name="binonly"),
                    {"src/main.rs": "fn main() {}\n#[test]\nfn bin_only_test() {}\n"}),
        "noauto": ('[package]\nname = "noauto"\nversion = "0.1.0"\nautotests = false\n\n'
                   '[[test]]\nname = "noauto_empty"\npath = "tests/noauto_empty.rs"\n',
                   {"src/lib.rs": "", "tests/noauto_empty.rs": "fn helper() {}\n",
                    "tests/noauto_other.rs": "#[test]\nfn noauto_other_works() {}\n"}),
        "claimed": ('[package]\nname = "claimed"\nversion = "0.1.0"\n\n'
                    '[[test]]\nname = "x_named"\npath = "tests/y_file.rs"\n',
                    {"src/lib.rs": "", "tests/y_file.rs": "#[test]\nfn y_file_works() {}\n",
                     "tests/x_named.rs": "fn helper() {}\n"}),
    }
    # 2026-11-01 review: the emptiness rule reads the target through scripts/rust_modules.py.
    # Each is checked with rustc (`--test` dep-info and `--list`): the first five list no test, the
    # rest list one (feature_gated with --cfg 'feature="slow"'); `hollow_parts/` is no target.
    pkg_files["hollow"] = (_MANIFEST.format(name="hollow"), {"src/lib.rs": "", **{
        f"tests/{rel}": body for rel, body in {
            "in_fn_body.rs": "fn host() {\n    #[test]\n    fn inner() {}\n}\n",
            "in_macro.rs": "macro_rules! never {\n    () => {\n        #[test]\n        fn t() {}\n    };\n}\n",
            "cfg_off.rs": "#[cfg(any())]\n#[test]\nfn t() {}\n",
            "macro_include.rs": 'macro_rules! never {\n    () => {\n        include!("hollow_parts/cases.rs");\n'
                                "    };\n}\n",
            "hollow_parts/cases.rs": "#[test]\nfn t() {}\n",
            "dir_target/main.rs": "fn main_helper() {}\n",
            "dir_target/stray.rs": "#[test]\nfn t() {}\n",
            "aggregated.rs": '#[path = "hollow_parts/agg_a.rs"]\nmod agg_a;\n',
            "hollow_parts/agg_a.rs": "#[test]\nfn t() {}\n",
            "passthrough.rs": "macro_rules! pass {\n    ($($t:tt)*) => { $($t)* };\n}\npass! {\n    #[test]\n"
                              "    fn t() {}\n}\n",
            "feature_gated.rs": '#![cfg(feature = "slow")]\n#[test]\nfn t() {}\n',
            "invoked_macro.rs": "macro_rules! gen {\n    ($n:ident) => {\n        #[test]\n        fn $n() {}\n"
                                "    };\n}\ngen!(made);\n",
        }.items()}})
    for name, (manifest, files) in pkg_files.items():
        d = root / "crates" / name
        for rel, body in files.items():
            (d / rel).parent.mkdir(parents=True, exist_ok=True)
            (d / rel).write_text(body)
        (d / "Cargo.toml").write_text(manifest)
    gate_rel = "scripts/demo_gate.sh"
    body = "#!/bin/sh\n" + "".join(f"{c}\n" for c in commands)
    (root / gate_rel).write_text(body)
    py_root = next((r for r in roots if r.endswith(".py")), None)
    for rel in roots:
        f = root / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        if rel == py_root:
            f.write_text('"""doc"""\n' + "".join(f"{c}\n" for c in (py_commands or [])))
        else:
            f.write_text("#!/bin/sh\ntrue\n")
    (root / REGISTRY_REL).write_text(
        json.dumps(
            {
                "rows": [
                    {
                        "id": "demo_gate",
                        "path": gate_rel,
                        "kind": "gate",
                        "claims": "hygiene",
                        "wired_by": list(roots[:1]),
                        "demonstrated": None,
                        "waiver": None,
                    }
                ]
            }
        )
    )
    return root


def _results_local(root: Path) -> dict[str, tuple[str, str]]:
    """Resolve against the SYNTHETIC tree, not the repo: cmd -> (verdict, why)."""
    script_code_only = _load_script_code_only(REPO_ROOT)
    results = resolve(root, collect(root, script_code_only))
    return {r["cmd"]: (r["verdict"], r["why"]) for r in results}


def _verdicts_local(root: Path) -> dict[str, str]:
    """Resolve against the SYNTHETIC tree, not the repo."""
    return {cmd: verdict for cmd, (verdict, _) in _results_local(root).items()}


# 2026-10-28 fixtures for the several-`-p` and glob rules (module docstring),
# and 2026-11-01 ones for the review of that change. Each row is (name, cmd,
# verdict, needles...). The OK rows are false reds: each is VACUOUS on the
# checker before 2026-10-28, which judged every `-p` alone and took a glob for
# a target name. The VACUOUS rows are guards: each still refuses, for the
# reason given, so no relaxation can pass for "accept anything with a second
# package", "accept any glob", "accept a filter found anywhere in a package" or
# "accept a file cargo builds into no target".
_T = "targo --unverified test --locked"
_MULTI_AND_GLOB_ARMS: list[tuple[str, str, str, tuple[str, ...]]] = [
    # -- the two false reds, each measured against cargo ----------------------
    ("a --test target owned by ONE of several -p packages resolves",
     f"{_T} -p demo -p other --test other_target", "OK", ()),
    ("a filter that resolves in ONE of several --lib packages resolves",
     f"{_T} -p demo -p other --lib -- other_test_fn", "OK", ()),
    ("a quoted --test '*' is cargo's glob, and it matches targets",
     f"{_T} -p other --test '*'", "OK", ()),
    ("a quoted --test 'present*' matches present_target",
     f"{_T} -p demo --test 'present*'", "OK", ()),
    ("a glob matching only in the SECOND -p package resolves",
     f"{_T} -p demo -p other --test 'other*'", "OK", ()),
    ("a glob over a harness = false target is exempt, as its name is",
     f"{_T} -p demo --test 'harnessless*'", "OK", ()),
    # -- one test binary: the filter must be IN a binary this run executes ----
    ("a filter in a --test target this run executes resolves",
     f"{_T} -p demo -p other --test other_target -- other_target_works", "OK", ()),
    ("a filter in a file module of a running lib resolves",
     f"{_T} -p demo -p other --lib -- deep_test_fn", "OK", ()),
    ("...in a file declared inside an inline module (src/outer/inner.rs)",
     f"{_T} -p demo -p other --lib -- inner_test_fn", "OK", ()),
    ("...in a file loaded through #[path]",
     f"{_T} -p demo -p other --lib -- placed_test_fn", "OK", ()),
    ("...in a child of a mod.rs, which lives beside it",
     f"{_T} -p demo -p other --lib -- leaf_test_fn", "OK", ()),
    ("an --exact filter that IS the test's path resolves",
     f"{_T} -p demo -p other --lib -- other_module::other_test_fn --exact", "OK", ()),
    ("a filter is matched to the test's whole PATH, as libtest matches it",
     f"{_T} -p demo -p other --lib -- outer::inner::inner_test_fn", "OK", ()),
    ("...a path prefix through a mod.rs child selects its tests",
     f"{_T} -p demo -p other --lib -- dirmod::leaf", "OK", ()),
    ("...a #[path] module takes its DECLARED name, under --exact too",
     f"{_T} -p demo -p other --lib -- placed::placed_test_fn --exact", "OK", ()),
    ("...an include!d test takes the module path in force where it is spliced",
     f"{_T} -p demo -p other --lib -- incl_host::included_test_fn", "OK", ()),
    ("a declared [[test]] path is read before a stray tests/<name>.rs",
     f"{_T} -p claimed --test x_named", "OK", ()),
    ("--test=NAME is a selector, and an existing one resolves",
     f"{_T} -p demo --test=present_target", "OK", ()),
    # -- the guards -------------------------------------------------------------
    ("a --test name NO selected package has is still VACUOUS, naming each",
     f"{_T} -p demo -p other --test absent_target", "VACUOUS",
     ("integration target of demo", "integration target of other")),
    ("a filter NO selected package has is still VACUOUS",
     f"{_T} -p demo -p other --lib -- absent_test_fn", "VACUOUS",
     ("in demo's CODE", "in other's CODE")),
    ("a filter whose `::` segments are split across two packages is VACUOUS",
     f"{_T} -p demo -p other --lib -- real_module::other_test_fn", "VACUOUS",
     ("segment 'other_test_fn' matches no module and no #[test] fn in demo's",
      "segment 'real_module' matches no module and no #[test] fn in other's")),
    ("a filter found only in a package that runs no binary here is VACUOUS",
     f"{_T} -p demo -p other --test other_target -- real_test_fn", "VACUOUS",
     ("occurs in demo's code, but matches no test path in a test binary this run "
      "executes there (it runs none)",)),
    ("a lib's test filter is VACUOUS when only integration targets run",
     f"{_T} -p demo -p other --test present_target --test other_target -- other_test_fn",
     "VACUOUS", ("occurs in other's code", "(it runs --test other_target)")),
    ("an integration target's test filter is VACUOUS when only libs run",
     f"{_T} -p demo -p other --lib -- other_target_works", "VACUOUS",
     ("occurs in other's code", "(it runs its lib)")),
    ("...and a tests/ FILE STEM alone does not rescue it",
     f"{_T} -p demo -p other --lib -- other_target", "VACUOUS", ("(it runs its lib)",)),
    ("...nor, inside the binary that runs, does the target's own file stem",
     f"{_T} -p demo -p other --test stemmed -- stemmed", "VACUOUS",
     ("occurs in other's code", "(it runs --test stemmed)")),
    ("--lib on a package with no lib runs none of it",
     f"{_T} -p binonly -p other --lib -- bin_only_test", "VACUOUS",
     ("occurs in binonly's code", "(it runs none)")),
    ("segments split across two binaries of ONE package are VACUOUS",
     f"{_T} -p demo -p other --lib -- other_module::other_target_works", "VACUOUS",
     ("occurs in other's code", "(it runs its lib)")),
    ("segments in the WRONG ORDER match no test path, though each name exists",
     f"{_T} -p demo -p other --lib -- other_test_fn::other_module", "VACUOUS",
     ("occurs in other's code", "matches no test path", "(it runs its lib)")),
    ("...nor do segments from two different modules of one binary",
     f"{_T} -p demo -p other --lib -- outer::deep_test_fn", "VACUOUS",
     ("occurs in other's code", "matches no test path", "(it runs its lib)")),
    ("a substring under --exact matches no test path",
     f"{_T} -p demo -p other --lib -- other_test --exact", "VACUOUS", ("matched --exact",)),
    ("a src/ file the lib never declares is not in the lib",
     f"{_T} -p demo -p other --lib -- orphan_test_fn", "VACUOUS", ("(it runs its lib)",)),
    ("a module of the BIN is not in the lib",
     f"{_T} -p demo -p other --lib -- cli_test_fn", "VACUOUS", ("(it runs its lib)",)),
    ("an inline module's `mod inner;` is not src/inner.rs",
     f"{_T} -p demo -p other --lib -- misplaced_test_fn", "VACUOUS", ("(it runs its lib)",)),
    ("a #[path] module is not the file its name would give",
     f"{_T} -p demo -p other --lib -- decoy_placed_test_fn", "VACUOUS", ("(it runs its lib)",)),
    # 2026-11-01: the tests libtest can NAME, read by scripts/rust_modules.py. rustc
    # warns "cannot test inner items" for the first; `--list` has neither.
    ("a #[test] fn inside a fn body is no test libtest runs",
     f"{_T} -p demo -p other --lib -- block_test_fn", "VACUOUS",
     ("occurs in other's code", "matches no test path", "(it runs its lib)")),
    ("...nor is one in a macro body nobody invokes",
     f"{_T} -p demo -p other --lib -- macro_test_fn", "VACUOUS",
     ("occurs in other's code", "matches no test path", "(it runs its lib)")),
    ("a glob that matches NOTHING is VACUOUS, as a glob",
     f"{_T} -p demo --test 'zz*'", "VACUOUS", ("is a glob that matches no",)),
    ("...and with several packages, naming each",
     f"{_T} -p demo -p other --test 'zz*'", "VACUOUS",
     ("is a glob that matches no integration target of demo, other",)),
    ("a glob matching ONLY targets that declare no test is VACUOUS",
     f"{_T} -p demo --test '[ce][om]*_target'", "VACUOUS",
     ("selects demo/commented_target, demo/empty_target, which declare ZERO",)),
    ("a glob matching an empty target BESIDE a full one is VACUOUS, as both names are",
     f"{_T} -p demo --test '[ep]*_target'", "VACUOUS",
     ("selects demo/empty_target, which declares ZERO",)),
    ("...across several packages too",
     f"{_T} -p demo -p other --test 'empty_targe[t]'", "VACUOUS",
     ("selects demo/empty_target, which declares ZERO",)),
    ("...and '*' over a package holding emptied targets names them",
     f"{_T} -p demo --test '*'", "VACUOUS",
     ("demo/commented_target, demo/empty_target",)),
    ("an empty target is refused although a namesake in another -p runs",
     f"{_T} -p demo -p other --test empty_target", "VACUOUS",
     ("--test empty_target of demo exists but declares ZERO",)),
    ("an UNQUOTED shell glob is judged by name, not as cargo's pattern",
     f"{_T} -p demo --test present*", "VACUOUS", ("UNQUOTED glob",)),
    ("under autotests = false an undeclared tests/ file is no target",
     f"{_T} -p noauto --test noauto_other", "VACUOUS",
     ("is not an integration target of noauto", "builds it into no target")),
    ("...and a glob matching only that file matches nothing",
     f"{_T} -p noauto --test 'noauto_o*'", "VACUOUS",
     ("is a glob that matches no integration target of noauto",)),
    ("a tests/ file whose path a declared target took is no target of its own",
     f"{_T} -p claimed --test y_file", "VACUOUS",
     ("is not an integration target of claimed", "builds it into no target")),
    ("--test=NAME is judged: a missing one is VACUOUS",
     f"{_T} -p demo --test=absent_target", "VACUOUS",
     ("--test absent_target is not an integration target of demo",)),
    ("--test='GLOB' is judged as cargo's glob",
     f"{_T} -p demo --test='zz*'", "VACUOUS", ("is a glob that matches no",)),
]
# 2026-11-01 review: the emptiness rule, read through scripts/rust_modules.py (`hollow` in `_mktree`).
# The VACUOUS rows each passed as OK on the rule before it (its own scan named a test there); the
# first OK row was VACUOUS on it (it never followed a `mod`). rustc lists no test in the first five.
_EMPTINESS_ARMS: list[tuple[str, str, str, tuple[str, ...]]] = [
    ("a #[test] fn in a fn body leaves the target empty (rustc: \"cannot test inner items\")",
     f"{_T} -p hollow --test in_fn_body", "VACUOUS", ("--test in_fn_body of hollow exists but declares ZERO",)),
    ("...as does one in a macro_rules! body nobody invokes",
     f"{_T} -p hollow --test in_macro", "VACUOUS", ("--test in_macro of hollow exists but declares ZERO",)),
    ("...one under #[cfg(any())]",
     f"{_T} -p hollow --test cfg_off", "VACUOUS", ("--test cfg_off of hollow exists but declares ZERO",)),
    ("...a file only an uninvoked macro include!s",
     f"{_T} -p hollow --test macro_include", "VACUOUS", ("--test macro_include of hollow exists but declares ZERO",)),
    ("...and a stray file beside a directory target's main.rs that no `mod` loads",
     f"{_T} -p hollow --test dir_target", "VACUOUS", ("--test dir_target of hollow exists but declares ZERO",)),
    ("a target holding its tests through #[path] mod is not empty (rustc --list: agg_a::t)",
     f"{_T} -p hollow --test aggregated", "OK", ()),
    ("a test in an item-level macro call's tokens may be written there: not refused (rustc --list: t)",
     f"{_T} -p hollow --test passthrough", "OK", ()),
    ("a test behind an undecided #![cfg(feature)] may run: not refused (rustc --list with it: t)",
     f"{_T} -p hollow --test feature_gated", "OK", ()),
    ("a test an invoked macro_rules! body writes is not refused (rustc --list: made)",
     f"{_T} -p hollow --test invoked_macro", "OK", ()),
]
_MULTI_AND_GLOB_CMDS = [cmd for _, cmd, _, _ in _MULTI_AND_GLOB_ARMS + _EMPTINESS_ARMS]


def _multi_and_glob_arms(arm, r: dict[str, tuple[str, str]]) -> None:
    for name, cmd, verdict, needles in _MULTI_AND_GLOB_ARMS + _EMPTINESS_ARMS:
        got = r.get(cmd)
        ok = got is not None and got[0] == verdict and all(n in got[1] for n in needles)
        arm(name, ok, got)
    # The argv form has no shell, so its glob reaches cargo unexpanded.
    got = r.get(f"{_T} -p demo --test 'spliced_*'")
    arm("an argv-list glob reaches cargo unexpanded (no shell) and resolves",
        got is not None and got[0] == "OK", got)


# 2026-11-01: the four holes measured in this gate's own module walk before it
# became scripts/rust_modules.py, each an EXACT answer for a crate rooted at
# agg.rs (`rel` holds one `#[test] fn t`; `rel=body`; `file=path`, `-` for a
# file libtest can name nothing in). Each answer was checked on the same tree
# with rustc: `trustc --edition 2021 --test --emit=dep-info` lists the files,
# the built binary's `--list --format=terse` the test paths. Each FAILS on the
# walk this gate had at beee22498, which answered x.rs=x in all four.
_MODULE_TREE_ARMS = [
    ("a `mod` in a macro body nobody invokes is not compiled (dep-info: agg.rs; --list: top)",
     ("agg.rs=macro_rules! m { () => { mod x; } }\n#[test]\nfn top() {}\n", "x.rs"), "agg.rs="),
    ("`#[cfg_attr(all(), path = \"y.rs\")] mod x;` never loads x.rs (dep-info: agg.rs y.rs; --list: x::t); "
     "the walk takes neither",
     ('agg.rs=#[cfg_attr(all(), path = "y.rs")]\nmod x;\n', "x.rs", "y.rs"), "agg.rs="),
    ("a #[path] mod in a fn body is compiled with no path libtest can name (dep-info: agg.rs x.rs; --list: top)",
     ('agg.rs=fn f() {\n    #[path = "x.rs"]\n    mod x;\n}\n#[test]\nfn top() {}\n', "x.rs"), "agg.rs= x.rs=-"),
    ("x.rs beside x/mod.rs is E0761 (dep-info: agg.rs; the crate does not build)",
     ("agg.rs=mod x;\n", "x.rs", "x/mod.rs"), "agg.rs="),
]


def _module_tree_arms(arm) -> None:
    for label, files, want in _MODULE_TREE_ARMS:
        with tempfile.TemporaryDirectory() as td:
            crate = Path(td)
            for f in files:
                rel, eq, body = f.partition("=")
                (crate / rel).parent.mkdir(parents=True, exist_ok=True)
                (crate / rel).write_text(body if eq else "#[test]\nfn t() {}\n")
            real = crate.resolve()
            got = {(str(f.relative_to(real)), path) for f, path in module_tree(crate, crate / "agg.rs")}
            exp = {(r, None if path == "-" else path) for r, _, path in (i.partition("=") for i in want.split())}
            arm(f"module_tree: {label}", got == exp, f"got {sorted(got, key=str)}")


def selftest(verbose: bool = True) -> int:
    passed = failed = 0

    def arm(name: str, ok: bool, detail: str = "") -> None:
        nonlocal passed, failed
        if ok:
            passed += 1
            if verbose:
                print(f"  ok   {name}")
        else:
            failed += 1
            print(f"  FAIL {name} {detail}")

    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        cmds = [
            "targo --unverified test --locked -p demo --lib -- real_module",
            "targo --unverified test --locked -p demo --lib -- real_test_fn",
            "targo --unverified test --locked -p demo --lib -- axiom_refutation_gate",
            "targo --unverified test --locked -p demo --test present_target",
            "targo --unverified test --locked -p demo --test absent_target",
            "targo --unverified test --locked -p demo --test empty_target",
            "targo --unverified test --locked -p demo --test commented_target",
            "targo --unverified test --locked -p demo --test harnessless_target",
            "targo --unverified test --locked -p demo --test spliced_target",
            "targo --unverified test --locked -p not_a_package --lib -- real_module",
            'targo --unverified test --locked -p demo --lib -- "$FILTER"',
            "targo --unverified test --locked -p demo --lib AND (if a native shard exists",
            "targo --unverified test --locked -p demo",
            "targo --unverified test --locked -p demo --lib -- real_module::real_test_fn",
            # Every other driver spelling SHELL_CARGO_RE claims to know, each
            # pointed at a missing target so recognition shows as VACUOUS.
            "targo trust test --locked -p demo --test absent_trust_target",
            "cargo test --locked -p demo --test absent_stock_target",
            "cargo +trust test --locked -p demo --test absent_channel_target",
        ] + _MULTI_AND_GLOB_CMDS
        py = [
            'ARGV = ["targo", "--unverified", "test", "--locked", "-p", "demo", "--lib", "--", "axiom_refutation_gate"]',
            'STOCK = ["cargo", "test", "--locked", "-p", "demo", "--test", "absent_argv_target"]',
            'GLOB = ["targo", "--unverified", "test", "--locked", "-p", "demo", "--test", "spliced_*"]',
        ]
        root = _mktree(tmp, cmds, py)
        v = _verdicts_local(root)

        arm("a module name resolves", v.get("targo --unverified test --locked -p demo --lib -- real_module") == "OK", v)
        arm("a #[test] fn name resolves", v.get("targo --unverified test --locked -p demo --lib -- real_test_fn") == "OK", v)
        arm(
            "THE BUG: a filter present only in a COMMENT and a STRING is VACUOUS",
            v.get("targo --unverified test --locked -p demo --lib -- axiom_refutation_gate") == "VACUOUS",
            v,
        )
        arm("an existing --test target resolves", v.get("targo --unverified test --locked -p demo --test present_target") == "OK", v)
        arm("a missing --test target is VACUOUS", v.get("targo --unverified test --locked -p demo --test absent_target") == "VACUOUS", v)
        # THE OTHER DIRECTION OF THE SAME HOLE (2026-09-15): the name check
        # asks only whether a source file exists. A target that EXISTS and
        # declares nothing exits 0 having run nothing -- the same vacuous
        # green, reached from the other side.
        arm(
            "a --test target that exists but declares NO test is VACUOUS",
            v.get("targo --unverified test --locked -p demo --test empty_target") == "VACUOUS",
            v,
        )
        arm(
            "...and a #[test] that survives only in a COMMENT or a STRING does not save it",
            v.get("targo --unverified test --locked -p demo --test commented_target") == "VACUOUS",
            v,
        )
        # The two shapes where refusing WOULD be wrong. Without these the rule
        # passes for one that reds every integration target it is shown.
        arm(
            "a harness = false target is exempt (it has a main, not tests)",
            v.get("targo --unverified test --locked -p demo --test harnessless_target") == "OK",
            v,
        )
        arm(
            "a target whose tests arrive through include!() is NOT empty",
            v.get("targo --unverified test --locked -p demo --test spliced_target") == "OK",
            v,
        )
        arm(
            "an unknown package is VACUOUS",
            v.get("targo --unverified test --locked -p not_a_package --lib -- real_module") == "VACUOUS",
            v,
        )
        arm("a dynamic filter is skipped, not guessed", v.get('targo --unverified test --locked -p demo --lib -- "$FILTER"') == "SKIP", v)
        arm(
            "prose that mentions targo --unverified test is skipped, not refused",
            v.get("targo --unverified test --locked -p demo --lib AND (if a native shard exists") == "SKIP",
            v,
        )
        arm("an unfiltered invocation is OK", v.get("targo --unverified test --locked -p demo") == "OK", v)
        arm(
            "every `::` segment is required",
            v.get("targo --unverified test --locked -p demo --lib -- real_module::real_test_fn") == "OK",
            v,
        )
        argv_cmd = "targo --unverified test --locked -p demo --lib -- axiom_refutation_gate"
        arm(
            "a Python argv list is parsed like a shell command",
            sum(1 for k, val in v.items() if k == argv_cmd and val == "VACUOUS") >= 1,
            v,
        )
        # The legacy and verified spellings are JUDGED, not skipped: were the
        # recognition of any of them dropped, its site would vanish from `v`.
        for spelled in (
            "targo trust test --locked -p demo --test absent_trust_target",
            "cargo test --locked -p demo --test absent_stock_target",
            "cargo +trust test --locked -p demo --test absent_channel_target",
            "cargo test --locked -p demo --test absent_argv_target",
        ):
            arm(f"`{spelled.split(' --locked')[0]}` is judged ({spelled.split()[-1]})",
                v.get(spelled) == "VACUOUS", v)

        _multi_and_glob_arms(arm, _results_local(root))
        _module_tree_arms(arm)
        try:
            walk_arms = _rust_modules().selftest()
            arm(f"the module walk's own {walk_arms} arms (scripts/rust_modules_arms.py) hold", True)
        except SystemExit as exc:
            arm("the module walk's own arms (scripts/rust_modules_arms.py) hold", False, str(exc))

        # ANTI-CORRELATION: the comment/string mentions must not rescue it. Same
        # tree, with the filter present as real code -- it must flip to OK.
        crate = root / "crates" / "demo" / "src" / "lib.rs"
        crate.write_text(_LIB + "\nmod axiom_refutation_gate {\n    #[test]\n    fn t() {}\n}\n")
        v2 = _verdicts_local(root)
        arm(
            "the same filter resolves once it is CODE (the arm is not always-red)",
            v2.get("targo --unverified test --locked -p demo --lib -- axiom_refutation_gate") == "OK",
            v2,
        )

    if verbose or failed:
        print(
            f"CARGO_TEST_SELECTORS_SELFTEST arms={passed + failed} "
            f"passed={passed} failed={failed}"
        )
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    if "--pinned-inputs" in argv:  # runs nothing; this script is the row's script_sha256
        print(*(p.as_posix() for p in (*_rust_modules().PINNED_INPUTS, _REGISTRY_SCRIPT)), sep="\n")
        return 0
    if "--selftest" in argv:
        return selftest()
    rc = selftest(verbose=False)
    if rc != 0:
        print("refusing to report: the checker's own self-test failed", file=sys.stderr)
        return 2
    return run(REPO_ROOT, listing="--list" in argv)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
