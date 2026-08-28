#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""A `cargo test` filter that selects ZERO tests must never be a green gate.

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
Every `cargo test` invocation on the ENFORCEMENT SURFACE -- the four runner
roots, every `gate`-row script the registry names, and every `demonstrated.ref`
the registry cites -- is resolved statically against the workspace source. An
invocation is REFUSED when it provably selects nothing:

  * `-p <pkg>` names a package that is not in this workspace;
  * `--test <target>` names an integration target with no source file;
  * a positional filter has a `::` segment that matches no module name and no
    `#[test]` function name anywhere in the package's own source.

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
Resolution is per PACKAGE, not per target: a filter naming a module that exists
in the crate's `tests/` while the invocation says `--lib` still resolves. That
is deliberate -- an over-approximation inside the right crate cannot produce a
false RED, and the class this gate exists for is the filter aimed at the WRONG
CRATE ENTIRELY. It is also static: a filter whose tests are all behind an
inactive `#[cfg(feature = ...)]` resolves here and still selects nothing at run
time. The runtime half of the property belongs to whoever runs the command;
`verify_runner.py`'s count check is that half for the suite.

Exit codes: 0 all resolvable, 1 a vacuous invocation, 2 self-test failure.

Usage:
    python3 scripts/check_cargo_test_selectors.py
    python3 scripts/check_cargo_test_selectors.py --list
    python3 scripts/check_cargo_test_selectors.py --selftest
"""

from __future__ import annotations

import ast
import importlib.util
import json
import re
import shlex
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
REGISTRY_REL = "data/gate_registry.json"

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


def _load_stripper(root: Path):
    """`strip_noncode` from scripts/check_add_decl_ratchet.py.

    Importing it is the point: the registry's own notes record a lane spent
    consolidating clean-auto onto ONE lexer copy after two duplicates drifted
    apart. A gate that lexes Rust in this repo uses the reference stripper.
    """
    ref = root / "scripts" / "check_add_decl_ratchet.py"
    spec = importlib.util.spec_from_file_location("_clean_add_decl_ratchet", ref)
    if spec is None or spec.loader is None:  # pragma: no cover - unreachable
        raise SystemExit(f"cannot load the reference lexer at {ref}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.strip_noncode


def _load_script_code_only(root: Path):
    """`script_code_only` from scripts/check_gate_registry.py.

    Same reason. It blanks `#` comments and Python docstrings, which is what
    keeps a `cargo test` line in a usage banner from being read as a call --
    the mention-is-not-an-invocation rule R3 already learned the hard way.
    """
    ref = root / "scripts" / "check_gate_registry.py"
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
        text = strip_noncode(raw)
        names: set[str] = set()
        for m in MOD_RE.finditer(text):
            names.add(m.group(1))
        for m in ATTR_TEST_RE.finditer(text):
            fm = FN_RE.search(text, m.end(), m.end() + 400)
            if fm:
                names.add(fm.group(1))
        for seg in candidates:
            if any(seg in n for n in names):
                found.add(seg)
                todo.discard(seg)
    return found


def integration_targets(crate: Path) -> set[str]:
    """Names cargo will accept for `--test <name>` in this crate."""
    names: set[str] = set()
    tests = crate / "tests"
    if tests.is_dir():
        for entry in tests.iterdir():
            if entry.is_file() and entry.suffix == ".rs":
                names.add(entry.stem)
            elif entry.is_dir() and (entry / "main.rs").is_file():
                names.add(entry.name)
    manifest = (crate / "Cargo.toml").read_text(errors="replace")
    for block in re.split(r"^\[\[test\]\]\s*$", manifest, flags=re.M)[1:]:
        head = re.split(r"^\[", block, flags=re.M)[0]
        m = TEST_NAME_RE.search(head)
        if m:
            names.add(m.group(1))
    return names


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


class NotACommand(Exception):
    """The text matched `cargo test` but is prose, not an invocation."""


class Unresolvable(Exception):
    """A real invocation whose selection cannot be decided statically."""


def parse_invocation(tokens: list[str]) -> dict:
    """Model `cargo test <cargo-args> [-- <libtest-args>]` selection."""
    packages: list[str] = []
    targets: list[tuple[str, str]] = []
    filters: list[str] = []
    lib = False
    broad = False
    after_dd = False
    i = 0
    while i < len(tokens):
        tok = tokens[i]
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
                targets.append((tok[2:], tokens[i + 1]))
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
    }


# Where a shell command ends. `)` closes a subshell or a function body and
# terminates; `(` does NOT, deliberately -- an opening paren mid-command is prose
# ("cargo test -p x --lib AND (if a native shard exists"), and cutting there
# would leave behind a tail of identifier-shaped English that parses as a filter
# list and reads as vacuous. Keeping the paren keeps the token that gives the
# prose away.
CMD_TERMINATOR = re.compile(r"\|\||&&|[|;&><`)]")
SHELL_CARGO_RE = re.compile(r"\bcargo\s+test\b")
ARGV_CARGO_RE = re.compile(r"""["']cargo["']\s*,\s*["']test["']""")


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
    """(lineno, command text) for each shell-form `cargo test` in `text`."""
    for lineno, line in _join_continuations(text):
        for m in SHELL_CARGO_RE.finditer(line):
            rest = line[m.start() :]
            end = CMD_TERMINATOR.search(rest, len("cargo test"))
            cmd = rest[: end.start()] if end else rest
            cmd = re.split(r"\s#", cmd)[0].strip()
            yield lineno, cmd


def argv_commands(text: str):
    """(lineno, command text) for each Python `["cargo", "test", ...]` list."""
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
    ref = root / "scripts" / "check_gate_registry.py"
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
        if isinstance(ref, str) and ref.strip().startswith("cargo test"):
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


def resolve(root: Path, entries: list[dict]) -> list[dict]:
    strip_noncode = _load_stripper(REPO_ROOT)
    packages = package_map(root)
    sel_cache: dict[tuple[str, str], bool] = {}
    tgt_cache: dict[str, set[str]] = {}
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
        try:
            inv = parse_invocation(tokens[2:])
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
        for pkg in inv["packages"]:
            crate = packages.get(pkg)
            if crate is None:
                problems.append(
                    f"-p {pkg} is not a package in this workspace "
                    f"(nothing would build, let alone run)"
                )
                continue
            if pkg not in tgt_cache:
                tgt_cache[pkg] = integration_targets(crate)
            for kind, name in inv["targets"]:
                if kind == "test" and name not in tgt_cache[pkg]:
                    problems.append(
                        f"--test {name} is not an integration target of {pkg} "
                        f"(no crates/{crate.name}/tests/{name}.rs)"
                    )
            wanted = {
                seg
                for filt in inv["filters"]
                for seg in filt.split("::")
                if seg
            }
            unknown = {s for s in wanted if (pkg, s) not in sel_cache}
            if unknown:
                hit = resolve_segments(crate, unknown, strip_noncode)
                for seg in unknown:
                    sel_cache[(pkg, seg)] = seg in hit
            for filt in inv["filters"]:
                for seg in [s for s in filt.split("::") if s]:
                    if not sel_cache[(pkg, seg)]:
                        problems.append(
                            f"filter {filt!r}: segment {seg!r} matches no module and no "
                            f"#[test] fn in {pkg}'s CODE -- this run selects zero tests "
                            f"and libtest reports `0 passed` as ok"
                        )
        if problems:
            results.append({**entry, "verdict": "VACUOUS", "why": "; ".join(problems)})
        else:
            results.append({**entry, "verdict": "OK", "why": "resolves"})
    return results


def run(root: Path, listing: bool = False) -> int:
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
            "A zero-match `cargo test` exits 0. Point the filter at the crate that "
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
    (crate / "Cargo.toml").write_text(_MANIFEST.format(name="demo"))
    (crate / "src" / "lib.rs").write_text(_LIB)
    (crate / "tests" / "present_target.rs").write_text("#[test]\nfn t() {}\n")
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


def _verdicts_local(root: Path) -> dict[str, str]:
    """Resolve against the SYNTHETIC tree, not the repo."""
    script_code_only = _load_script_code_only(REPO_ROOT)
    results = resolve(root, collect(root, script_code_only))
    return {r["cmd"]: r["verdict"] for r in results}


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
            "cargo test --locked -p demo --lib -- real_module",
            "cargo test --locked -p demo --lib -- real_test_fn",
            "cargo test --locked -p demo --lib -- axiom_refutation_gate",
            "cargo test --locked -p demo --test present_target",
            "cargo test --locked -p demo --test absent_target",
            "cargo test --locked -p not_a_package --lib -- real_module",
            'cargo test --locked -p demo --lib -- "$FILTER"',
            "cargo test --locked -p demo --lib AND (if a native shard exists",
            "cargo test --locked -p demo",
            "cargo test --locked -p demo --lib -- real_module::real_test_fn",
        ]
        py = ['ARGV = ["cargo", "test", "--locked", "-p", "demo", "--lib", "--", "axiom_refutation_gate"]']
        root = _mktree(tmp, cmds, py)
        v = _verdicts_local(root)

        arm("a module name resolves", v.get("cargo test --locked -p demo --lib -- real_module") == "OK", v)
        arm("a #[test] fn name resolves", v.get("cargo test --locked -p demo --lib -- real_test_fn") == "OK", v)
        arm(
            "THE BUG: a filter present only in a COMMENT and a STRING is VACUOUS",
            v.get("cargo test --locked -p demo --lib -- axiom_refutation_gate") == "VACUOUS",
            v,
        )
        arm("an existing --test target resolves", v.get("cargo test --locked -p demo --test present_target") == "OK", v)
        arm("a missing --test target is VACUOUS", v.get("cargo test --locked -p demo --test absent_target") == "VACUOUS", v)
        arm(
            "an unknown package is VACUOUS",
            v.get("cargo test --locked -p not_a_package --lib -- real_module") == "VACUOUS",
            v,
        )
        arm("a dynamic filter is skipped, not guessed", v.get('cargo test --locked -p demo --lib -- "$FILTER"') == "SKIP", v)
        arm(
            "prose that mentions cargo test is skipped, not refused",
            v.get("cargo test --locked -p demo --lib AND (if a native shard exists") == "SKIP",
            v,
        )
        arm("an unfiltered invocation is OK", v.get("cargo test --locked -p demo") == "OK", v)
        arm(
            "every `::` segment is required",
            v.get("cargo test --locked -p demo --lib -- real_module::real_test_fn") == "OK",
            v,
        )
        argv_cmd = "cargo test --locked -p demo --lib -- axiom_refutation_gate"
        arm(
            "a Python argv list is parsed like a shell command",
            sum(1 for k, val in v.items() if k == argv_cmd and val == "VACUOUS") >= 1,
            v,
        )

        # ANTI-CORRELATION: the comment/string mentions must not rescue it. Same
        # tree, with the filter present as real code -- it must flip to OK.
        crate = root / "crates" / "demo" / "src" / "lib.rs"
        crate.write_text(_LIB + "\nmod axiom_refutation_gate {\n    #[test]\n    fn t() {}\n}\n")
        v2 = _verdicts_local(root)
        arm(
            "the same filter resolves once it is CODE (the arm is not always-red)",
            v2.get("cargo test --locked -p demo --lib -- axiom_refutation_gate") == "OK",
            v2,
        )

    if verbose or failed:
        print(
            f"CARGO_TEST_SELECTORS_SELFTEST arms={passed + failed} "
            f"passed={passed} failed={failed}"
        )
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    if "--selftest" in argv:
        return selftest()
    rc = selftest(verbose=False)
    if rc != 0:
        print("refusing to report: the checker's own self-test failed", file=sys.stderr)
        return 2
    return run(REPO_ROOT, listing="--list" in argv)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
