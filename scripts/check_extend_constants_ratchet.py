#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed ratchet for the extend_constants_* bulk-import bypass (#4).

extend_constants_unchecked / extend_constants_structural register constants in
bulk, bypassing per-declaration kernel type-checking. This scanner enumerates
every source `.extend_constants_*(` call site under crates/ and asserts each is
accounted for in data/unchecked_decl_ratchet.json (production_sites) and that
the production counts do not exceed the recorded baseline. A NEW, unaccounted
bypass fails the gate — forcing a // SOUNDNESS: comment + an explicit ratchet
entry before it can land.

WHY IT ACCOUNTS PER SITE (2026-08-25, lane LOOSE)
-------------------------------------------------
`production_sites` used to be read as a SET of (file, method) pairs. That is a
BLANKET suppression at FILE granularity — the same shape as the
`test_excluded_sites` skip list retired one layer up the same day, and it was
equally live. MEASURED at 0b3b94e5b:
crates/clean-mathverse/src/cli/per_constant_load.rs carried TWO calls (lines
1762 and 1767) under ONE row that declared no count, so a THIRD would have been
accepted with no entry of its own — bounded only by an aggregate that a
simultaneous removal elsewhere keeps flat. Its own `trust` text already said
"2 call sites"; nothing read it.

Two rules now, both lifted from the sibling scripts/check_add_decl_ratchet.py,
which has capped per site since 2026-08-22:

  * `occurrences` (default 1) CAPS the calls a row covers. More is RED; fewer
    is a NOTE to lower it. A non-positive or unparsable value is REFUSED, not
    read as "unlimited".
  * every accounted call must carry a `// SOUNDNESS:` comment within
    SOUNDNESS_WINDOW (40) lines above it. This gate has ASKED for that comment
    in its remediation text since 2026-06-17 and never checked it, while the
    ratchet file CLAIMED "each production site below carries a // SOUNDNESS:
    comment at its call". At HEAD all seven do; that is now a measurement.

WHY IT LEXES (2026-08-25, lane ANTICORR)
----------------------------------------
Until this change the scanner ran its regex over RAW LINES. It therefore
counted the token wherever it appeared — including inside a `//` comment, a
doc comment, or a string literal. That is the same defect that killed
`prover_phase_0_audit.sh` (see the `retired` list in data/gate_registry.json),
and here it was not merely loose, it was ANTI-CORRELATED with the property the
gate exists to protect, in the most direct way possible: the gate's OWN
remediation text says

    -> add a // SOUNDNESS: comment at the call AND an entry under
       data/unchecked_decl_ratchet.json

and writing that comment — if it quoted the call, which is the natural way to
write it — was itself a new "unaccounted call site". MEASURED 2026-08-25 at
438a64131: a two-line `// SOUNDNESS:` comment planted in
crates/clean-kernel/src/env/snapshot.rs reading

    // SOUNDNESS: this path deliberately does NOT call
    // env.extend_constants_unchecked(decls); every constant is re-checked.

turned this gate RED (`FAIL: unaccounted extend_constants_* bulk-bypass call
site(s): crates/clean-kernel/src/env/snapshot.rs:13`, exit=1) while
scripts/check_add_decl_ratchet.py — the parser-based sibling, on the same tree,
with the same plant — printed `OK` and exit 0. A gate that reddens on the
documentation it demands trains people to delete the documentation.

So the scanner now does what its two siblings
(scripts/check_add_decl_ratchet.py, scripts/check_env_bypass_census.py) already
did:

  * comments (line and block), string/char/raw-string literals are BLANKED
    before matching, line numbers preserved;
  * inline `#[cfg(test)] mod` blocks are excluded by brace tracking, in
    addition to the test-FILE predicate that was already here — and the
    tracker fails CLOSED, so a file whose braces do not balance is an error,
    never a silent skip.

`--selftest` pins all of that with mutation arms, including the exact plant
above; the gate runs it before every measurement, so a green from the gate is
also a statement that the gate can still say no.

Wired into scripts/local_gate.sh. Pure-stdlib; no cargo build required.

`--selftest` includes the lexing and per-site controls, plus a standing plant
in an isolated copy of the real scanner inputs. The real snapshot.rs bytes,
module graph and ratchet remain authoritative; no live kernel file is written.

Usage:
    python3 scripts/check_extend_constants_ratchet.py
    python3 scripts/check_extend_constants_ratchet.py --selftest
"""
from __future__ import annotations

import contextlib
import hashlib
import io
import json
import re
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_REL = Path("data") / "unchecked_decl_ratchet.json"
CRATES_REL = Path("crates")

# Dot-call form only: `<recv>.extend_constants_unchecked(` / `..._structural(`.
# This deliberately does NOT match the method definitions (`fn extend_constants_*`
# in env/registration.rs) or the trait delegation (`Environment::extend_constants_*`
# in env/trusted_ext.rs, a `::` call). Doc comments and string literals are not
# excluded by the REGEX — they are erased by strip_noncode() before it runs.
# CLOSED BY CONSTRUCTION (audit r11 M11-5). This was dot-only, and it is the
# SOLE gate over the bulk doors -- the env-bypass census hands them off via
# POINTER_METHODS and there is no Rust mirror. Measured at env/snapshot.rs:
# `env.extend_constants_unchecked(cs)` fired, while `Environment::...`,
# `TrustedEnvExt::...`, `<Environment as TrustedEnvExt>::...` and `Self::...`
# were ALL byte-identical to baseline -- and TrustedEnvExt is `pub use`-exported,
# so any of the 27 crates could spell it. Same rule as add_decl now: the NAME in
# call position, minus a definition. A list of accepted prefixes is always one
# spelling short.
CALL_RE = re.compile(r"\bextend_constants_(unchecked|structural)\s*\(")
DEFINITION_RE = re.compile(r"\bfn\s+extend_constants_(unchecked|structural)\s*[(<]")
QUICK_RE = re.compile(r"extend_constants_(unchecked|structural)")
CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\b")

# PER-SITE JUSTIFICATION (2026-08-25, lane LOOSE). Read on the RAW text, not
# the blanked text: this is the one place the gate WANTS the prose.
SOUNDNESS_RE = re.compile(r"//.*\bSOUNDNESS\b")
SOUNDNESS_WINDOW = 40

# Rust non-code spans — same construction and rationale as
# check_add_decl_ratchet.py and check_env_bypass_census.py (ordered alternation;
# each match is replaced by blanks so line/column geometry is preserved).
NONCODE_RE = re.compile(
    r"/\*.*?\*/"                    # block comment (non-nested)
    r"|//[^\n]*"                    # line comment
    r'|(?:b?r)(#*)"(?:.|\n)*?"\1'   # raw string   r"..."  r#"..."#
    r'|b?"(?:\\.|[^"\\])*"'         # string literal
    r"|'(?:\\.|[^\\'])'",           # char literal
    re.DOTALL,
)


def _blank(match: re.Match[str]) -> str:
    return "".join("\n" if ch == "\n" else " " for ch in match.group(0))


def strip_noncode(text: str) -> str:
    return NONCODE_RE.sub(_blank, text)


def _blank_comment_only(match: re.Match[str]) -> str:
    """Blank a span only if it is a COMMENT; keep string literals verbatim.

    AUDIT r12 M12-1. `cfg_test_included_paths` read RAW source, so two `//`
    comment lines anywhere in the repo naming a file in a `#[cfg(test)]
    #[path=...]` pair excluded that file from all three fail-closed scanners --
    measured end to end: an unaccounted `add_decl_unchecked` in the live
    production module env/algebra_nat_testbit_def.rs went rc=1 -> rc=0. That is
    CLAUDE.md's own rule ("any gate that reads Rust or Lean source must blank
    comments and string literals first") broken in the file CLAUDE.md names as
    the reference.
    Comments only, because `#[path = "..."]` IS a string literal: blanking
    strings would blind the derivation to the very thing it reads. Using the
    tested NONCODE_RE means a `//` INSIDE a string is still not a comment.
    """
    text = match.group(0)
    if text.startswith("//") or text.startswith("/*"):
        return "".join("\n" if ch == "\n" else " " for ch in text)
    return text


def strip_comments_keep_strings(text: str) -> str:
    return NONCODE_RE.sub(_blank_comment_only, text)


def is_test_path(rel: Path) -> bool:
    """True for test FILES (whole-file test targets). Inline #[cfg(test)] blocks
    inside otherwise-production files are handled by scan_file's brace tracker;
    entries still listed in test_excluded_sites are honoured for compatibility."""
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
    # `tests.rs`, `*_tests.rs`, `test_*.rs`, `tests_*.rs`
    # AUDIT r11 M11-3: the trailing `or "test" in name` was an UNANCHORED
    # substring, so it dropped 12 live production files -- among them
    # crates/clean-kernel/src/env/algebra_nat_testbit_*.rs, a module registered
    # from env/mod.rs and called from env/soundness_certificate.rs. Measured:
    # flipping one `self.add_decl(` to `self.add_decl_unchecked(` there -- the
    # plain dot form the control arm fires on -- left all three scanners green,
    # which made it the cheapest way in the tree to register an unchecked
    # declaration into the kernel's own soundness-certificate path with no
    # `// SOUNDNESS:` comment and no ratchet row. The anchored patterns before
    # it already cover real test files; nothing recorded that the substring
    # excluded production code, and no waiver row existed for it.
    return bool(re.search(r"(^test_|_tests?\.rs$|^tests?\.rs$|^tests_)", name))

# AUDIT r11 M11-3, second half. Removing the unanchored `"test" in name`
# substring (which dropped 12 live PRODUCTION files, including
# env/algebra_nat_testbit_*.rs on the kernel's soundness-certificate path)
# exposed the real question the substring was badly approximating: some files
# are test-only despite an unremarkable name, because they are included via
# `#[cfg(test)] #[path = "..."] mod ...`.
#
# DERIVED, not guessed: scan the tree for that declaration pair and treat
# exactly the named files as test code. A filename heuristic is an enumeration
# of spellings; this is what the compiler actually does.
_CFG_TEST_PATH_RE = re.compile(
    r'#\[cfg\(test\)\]\s*(?:#\[[^\]]*\]\s*)*#\[path\s*=\s*"([^"]+)"\]')


_CFG_TEST_CACHE = {}

# ---------------------------------------------------------------------------
# AUDIT r14 (M14-1, M14-2, M14-9): ONE target-side classification, computed ONCE.
#
# Rounds 11-13 answered "is this file test code?" from the DECLARING side, with
# a new heuristic each round: a filename substring, then a `#[cfg(test)]
# #[path]` grep, then a crate-wide `mod <stem>` grep, then a 200-character
# proximity window for the guard. Round 14 measured four independent escapes
# through the declaring side (an orphan `mod.rs`, a stem collision, a
# self-vouching orphan, and a `mod` named only inside a COMMENT) plus two
# through the window (two ordinary lines reverse the override; one blank line
# reverses it the other way), and a 5.5x cost regression from doing the work
# per scanner.
#
# The question is answered on the TARGET side now, and only once: a file is
# PRODUCTION if the compiler can reach it without a cfg(test) gate -- as a
# plain `mod`, or through an unguarded `#[path]`. Production wins over every
# name and every declaration. Nothing a declaring file says about itself can
# make a production-reachable file invisible, which is what all four escapes
# needed.
# ---------------------------------------------------------------------------

_INCLUDE_RE = re.compile(r'include!\s*\(\s*"([^"]+)"')
_ATTR_RUN_RE = re.compile(r"#\[[^\]]*\]\s*\Z", re.S)
def _cfg_split_top(args):
    """Split a cfg argument list on commas at paren depth zero."""
    out, depth, start = [], 0, 0
    for idx, ch in enumerate(args):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "," and depth == 0:
            out.append(args[start:idx].strip())
            start = idx + 1
    tail = args[start:].strip()
    if tail:
        out.append(tail)
    return [x for x in out if x]


def _cfg_parse(body):
    """A cfg predicate as a tree: ('all'|'any'|'not', [..]) or ('atom', text)."""
    body = body.strip()
    for kind in ("all", "any", "not"):
        if body.startswith(kind):
            rest = body[len(kind):].lstrip()
            if rest.startswith("(") and rest.endswith(")"):
                return (kind, [_cfg_parse(x) for x in _cfg_split_top(rest[1:-1])])
    return ("atom", body)


def _cfg_atoms(node, out):
    kind, payload = node
    if kind == "atom":
        if payload != "test":
            out.add(payload)
        return out
    for child in payload:
        _cfg_atoms(child, out)
    return out


def _cfg_eval(node, env):
    kind, payload = node
    if kind == "atom":
        return False if payload == "test" else env[payload]
    if kind == "not":
        return not all(_cfg_eval(c, env) for c in payload)
    if kind == "all":
        return all(_cfg_eval(c, env) for c in payload)
    if kind == "any":
        return any(_cfg_eval(c, env) for c in payload)
    return True


# The most free atoms this will enumerate before giving up and answering
# PRODUCTION.  Real cfgs in this tree carry at most three.
_CFG_ATOM_CAP = 12


def _cfg_body_is_test_only(body):
    """Is an item under this cfg predicate unreachable whenever `test` is OFF?

    AUDIT r15 M15-1.  The r14 rule dispatched on the OUTERMOST connective and
    then searched the unparsed argument text for the token `test`
    (`if kind == "all": return re.search(r"\bmyword\b", args)`).  Three
    measured consequences, all in the fail-OPEN direction, and all inverting
    the docstring this function has carried since r14:

      * `#[cfg(all(not(test)))]` -- an item compiled in every NON-test build --
        classified TEST-ONLY, the exact inverse of the truth.  So did
        `all(unix, not(test))` and `all(not(test), feature = "math-overlays")`.
      * `#[cfg(all(unix, feature = "test-utils"))]` classified TEST-ONLY,
        because the token search reads inside a STRING LITERAL -- the very
        thing CLAUDE.md forbids a source-reading gate from doing.
      * `#[cfg(all(any(test, feature = "x")))]` classified TEST-ONLY though the
        feature alone compiles it.

    A `mod` so guarded was dropped from all three bypass scanners AND from the
    Rust mirror, which is why the set-equality arm between the two producers
    stayed green: they were blind in the same place.

    The rule is now the definition itself, decided rather than pattern-matched:
    test-only means the predicate is UNSATISFIABLE once `test` is false.  Every
    non-`test` atom is a free variable (a feature, a target_os, anything), so
    the question is decided by enumeration over the atoms actually present.
    That is correct under negation, which a token search cannot be: `not(unix)`
    is satisfiable with `test` off and must stay PRODUCTION.
    """
    tree = _cfg_parse(body)
    atoms = sorted(_cfg_atoms(tree, set()))
    if len(atoms) > _CFG_ATOM_CAP:
        # Answer PRODUCTION rather than guess: a file scanned needlessly costs
        # nothing, a file skipped needlessly is the hole this rule exists for.
        return False
    for mask in range(1 << len(atoms)):
        env = {a: bool(mask & (1 << i)) for i, a in enumerate(atoms)}
        if _cfg_eval(tree, env):
            return False
    return True


def _cfg_is_test_only(attr):
    """`#[cfg(..)]` -> test-only?  Anything that is not a cfg is not a guard."""
    m = re.search(r"\bcfg\s*\((.*)\)\s*\]?\s*$", attr, re.S)
    if not m:
        return False
    return _cfg_body_is_test_only(m.group(1).strip())


# AUDIT r15 M15-1: the lattice itself, as a table of known answers, run by every
# scanner's --selftest.  A parity test between two producers cannot catch a
# blindness they SHARE -- and they did share this one, which is how five
# inverted spellings survived r14's set-equality arm.
_CFG_LATTICE_CASES = (
    ("test", True),
    ('all(test, feature = "x")', True),
    ('any(test, feature = "x")', False),
    # the five spellings r14 classified backwards
    ("all(not(test))", False),
    ("all(unix, not(test))", False),
    ('all(not(test), feature = "math-overlays")', False),
    ('all(unix, feature = "test-utils")', False),
    ('all(any(test, feature = "x"))', False),
    # negation of a NON-test atom must stay production
    ("not(test)", False),
    ("not(unix)", False),
    # genuinely unsatisfiable without `test`
    ("any(all(test, unix), all(test, windows))", True),
    ("any(test, all(test, unix))", True),
    ("all(unix)", False),
    ("any(test)", True),
    ("all(test)", True),
    ('feature = "x"', False),
)


def cfg_lattice_failures():
    """Spellings this scanner's cfg rule answers backwards.  Empty is correct."""
    return [body for body, want in _CFG_LATTICE_CASES
            if _cfg_is_test_only("#[cfg(" + body + ")]") is not want]

# ---------------------------------------------------------------- module edges
# AUDIT r16 M16-1.  The scope derivation recognised exactly two spellings of a
# module edge -- `#[path = "..."]` matched by a `#\[`-ANCHORED regex, and
# `include!("...")` with a literal argument -- and an unrecognised spelling
# produced NO edge, i.e. it FAILED OPEN in three fail-closed gates.
#
# Measured, with no new code at all: respelling the repo's only two live
# `#[path]` edges (crates/clean-elab/src/bin/soundness_gate/main.rs:16,19) as
# `#[cfg_attr(not(test), path = ...)]` -- which rustc compiles into every
# NON-test build -- moved 675 lines of `crates/clean-elab/tests/soundness_gate/`
# from `prod` to `test_only` in all three producers, and a planted
# `add_decl_unchecked` there went from rc 1 to rc 0.  Those are the very files
# audit r14 M14-11 exists to protect, compiled into the `[[bin]]` that
# scripts/kernel_soundness_gate.sh RUNS to mint launch evidence.
#
# The rule is now: find the edge from the ATTRIBUTE, at any nesting depth; route
# its governing condition through the r15 SAT lattice (which already answers
# `cfg_attr(test, ..)` guarded and `cfg_attr(not(test), ..)` production, and was
# simply never asked); and take the STRICT side on anything unrecognised.  A
# widened regex would only have added a third spelling to an enumeration --
# measured, `include!(concat!("zz", "_shared.rs"))` compiles the target in a
# non-test build and defeats it.
_STRLIT_RE = re.compile(r'"((?:[^"\\]|\\.)*)"')
_PATH_KV_RE = re.compile(r'\bpath\s*=\s*"((?:[^"\\]|\\.)*)"')
_CFG_ATTR_RE = re.compile(r"\bcfg_attr\s*\(")
_INCLUDE_CALL_RE = re.compile(r"\binclude!\s*\(")
# Filled by classify_paths; a scanner reds on it rather than guessing a target.
_UNRESOLVED_EDGES: list[str] = []


def _balanced(src, open_idx, opener, closer):
    """Body between the delimiters starting at `open_idx`, or None."""
    if open_idx >= len(src) or src[open_idx] != opener:
        return None
    depth = 0
    i = open_idx
    while i < len(src):
        if src[i] == opener:
            depth += 1
        elif src[i] == closer:
            depth -= 1
            if depth == 0:
                return src[open_idx + 1:i]
        i += 1
    return None


def _attr_spans(src):
    """(offset, text) for every bracket-matched `#[...]` / `#![...]`."""
    out = []
    i = 0
    while True:
        j = src.find("#", i)
        if j < 0:
            return out
        k = j + 1
        if k < len(src) and src[k] == "!":
            k += 1
        if k >= len(src) or src[k] != "[":
            i = j + 1
            continue
        body = _balanced(src, k, "[", "]")
        if body is None:
            return out
        out.append((j, src[j:k + len(body) + 2]))
        i = k + len(body) + 2


def _path_edges(src):
    """(offset, target, cond_is_test_only) for every attribute naming a module.

    `cond_is_test_only` is the verdict for the attribute's OWN `cfg_attr`
    condition; the item's surrounding attribute run is applied by the caller.
    """
    out = []
    for offset, text in _attr_spans(src):
        if "path" not in text:
            continue
        cond_test_only = False
        m_cfg = _CFG_ATTR_RE.search(text)
        if m_cfg:
            body = _balanced(text, m_cfg.end() - 1, "(", ")")
            parts = _cfg_split_top(body) if body is not None else []
            if parts:
                cond_test_only = _cfg_body_is_test_only(parts[0])
        m = _PATH_KV_RE.search(text)
        if m:
            out.append((offset, m.group(1), cond_test_only))
            continue
        # An attribute that MENTIONS `path` but whose target cannot be read.
        # Strict side: every path-shaped literal in it is a production edge.
        for lit in _STRLIT_RE.findall(text):
            if lit.endswith(".rs"):
                out.append((offset, lit, False))
    return out


def _include_edges(src, rel):
    """(offset, target) for every `include!` module edge.

    `include_str!` / `include_bytes!` are not module edges and do not match.
    An argument this cannot resolve is recorded in `_UNRESOLVED_EDGES` rather
    than silently producing no edge -- an unreadable edge is not an absent one.
    """
    out = []
    for m in _INCLUDE_CALL_RE.finditer(src):
        body = _balanced(src, m.end() - 1, "(", ")")
        if body is None:
            _UNRESOLVED_EDGES.append(f"{rel}: an `include!` whose argument list never closes")
            continue
        lits = _STRLIT_RE.findall(body)
        stripped = body.strip()
        if len(lits) == 1 and stripped == '"%s"' % lits[0]:
            out.append((m.start(), lits[0]))
            continue
        # Not a bare literal: try the concatenation, then each literal, and
        # record it if nothing looks like a module path.
        cands = [x for x in ["".join(lits)] + lits if x.endswith(".rs")]
        if cands:
            for c in cands:
                out.append((m.start(), c))
        elif lits or stripped:
            _UNRESOLVED_EDGES.append(
                f"{rel}: `include!({stripped[:60]})` names no resolvable module path -- "
                f"an edge this gate cannot read is not an edge it may ignore")
    return out

# AUDIT r16 M16-1: a known-answer table for the EDGE EXTRACTOR, beside r15's
# table for the cfg lattice. The parity arm between the Python and Rust
# producers cannot serve here -- both were blind identically, which is the whole
# reason the cfg_attr spelling survived r14 and r15.
# Each case is (source, expected [(target, cond_test_only)] ) with the item's
# own attribute run applied separately by the caller.
_EDGE_CASES = (
    ('#[path = "a.rs"]\nmod a;', [("a.rs", False)]),
    ('#[cfg_attr(not(test), path = "b.rs")]\nmod b;', [("b.rs", False)]),
    ('#[cfg_attr(test, path = "c.rs")]\nmod c;', [("c.rs", True)]),
    ('#[cfg_attr(feature = "x", path = "d.rs")]\nmod d;', [("d.rs", False)]),
    ('#[cfg_attr(all(test, unix), path = "e.rs")]\nmod e;', [("e.rs", True)]),
    ('#[cfg_attr(any(test, feature = "x"), path = "f.rs")]\nmod f;', [("f.rs", False)]),
    # whitespace and newlines inside the attribute
    ('#[ path\n   =\n  "g.rs" ]\nmod g;', [("g.rs", False)]),
    # an attribute that MENTIONS path but whose target cannot be read: strict
    ('#[some_macro(path = PATHS::H, other = "h.rs")]\nmod h;', [("h.rs", False)]),
    # not a module edge
    ('#[doc = "not a path"]\nmod i;', []),
)
_INCLUDE_CASES = (
    ('include!("a.rs");', ["a.rs"], 0),
    ('include!(  "b.rs"  );', ["b.rs"], 0),
    # the joined form AND each path-shaped piece: an edge this cannot read
    # exactly is one it must over-approximate, never drop
    ('include!(concat!("c", "_x.rs"));', ["c_x.rs", "_x.rs"], 0),
    ('include_str!("d.rs");', [], 0),
    ('include_bytes!("e.rs");', [], 0),
    ('include!(some_macro!());', [], 1),
)


def edge_extractor_failures():
    """Cases the edge extractor answers wrongly. Empty is correct."""
    bad = []
    for src, want in _EDGE_CASES:
        got = [(t, c) for _, t, c in _path_edges(src)]
        if got != want:
            bad.append(f"{src!r}: got {got}, want {want}")
    for src, want, want_unresolved in _INCLUDE_CASES:
        before = len(_UNRESOLVED_EDGES)
        got = [t for _, t in _include_edges(src, "selftest")]
        unresolved = len(_UNRESOLVED_EDGES) - before
        del _UNRESOLVED_EDGES[before:]
        if got != want or unresolved != want_unresolved:
            bad.append(f"{src!r}: got {got}/{unresolved} unresolved, "
                       f"want {want}/{want_unresolved}")
    return bad


_MOD_DECL_ANY_RE = re.compile(r"^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?mod[ \t]+([A-Za-z0-9_]+)[ \t]*;",
                              re.M)
_CLASSIFY_CACHE = {}


def _attribute_run_is_cfg_test(src, at):
    """Is the attribute at `at` inside a run of attributes that includes cfg(test)?

    AUDIT r14 M14-1: the guard was `src[at-200:at]` split on a blank line, i.e.
    "is there a cfg(test) textually near this attribute". Measured: inserting
    `#[cfg(test)]\nuse std::fmt as _;` above an UNGUARDED `#[path]` made the
    override vanish (the include is still unguarded to rustc), and inserting one
    BLANK LINE between a genuinely guarded pair made a test include read as
    production. Walk the contiguous attribute run instead -- what the compiler
    actually associates with the item.
    """
    head = src[:at]
    while True:
        m = _ATTR_RUN_RE.search(head)
        if not m:
            return False
        attr = m.group(0).strip()
        if _cfg_is_test_only(attr):
            return True
        head = head[:m.start()]


def classify_paths(root):
    """(production_paths, test_only_paths) for every .rs under crates/.

    Computed ONCE per root and cached: audit r14 M14-9 measured the r13
    per-scanner derivations at 26.6 s / 23.0 s / 25.8 s, taking the pre-push
    hook to 101.8 s against a committed 17.5-18.5 s budget -- a cost regression
    the audit imposed on every lane's push path.
    """
    # AUDIT r15 M15-1: every path below is `.resolve()`d, so the root must be
    # too.  It was not, and on macOS -- where /var is a symlink to /private/var
    # -- `path.relative_to(root)` raised ValueError for every file under a
    # temp-dir root.  Nothing caught it because no selftest tree has ever
    # reached this function (see `.git` in _selftest_tree below).
    root = Path(root).resolve()
    key = str(root)
    if key in _CLASSIFY_CACHE:
        return _CLASSIFY_CACHE[key]
    scope = root / "crates"
    prod, test_only, guarded = set(), set(), set()
    if not scope.is_dir():
        _CLASSIFY_CACHE[key] = (prod, test_only)
        return prod, test_only
    sources = {}
    for rs in scope.rglob("*.rs"):
        try:
            sources[rs.resolve()] = rs.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
    # every `mod x;` declared OUTSIDE a cfg(test) attribute run, plus every
    # unguarded `#[path]`, is a PRODUCTION edge; comments and strings are
    # blanked first, which is the rule CLAUDE.md states and r13's grep broke.
    for path, raw in sources.items():
        if is_test_path(path.relative_to(root)):
            continue
        src = strip_comments_keep_strings(raw)
        for m in _MOD_DECL_ANY_RE.finditer(src):
            sink = guarded if _attribute_run_is_cfg_test(src, m.start()) else prod
            stem = m.group(1)
            for cand in (path.parent / f"{stem}.rs", path.parent / stem / "mod.rs"):
                if cand.resolve() in sources:
                    sink.add(cand.resolve())
        # AUDIT r14 M14-10: Rust has TWO inclusion mechanisms and the derivation
        # knew one. Measured A/B on the same planted file: pulled in by
        # `#[path] mod` -> rc=1 on both gates; pulled in by `include!(..)` ->
        # rc=0 on both. The tree already uses include! 151 times, twice
        # unconditionally from production (expr/mod.rs:428,431), so one line
        # added to an already-included file outside its inner `mod` was
        # production code invisible to all three fail-closed gates.
        _rel_for_edges = path.relative_to(root)
        _edges = [(off, tgt, cond) for off, tgt, cond in _path_edges(src)]
        _edges += [(off, tgt, False) for off, tgt in _include_edges(src, _rel_for_edges)]
        for off, tgt_s, cond_test_only in _edges:
            guard = cond_test_only or _attribute_run_is_cfg_test(src, off)
            sink = guarded if guard else prod
            tgt = (path.parent / tgt_s).resolve()
            if tgt in sources:
                sink.add(tgt)
    # A file is TEST-ONLY when the compiler reaches it only behind a cfg(test)
    # gate, or its name says so -- and in BOTH cases only if no production edge
    # reaches it. Collecting the guarded edges in the same pass is what makes
    # this a partition rather than two unrelated questions; the first cut of
    # this rewrite collected only production edges, so a cfg-test-included file
    # with an ordinary name fell into NEITHER set and was scanned as production
    # (measured on closure_load_v3_tests_binding.rs).
    for path in sources:
        rel = path.relative_to(root)
        if path not in prod and (path in guarded or is_test_path(rel)):
            test_only.add(path)
    _CLASSIFY_CACHE[key] = (prod, test_only)
    return prod, test_only


def _repo_root_of(path):
    p = Path(path).resolve()
    for _ in range(64):
        if (p / ".git").exists():
            return p
        if p == p.parent:
            return None
        p = p.parent
    return None


def is_test_like(path, rel):
    """Name-shaped OR declared under a cfg(test) `#[path]`, from the ONE pass.

    AUDIT r14 M14-9: the r13 repairs ran three independent tree walks per
    scanner -- `cfg_test_included_paths`, `production_included_paths` and a
    crate-wide `mod <stem>` grep per (crate, stem) -- measured at 26.6 s /
    23.0 s / 25.8 s and taking the pre-push hook to 101.8 s against its
    committed 17.5-18.5 s budget. classify_paths answers both halves in a
    single cached pass.
    """
    root = _repo_root_of(path)
    if root is None:
        return is_test_path(rel)
    _, test_only = classify_paths(root)
    return Path(path).resolve() in test_only or is_test_path(rel)


def is_production_file(path):
    """True when the compiler reaches this file without a cfg(test) gate."""
    root = _repo_root_of(path)
    if root is None:
        return False
    prod, _ = classify_paths(root)
    return Path(path).resolve() in prod


# Any `#[path = "..."]` inclusion, guarded or not (audit r13 M13-5/M13-6).
_ANY_PATH_RE = re.compile(r'#\[\s*path\s*=\s*"([^"]+)"\s*\]')
_CFG_TEST_ATTR_RE = re.compile(r"#\[\s*cfg\s*\(\s*(?:all\s*\(\s*)?test\b")


def production_included_paths(root):
    """Files pulled in by an UNGUARDED `#[path]` from a non-test file.

    AUDIT r13 M13-6: `crates/clean-elab/src/bin/soundness_gate/main.rs` includes
    two files from `tests/` with NO `#[cfg(test)]`, and `crates/clean-elab/
    Cargo.toml` declares that `[[bin]]`, which `scripts/kernel_soundness_gate.sh`
    RUNS as a full-mode gate leg minting the trust-core launch evidence. All four
    scanners called those ~675 lines test code because `"tests" in rel.parts`, so
    the binary whose PASS is launch evidence was the one file set no bypass gate
    covered -- measured: four unaccounted doors planted there left all three
    gates green, versus red for the identical calls under `src/`.

    A path included WITHOUT a cfg(test) guard, from a file that is not itself
    test code, is production, and this overrides the name-based predicate.
    """
    out = set()
    scope = root / "crates"
    if not scope.is_dir():
        return out
    for rs in scope.rglob("*.rs"):
        rel = rs.relative_to(root)
        if is_test_path(rel):
            continue
        try:
            src = strip_comments_keep_strings(rs.read_text(encoding="utf-8", errors="replace"))
        except OSError:
            continue
        for m in _ANY_PATH_RE.finditer(src):
            head = src[max(0, m.start() - 200):m.start()]
            if _CFG_TEST_ATTR_RE.search(head.rsplit("\n\n", 1)[-1]):
                continue          # guarded: handled by cfg_test_included_paths
            tgt = (rs.parent / m.group(1)).resolve()
            try:
                tgt.relative_to(scope.resolve())
            except ValueError:
                continue          # outside crates/: not our scope
            out.add(str(tgt))
    return out


_PROD_INCLUDED_CACHE = {}

_DECLARED_MODS_CACHE = {}


def _crate_declares_module(crate_root, stem):
    """Is there a `mod <stem>;` (or `#[path=...] mod`) anywhere in this crate?

    AUDIT r13 M13-5, the orphan route: a 3-line file that NOTHING compiles could
    name any production file in a `#[cfg(test)] #[path=...] mod` pair and mask it
    from all three fail-closed gates -- measured end to end (plant red, add
    orphan, all three green). A declaration only counts if the file carrying it
    is itself compiled, and the cheap sound test for that is whether the crate
    declares the module at all. A crate root (lib.rs / main.rs / mod.rs) is
    compiled by definition.
    """
    key = (str(crate_root), stem)
    if key in _DECLARED_MODS_CACHE:
        return _DECLARED_MODS_CACHE[key]
    pat = re.compile(r"\bmod\s+" + re.escape(stem) + r"\s*[;{]")
    found = False
    for rs in crate_root.rglob("*.rs"):
        try:
            if pat.search(rs.read_text(encoding="utf-8", errors="replace")):
                found = True
                break
        except OSError:
            continue
    _DECLARED_MODS_CACHE[key] = found
    return found



def is_production_included(path):
    """True when `path` is compiled into production through an unguarded include."""
    p = Path(path).resolve()
    root = p
    for _ in range(64):
        if (root / ".git").exists():
            break
        if root == root.parent:
            return False
        root = root.parent
    else:
        return False
    if not (root / ".git").exists():
        return False
    key = str(root)
    if key not in _PROD_INCLUDED_CACHE:
        _PROD_INCLUDED_CACHE[key] = production_included_paths(root)
    return str(p) in _PROD_INCLUDED_CACHE[key]



def is_cfg_test_included(path):
    """True when `path` is reachable ONLY via `#[cfg(test)] #[path=...] mod`.

    Cached per repo root; the root is derived from the path itself so no caller
    has to thread it through.
    """
    p = Path(path).resolve()
    root = p
    # BOUNDED, and it must find a real repo root. An unbounded walk reaches "/"
    # for any path outside a checkout (every selftest temp dir), and the rglob
    # that follows then scans the whole filesystem -- measured as a hang the
    # moment this landed. No repo root means no `#[cfg(test)] #[path=...]`
    # derivation is available, which is not the same as "this is test code".
    for _ in range(64):
        if (root / ".git").exists():
            break
        if root == root.parent:
            return False
        root = root.parent
    else:
        return False
    if not (root / ".git").exists():
        return False
    key = str(root)
    if key not in _CFG_TEST_CACHE:
        _CFG_TEST_CACHE[key] = cfg_test_included_paths(root)
    return str(p) in _CFG_TEST_CACHE[key]


def cfg_test_included_paths(root):
    """Files included ONLY through a `#[cfg(test)] #[path=...] mod` declaration."""
    out = set()
    # AUDIT r12 M12-5: scan the scanners' OWN declared scope, not the repo root.
    # `root.rglob("*.rs")` walked 198,617 files here -- `.claude/worktrees/` (33
    # nested agent checkouts) and `target/` are both gitignored and both were
    # walked AND read. Measured: 184 s to walk, 388 s per derivation, four
    # derivations per pre-push run = ~26 minutes of pure derivation on a hook
    # whose own cost table exists because "a hook like that does not get a gate
    # installed; it gets --no-verify installed". Scoped: 0.07 s over 7,054 files.
    scope = root / "crates"
    if not scope.is_dir():
        scope = root
    for rs in scope.rglob("*.rs"):
        try:
            src = rs.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in _CFG_TEST_PATH_RE.finditer(strip_comments_keep_strings(src)):
            # AUDIT r13 M13-5: three escape routes measured, all closed here.
            # (1) The DECLARING file must itself be production code -- an
            #     ORPHAN 3-line file that nothing compiles could otherwise mask
            #     an arbitrary production file from all three gates.
            # (2) The target must stay INSIDE the declaring crate: the old
            #     `(rs.parent / path).resolve()` accepted unrestricted `..`.
            # (3) The target must not be reachable as production through an
            #     unguarded include (M13-6), which wins.
            # The remaining lexer routes (a NESTED block comment, a raw string)
            # are handled by strip_comments_keep_strings using the tested
            # NONCODE_RE rather than an ad-hoc scan.
            tgt = (rs.parent / m.group(1)).resolve()
            crate_root = None
            for anc in rs.parents:
                if (anc / "Cargo.toml").exists():
                    crate_root = anc.resolve()
                    break
            if crate_root is None:
                continue
            # the DECLARING file must itself be compiled: a crate root, or a
            # module the crate actually declares (audit r13 M13-5, orphan route)
            if rs.name not in ("lib.rs", "main.rs", "mod.rs") \
                    and not _crate_declares_module(crate_root, rs.stem):
                continue
            try:
                tgt.relative_to(crate_root)
            except ValueError:
                continue
            out.add(str(tgt))
    return out



def scan_file(path: Path, rel: Path) -> list[dict]:
    """Production `.extend_constants_*(` hits in one file.

    Comments and literals are erased first; inline `#[cfg(test)] mod` bodies are
    skipped by brace tracking. Raises on unbalanced braces (fail closed)."""
    raw_text = path.read_text(errors="strict")
    if not QUICK_RE.search(raw_text):
        return []
    lines = strip_noncode(raw_text).splitlines()
    prod: list[dict] = []
    in_cfg_test = False
    depth = 0
    pending_cfg = False
    for lineno, line in enumerate(lines, 1):
        if not in_cfg_test:
            if CFG_TEST_RE.search(line):
                pending_cfg = True
                continue
            if pending_cfg:
                if MOD_RE.search(line):
                    if "{" in line:
                        in_cfg_test = True
                        depth = line.count("{") - line.count("}")
                        if depth <= 0:
                            in_cfg_test = False
                    pending_cfg = False
                    continue
                if line.strip():
                    pending_cfg = False
        else:
            depth += line.count("{") - line.count("}")
            if depth <= 0:
                in_cfg_test = False
            continue
        # AUDIT r12 M12-4: the definition exclusion was LINE-granular, so a real
        # call sharing a line with a matching `fn` header was dropped whole --
        # measured with a one-line `#[rustfmt::skip] impl BackdoorExt for
        # Environment { fn extend_constants_unchecked(..) { Environment::extend_constants_unchecked(self, d) } }`
        # in a production kernel file: rc=0 on one line, rc=1 split over two.
        # Definitions are removed from the SPAN they occupy; calls elsewhere on
        # the line still count.
        line = DEFINITION_RE.sub(lambda m: " " * len(m.group(0)), line)
        if False:
            # a definition is not a use of the door (audit r11 M11-5)
            continue
        for m in CALL_RE.finditer(line):
            prod.append(
                {
                    "file": str(rel),
                    "line": lineno,
                    "method": f"extend_constants_{m.group(1)}",
                }
            )
    if in_cfg_test:
        raise ValueError(
            f"{rel}: a #[cfg(test)] mod block never closed (brace tracking ran off the "
            f"end of the file). Refusing to classify this file — fix the source or the "
            f"tracker; an unreadable file is not a clean one."
        )
    return prod



# AUDIT r15 M15-2 leg B: a justification must BELONG to the site it justifies.
# The window was `lineno - 1 - SOUNDNESS_WINDOW` unconditionally -- "is there
# ANY `// SOUNDNESS:` above" -- so in a file whose commented sites sit closer
# together than the window, every site is covered by its NEIGHBOUR's comment.
# Measured in crates/clean-kernel/src/env/trusted_ext.rs, whose 32 blocks sit
# 6-11 lines apart: per block, 31 of the 32 comments could be deleted with every
# gate still green, though each block's own text says removing it makes the call
# COUNTED. The floor is now the nearest of the window, the previous watched CALL
# in this file, and the top of the enclosing `fn`'s attribute/doc run.
_OWNER_FN_RE = re.compile(r"\bfn\s+[A-Za-z0-9_]+\s*[(<]")


def _owner_floor(lines: list[str], lineno: int, prev_call_line: int = 0) -> int:
    floor = max(0, lineno - 1 - SOUNDNESS_WINDOW)
    if prev_call_line:
        floor = max(floor, prev_call_line)
    i = lineno - 1
    while i > 0:
        if _OWNER_FN_RE.search(lines[i - 1]):
            j = i - 1
            while j > 0 and lines[j - 1].strip().startswith(("#[", "///", "//!")):
                j -= 1
            floor = max(floor, j)
            break
        i -= 1
    return floor


def has_soundness_comment(raw_lines: list[str], lineno: int,
                          prev_call_line: int = 0) -> bool:
    """True if a `// SOUNDNESS:` comment that BELONGS to this site sits above it.
    Same rule and window as the sibling scripts/check_add_decl_ratchet.py."""
    start = _owner_floor(raw_lines, lineno, prev_call_line)
    return any(SOUNDNESS_RE.search(l) for l in raw_lines[start:lineno])


def load_ratchet(root: Path) -> dict:
    try:
        data = json.loads((root / RATCHET_REL).read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {root / RATCHET_REL}: {exc}")
    block = data.get("extend_constants")
    if not isinstance(block, dict):
        sys.exit(f"FAIL: {root / RATCHET_REL} missing the 'extend_constants' block (#4).")
    return block


def run(root: Path) -> int:
    # AUDIT r15/r16: caches are keyed on the ROOT alone and the unresolved-edge
    # residue accumulates per pass; production runs once, a selftest does not.
    _CLASSIFY_CACHE.clear()
    _UNRESOLVED_EDGES.clear()
    block = load_ratchet(root)
    # PER-SITE, not per (file, method) BLANKET (2026-08-25, lane LOOSE).
    #
    # `production_sites` used to be read as a SET of (file, method) pairs, with
    # only the repo-wide `*_production_count` behind it. That is a blanket
    # suppression at file granularity and it was live: a second, undeclared
    # `env.extend_constants_structural(...)` in an already-listed file was
    # accepted with no entry of its own, bounded only by an aggregate that a
    # simultaneous removal elsewhere could keep flat. MEASURED at 0b3b94e5b:
    # crates/clean-mathverse/src/cli/per_constant_load.rs carried TWO calls
    # (lines 1762 and 1767) under ONE row that declared no count -- exactly the
    # `test_excluded_sites` shape lane ANTICORR retired one layer up.
    #
    # Two rules now, both taken from the sibling check_add_decl_ratchet.py:
    #   * `occurrences` (default 1) CAPS how many calls a row may cover, so a
    #     sanctioned site cannot quietly gain a neighbour;
    #   * every accounted call must carry its own `// SOUNDNESS:` comment within
    #     SOUNDNESS_WINDOW lines above it -- the half of the CLAUDE.md rule this
    #     gate has always ASKED for in its remediation text and never checked.
    declared: dict[tuple[str, str], int] = {}
    for s in block.get("production_sites", []):
        if "file" not in s or "method" not in s:
            continue
        try:
            occurrences = int(s.get("occurrences", 1))
        except (TypeError, ValueError):
            occurrences = -1
        if occurrences < 1:
            print(
                f"FAIL: production_sites row {s.get('file')} / {s.get('method')} has a "
                f"non-positive `occurrences`; a row justifies at least one call site.",
                file=sys.stderr,
            )
            return 1
        declared[(s["file"], s["method"])] = occurrences
    prod = set(declared)
    # `test_excluded_sites` is RETIRED, and refused rather than ignored.
    #
    # It was a hand-maintained list of (file, method) pairs to skip, written
    # because the old scanner could not see inline `#[cfg(test)] mod` blocks. It
    # is a BLANKET suppression of the pair: MEASURED 2026-08-25 (lane ANTICORR),
    # a real production `env.extend_constants_unchecked(cs)` planted in
    # crates/clean-olean/src/import/load_register.rs -- one of the six listed
    # files -- was accepted silently, exit 0, by the gate whose whole job is to
    # refuse exactly that. All six rows were dead: with the list emptied the
    # brace-tracked cfg(test) exclusion below keeps the gate green on its own.
    stale_excludes = [
        f"{s.get('file')}  {s.get('method')}"
        for s in block.get("test_excluded_sites", [])
        if "file" in s and "method" in s
    ]
    base_unchecked = int(block.get("unchecked_production_count", -1))
    base_structural = int(block.get("structural_production_count", -1))

    counts = {"unchecked": 0, "structural": 0}
    unaccounted: list[str] = []
    unjustified: list[str] = []
    seen: dict[tuple[str, str], int] = {}

    for path in sorted((root / CRATES_REL).rglob("*.rs")):
        rel = path.relative_to(root)
        # AUDIT r14 M14-1/M14-2: ONE target-side question. A file the compiler
        # reaches without a cfg(test) gate is production, whatever its name and
        # whatever any declaring file says; everything else that looks like test
        # code is excluded. This replaces the declaring-side stack (name
        # substring -> cfg(test)#[path] grep -> crate-wide mod grep -> proximity
        # window), through which round 14 measured six independent escapes.
        if not is_production_file(path) and is_test_like(path, rel):
            # test-only by NAME, or by being included solely through a
            # `#[cfg(test)] #[path=...] mod` declaration (audit r11 M11-3)
            continue
        try:
            hits = scan_file(path, rel)
        except OSError as exc:
            sys.exit(f"FAIL: cannot read {rel}: {exc}")
        except ValueError as exc:
            print(f"FAIL: {exc}", file=sys.stderr)
            return 1
        # Re-read for the SOUNDNESS-comment window: `scan_file` returns blanked
        # text, and this is the one place the gate wants the prose. Fail CLOSED
        # if the second read does not agree with the first.
        raw_lines: list[str] = []
        if hits:
            try:
                raw_lines = path.read_text(errors="strict").splitlines()
            except OSError as exc:
                print(f"FAIL: cannot re-read {rel} for its justification: {exc}", file=sys.stderr)
                return 1
        _prev_hit_line = 0
        for hit in hits:
            key = (hit["file"], hit["method"])
            _prev, _prev_hit_line = _prev_hit_line, hit["line"]
            if key in prod:
                counts[hit["method"].removeprefix("extend_constants_")] += 1
                seen[key] = seen.get(key, 0) + 1
                if not has_soundness_comment(raw_lines, hit["line"], _prev):
                    unjustified.append(f"{hit['file']}:{hit['line']}  {hit['method']}")
                continue
            unaccounted.append(f"{hit['file']}:{hit['line']}  {hit['method']}")

    ok = True
    for key, occurrences in sorted(declared.items()):
        found = seen.get(key, 0)
        if found > occurrences:
            ok = False
            print(
                f"FAIL: {key[0]} / {key[1]} has {found} production call sites but is "
                f"justified for {occurrences}. A sanctioned site is NOT a blanket "
                f"suppression of the file: give the new call its own row (or raise "
                f"`occurrences` with a justification that covers it).",
                file=sys.stderr,
            )
        elif found < occurrences:
            print(
                f"NOTE: {key[0]} / {key[1]} declares occurrences={occurrences} but "
                f"{found} were measured; lower it."
            )
    if unjustified:
        ok = False
        print(
            "FAIL: accounted extend_constants_* call site(s) with no // SOUNDNESS: "
            f"comment within {SOUNDNESS_WINDOW} lines above:",
            file=sys.stderr,
        )
        for u in unjustified:
            print(f"  {u}", file=sys.stderr)
        print(
            "  -> the ratchet entry is only half the rule. CLAUDE.md requires the "
            "justification AT THE CALL; data/unchecked_decl_ratchet.json has always "
            "CLAIMED every site carries one, and until 2026-08-25 nothing checked it.",
            file=sys.stderr,
        )
    if stale_excludes:
        ok = False
        print(
            "FAIL: data/unchecked_decl_ratchet.json -> extend_constants still lists "
            "test_excluded_sites, which is RETIRED:",
            file=sys.stderr,
        )
        for s in stale_excludes:
            print(f"  {s}", file=sys.stderr)
        print(
            "  -> the scanner now excludes inline #[cfg(test)] mod blocks by brace "
            "tracking, so the list is unnecessary; and it is a BLANKET (file, method) "
            "suppression that hides a future PRODUCTION bypass in the same file "
            "(measured 2026-08-25 in crates/clean-olean/src/import/load_register.rs). "
            "Delete the key.",
            file=sys.stderr,
        )
    if unaccounted:
        ok = False
        print("FAIL: unaccounted extend_constants_* bulk-bypass call site(s):", file=sys.stderr)
        for u in unaccounted:
            print(f"  {u}", file=sys.stderr)
        print(
            "  -> add a // SOUNDNESS: comment at the call AND a production_sites "
            "entry under data/unchecked_decl_ratchet.json -> extend_constants. "
            "(test_excluded_sites is RETIRED: inline #[cfg(test)] mod blocks are "
            "excluded automatically, and the list hid production bypasses.)",
            file=sys.stderr,
        )

    for label, found, base in (
        ("unchecked", counts["unchecked"], base_unchecked),
        ("structural", counts["structural"], base_structural),
    ):
        if found > base:
            ok = False
            print(
                f"FAIL: {label} production bypass count {found} exceeds baseline {base} "
                f"(data/unchecked_decl_ratchet.json). New bypass must be justified + ratcheted.",
                file=sys.stderr,
            )
        elif found < base:
            # Improvement — allowed, but the baseline is now stale.
            print(
                f"NOTE: {label} production bypass count {found} is BELOW baseline {base}; "
                f"lower extend_constants.{label}_production_count in the ratchet.",
            )

    if ok:
        print(
            f"OK: extend_constants bypass ratchet — "
            f"unchecked={counts['unchecked']}/{base_unchecked}, "
            f"structural={counts['structural']}/{base_structural} production sites accounted for."
        )
        return 0
    return 1


# ---------------------------------------------------------------------------
# Self-test: the gate must be able to say NO, and must NOT say no to prose.
# ---------------------------------------------------------------------------

def _selftest_tree() -> Path:
    """A minimal fake repo the mutation arms can edit freely."""
    tmp = Path(tempfile.mkdtemp(prefix="extend_constants_selftest_"))
    # AUDIT r15 M15-1: without a `.git`, `_repo_root_of` returns None, so
    # `is_production_file` is False and `is_test_like` falls back to the NAME
    # predicate -- i.e. `classify_paths`, the whole target-side rule round 14
    # introduced, was reached by NO selftest arm in any of the three scanners.
    # One mkdir makes every arm below exercise it.
    (tmp / ".git").mkdir()
    (tmp / "data").mkdir()
    (tmp / "crates" / "c" / "src").mkdir(parents=True)
    (tmp / "data" / RATCHET_REL.name).write_text(
        json.dumps(
            {
                "extend_constants": {
                    "unchecked_production_count": 0,
                    "structural_production_count": 0,
                    "production_sites": [],
                    "test_excluded_sites": [],
                }
            },
            indent=2,
        )
    )
    (tmp / "crates" / "c" / "src" / "lib.rs").write_text(
        "pub fn clean() {}\n"
        "\n"
        "#[cfg(test)]\n"
        "mod tests {\n"
        "    use super::*;\n"
        "    #[test]\n"
        "    fn t() {\n"
        "        env.extend_constants_unchecked(d);\n"
        "    }\n"
        "}\n"
    )
    return tmp


def _write_ratchet(root: Path, doc: dict) -> None:
    (root / RATCHET_REL).write_text(json.dumps(doc, indent=2))


def _read_ratchet(root: Path) -> dict:
    return json.loads((root / RATCHET_REL).read_text())


def _quiet_run(root: Path) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root)
    return rc, buf.getvalue()


def _arm(name: str, root: Path, expect: int, contains: tuple[str, ...] = ()) -> bool:
    rc, captured = _quiet_run(root)
    good = rc == expect and all(text in captured for text in contains)
    print(f"  [{'ok ' if good else 'FAIL'}] {name}: exit {rc} (expected {expect})")
    if not good and captured:
        print("    --- the arm's own output ---")
        for line in captured.rstrip("\n").splitlines():
            print(f"    {line}")
    return good


PLANT = "\npub fn smuggle(env: &mut E, d: D) { env.extend_constants_unchecked(d); }\n"
# The same plant WITH the per-site justification CLAUDE.md requires at the call.
PLANT_JUSTIFIED = "\n// SOUNDNESS: selftest justification.\n" + PLANT.lstrip("\n")
# Two justified calls in ONE file: legal only if the row declares occurrences=2.
PLANT_JUSTIFIED_TWICE = PLANT_JUSTIFIED + PLANT_JUSTIFIED.replace("smuggle", "smuggle2")

# The exact prose that turned the OLD, raw-line scanner RED (see the header).
SOUNDNESS_PROSE = (
    "\n// SOUNDNESS: this path deliberately does NOT call\n"
    "// env.extend_constants_unchecked(decls); every constant is re-checked.\n"
)


def _git_clean(rel: str) -> bool:
    """True iff `rel` matches HEAD with nothing staged and nothing in the worktree."""
    for args in (["diff", "--quiet", "--", rel], ["diff", "--quiet", "--cached", "--", rel]):
        r = subprocess.run(["git", "-C", str(REPO_ROOT), *args], capture_output=True, check=False)
        if r.returncode != 0:
            return False
    return True


def _scanner_inputs(root: Path) -> list[Path]:
    """The complete input closure of run()/classify_paths(), not a Git inventory."""
    scope = root / CRATES_REL
    if not scope.is_dir() or scope.is_symlink():
        raise ValueError(f"scanner input directory is absent or symlinked: {scope}")
    sources = []
    for path in scope.rglob("*"):
        # Even an untraversed directory symlink can redirect a resolved module
        # edge. Omitting it would silently change the classifier's authority.
        if path.is_symlink() or path.name == ".git":
            raise ValueError(f"symlinked scanner input or nested repository marker: {path}")
        if path.name.endswith(".rs"):
            sources.append(path.relative_to(root))
    return [RATCHET_REL, *sorted(sources)]


def _scanner_input(root: Path, rel: Path) -> tuple[bytes, tuple]:
    path = root / rel
    if path.resolve() != path:
        raise ValueError(f"refusing symlinked scanner input: {rel}")
    before = path.stat()
    if not stat.S_ISREG(before.st_mode):
        raise ValueError(f"scanner input is not a regular file: {rel}")
    data = path.read_bytes()
    after = path.stat()

    def identity(info):
        return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    if identity(before) != identity(after):
        raise ValueError(f"scanner input changed while reading: {rel}")
    return data, (hashlib.sha256(data).digest(), identity(after))


def _scanner_input_state(root: Path) -> dict:
    return {rel: _scanner_input(root, rel)[1] for rel in _scanner_inputs(root)}


def _copy_scanner_inputs(source: Path, destination: Path) -> dict:
    """Copy every source/ledger byte independently; never link to the live tree."""
    source, destination = source.resolve(), destination.resolve()
    if source == destination or source in destination.parents or destination in source.parents:
        raise ValueError("scanner snapshot must not overlap the source tree")
    if any(destination.iterdir()):
        raise ValueError("scanner snapshot destination must be empty")
    state = {}
    for rel in _scanner_inputs(source):
        data, state[rel] = _scanner_input(source, rel)
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(data)
        if target.read_bytes() != data:
            raise ValueError(f"scanner snapshot copy differs: {rel}")
    # This marker is essential: without it _repo_root_of bypasses the real
    # module classifier. No Git index, caches, or synthetic ratchet is copied.
    (destination / ".git").mkdir()
    if _scanner_input_state(source) != state:
        raise ValueError("scanner inputs changed while copying; refusing an incoherent baseline")
    return state


def _standing_plant_arms(root: Path, lock: Path) -> tuple[int, int, int]:
    """Real-input falsification without writing or restoring any live input."""
    root = root.resolve()
    rel = Path("crates/clean-kernel/src/env/snapshot.rs")
    real = root / rel
    holding = False
    for _ in range(600):
        try:
            lock.mkdir()
            holding = True
            break
        except FileExistsError:
            time.sleep(0.1)
    passed = failed = 0

    def check(name, copy, expect, contains=()):
        nonlocal passed, failed
        good = _arm(name, copy, expect, contains)
        passed += int(good)
        failed += int(not good)
        return good

    try:
        if not holding:
            print(f"  [SKIP] REAL INPUT arms: another selftest has held {lock} for 60 s")
            return 0, 0, 2
        if not real.is_file():
            print(f"  [FAIL] REAL INPUT arms: {rel} is absent — the arm IS the demonstration")
            return 0, 2, 0
        if not _git_clean(str(rel)):
            print(f"  [SKIP] REAL INPUT arms: {rel} is dirty in the working tree or index. "
                  "A dirty file may be a leaked plant from an older killed selftest; "
                  "it must not become a baseline. Commit or stash it and re-run.")
            return 0, 0, 2
        original_identity = None
        state = None
        try:
            _, original_identity = _scanner_input(root, rel)
            with tempfile.TemporaryDirectory(prefix="extend_constants_real_inputs_") as tmp:
                copy = Path(tmp).resolve()
                state = _copy_scanner_inputs(root, copy)
                snapshot = copy / rel
                original = snapshot.read_bytes()
                plant_line = len((original + b"\n").splitlines()) + 1
                if check("REAL INPUT copy unmodified baseline is green", copy, 0):
                    try:
                        snapshot.write_bytes(original + SOUNDNESS_PROSE.encode("utf-8"))
                        check("REAL INPUT copy + the // SOUNDNESS: prose is green", copy, 0)
                        snapshot.write_bytes(original + PLANT.encode("utf-8"))
                        check("REAL INPUT copy + a real unaccounted bypass is RED", copy, 1,
                              ("FAIL: unaccounted extend_constants_* bulk-bypass call site(s):",
                               f"{rel}:{plant_line}  extend_constants_unchecked"))
                    finally:
                        snapshot.write_bytes(original)
                    if snapshot.read_bytes() != original:
                        raise ValueError("isolated snapshot restoration differs from original bytes")
                    check("REAL INPUT copy restored baseline is green", copy, 0)
        except (OSError, ValueError, SystemExit) as exc:
            print(f"  [FAIL] REAL INPUT arms: {exc}")
            failed += 1
        finally:
            try:
                if original_identity is not None and _scanner_input(root, rel)[1] != original_identity:
                    raise ValueError(f"live {rel} changed during the arms; leaving all edits untouched")
                if state is not None and _scanner_input_state(root) != state:
                    raise ValueError("live scanner inputs changed during the arms; leaving edits untouched")
            except (OSError, ValueError) as exc:
                print(f"  [FAIL] REAL INPUT preservation: {exc}")
                failed += 1
        return passed, failed, 0
    finally:
        if holding:
            with contextlib.suppress(OSError):
                lock.rmdir()


def selftest() -> int:
    passed = failed = skipped = 0
    _edge_bad = edge_extractor_failures()
    if _edge_bad:
        print(f"  [FAIL] edge extractor: {_edge_bad}")
        failed += 1
    else:
        print(f"  [ok  ] edge extractor: {len(_EDGE_CASES) + len(_INCLUDE_CASES)} module-edge "
              f"spellings, including the cfg_attr form audit r16 M16-1 found invisible")
        passed += 1
    _lattice_bad = cfg_lattice_failures()
    if _lattice_bad:
        print(f"  [FAIL] cfg lattice: classified backwards: {_lattice_bad}")
        failed += 1
    else:
        print(f"  [ok  ] cfg lattice: {len(_CFG_LATTICE_CASES)} spellings, "
              f"including the five audit r15 M15-1 found inverted")
        passed += 1

    def check(name: str, root: Path, expect: int) -> None:
        nonlocal passed, failed
        if _arm(name, root, expect):
            passed += 1
        else:
            failed += 1

    root = _selftest_tree()
    lib = root / "crates" / "c" / "src" / "lib.rs"
    baseline = lib.read_text()
    try:
        # 1. pristine tree: the only hit is inside `#[cfg(test)] mod` -> green
        check("pristine tree with only a cfg(test) bypass is green", root, 0)

        # 2. a production bypass, unaccounted -> RED
        lib.write_text(baseline + PLANT)
        check("NEW unaccounted production extend_constants_unchecked is RED", root, 1)

        # 3. same site, accounted AND justified at the call -> green
        lib.write_text(baseline + PLANT_JUSTIFIED)
        doc = _read_ratchet(root)
        doc["extend_constants"]["unchecked_production_count"] = 1
        doc["extend_constants"]["production_sites"] = [
            {
                "file": "crates/c/src/lib.rs",
                "method": "extend_constants_unchecked",
                "trust": "selftest",
            }
        ]
        _write_ratchet(root, doc)
        check("an accounted production bypass is green", root, 0)

        # 4. baseline lowered below the measured sites -> RED
        doc["extend_constants"]["unchecked_production_count"] = 0
        _write_ratchet(root, doc)
        check("measured sites exceeding the declared baseline is RED", root, 1)

        # 5. THE ANTI-CORRELATION ARM. The `// SOUNDNESS:` comment the gate's own
        #    remediation text demands, quoting the call, must NOT be a hit. The
        #    raw-line scanner this replaced failed exactly here (measured
        #    2026-08-25 at 438a64131 on the real crates/clean-kernel/src/env/
        #    snapshot.rs). If this arm ever goes red again, the gate is once more
        #    punishing the documentation it asks for.
        doc["extend_constants"]["unchecked_production_count"] = 0
        doc["extend_constants"]["production_sites"] = []
        _write_ratchet(root, doc)
        lib.write_text(baseline + SOUNDNESS_PROSE)
        check("a // SOUNDNESS: comment quoting the call is NOT a bypass", root, 0)

        # 6. a doc comment quoting the call is not a hit either
        lib.write_text(
            baseline
            + "\n/// Callers must not use `env.extend_constants_structural(d)` here.\n"
            + "/** block form: env.extend_constants_unchecked(d) */\n"
        )
        check("doc/block comments quoting the call are NOT bypasses", root, 0)

        # 7. a string literal naming the call is not a hit
        lib.write_text(
            baseline
            + '\npub fn msg() -> &\'static str { "use env.extend_constants_unchecked(d)" }\n'
        )
        check("a string literal naming the call is NOT a bypass", root, 0)

        # 8. ...but a real call on the SAME line as a comment still counts
        lib.write_text(
            baseline
            + "\npub fn s(env: &mut E, d: D) { env.extend_constants_unchecked(d); } // see above\n"
        )
        check("a real call with a trailing comment is still counted", root, 1)

        # 9. EVERY spelling of a call through the bulk door IS a bypass.
        #
        # THIS ARM USED TO ASSERT THE OPPOSITE (audit r11 M11-5): it pinned the
        # dot-only rule green, and this scanner is the SOLE gate over the bulk
        # doors -- the env census hands them off via POINTER_METHODS and there
        # is no Rust mirror. Measured then: `Environment::`, `TrustedEnvExt::`,
        # `<Environment as TrustedEnvExt>::` and `Self::` forms were all
        # byte-identical to baseline, and TrustedEnvExt is `pub use`-exported,
        # so any of the 27 crates could spell one.
        for label, call in (
            ("Environment::", "Environment::extend_constants_unchecked(e, d);"),
            ("TrustedEnvExt::", "TrustedEnvExt::extend_constants_unchecked(e, d);"),
            ("fully qualified", "<Environment as TrustedEnvExt>::extend_constants_unchecked(e, d);"),
            ("Self::", "Self::extend_constants_unchecked(e, d);"),
        ):
            lib.write_text(baseline + f"\npub fn deleg(e: &mut E, d: D) {{ {call} }}\n")
            check(f"a {label} call through the bulk door IS a bypass", root, 1)

        # 10. an unbalanced cfg(test) mod fails CLOSED, never skips
        lib.write_text(
            "#[cfg(test)]\nmod tests {\n    fn t() { env.extend_constants_unchecked(d); }\n"
        )
        check("an unterminated cfg(test) block fails closed", root, 1)

        # 11. a leftover test_excluded_sites row is REFUSED, not honoured
        lib.write_text(baseline + PLANT)
        doc = _read_ratchet(root)
        doc["extend_constants"]["unchecked_production_count"] = 0
        doc["extend_constants"]["production_sites"] = []
        doc["extend_constants"]["test_excluded_sites"] = [
            {"file": "crates/c/src/lib.rs", "method": "extend_constants_unchecked"}
        ]
        _write_ratchet(root, doc)
        check("a test_excluded_sites row can no longer hide a production bypass", root, 1)

        # 12. PER-SITE JUSTIFICATION (lane LOOSE): an ACCOUNTED site whose
        #     `// SOUNDNESS:` comment is deleted is RED. The ratchet entry is
        #     only half the rule; this gate asked for the other half in its
        #     remediation text for two months and never checked it.
        lib.write_text(baseline + PLANT)
        doc = _read_ratchet(root)
        doc["extend_constants"].pop("test_excluded_sites", None)
        doc["extend_constants"]["unchecked_production_count"] = 1
        doc["extend_constants"]["production_sites"] = [
            {
                "file": "crates/c/src/lib.rs",
                "method": "extend_constants_unchecked",
                "trust": "selftest",
            }
        ]
        _write_ratchet(root, doc)
        check("an accounted site with NO // SOUNDNESS: comment is RED", root, 1)

        # 13. THE BLANKET-SUPPRESSION ARM. A row is not a licence for the FILE.
        #     A second justified call under a row that declares no `occurrences`
        #     is RED -- this is the shape that let a real production bypass hide
        #     behind `test_excluded_sites` (retired 2026-08-25), one layer up.
        lib.write_text(baseline + PLANT_JUSTIFIED_TWICE)
        doc["extend_constants"]["unchecked_production_count"] = 2
        _write_ratchet(root, doc)
        check("a SECOND call under a one-site row is RED", root, 1)

        # 14. ...and legal once the row declares it, with a justification that
        #     covers both calls.
        doc["extend_constants"]["production_sites"][0]["occurrences"] = 2
        _write_ratchet(root, doc)
        check("two calls under a row declaring occurrences=2 is green", root, 0)

        # 15. a row may not declare a non-positive or unparsable `occurrences`
        #     and thereby cover nothing while still marking the pair accounted.
        doc["extend_constants"]["production_sites"][0]["occurrences"] = 0
        _write_ratchet(root, doc)
        check("occurrences=0 is REFUSED, not read as 'unlimited'", root, 1)

        # 16. an unreadable ratchet fails closed
        lib.write_text(baseline)
        (root / RATCHET_REL).write_text("{ not json")
        rc = 0
        try:
            _quiet_run(root)
        except SystemExit as exc:
            rc = 1 if exc.code else 0
        good = rc == 1
        print(f"  [{'ok ' if good else 'FAIL'}] an unparsable ratchet fails closed: {good}")
        passed += 1 if good else 0
        failed += 0 if good else 1

        # 17. The standing plant uses the REAL source graph and ledger, copied
        # into isolation. The old live-file arm leaked a plant under concurrent
        # runs (2026-09-14) and invalidated kernel build fingerprints even when
        # restored. Keep its lock/cleanliness policies; never write live inputs.
        lock = Path(tempfile.gettempdir()) / "clean-extend-constants-selftest.lock"
        real_passed, real_failed, real_skipped = _standing_plant_arms(REPO_ROOT, lock)
        passed += real_passed
        failed += real_failed
        skipped += real_skipped
    finally:
        import shutil

        shutil.rmtree(root, ignore_errors=True)

    tail = f", {skipped} SKIPPED (never counted as passed)" if skipped else ""
    print(f"selftest: {passed} passed, {failed} failed{tail}")
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    # The runners call the isolated selftest first, then measure the live tree.
    # Neither invocation writes or restores any tracked scanner input.
    if "--selftest" in argv:
        return selftest()
    return run(REPO_ROOT)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
