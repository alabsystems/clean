#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The add_decl_structural / add_decl_unchecked bypass ratchet, MEASURED.

WHY THIS EXISTS
---------------
CLAUDE.md makes this a first-class soundness rule:

    `add_decl_structural` / `add_decl_unchecked` require a `// SOUNDNESS:`
    comment and a tracking issue. Tracked in
    `data/unchecked_decl_ratchet.json`; only goes down.

Two gates read that artifact and neither reads the SOURCE TREE:

  * `validate_unchecked_decl_ratchet` (crates/clean-cli/src/cmd_replacement/
    gate_checks.rs) checks the JSON is internally consistent — rows sum to the
    declared counts, trust strings non-empty, no zero counts.
  * `check_unchecked_decl_ratchet_zero` (scripts/deny_sorry_gate.sh) asserted the
    two declared counts were literally `0`, and recorded
    `unchecked_decl_ratchet_zero: passed` into
    reports/deny-sorry-launch-evidence.json. SUPERSEDED 2026-08-23 (G6): the
    literal 0 was false, and that lane is now
    `unchecked_decl_ratchet_accounted`, which imports SANCTIONED_SITES from here
    and calls this scanner instead of reading a number.

So the whole "the unchecked-decl ratchet is at 0/0" claim was a claim about a
JSON literal. Nothing re-derived it from the tree. Adding
`env.add_decl_unchecked(d)` to a production file — no `// SOUNDNESS:` comment,
no ratchet entry — passed every gate in the repo (demonstrated 2026-08-22 by
planting exactly that in crates/clean-kernel/src/env/snapshot.rs: seven
python gates plus paragon were byte-identical with and without it).

This is the missing scanner. It is the same shape as
scripts/check_extend_constants_ratchet.py, which does for the *bulk*
`extend_constants_*` bypass exactly what nobody had done for `add_decl_*`.

WHAT IT MEASURES
----------------
Dot-call form only: `<recv>.add_decl_unchecked(` / `<recv>.add_decl_structural(`.
This deliberately does NOT match the method definitions (`fn add_decl_*` in
env/decl_add.rs), the trait declarations or the `Environment::add_decl_*(self, …)`
delegations in env/trusted_ext.rs (a `::` call), doc comments, or string
literals — the same exclusions the extend_constants gate documents.

Test code is excluded two ways, because both classes exist here:
  * test FILES, by the byte-identical predicate the extend_constants gate uses;
  * inline `#[cfg(test)] mod` blocks inside otherwise-production files, by brace
    tracking. 48 of the tree's 49 non-test-path hits are of this second kind, so
    a gate without it would be 48 false positives and would be switched off.
    The tracker fails CLOSED: a file whose braces do not balance is an error,
    never a skip.

VERDICTS
--------
A measured production site must be ACCOUNTED FOR, one of two ways:
  * `add_decl_{structural,unchecked}_production_sites` — the normal route; the
    site counts toward the ratchet total and `deny_sorry_gate.sh` sees it.
  * `add_decl_measured_disagreements` — a site the tree HAS and the counts do
    NOT, recorded with its reason and the reconciliation owed. The disagreement
    is printed on every run instead of being silently excluded. A disagreement
    row that no longer matches a live site is STALE and fails — the debt cannot
    be abandoned quietly either.

…and, either way, the site must be named in `SANCTIONED_SITES` BELOW — the
allowlist that lives in CODE, not in the artifact. That is the half of "only
goes down" a JSON count can never enforce: before it, a new bypass could be
legalised by writing a row about it. Now legalising one requires editing this
file, and the per-site cap means even a sanctioned site cannot quietly gain a
second occurrence.

Every accounted site must still carry a `// SOUNDNESS:` comment within
`SOUNDNESS_WINDOW` lines above the call. That is the half of the CLAUDE.md rule
no gate has ever enforced.

Exit codes: 0 accounted, 1 unaccounted/unsanctioned/stale/over-baseline, 2 self-test
failure.

Usage:
    python3 scripts/check_add_decl_ratchet.py
    python3 scripts/check_add_decl_ratchet.py --list
    python3 scripts/check_add_decl_ratchet.py --selftest
"""

from __future__ import annotations

import contextlib
import io
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_REL = Path("data") / "unchecked_decl_ratchet.json"
CRATES_REL = Path("crates")

# AUDIT r10 M10-5: the shape was `.add_decl_*(` only, so a production
# `Environment::add_decl_unchecked(env, d)` -- ordinary Rust, no trait import
# needed -- was invisible to this scanner, to its Rust mirror AND to the
# env-bypass census (which excludes add_decl_* as "watched by the siblings").
# Measured with a plant in crates/clean-kernel/src/env/snapshot.rs: output
# byte-identical to baseline, rc 0, with no `// SOUNDNESS:` comment and no
# ratchet row. The UFCS form is now counted; the two genuine delegations are
# scoped off BY FILE below, not by call shape, because a shape exclusion holds
# in every file and that is exactly how this escaped.
# CLOSED BY CONSTRUCTION, not by enumeration (audit r11, self-review of the
# r10 M10-5 fix). r10 replaced "a leading dot" with "a leading dot OR
# Environment::/TrustedEnvExt::" -- which is still a LIST of call shapes, and a
# list of shapes is always one spelling short. Measured immediately after:
# `<Environment as TrustedEnvExt>::add_decl_unchecked(...)`, an import alias
# (`use Environment as E; E::add_decl_unchecked(...)`) and a generic
# `T::add_decl_unchecked(...)` were all still INVISIBLE.
#
# The rule is now the NAME in call position, whatever precedes it, minus the
# two things that are not calls: a definition (`fn add_decl_unchecked(`) and
# the file that defines the door (DELEGATION_FILES). Adding a new way to spell
# a path cannot reopen this.
CALL_RE = re.compile(r"\badd_decl_(unchecked|structural)\s*\(")
DEFINITION_RE = re.compile(r"\bfn\s+add_decl_(unchecked|structural)\s*[(<]")
# The trait's own declaration and its two delegating impls live here; counting
# them would be counting the definition, not a call site.
DELEGATION_FILES = {"crates/clean-kernel/src/env/trusted_ext.rs"}
CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\b")
SOUNDNESS_RE = re.compile(r"//.*\bSOUNDNESS\b")
SOUNDNESS_WINDOW = 40

# The sanctioned production bypasses, PINNED IN CODE: (file, method) -> the
# maximum number of production call sites that site may contain.
#
# A ratchet row — a `*_production_sites` entry OR an
# `add_decl_measured_disagreements` entry — is honoured ONLY for a key named
# here. Both routes suppress a RED, so both must cost a reviewed source change;
# otherwise "the artifact says it is fine" remains a self-issued licence, which
# is the exact failure this gate was written for.
#
# G6 (2026-08-23): the one entry is the Metamath two-pass PASS-1 proof-drop arm
# of `Environment::add_decl`. It registers a `Declaration::Axiom` without
# `infer_sort`/`check_type`, and it is sound only because (1) it fails closed
# outside the `MmAxiomOnlyGuard` two-pass sentinel, (2) PASS-2 re-adds every
# in-range theorem through the CHECKED `add_decl`, and (3) `mm_gate` drops any
# verified theorem whose transitive `$p` closure is not itself verified, so only
# that gated set is ever exported. The full argument, with the file references,
# is the `trust` prose on the site's row in data/unchecked_decl_ratchet.json.
SANCTIONED_SITES: dict[tuple[str, str], int] = {
    ("crates/clean-kernel/src/env/decl_add.rs", "add_decl_unchecked"): 1,
    # AUDIT r11 M11-6. The two `TrustedEnvExt for Environment` delegations,
    # capped at one call each. SOUNDNESS ARGUMENT: each body is exactly one
    # forward to the inherent method of the same name and confers no capability
    # -- reaching the line requires already holding an `Environment`, which can
    # call the inherent method directly, so the trait adds a spelling and not an
    # authority. They are listed as SITES because audit r10 had excluded the
    # whole FILE, which is a suppression: measured, one extra
    # `self.add_decl_unchecked(..)` planted inside an existing delegation body
    # was then invisible to every scanner, while the pre-r10 scanner caught it.
    ("crates/clean-kernel/src/env/trusted_ext.rs", "add_decl_unchecked"): 1,
    ("crates/clean-kernel/src/env/trusted_ext.rs", "add_decl_structural"): 1,
}


def is_test_path(rel: Path) -> bool:
    """True for test FILES. Byte-identical to check_extend_constants_ratchet.py
    so the two bypass gates cannot drift into disagreeing about what a test is."""
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
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
    # Anchored at the attribute head: `#[rustfmt::cfg(test)]` (any tool path) is
    # inert to rustc, so `\bcfg` anywhere in the attribute read a production
    # declaration as test-only (docs/issues/2026-11-16-python-rust-lexer-copies.md).
    m = re.match(r"#!?\[\s*cfg\s*\((.*)\)\s*\]?\s*$", attr.strip(), re.S)
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


# The attribute HEAD as well as its predicate: a tool path makes `cfg` inert to
# rustc (docs/issues/2026-11-16-python-rust-lexer-copies.md).
_CFG_HEAD_CASES = (
    ("#[cfg(test)]", True),
    ("#[ cfg ( test ) ]", True),
    ("#[rustfmt::cfg(test)]", False),
    ("#[clippy::cfg(test)]", False),
    ("#[diagnostic::cfg(test)]", False),
    ("#[doc = \"cfg(test)\"]", False),
)


def cfg_lattice_failures():
    """Spellings this scanner's cfg rule answers backwards.  Empty is correct."""
    return [body for body, want in _CFG_LATTICE_CASES
            if _cfg_is_test_only("#[cfg(" + body + ")]") is not want] + [
        attr for attr, want in _CFG_HEAD_CASES if _cfg_is_test_only(attr) is not want]

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


# ---------------------------------------------------------------------------
# 2026-11-16: the MODULE TREE, resolved the way rustc resolves it.
#
# Until this date `mod x;` was looked up BESIDE the declaring file, any file
# not named like a test contributed edges whether or not anything compiled it,
# and a file named like a test contributed none. rustc looks beside a file only
# from a crate root, a `mod.rs` or a `#[path]` target: an ordinary `foo.rs` owns
# `foo/`. And a cfg(test) gate on a module covers every module it declares.
# Measured on 61ccc12c14: 205 files rustc reaches ONLY through a cfg(test) gate
# were scanned as production -- 116 made production by an unguarded `mod` in a
# parent that is itself test-only (a `mod.rs` under a gated module), 89 reached
# by no edge the old rule read. Among the 89:
# tactic/mathverse_use_tests/trust_gate_tests/dependency_replay.rs, whose
# test-only `add_decl_structural` reddened add-decl-ratchet once 79a1983740 moved
# it out of an inline `#[cfg(test)] mod` (tactic/mod.rs declares
# `#[cfg(test)] mod mathverse_use_tests;`, the tree's only route to it). No file
# moved the other way.
#
# The rule, mirrored arm for arm by
# crates/clean-cli/src/cmd_replacement/rust_source_scope.rs and held to the same
# SET by `add_decl_scan_scope_matches_the_python_producer`:
#   1. ROOTS by Cargo's target layout: `src/lib.rs`, `src/main.rs`,
#      `src/bin/*.rs`, `src/bin/*/main.rs`, the same two shapes under `examples/`
#      and `benches/`, and a `build.rs` beside a `src/` directory are PRODUCTION
#      roots, whatever the file is named; the two shapes under `tests/`, and any
#      root inside a `tests` directory, are TEST roots.
#   2. A WALK from the roots carries, per module, the directory `mod x;` looks
#      in and whether a cfg-requires-test gate has been crossed. Declarations are
#      read from source with comments AND strings blanked; a `#[path]` or
#      `include!` edge counts only where its first byte is code. `x.rs` reached by
#      a plain `mod x;` owns `x/`; a `#[path]` target (resolved against the
#      declaring file's directory) owns its own directory, as rustc treats every
#      `#[path]` file as a `mod.rs`; `include!` text inherits the includer's
#      directories. A `mod x;` whose attribute run names an unconditional
#      `#[path]` has no default target. A declaration inside an inline `mod {}`
#      (brace depth > 0) is NOT walked: its directory depends on the inline chain.
#   3. PRODUCTION = reached by the walk with no gate crossed, plus every target
#      of an UNGUARDED edge out of a file that is not test-only, looked up
#      loosely (beside the file, in its own stem directory and in every walked
#      directory, at any depth). Production wins over everything below.
#   4. TEST-ONLY = reached by the walk only through a gate (or from a test root),
#      or named like a test, and not production. A file the walk never reaches is
#      never made test-only by a declaration -- that was the self-vouching orphan
#      route of r13/r14 -- and is scanned unless its NAME says test.
# ---------------------------------------------------------------------------

_NOT_NEWLINE_RE = re.compile(r"[^\n]")
_MOD_WORD_RE = re.compile(r"\bmod\b")
_UNCONDITIONAL_PATH_ATTR_RE = re.compile(r"#\[\s*path\s*=")
_ROOT_DIR_SHAPES = ((("src", "bin"), "prod"), (("examples",), "prod"),
                    (("benches",), "prod"), (("tests",), "test"))


def _blank_noncode_span(match):
    """`_blank`, faster: the same spaces, the same newlines."""
    text = match.group(0)
    return _NOT_NEWLINE_RE.sub(" ", text) if "\n" in text else " " * len(text)


def _blank_comment_span(match):
    """`_blank_comment_only`, faster: comments blanked, literals kept verbatim."""
    text = match.group(0)
    return _blank_noncode_span(match) if text[:2] in ("//", "/*") else text


def _target_root_kind(path, rel):
    """'prod' / 'test' / None: the Cargo target this file's path SHAPE names.

    A root inside a `tests` directory (an integration test, or a fixture crate
    under one) is a TEST root; any other root is PRODUCTION whatever its file
    name, because `cargo build` compiles `src/bin/test_tool.rs` as surely as
    `src/bin/tool.rs`."""
    kind = _target_shape(path)
    if kind and any(part in ("tests", "tests2") for part in rel.parts[:-1]):
        return "test"
    return kind


def _target_shape(path):
    parts = path.parts
    n = len(parts)
    name = parts[-1]
    if n >= 2 and parts[-2] == "src" and name in ("lib.rs", "main.rs"):
        return "prod"
    if name == "build.rs" and (path.parent / "src").is_dir():
        return "prod"
    for base, kind in _ROOT_DIR_SHAPES:
        k = len(base)
        if n >= k + 1 and tuple(parts[n - 1 - k:n - 1]) == base:
            return kind
        if n >= k + 2 and name == "main.rs" and tuple(parts[n - 2 - k:n - 2]) == base:
            return kind
    return None


def _attribute_run_names_path(src, at):
    """Does the attribute run ending at `at` carry an unconditional `#[path = ..]`?"""
    head = src[:at]
    while True:
        m = _ATTR_RUN_RE.search(head)
        if not m:
            return False
        if _UNCONDITIONAL_PATH_ATTR_RE.match(m.group(0)):
            return True
        head = head[:m.start()]


def _depths_at(full, offsets):
    """{offset: brace depth} over code-only text, for the requested offsets."""
    out = {}
    depth = 0
    prev = 0
    for off in sorted(set(offsets)):
        seg = full[prev:off]
        depth += seg.count("{") - seg.count("}")
        prev = off
        out[off] = depth
    return out


def _module_edges(raw, rel):
    """(decls, path_edges, include_edges, unresolved) for one file.

    decls:         (stem, gated, top_level, has_default_target)
    path_edges:    (target, gated, top_level)
    include_edges: (target, gated, top_level)
    """
    # A file with no `mod` word, no `path` and no `include!` anywhere has no edge:
    # blanking only ever turns characters into spaces, so this is a superset test.
    if not _MOD_WORD_RE.search(raw) and "path" not in raw and "include!" not in raw:
        return [], [], [], []
    full = NONCODE_RE.sub(_blank_noncode_span, raw)       # == strip_noncode(raw)
    decl_hits = [(m.group(1), m.start()) for m in _MOD_DECL_ANY_RE.finditer(full)]
    if not decl_hits and "path" not in raw and "include!" not in raw:
        return [], [], [], []
    keep = NONCODE_RE.sub(_blank_comment_span, raw)       # == strip_comments_keep_strings(raw)
    path_hits = [(off, tgt, cond) for off, tgt, cond in _path_edges(keep)
                 if full[off:off + 1] == "#"]
    # An `include!` spelled inside a literal is not an edge, nor an unread one.
    code_includes = keep
    for m in reversed(list(_INCLUDE_CALL_RE.finditer(keep))):
        if full[m.start():m.start() + 1] != "i":
            code_includes = (code_includes[:m.start()] + " " * (m.end() - m.start())
                             + code_includes[m.end():])
    before = len(_UNRESOLVED_EDGES)
    include_hits = list(_include_edges(code_includes, rel))
    unresolved = _UNRESOLVED_EDGES[before:]
    del _UNRESOLVED_EDGES[before:]
    depth = _depths_at(full, [o for _, o in decl_hits] + [o for o, _, _ in path_hits]
                       + [o for o, _ in include_hits])
    decls = [(stem, _attribute_run_is_cfg_test(keep, off), depth[off] == 0,
              not _attribute_run_names_path(keep, off))
             for stem, off in decl_hits]
    paths = [(tgt, cond or _attribute_run_is_cfg_test(keep, off), depth[off] == 0)
             for off, tgt, cond in path_hits]
    includes = [(tgt, _attribute_run_is_cfg_test(keep, off), depth[off] == 0)
                for off, tgt in include_hits]
    return decls, paths, includes, unresolved


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
    if not scope.is_dir():
        _CLASSIFY_CACHE[key] = (set(), set())
        return set(), set()
    sources = {}
    for rs in scope.rglob("*.rs"):
        try:
            sources[rs.resolve()] = rs.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
    canon = {}

    def known(candidate):
        """The resolved source file `candidate` names, or None."""
        if candidate not in canon:
            resolved = candidate.resolve() if candidate.exists() else None
            canon[candidate] = resolved if resolved in sources else None
        return canon[candidate]

    rels = {path: path.relative_to(root) for path in sources}
    named = {path for path, rel in rels.items() if is_test_path(rel)}
    # A file headed `#![cfg(test)]` (`headed_cfg_test`) is gated from its first
    # item: no non-test build compiles it or anything it declares, whatever
    # reaches it, so the walk gates it and the loose closure never reads it.
    headed = {path for path, raw in sources.items() if headed_cfg_test(raw)}
    edges, unresolved = {}, {}
    for path, raw in sources.items():
        decls, paths, includes, unread = _module_edges(raw, rels[path])
        edges[path] = (decls, paths, includes)
        unresolved[path] = unread

    # (2) the walk: state = (file, dir `#[path]` resolves in, dir `mod x;` looks in, gated)
    work = [(path, path.parent, path.parent, kind == "test")
            for path in sources for kind in (_target_root_kind(path, rels[path]),) if kind]
    seen, gated_bits, walked_dirs, path_dirs = set(), {}, {}, {}
    while work:
        state = work.pop()
        if state in seen:
            continue
        seen.add(state)
        path, pdir, mdir, gated = state
        gated = gated or path in headed
        gated_bits.setdefault(path, set()).add(gated)
        walked_dirs.setdefault(path, set()).add(mdir)
        path_dirs.setdefault(path, set()).add(pdir)
        decls, paths, includes = edges[path]
        for stem, guard, top, has_default in decls:
            if not (top and has_default):
                continue
            for cand in (mdir / f"{stem}.rs", mdir / stem / "mod.rs"):
                target = known(cand)
                if target is not None:
                    work.append((target, target.parent, mdir / stem, gated or guard))
        for tgt, guard, top in paths:
            target = known(pdir / tgt) if top else None
            if target is not None:
                work.append((target, target.parent, target.parent, gated or guard))
        for tgt, guard, top in includes:
            target = known(path.parent / tgt) if top else None
            if target is not None:
                work.append((target, pdir, mdir, gated or guard))
    reached_open = {path for path, bits in gated_bits.items() if False in bits}
    reached_gated_only = {path for path, bits in gated_bits.items() if False not in bits}

    # (3) production: the open walk, then every unguarded edge out of a file that
    # is not test-only, looked up loosely.
    def loose_targets(path):
        decls, paths, includes = edges[path]
        mdirs = {path.parent, path.parent / path.stem} | walked_dirs.get(path, set())
        pdirs = {path.parent} | path_dirs.get(path, set())
        for stem, guard, _top, _default in decls:
            if not guard:
                for d in mdirs:
                    for cand in (d / f"{stem}.rs", d / stem / "mod.rs"):
                        target = known(cand)
                        if target is not None:
                            yield target
        for tgt, guard, _top in paths:
            if not guard:
                for d in pdirs:
                    target = known(d / tgt)
                    if target is not None:
                        yield target
        for tgt, guard, _top in includes:
            if not guard:
                target = known(path.parent / tgt)
                if target is not None:
                    yield target

    prod = set(reached_open)
    work = [path for path in sources if path not in headed and (
            path in reached_open or (path not in reached_gated_only and path not in named))]
    done = set()
    while work:
        path = work.pop()
        if path in done:
            continue
        done.add(path)
        for target in loose_targets(path):
            prod.add(target)
            if target not in done and target not in headed:
                work.append(target)
    # (4) test-only: gated-only or test-named, and never production; a headed
    # file is test-only whatever reaches it.
    test_only = ((reached_gated_only | named) - prod) | headed
    prod -= headed
    # An `include!` this cannot read is a red wherever the file is scanned.
    for path in sorted(sources):
        if path not in test_only:
            _UNRESOLVED_EDGES.extend(unresolved[path])
    _CLASSIFY_CACHE[key] = (prod, test_only)
    return prod, test_only


# Known answers for the MODULE TREE, beside the cfg lattice's and the edge
# extractor's tables. Each case is (name, {crate-relative path: source},
# crate-relative file, want): want "test" means test-only, "prod" means
# production, "scan" means scanned (production, or reached by no route).
_MODULE_TREE_CASES = (
    ("a module under a cfg(test) gate is test code, through a non-mod.rs parent "
     "that owns its directory (the 79a1983740 shape)",
     {"src/lib.rs": "#[cfg(test)]\nmod a;\n", "src/a.rs": "mod b;\n", "src/a/b.rs": ""},
     "src/a/b.rs", "test"),
    ("the same file declared WITHOUT cfg(test) is production",
     {"src/lib.rs": "mod a;\n", "src/a.rs": "mod b;\n", "src/a/b.rs": ""},
     "src/a/b.rs", "prod"),
    ("the gate is carried through a test-named module",
     {"src/lib.rs": "#[cfg(test)]\nmod x_tests;\n", "src/x_tests.rs": "mod deep;\n",
      "src/x_tests/deep.rs": ""},
     "src/x_tests/deep.rs", "test"),
    ("a test-named module declared without a gate is production, and so is its child",
     {"src/lib.rs": "mod x_tests;\n", "src/x_tests.rs": "mod deep;\n",
      "src/x_tests/deep.rs": ""},
     "src/x_tests/deep.rs", "prod"),
    ("a gated declaration in a non-mod.rs file does not mask the SIBLING of its target",
     {"src/lib.rs": "mod a;\n", "src/a.rs": "#[cfg(test)]\nmod b;\n", "src/a/b.rs": "",
      "src/b.rs": ""},
     "src/b.rs", "scan"),
    ("...while its real target is test code",
     {"src/lib.rs": "mod a;\n", "src/a.rs": "#[cfg(test)]\nmod b;\n", "src/a/b.rs": "",
      "src/b.rs": ""},
     "src/a/b.rs", "test"),
    ("a file nothing compiles cannot vouch a gate for another file",
     {"src/lib.rs": "pub fn f() {}\n",
      "src/orphan.rs": "#[cfg(test)]\n#[path = \"victim.rs\"]\nmod v;\n", "src/victim.rs": ""},
     "src/victim.rs", "scan"),
    ("nor can a test-named file nothing compiles",
     {"src/lib.rs": "pub fn f() {}\n",
      "src/zz_tests.rs": "#[path = \"victim.rs\"]\nmod v;\n", "src/victim.rs": ""},
     "src/victim.rs", "scan"),
    ("a cfg(test) `#[path]` cannot make a crate root test code",
     {"src/lib.rs": "#[cfg(test)]\n#[path = \"bin/tool.rs\"]\nmod tool;\n",
      "src/bin/tool.rs": "fn main() {}\n"},
     "src/bin/tool.rs", "prod"),
    ("a binary named like a test is a production root, and so is its module",
     {"src/lib.rs": "", "src/bin/test_tool.rs": "mod helper;\nfn main() {}\n",
      "src/bin/helper.rs": ""},
     "src/bin/helper.rs", "prod"),
    ("an integration test's module is test code",
     {"src/lib.rs": "", "tests/it.rs": "mod helper;\n", "tests/helper_impl.rs": "",
      "tests/helper.rs": ""},
     "tests/helper.rs", "test"),
    ("a `#[path]` target owns its own directory",
     {"src/lib.rs": "#[cfg(test)]\n#[path = \"t/x_impl.rs\"]\nmod x;\n",
      "src/t/x_impl.rs": "mod y;\n", "src/t/y.rs": ""},
     "src/t/y.rs", "test"),
    ("an `#[path]` declaration has no default target",
     {"src/lib.rs": "#[cfg(test)]\n#[path = \"x_impl.rs\"]\nmod x;\n",
      "src/x_impl.rs": "", "src/x.rs": ""},
     "src/x.rs", "scan"),
    ("`include!` text resolves `mod` where its includer does, under the include's gate",
     {"src/lib.rs": "#[cfg(test)]\ninclude!(\"inc.rs\");\n", "src/inc.rs": "mod sub;\n",
      "src/sub.rs": ""},
     "src/sub.rs", "test"),
    ("a declaration inside an inline module is not resolved as a gate",
     {"src/lib.rs": "mod inner {\n    #[cfg(test)]\n    mod deep;\n}\n",
      "src/inner/deep.rs": "", "src/deep.rs": ""},
     "src/inner/deep.rs", "scan"),
    ("a file headed `#![cfg(test)]` is test code even under an ungated `mod`",
     {"src/lib.rs": "mod a;\n", "src/a.rs": "// c\n#![cfg(test)]\nmod b;\n", "src/a/b.rs": ""},
     "src/a.rs", "test"),
    ("...and so is every module it declares",
     {"src/lib.rs": "mod a;\n", "src/a.rs": "// c\n#![cfg(test)]\nmod b;\n", "src/a/b.rs": ""},
     "src/a/b.rs", "test"),
    ("the head rule reads only a leading `#![cfg(test)]`: one after another inner "
     "attribute (which rustc honours) is still scanned, the fail-safe direction",
     {"src/lib.rs": "mod a;\n", "src/a.rs": "#![allow(dead_code)]\n#![cfg(test)]\nmod b;\n",
      "src/a/b.rs": ""},
     "src/a/b.rs", "scan"),
    ("a declaration spelled inside a string literal is not an edge",
     {"src/lib.rs": "pub const S: &str = \"\n#[cfg(test)]\nmod fake;\n\";\n",
      "src/fake.rs": ""},
     "src/fake.rs", "scan"),
)


def module_tree_failures():
    """Cases the module-tree classification answers wrongly. Empty is correct."""
    bad = []
    for name, files, target, want in _MODULE_TREE_CASES:
        tmp = Path(tempfile.mkdtemp(prefix="module_tree_case_")).resolve()
        try:
            (tmp / ".git").mkdir()
            crate = tmp / "crates" / "c"
            for rel, text in files.items():
                (crate / rel).parent.mkdir(parents=True, exist_ok=True)
                (crate / rel).write_text(text)
            _CLASSIFY_CACHE.pop(str(tmp), None)
            prod, test_only = classify_paths(tmp)
            _CLASSIFY_CACHE.pop(str(tmp), None)
            path = (crate / target).resolve()
            got = "prod" if path in prod else "test" if path in test_only else "scan"
            if got != want and not (want == "scan" and got == "prod"):
                bad.append(f"{name}: {target} is {got}, want {want}")
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    return bad


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
            # NONCODE_RE rather than an ad-hoc scan. (Nesting only since
            # 2026-11-16: until then the block-comment pattern closed at the
            # first `*/`, whatever this comment said.)
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



# Rust non-code spans, in the order a lexer would see them. Ordered
# alternation matters: a `//` inside a string literal must not win, so the
# string alternatives come after the comment ones only where they cannot
# overlap — block and line comments first, then raw strings (whose `#`-fence
# backreference makes them unambiguous), then plain strings, then chars.
#
# BEGIN shared Rust lexer (2026-11-16; docs/issues/2026-11-16-python-rust-lexer-copies.md).
# Kept byte-identical in every copy; the copies are listed in that issue.
# Block comments NEST in Rust (`/* a /* b */ c */` is one comment), which no `re`
# pattern matches, so the pattern matches only the OPENER and `_NestingLexer`
# extends it to its balanced close. A raw-string prefix needs a token boundary:
# to rustc, `1r"x"` (a suffixed integer), `'r"x"` (a lifetime) and `xr"x"` (an
# edition-2018 identifier) are a token followed by an ordinary string.
_NONCODE_TOKEN_RE = re.compile(
    r"/\*"                                              # block comment OPENER (nests)
    r"|//[^\n]*"                                        # line comment
    r'|(?<![A-Za-z0-9_\'])[bc]?r(#*)"(?:.|\n)*?"\1'      # raw string   r"..."  r#"..."#
    r'|b?"(?:\\.|[^"\\])*"'                             # string literal
    # char literal; the `\x..` and `\u{..}` escapes rustc accepts (rust_modules.ESC_CHAR)
    r"|'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f](?:_*[0-9A-Fa-f]){0,5}_*\}|.)|[^\\'])'",
    re.DOTALL,
)


class _NestingLexer:
    """`_NONCODE_TOKEN_RE` with each block-comment opener extended to its balanced close.

    Answers `sub` and `finditer` as a compiled pattern does, so every caller
    reads as before. Leftmost `/*` and `*/` tokens are rustc's own greedy
    reading (`/*/` opens, `*/*` closes). An unterminated comment, which rustc
    refuses, runs to the end of the text. A comment match has no groups that
    participate: `group(1)` is None, as for every match but a raw string's.
    A text with no `/*` at all holds no block comment, so the pattern alone is
    exact there; that is 98% of the tree's bytes, and it keeps the old speed.
    """

    _BLOCK_RE = re.compile(r"/\*|\*/")
    _SPAN_RE = re.compile(r"[\s\S]*(?:(x))?")

    def finditer(self, text, pos=0, endpos=None):
        """As `Pattern.finditer`: `endpos` ends the text, for a comment too."""
        stop = len(text) if endpos is None else max(0, min(endpos, len(text)))
        if "/*" not in text:
            yield from _NONCODE_TOKEN_RE.finditer(text, pos, stop)
            return
        while True:
            for m in _NONCODE_TOKEN_RE.finditer(text, pos, stop):
                if m.group(0) != "/*":
                    yield m
                    continue
                depth, end = 0, stop
                for tok in self._BLOCK_RE.finditer(text, m.start(), stop):
                    depth += 1 if tok.group(0) == "/*" else -1
                    if depth == 0:
                        end = tok.end()
                        break
                yield self._SPAN_RE.match(text, m.start(), end)
                pos = end
                break  # resume the token scan after the whole comment
            else:
                return

    def sub(self, repl, text):
        if "/*" not in text:
            return _NONCODE_TOKEN_RE.sub(repl, text)
        out, pos = [], 0
        for m in self.finditer(text):
            out.append(text[pos:m.start()])
            out.append(repl(m))
            pos = m.end()
        out.append(text[pos:])
        return "".join(out)


NONCODE_RE = _NestingLexer()


# A file-level `#![cfg(test)]` configures the whole module out of every
# non-test build, whatever route reaches the file: a `mod` declaration, a
# `#[path]`, a symlink, a case alias on a case-insensitive volume; `include!`
# refuses an inner attribute outright (each probed with rustc on 2026-11-16,
# docs/issues/2026-11-16-verdict-set-rmint-outlined-test-module.md). So it is
# evidence the file carries itself, needing no module graph. Only blank lines
# and `//` line comments may precede it: a line comment ends at `\n` alone (a
# U+2028 inside one does not end it, so lines split on `\n`, never
# `splitlines`), while a block comment nests and a string or another attribute
# would need this lexer. Any other head keeps the file production.
_HEAD_SKIP_RE = re.compile(r"[ \t\r]*(?://[^\n]*)?")
_HEAD_CFG_TEST_RE = re.compile(r"[ \t\r]*#!\[[ \t]*cfg[ \t]*\([ \t]*test[ \t]*\)[ \t]*\][ \t\r]*")


def headed_cfg_test(text):
    """Is the file's first line that is not blank or a `//` comment exactly `#![cfg(test)]`?"""
    for line in text.split("\n"):
        if _HEAD_CFG_TEST_RE.fullmatch(line):
            return True
        if not _HEAD_SKIP_RE.fullmatch(line):
            return False
    return False


_HEAD_CASES = (
    ("// c\n//! doc\n\n#![cfg(test)]\nfn f() {}\n", True),
    ("// c\r\n\r\n#![ cfg ( test ) ]\r\nfn f() {}\n", True),
    ("/* c */\n#![cfg(test)]\n", False),
    ("#![allow(dead_code)]\n#![cfg(test)]\n", False),
    ('#![cfg(any(test, feature = "x"))]\n', False),
    ("#![cfg(not(test))]\n", False),
    ("#![rustfmt::cfg(test)]\n", False),
    ("#[cfg(test)]\nmod m;\n", False),
    ("fn f() {}\n#![cfg(test)]\n", False),
    ("// c\u2028#![cfg(test)]\n", False),
)


def _lexer_blank(m):
    return "".join("\n" if ch == "\n" else " " for ch in m.group(0))


def _lexer_blank_comments(m):
    return _lexer_blank(m) if m.group(0).startswith(("//", "/*")) else m.group(0)


# (name, source, mode, must survive, must vanish), each a reading rustc makes.
# The old pattern made every reading not marked "guard" wrongly; a guard pins one
# it already made, against a regression in the new lexer.
_LEXER_CASES = (
    ("nested comment hides a cfg", "/* /* */ #[cfg(test)] // */\nmod m;\n", "comments",
     ("mod m;",), ("cfg(test)",)),
    ("nested comment holds a quote", '/* /* */ " */\nconst A: &str = "//"; #[path = "d.rs"] mod s;\n',
     "comments", ('#[path = "d.rs"] mod s;',), ()),
    ("three levels", "/* 1 /* 2 /* 3 */ 2 */ 1 */ fn f() {}\n", "all", ("fn f() {}",), ("1", "2", "3")),
    ("unterminated runs to the end", "/* a /* b */\nfn f() {}\n", "all", (), ("fn",)),
    ("guard: `/*/` opens", "/*/ c */ fn f() {}\n", "all", ("fn f() {}",), ("c",)),
    ("guard: an opener in a string", 'let s = "/*"; fn f() {}\n', "all", ("fn f() {}",), ()),
    ("guard: `//*` is a line comment", "//* c\nfn f() {}\n", "all", ("fn f() {}",), ("c",)),
    ("`1r` is a suffixed integer", 'eat!(1r"\\" // "); #[path = "d.rs"] mod m;\n', "comments",
     ('#[path = "d.rs"] mod m;',), ()),
    ("`'r` is a lifetime", 'eat!(\'r"\\" // "); #[path = "d.rs"] mod m;\n', "comments",
     ('#[path = "d.rs"] mod m;',), ()),
    ("`xr` is an identifier", 'eat!(xr"\\" // "); #[path = "d.rs"] mod m;\n', "comments",
     ('#[path = "d.rs"] mod m;',), ()),
    ("guard: `cr` opens a raw C string", 'x(cr"\\" // "); #[path = "d.rs"] mod m;\n', "comments", (), ("#[path",)),
    ("guard: `br` opens a raw byte string", 'x(br"\\" // "); #[path = "d.rs"] mod m;\n', "comments",
     (), ("#[path",)),
    ("`\\x..` and `\\u{..}` are char escapes",
     "let c = ['\\x41', b'\\xFF', '\\u{1F_600}', '\\u{41_}', '\\u{10FFFF}']; fn f() {}\n", "all",
     ("fn f() {}", ", b"), ("x41", "xFF", "1F_600", "41_", "10FFFF")),
    ("guard: `\\'`, `\\\\` and `\\\"` are char escapes", "let q = ['\\'', '\\\\', '\\\"']; fn f() {}\n",
     "all", ("fn f() {}", ", "), ("\\",)),
)


def lexer_failures():
    """Cases this lexer reads differently from rustc. Empty is correct."""
    bad = []
    for name, src, mode, keep, gone in _LEXER_CASES:
        out = NONCODE_RE.sub(_lexer_blank if mode == "all" else _lexer_blank_comments, src)
        if len(out) != len(src) or any(k not in out for k in keep) or any(g in out for g in gone):
            bad.append(name)
    groups = [m.group(1) for m in NONCODE_RE.finditer('/* /* */ */ r#"x"# "y"')]
    if groups != [None, "#", None]:
        bad.append(f"group(1) per match: {groups}")
    window = [m.span() for m in NONCODE_RE.finditer('a /* b /* c */ d */ "e"', 2, 15)]
    if window != [(2, 15)]:
        bad.append(f"pos/endpos window: {window}")
    bad += [f"file head {src!r}" for src, want in _HEAD_CASES if headed_cfg_test(src) is not want]
    return bad
# END shared Rust lexer.


def _blank(match: re.Match[str]) -> str:
    """Replace a non-code span with spaces, preserving newlines.

    Line numbers and column positions therefore survive stripping exactly, so a
    hit's reported line still indexes the ORIGINAL file.
    """
    return "".join("\n" if ch == "\n" else " " for ch in match.group(0))


def strip_noncode(text: str) -> str:
    """Blank out comments and string/raw-string/char literals.

    Brace counting over the raw text is wrong: `'{'`, `"}"` and a `{` inside a
    doc comment all unbalance it. Measured 2026-08-22 over the 6,815 .rs files
    under crates/: raw counting leaves 22 files apparently unbalanced (and a
    gate that fails closed on 22 healthy files is a gate that gets deleted);
    after stripping, ZERO are unbalanced. 4.8 s for the whole tree.
    """
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


def scan_file(path: Path, rel: Path) -> tuple[list[dict], list[dict]]:
    """(production hits, cfg(test) hits) for one file. Raises on unbalanced braces."""
    raw_text = path.read_text(errors="strict")
    raw_lines = raw_text.splitlines()
    lines = strip_noncode(raw_text).splitlines()
    prod: list[dict] = []
    tested: list[dict] = []
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
                    # the attribute annotated something that is not a `mod` (a
                    # fn, a use, a const): not a block, so nothing to track.
                    pending_cfg = False
        else:
            depth += line.count("{") - line.count("}")
            if depth <= 0:
                in_cfg_test = False
        # AUDIT r12 M12-4: the definition exclusion was LINE-granular -- a real
        # call sharing a line with a matching `fn` header was dropped WHOLE.
        # Measured with a one-line `#[rustfmt::skip] impl BackdoorExt for
        # Environment { fn add_decl_unchecked(..) { Environment::add_decl_unchecked(self, d) } }`
        # in a production kernel file: rc=0 on one line, rc=1 split over two.
        # A definition is blanked over the SPAN it occupies, before matching, so
        # calls elsewhere on the same line still count.
        line = DEFINITION_RE.sub(lambda d: " " * len(d.group(0)), line)
        # AUDIT r13 M13-4: this was `search`, i.e. AT MOST ONE hit per line,
        # while both siblings use `finditer`. So `occurrences` counted LINES,
        # not calls, and a second `add_decl_unchecked` on an already-sanctioned
        # line was absorbed with no count change and no `// SOUNDNESS:`
        # obligation -- in the file CLAUDE.md names as the reference
        # implementation, feeding the deny-sorry launch evidence. The M12-4
        # comment eight lines above, asserting that calls elsewhere on the line
        # still count, was true of the blanking and false of the counting.
        matches = list(CALL_RE.finditer(line))
        if not matches:
            continue
        for m in matches:
        # AUDIT r11 M11-6: the r10 whole-FILE exclusion of env/trusted_ext.rs is
        # RETIRED. It was a strict coverage regression -- one extra
        # `self.add_decl_unchecked(..)` planted INSIDE an existing delegation
        # body was invisible to every scanner, while the pre-r10 scanner caught
        # it -- and it is the shape CLAUDE.md forbids: "A skip list that names a
        # FILE is a suppression; a row that names a SITE, caps it, and points at
        # the comment is an account." The two delegations are capped
        # production_sites rows now, each with its `// SOUNDNESS:` comment.
            hit = {
                "file": str(rel),
                "line": lineno,
                "method": f"add_decl_{m.group(1)}",
                "text": raw_lines[lineno - 1].strip()[:100],
            }
            (tested if in_cfg_test else prod).append(hit)
    if in_cfg_test:
        raise ValueError(
            f"{rel}: a #[cfg(test)] mod block never closed (brace tracking ran off the "
            f"end of the file). Refusing to classify this file — fix the source or the "
            f"tracker; an unreadable file is not a clean one."
        )
    return prod, tested



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


def has_soundness_comment(path: Path, lineno: int, prev_call_line: int = 0) -> bool:
    lines = path.read_text(errors="strict").splitlines()
    start = _owner_floor(lines, lineno, prev_call_line)
    return any(SOUNDNESS_RE.search(l) for l in lines[start:lineno])


def measure(root: Path) -> tuple[list[dict], list[dict], list[str]]:
    # AUDIT r15 M15-1: the classification cache is keyed on the ROOT alone, so a
    # second measure() in one process answered from the first tree.  Production
    # calls measure() exactly once, so clearing here costs nothing there -- but
    # a selftest that mutates the tree between arms was silently re-reading the
    # first arm's answer, which makes every later arm vacuous.  Measured: an
    # eight-guard sweep reported the FIRST guard's verdict eight times.
    _CLASSIFY_CACHE.clear()
    _UNRESOLVED_EDGES.clear()
    prod: list[dict] = []
    tested: list[dict] = []
    errors: list[str] = []
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
            p, t = scan_file(path, rel)
        except (OSError, UnicodeDecodeError) as exc:
            errors.append(f"cannot read {rel}: {exc}")
            continue
        except ValueError as exc:
            errors.append(str(exc))
            continue
        prod.extend(p)
        tested.extend(t)
    return prod, tested, errors


def load_ratchet(root: Path) -> dict:
    path = root / RATCHET_REL
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        raise SystemExit(f"FAIL: cannot read {RATCHET_REL}: {exc}")


def run(
    root: Path,
    list_only: bool = False,
    sanctioned: dict[tuple[str, str], int] | None = None,
) -> int:
    sanctioned = SANCTIONED_SITES if sanctioned is None else sanctioned
    ratchet = load_ratchet(root)
    prod, tested, errors = measure(root)

    accounted: dict[tuple[str, str], str] = {}
    for key, method in (
        ("add_decl_structural_production_sites", "add_decl_structural"),
        ("add_decl_unchecked_production_sites", "add_decl_unchecked"),
    ):
        for site in ratchet.get(key, []) or []:
            if isinstance(site, dict) and "file" in site:
                accounted[(site["file"], site.get("method", method))] = "counted"
    disagreements = ratchet.get("add_decl_measured_disagreements", []) or []
    for row in disagreements:
        if isinstance(row, dict) and "file" in row and "method" in row:
            accounted[(row["file"], row["method"])] = "disagreement"

    if list_only:
        print(f"production sites ({len(prod)}):")
        for h in prod:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}")
        print(f"inline cfg(test) sites: {len(tested)}")
        return 0

    ok = True
    if errors:
        ok = False
        print("FAIL: the add_decl scanner could not classify part of the tree:", file=sys.stderr)
        for e in errors:
            print(f"  {e}", file=sys.stderr)

    unaccounted = [h for h in prod if (h["file"], h["method"]) not in accounted]
    if unaccounted:
        ok = False
        print("FAIL: unaccounted add_decl_* bypass call site(s) in production code:", file=sys.stderr)
        for h in unaccounted:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}", file=sys.stderr)
        print(
            "  -> a declaration registered without type checking. Add a // SOUNDNESS: "
            "comment at the call AND an entry under data/unchecked_decl_ratchet.json "
            "(add_decl_*_production_sites, which raises the ratchet count and is seen by "
            "scripts/deny_sorry_gate.sh).",
            file=sys.stderr,
        )

    # Every accounted site must actually carry its SOUNDNESS comment — the half
    # of the CLAUDE.md rule no gate has enforced.
    _prev_line_in_file: dict[str, int] = {}
    for h in prod:
        _prev = _prev_line_in_file.get(h["file"], 0)
        _prev_line_in_file[h["file"]] = h["line"]
        if (h["file"], h["method"]) not in accounted:
            continue
        if not has_soundness_comment(root / h["file"], h["line"], _prev):
            ok = False
            print(
                f"FAIL: {h['file']}:{h['line']} {h['method']} is accounted for in the ratchet "
                f"but carries no // SOUNDNESS: comment within {SOUNDNESS_WINDOW} lines above "
                f"the call.",
                file=sys.stderr,
            )

    # A ratchet row may only speak for a site the CODE allowlist sanctions. An
    # artifact that could legalise its own bypass is not a ratchet.
    for (f, m), kind in sorted(accounted.items()):
        if (f, m) not in sanctioned:
            ok = False
            print(
                f"FAIL: data/unchecked_decl_ratchet.json records a {kind} row for {f} / {m}, "
                f"which is NOT in SANCTIONED_SITES in {Path(__file__).name}. A ratchet row cannot "
                f"authorize a bypass by itself — add the site to the code allowlist, with its "
                f"soundness argument, or remove the bypass.",
                file=sys.stderr,
            )

    # A sanctioned site may not quietly grow extra call sites either.
    per_site: dict[tuple[str, str], int] = {}
    for h in prod:
        key = (h["file"], h["method"])
        per_site[key] = per_site.get(key, 0) + 1
    for key, seen in sorted(per_site.items()):
        cap = sanctioned.get(key)
        if cap is not None and seen > cap:
            ok = False
            print(
                f"FAIL: {key[0]} / {key[1]} has {seen} production call sites but "
                f"SANCTIONED_SITES caps it at {cap}. A sanctioned bypass does not license "
                f"further copies of itself.",
                file=sys.stderr,
            )

    # A ratchet row that no longer matches a live site is STALE. Debt may be
    # paid off, but it is not allowed to evaporate unremarked.
    live = {(h["file"], h["method"]) for h in prod}
    for (f, m), kind in sorted(accounted.items()):
        if (f, m) not in live:
            ok = False
            print(
                f"FAIL: data/unchecked_decl_ratchet.json records a {kind} row for "
                f"{f} / {m} and no such production call site exists in the tree. "
                f"If the bypass was removed, remove the row (the ratchet only goes down).",
                file=sys.stderr,
            )

    counts = {"add_decl_structural": 0, "add_decl_unchecked": 0}
    for h in prod:
        if accounted.get((h["file"], h["method"])) == "counted":
            counts[h["method"]] += 1
    for method, declared_key in (
        ("add_decl_structural", "add_decl_structural_count"),
        ("add_decl_unchecked", "add_decl_unchecked_count"),
    ):
        declared = ratchet.get(declared_key)
        if not isinstance(declared, int):
            ok = False
            print(f"FAIL: {RATCHET_REL} has no integer {declared_key}", file=sys.stderr)
            continue
        if counts[method] > declared:
            ok = False
            print(
                f"FAIL: measured {method} production sites {counts[method]} exceeds the "
                f"declared {declared_key}={declared}. A new bypass must be justified and "
                f"ratcheted, never absorbed.",
                file=sys.stderr,
            )

    if disagreements:
        print("ADD_DECL_RATCHET=disagreement — the tree and the counts do not agree:")
        for row in disagreements:
            print(f"  {row.get('file')} / {row.get('method')}: {row.get('reason', '(no reason given)')}")
            if row.get("reconciliation"):
                print(f"    owed: {row['reconciliation']}")

    if ok:
        print(
            f"OK: add_decl bypass ratchet — production sites: "
            f"structural={counts['add_decl_structural']}/"
            f"{ratchet.get('add_decl_structural_count')}, "
            f"unchecked={counts['add_decl_unchecked']}/"
            f"{ratchet.get('add_decl_unchecked_count')}, "
            f"disagreements={len(disagreements)}; "
            f"{len(tested)} inline cfg(test) sites excluded."
        )
        return 0
    return 1


# ---------------------------------------------------------------------------
# self-test: a gate that has never been shown to fail is not a gate
# ---------------------------------------------------------------------------

SELFTEST_CASES: list[tuple[str, str]] = []


def _selftest_tree() -> Path:
    """A minimal fake repo the mutation arms can edit freely."""
    tmp = Path(tempfile.mkdtemp(prefix="add_decl_selftest_"))
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
                "add_decl_structural_count": 0,
                "add_decl_unchecked_count": 0,
                "add_decl_structural_production_sites": [],
                "add_decl_unchecked_production_sites": [],
                "files": [],
                "last_updated": "selftest",
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
        "        env.add_decl_unchecked(d);\n"
        "    }\n"
        "}\n"
    )
    return tmp


def _write_ratchet(root: Path, doc: dict) -> None:
    (root / RATCHET_REL).write_text(json.dumps(doc, indent=2))


def _read_ratchet(root: Path) -> dict:
    return json.loads((root / RATCHET_REL).read_text())


def _quiet_run(root: Path, sanctioned: dict[tuple[str, str], int] | None) -> tuple[int, str]:
    """Run the gate capturing its output: a mutation arm is SUPPOSED to print
    failures, and a passing self-test that fills the log with `FAIL:` lines is a
    log nobody can read. The capture is replayed only when an arm misbehaves."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root, sanctioned=sanctioned)
    return rc, buf.getvalue()


def _arm(
    name: str,
    root: Path,
    expect: int,
    sanctioned: dict[tuple[str, str], int] | None = None,
) -> bool:
    rc, captured = _quiet_run(root, sanctioned)
    good = rc == expect
    print(f"  [{'ok ' if good else 'FAIL'}] {name}: exit {rc} (expected {expect})")
    if not good and captured:
        print("    --- the arm's own output ---")
        for line in captured.rstrip("\n").splitlines():
            print(f"    {line}")
    return good


# The fake tree's own allowlist. Arms 1-12 exercise the accounting logic on a
# synthetic path, so they carry a synthetic sanction; arms 13-16 use the REAL
# SANCTIONED_SITES and are the ones that pin the shipped allowlist.
FAKE_SANCTIONED: dict[tuple[str, str], int] = {
    ("crates/c/src/lib.rs", "add_decl_unchecked"): 1,
    ("crates/c/src/lib.rs", "add_decl_structural"): 1,
}

PLANT = "\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"


def selftest() -> int:
    passed = failed = 0
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
        print(f"  [ok  ] cfg lattice: {len(_CFG_LATTICE_CASES) + len(_CFG_HEAD_CASES)} spellings, "
              f"including the five audit r15 M15-1 found inverted and three tool paths")
        passed += 1
    _lexer_bad = lexer_failures()
    if _lexer_bad:
        print(f"  [FAIL] lexer: read differently from rustc: {_lexer_bad}")
        failed += 1
    else:
        print(f"  [ok  ] lexer: {len(_LEXER_CASES)} readings, nested comments and raw-string "
              f"prefixes among them")
        passed += 1
    _tree_bad = module_tree_failures()
    if _tree_bad:
        for _line in _tree_bad:
            print(f"  [FAIL] module tree: {_line}")
        failed += 1
    else:
        print(f"  [ok  ] module tree: {len(_MODULE_TREE_CASES)} layouts resolved as rustc "
              f"resolves them, including the 79a1983740 cfg(test) chain")
        passed += 1

    def check(
        name: str,
        root: Path,
        expect: int,
        sanctioned: dict[tuple[str, str], int] | None = FAKE_SANCTIONED,
    ) -> None:
        nonlocal passed, failed
        if _arm(name, root, expect, sanctioned):
            passed += 1
        else:
            failed += 1

    root = _selftest_tree()
    lib = root / "crates" / "c" / "src" / "lib.rs"
    baseline = lib.read_text()
    try:
        # 1. pristine tree: only a cfg(test) hit -> green
        check("pristine tree with only a cfg(test) bypass is green", root, 0)


        # AUDIT r15 M15-1, end to end: a bypass in a module the compiler
        # compiles in EVERY non-test build must be RED whatever the guard is
        # spelled like.  The five spellings below all read TEST-ONLY under the
        # r14 rule -- and every recorded demonstration for this scanner used an
        # UNGUARDED `mod`, which is why four rounds of hardening walked past it.
        lib.write_text(baseline)
        probe = root / "crates" / "c" / "src" / "probe.rs"
        probe.write_text(
            "pub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        for guard, want in (
            ("", 1),
            ("#[cfg(all(not(test)))]", 1),
            ("#[cfg(all(unix, not(test)))]", 1),
            ('#[cfg(all(not(test), feature = "math-overlays"))]', 1),
            ('#[cfg(all(any(test, feature = "x")))]', 1),
            ('#[cfg(all(unix, feature = "test-utils"))]', 1),
            ("#[cfg(test)]", 0),
            ('#[cfg(all(test, feature = "x"))]', 0),
        ):
            lib.write_text(baseline + "\n" + guard + "\nmod probe;\n")
            check(
                f"a production bypass behind {guard or '<no guard>'} is "
                f"{'RED' if want else 'green'}",
                root,
                want,
            )
        probe.unlink()
        lib.write_text(baseline)

        # 1c. The 79a1983740 shape, end to end: a bypass in a module the
        # compiler reaches only through a cfg(test) gate one file up -- through
        # an ordinary `chain.rs` that owns `chain/` -- is test code; the same
        # files with that gate removed are production and RED.
        chain = root / "crates" / "c" / "src" / "chain.rs"
        chain_dir = root / "crates" / "c" / "src" / "chain"
        chain_dir.mkdir()
        chain.write_text("mod deep;\n")
        (chain_dir / "deep.rs").write_text(
            "pub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        for guard, want in (("#[cfg(test)]", 0), ("", 1)):
            lib.write_text(baseline + "\n" + guard + "\nmod chain;\n")
            check(
                f"a bypass in chain/deep.rs under `{guard or '<no guard>'} mod chain;` is "
                f"{'RED' if want else 'green'}",
                root,
                want,
            )
        shutil.rmtree(chain_dir)
        chain.unlink()
        lib.write_text(baseline)

        # 2. a production bypass, unaccounted -> RED
        lib.write_text(baseline + "\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n")
        check("NEW unaccounted production add_decl_unchecked is RED", root, 1)

        # 3. same, but accounted AND with a SOUNDNESS comment -> green
        doc = _read_ratchet(root)
        doc["add_decl_unchecked_count"] = 1
        doc["add_decl_unchecked_production_sites"] = [
            {"file": "crates/c/src/lib.rs", "method": "add_decl_unchecked", "trust": "selftest"}
        ]
        _write_ratchet(root, doc)
        lib.write_text(
            baseline
            + "\n// SOUNDNESS: selftest justification.\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        check("accounted + SOUNDNESS-commented production bypass is green", root, 0)

        # 4. accounted but the SOUNDNESS comment removed -> RED
        lib.write_text(baseline + "\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n")
        check("accounted site whose SOUNDNESS comment was deleted is RED", root, 1)

        # 5. count lowered below the measured sites -> RED
        lib.write_text(
            baseline
            + "\n// SOUNDNESS: selftest justification.\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        doc = _read_ratchet(root)
        doc["add_decl_unchecked_count"] = 0
        _write_ratchet(root, doc)
        check("measured sites exceeding the declared count is RED", root, 1)

        # 6. the bypass removed but the row left behind -> RED (stale)
        lib.write_text(baseline)
        doc["add_decl_unchecked_count"] = 1
        _write_ratchet(root, doc)
        check("a ratchet row with no live call site is RED (stale debt)", root, 1)

        # 7. a disagreement row accounts for a site the counts do not -> green
        lib.write_text(
            baseline
            + "\n// SOUNDNESS: selftest justification.\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        doc = _read_ratchet(root)
        doc["add_decl_unchecked_count"] = 0
        doc["add_decl_unchecked_production_sites"] = []
        doc["add_decl_measured_disagreements"] = [
            {
                "file": "crates/c/src/lib.rs",
                "method": "add_decl_unchecked",
                "reason": "selftest disagreement",
                "reconciliation": "selftest",
            }
        ]
        _write_ratchet(root, doc)
        check("a recorded disagreement accounts for the site (and prints)", root, 0)

        # 8. a SECOND production bypass is still RED even with a disagreement row
        lib.write_text(
            lib.read_text()
            + "\n// SOUNDNESS: second.\npub fn smuggle2(env: &mut E, d: D) { env.add_decl_structural(d); }\n"
        )
        check("a second, different-method bypass is still RED", root, 1)

        # 9. `Environment::add_decl_unchecked(e, d)` IS a hit (audit r10 M10-5).
        #
        # THIS ARM USED TO ASSERT THE OPPOSITE, and that is what the audit
        # found: excluding the UFCS form by call SHAPE excused it in EVERY
        # file, so a production bypass planted in crates/clean-kernel/src/env/
        # snapshot.rs -- no `// SOUNDNESS:` comment, no ratchet row -- produced
        # output byte-identical to baseline at rc 0. The two genuine
        # delegations are excluded by FILE now (DELEGATION_FILES), so the
        # honest split is: the definition file is out of scope, and a UFCS call
        # anywhere else is a bypass like any other.
        lib.write_text(baseline + "\npub fn deleg(e: &mut E, d: D) { Environment::add_decl_unchecked(e, d); }\n")
        doc = _read_ratchet(root)
        doc["add_decl_measured_disagreements"] = []
        _write_ratchet(root, doc)
        check("a :: delegation call OUTSIDE the definition file IS a bypass", root, 1)

        # 9b. EVERY other spelling of the same call is a bypass too (audit r11).
        # The r10 fix enumerated shapes; these three were still invisible the
        # moment it landed, which is why the rule is now "the name in call
        # position" rather than a list of accepted prefixes.
        for label, call in (
            ("fully qualified", "<Environment as TrustedEnvExt>::add_decl_unchecked(e, d);"),
            ("import alias", "E::add_decl_unchecked(e, d);"),
            ("generic parameter", "T::add_decl_unchecked(e, d);"),
        ):
            lib.write_text(baseline + f"\npub fn deleg(e: &mut E, d: D) {{ {call} }}\n")
            doc = _read_ratchet(root)
            doc["add_decl_measured_disagreements"] = []
            _write_ratchet(root, doc)
            check(f"a {label} call through the watched door IS a bypass", root, 1)

        # 10. a call quoted in a `//` comment is NOT a hit
        lib.write_text(baseline + "\n// see env.add_decl_unchecked(d) for the bypass\n")
        check("a call quoted in a comment is not counted", root, 0)

        # 11. an unbalanced cfg(test) mod fails CLOSED, never skips
        lib.write_text("#[cfg(test)]\nmod tests {\n    fn t() { env.add_decl_unchecked(d); }\n")
        check("an unterminated cfg(test) block fails closed", root, 1)

        # 11b-c. Test-ness a file carries (2026-11-16,
        # docs/issues/2026-11-16-python-rust-lexer-copies.md).
        src_dir = root / "crates" / "c" / "src"
        lib.write_text(baseline + "\nmod headed;\n")
        (src_dir / "headed.rs").write_text("// note\n\n#![cfg(test)]\n" + PLANT)
        check("a file headed #![cfg(test)] is test code, whatever declares it", root, 0)
        (src_dir / "headed.rs").write_text("// note\n\n#![cfg(any(test, feature = \"x\"))]\n" + PLANT)
        check("a file headed by any other cfg stays production", root, 1)
        (src_dir / "headed.rs").unlink()

        # 12. an unreadable ratchet fails closed
        lib.write_text(baseline)
        (root / RATCHET_REL).write_text("{ not json")
        rc = 0
        try:
            _quiet_run(root, FAKE_SANCTIONED)
        except SystemExit as exc:
            rc = 1 if exc.code else 0
        good = rc == 1
        print(f"  [{'ok ' if good else 'FAIL'}] an unparsable ratchet fails closed: {good}")
        passed += 1 if good else 0
        failed += 0 if good else 1

        # -------------------------------------------------------------------
        # 13-16 run against the REAL SANCTIONED_SITES.
        #
        # 13/14 are THE PERMANENT PLANT. The 2026-08-22 falsification that
        # justified writing this gate was an `env.add_decl_unchecked(d)` added
        # to production code in crates/clean-kernel/src/env/snapshot.rs, with no
        # SOUNDNESS comment and no ratchet entry: six python gates plus paragon
        # were byte-identical with and without it. It is kept here as a standing
        # arm, on the REAL file at its REAL repo-relative path, so the
        # demonstration cannot decay into an anecdote in a commit message. The
        # unplanted copy must be GREEN — that is not free: snapshot.rs already
        # contains two `add_decl_unchecked` calls inside a `#[cfg(test)] mod`,
        # so arm 13 also pins the brace tracking on a real file — and the
        # planted copy must be RED.
        real = REPO_ROOT / "crates" / "clean-kernel" / "src" / "env" / "snapshot.rs"
        plant_root = Path(tempfile.mkdtemp(prefix="add_decl_selftest_plant_"))
        try:
            (plant_root / "data").mkdir()
            snap_rel = Path("crates/clean-kernel/src/env/snapshot.rs")
            (plant_root / snap_rel).parent.mkdir(parents=True)
            _write_ratchet(
                plant_root,
                {
                    "add_decl_structural_count": 0,
                    "add_decl_unchecked_count": 0,
                    "add_decl_structural_production_sites": [],
                    "add_decl_unchecked_production_sites": [],
                    "files": [],
                    "last_updated": "selftest",
                },
            )
            if not real.is_file():
                print(
                    "  [FAIL] the permanent plant arm cannot find "
                    f"{snap_rel} — the arm is the demonstration, not an optional extra"
                )
                failed += 1
            else:
                clean_src = real.read_text(encoding="utf-8")
                (plant_root / snap_rel).write_text(clean_src)
                check(
                    "REAL snapshot.rs, unplanted, is green (its cfg(test) bypasses excluded)",
                    plant_root,
                    0,
                    None,
                )

                (plant_root / snap_rel).write_text(clean_src + PLANT)
                check(
                    "REAL snapshot.rs + the 2026-08-22 planted bypass is RED",
                    plant_root,
                    1,
                    None,
                )

                # 15. …and a ratchet row written ABOUT the plant does not
                # legalise it: snapshot.rs is not in SANCTIONED_SITES.
                (plant_root / snap_rel).write_text(
                    clean_src + "\n// SOUNDNESS: fabricated justification.\n" + PLANT
                )
                _write_ratchet(
                    plant_root,
                    {
                        "add_decl_structural_count": 0,
                        "add_decl_unchecked_count": 1,
                        "add_decl_structural_production_sites": [],
                        "add_decl_unchecked_production_sites": [
                            {
                                "file": str(snap_rel),
                                "method": "add_decl_unchecked",
                                "trust": "fabricated",
                            }
                        ],
                        "files": [],
                        "last_updated": "selftest",
                    },
                )
                check(
                    "a ratchet row + SOUNDNESS comment CANNOT self-authorize an "
                    "unsanctioned bypass",
                    plant_root,
                    1,
                    None,
                )

            # 16. the sanctioned site does not license a SECOND copy of itself.
            sanct_rel = Path("crates/clean-kernel/src/env/decl_add.rs")
            (plant_root / snap_rel).unlink(missing_ok=True)
            (plant_root / sanct_rel).write_text(
                "// SOUNDNESS: the sanctioned one.\n"
                "pub fn a(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
                "// SOUNDNESS: a second, unsanctioned copy.\n"
                "pub fn b(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
            )
            _write_ratchet(
                plant_root,
                {
                    "add_decl_structural_count": 0,
                    "add_decl_unchecked_count": 2,
                    "add_decl_structural_production_sites": [],
                    "add_decl_unchecked_production_sites": [
                        {
                            "file": str(sanct_rel),
                            "method": "add_decl_unchecked",
                            "occurrences": 2,
                            "trust": "the real row, widened",
                        }
                    ],
                    "files": [],
                    "last_updated": "selftest",
                },
            )
            check(
                "a SECOND call site in the sanctioned file exceeds its cap and is RED",
                plant_root,
                1,
                None,
            )
        finally:
            shutil.rmtree(plant_root, ignore_errors=True)
    finally:
        shutil.rmtree(root, ignore_errors=True)

    print(f"selftest: {passed} passed, {failed} failed")
    return 0 if failed == 0 else 2


def dump_scope(root: Path) -> list[str]:
    """Every file `measure` will SCAN, as repo-relative slash paths.

    AUDIT r14 M14-11: the Rust producer of this same lane id
    (`crates/clean-cli/src/cmd_replacement/add_decl_bypass_scan.rs`) reimplements
    the scope rule, and the only arm keeping the two together compared the
    SITES found in today's tree -- which agree whenever both are blind in the
    same place. This is the scope itself, so the Rust arm can assert set
    equality against the rule rather than against an outcome.
    """
    out = []
    for path in sorted((root / CRATES_REL).rglob("*.rs")):
        rel = path.relative_to(root)
        if not is_production_file(path) and is_test_like(path, rel):
            continue
        out.append(str(rel).replace("\\", "/"))
    return out


def main(argv: list[str]) -> int:
    if "--dump-scope" in argv:
        for rel in dump_scope(REPO_ROOT):
            print(rel)
        return 0
    if "--module-tree-cases" in argv:
        # The known-answer table, for the Rust producer's own arm to answer: one
        # table, two producers, so neither can drift from it alone.
        print(json.dumps([{"name": name, "files": files, "target": target, "want": want}
                          for name, files, target, want in _MODULE_TREE_CASES], indent=1))
        return 0
    if "--lexer-cases" in argv:
        # The shared lexer's, the file-head rule's and the cfg head's known
        # answers, for the Rust producer's mirror to answer too.
        print(json.dumps({
            "lexer": [{"name": name, "source": src, "mode": mode, "survive": list(keep),
                       "vanish": list(gone)} for name, src, mode, keep, gone in _LEXER_CASES],
            "file_head": [{"source": src, "want": want} for src, want in _HEAD_CASES],
            "cfg_head": [{"attr": attr, "want": want} for attr, want in _CFG_HEAD_CASES],
        }, indent=1))
        return 0
    if "--selftest" in argv:
        return selftest()
    return run(REPO_ROOT, list_only="--list" in argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
