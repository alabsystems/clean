#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The widened environment-bypass census scanner (program G-SCAN, 2026-08-23).

WHY THIS EXISTS
---------------
Two scanners watch four methods:

  * scripts/check_add_decl_ratchet.py       — add_decl_unchecked / add_decl_structural
  * scripts/check_extend_constants_ratchet.py — extend_constants_unchecked / _structural

The recon census (docs/analysis/spine-lattice-recon-2026-08-22.md §3, 18 items)
measured that those four are a fraction of the surface through which a
declaration, an inductive family, a recursor, an axiom, or a whole deserialized
Environment becomes visible to the kernel without full checking. The
`TrustedEnvExt` trait (crates/clean-kernel/src/env/trusted_ext.rs) is the
deliberate cross-crate choke point enumerating most of that surface — and until
this scanner, items 5-13 and 16-18 of the census had partial or ZERO scanner
coverage: `env.extend_inductives_unchecked(..)` could be added to any
production file and every gate in the repo stayed green.

WHAT IT MEASURES
----------------
Production call sites (crates/**/*.rs, test files and inline #[cfg(test)] mods
excluded) of every watched method, in BOTH call forms:

  * dot-call:            `<recv>.upgrade_axiom_stubs(`
  * qualified:           `Environment::register_inductive(` /
                         `TrustedEnvExt::register_inductive(`

plus the env deserialization entry points, which are associated
functions (no receiver) and are matched in `Environment::<name>(` form only:
`from_json`, `load_from_file`, `load_snapshot`, `from_dag_bincode`.

`crates/clean-kernel/src/env/trusted_ext.rs` is excluded wholesale: its impl
bodies are the definitions/delegations (`Environment::method(self, …)`), not
usage. Known match-form limits, inherited deliberately from the two sibling
scanners: an aliased qualified call (`use Environment as E; E::from_json(..)`)
or a function-pointer capture is not matched; dot-call matching is
receiver-blind, so a same-named method on another type over-matches (fails
CLOSED, and the census names the file, so a false positive is visible and
cheap to account).

The watched-method list lives IN THIS FILE (code, not artifact), and the
scanner additionally re-parses the `TrustedEnvExt` trait on every run: a new
trait method that is neither watched here nor covered by a sibling scanner is
a RED, so the choke point cannot quietly widen.

THE CENSUS ARTIFACT
-------------------
data/env_bypass_census.json — one row per watched method/site-class, seeded
from the recon's numbered census with classification (E/P/S), guard notes, and
the R1-* disposition job from designs/2026-08-22-spine-and-lattice-program.md
§5. The add_decl_* / extend_constants_* rows already ledgered in
data/unchecked_decl_ratchet.json are CROSS-REFERENCED (a pointer row naming
the ledger and its scanner), never copied — one accounting point per site.

VERDICTS (all fail-closed)
--------------------------
  * a production call whose (method, file) no census row accounts for → RED
  * a census row naming a site (or prefix) with no live call left     → RED (stale)
  * a capped delegation row that excused nothing this pass            → RED (stale)
  * a delegation row naming a file other than the choke-point trait,
    or a method not on the live trait                                 → RED
  * an excused delegation past its cap, missing the // SOUNDNESS:
    comment that BELONGS to it, or not sitting inside `fn <method>`
    of `impl TrustedEnvExt for Environment`                           → COUNTED
  * a row's measured occurrences above its max_occurrences baseline   → RED
  * a TrustedEnvExt trait method neither watched nor cross-referenced → RED
  * census incomplete (a watched method in no row), or a row naming an
    unwatched/duplicated method                                       → RED
  * a cross-reference pointing at a scanner or ledger that is gone    → RED
  * an unreadable census, or an unbalanced #[cfg(test)] mod           → fail closed

// SOUNDNESS comment enforcement is PARTIAL, and the split is deliberate.
It IS enforced at every site the gate EXCUSES: a `trusted_ext_delegation_sites`
row buys at most `occurrences` calls and only where the comment CLAUDE.md
demands sits within SOUNDNESS_WINDOW lines above (audit r14 M14-3 -- an excuse
that requires nothing of the site is a suppression). It is NOT yet enforced at
the ~60 sites the census merely COUNTS: those predate the census, and reddening
them today would be the R1-* ring work each row's disposition_job names, not
this gate's verdict.

Exit codes: 0 accounted, 1 unaccounted/stale/over-baseline/drift, 2 self-test
failure.

Usage:
    python3 scripts/check_env_bypass_census.py
    python3 scripts/check_env_bypass_census.py --list
    python3 scripts/check_env_bypass_census.py --selftest
"""

from __future__ import annotations

import contextlib
import io
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CENSUS_REL = Path("data") / "env_bypass_census.json"
CRATES_REL = Path("crates")
TRUSTED_EXT_REL = Path("crates/clean-kernel/src/env/trusted_ext.rs")

# AUDIT r14 M14-3: the `TrustedEnvExt for Environment` delegations are accounted
# by CAPPED ROWS IN THE ARTIFACT, not by a table in this scanner's source.
#
# Round 12 excused them by a SHAPE (a name check on a sticky variable, which made
# all 35 watched doors invisible behind a wrapper named after the door). Round 13
# replaced that with a hardcoded `(line, method)` set here. That set pinned a
# POSITION and capped NOTHING: it lived in the gate rather than in the ledger the
# gate reads, it carried no `occurrences`, no trust prose and no owner, and it
# required no `// SOUNDNESS:` comment at the site -- so it was one more suppression
# written in a place no reviewer of `data/env_bypass_census.json` would ever read.
#
# The account now matches its sibling in `data/unchecked_decl_ratchet.json`: a row
# names `{file, method, occurrences, trust}`, the excuse covers at most
# `occurrences` calls of that door in that file, and each excused call must carry
# the `// SOUNDNESS:` comment CLAUDE.md demands within `SOUNDNESS_WINDOW` lines
# above it. A row nothing uses is STALE and refuses.
DELEGATION_SITES_KEY = "trusted_ext_delegation_sites"
SOUNDNESS_WINDOW = 40
SOUNDNESS_RE = re.compile(r"//\s*SOUNDNESS:")
_DELEGATION_CACHE: dict[str, dict[tuple[str, str], int]] = {}
# usage tally of the current `measure()` pass, so a row nothing matched is caught
_DELEGATION_USE: dict[tuple[str, str], int] = {}
# which line spent each slot (audit r16 M16-1)
_DELEGATION_CONSUMERS: dict[tuple[str, str], list[int]] = {}


def delegation_caps(root) -> dict[tuple[str, str], int]:
    """`{(file, method): occurrences}` from the census artifact."""
    key = str(root)
    if key in _DELEGATION_CACHE:
        return _DELEGATION_CACHE[key]
    caps: dict[tuple[str, str], int] = {}
    try:
        doc = json.loads((Path(root) / CENSUS_REL).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        _DELEGATION_CACHE[key] = caps
        return caps
    for row in doc.get(DELEGATION_SITES_KEY, []) or []:
        if not isinstance(row, dict):
            continue
        rel, method = row.get("file"), row.get("method")
        if not isinstance(rel, str) or not isinstance(method, str):
            continue
        try:
            occurrences = int(row.get("occurrences", 1))
        except (TypeError, ValueError):
            occurrences = 0
        caps[(rel, method)] = max(0, occurrences)
    _DELEGATION_CACHE[key] = caps
    return caps


def _owner_floor(raw_lines, lineno: int, prev_call_line: int, fn_line: int) -> int:
    """Where THIS site's justification may start, as a 0-based line index.

    AUDIT r15 M15-2 leg B.  The window was `lineno - 1 - SOUNDNESS_WINDOW`
    unconditionally -- "is there ANY `// SOUNDNESS:` above", never "is there one
    belonging to this call".  In crates/clean-kernel/src/env/trusted_ext.rs the
    32 commented blocks sit 6-11 lines apart, so measured PER BLOCK, 31 of the
    32 comments could be deleted with every gate still green and output
    byte-identical: only block #1 was load-bearing, and only because nothing
    precedes it.  Each of the 28 rows, and the comment at each site, says in so
    many words that removing it makes the call COUNTED.  It did not.

    The floor is the nearest of: the window, the previous watched CALL in this
    file (a comment below that call cannot belong to this one), and the top of
    the enclosing `fn`'s own attribute/doc run.
    """
    floor = max(0, lineno - 1 - SOUNDNESS_WINDOW)
    if prev_call_line:
        floor = max(floor, prev_call_line)
    if fn_line:
        i = fn_line - 1
        while i > 0:
            t = raw_lines[i - 1].strip()
            if t.startswith(("#[", "///", "//!")) or (t.startswith("//") and i == fn_line - 1):
                i -= 1
            else:
                break
        floor = max(floor, i)
    return floor


def _has_soundness_comment(raw_lines, lineno: int, prev_call_line: int = 0,
                           fn_line: int = 0) -> bool:
    start = _owner_floor(raw_lines, lineno, prev_call_line, fn_line)
    return any(SOUNDNESS_RE.search(l) for l in raw_lines[start : lineno - 1])


# ---------------------------------------------------------------------------
# The watched surface, PINNED IN CODE. A census row may only speak for a
# method named here; widening the census artifact alone cannot widen the watch.
# ---------------------------------------------------------------------------

# TrustedEnvExt methods NOT already watched by a sibling scanner, plus the
# bypass-capable Environment methods the recon found outside the trait.
DOT_WATCHED: frozenset[str] = frozenset(
    {
        # TrustedEnvExt (trusted_ext.rs), minus the four cross-referenced ones
        "init_quot",
        "clone_pruned_shadowing_overlay",
        "set_param_names",
        "set_param_infos",
        "set_typed_param_names",
        "set_typed_param_infos",
        "register_structure_fields",
        "register_recursor_unchecked",
        "extend_inductives_unchecked",
        "extend_constructors_unchecked",
        "extend_recursors_unchecked",
        "register_persistent_extension",
        "add_persistent_extension_entries",
        "get_persistent_extension_state",
        "get_persistent_extension_module_entries",
        "register_inductive",
        "register_constructor",
        "register_recursor",
        "set_reducibility",
        "upgrade_axiom_stubs",
        # R1-STUB / R1-IND replacement lanes (2026-08-24): the checked stub
        # upgrade and the structural inductive-family tier. Hardened, but they
        # still admit declarations below FullKernelCheck, so they stay watched
        # rather than silently trusted.
        "upgrade_axiom_stubs_checked",
        "extend_inductives_structural",
        "extend_constructors_structural",
        "extend_recursors_structural",
        "discharge_axiom_stub_for_inductive_import",
        "init_native_reducers",
        "init_arith_native_reducers",
        "materialize_extension_states",
        "export_extension_states",
        # bypass doors outside the trait (recon §3 items 5, 10, 11, 12)
        "register_inductive_unchecked",
        "register_constructor_unchecked",
        "add_skolem_axiom",
        "add_constant_unchecked_for_test",
        "set_constant_source",
        # TG6 local kernel facts (2026-11-05): replays a stored delta with the
        # producing check's stamps and no re-check.
        "apply_local_fact_delta",
    }
)

# Env deserialization entry points: associated functions, matched only as
# `Environment::<name>(` (they take no receiver, so no dot form exists).
ASSOC_WATCHED: frozenset[str] = frozenset({
    "from_json", "load_from_file", "load_snapshot", "from_dag_bincode",
    "from_legacy_dag_bincode",
})

# Watched by the sibling scanners; cross-referenced in the census, never
# scanned here — one accounting point per site.
POINTER_METHODS: frozenset[str] = frozenset(
    {
        "add_decl_unchecked",
        "add_decl_structural",
        "extend_constants_unchecked",
        "extend_constants_structural",
    }
)

WATCHED: frozenset[str] = DOT_WATCHED | ASSOC_WATCHED

_dot_alt = "|".join(sorted(DOT_WATCHED, key=len, reverse=True))
# CLOSED BY CONSTRUCTION (audit r12 M12-3). This kept the pre-r11 enumeration
# after both siblings had abandoned it, and it is the SOLE gate for 31 of its 35
# watched doors (the four add_decl_*/extend_constants_* are delegated to the
# sibling ratchets). Measured against a firing control: `Self::`,
# `<Environment as TrustedEnvExt>::`, an import alias and a generic `T::` call
# were all byte-identical to baseline. The rule is the NAME in call position,
# whatever precedes it, minus a definition.
# Any RECEIVER or PATH qualifier, never a list of specific ones: a dot, or any
# identifier (or a `>` closing a qualified path) followed by `::`. That admits
# Environment::, TrustedEnvExt::, Self::, an import alias, a generic parameter
# and `<Environment as TrustedEnvExt>::` alike, and it cannot be reopened by
# inventing another spelling. Unlike the sibling ratchets this scanner may NOT
# use the bare name: several watched doors (`register_inductive`, `init_quot`,
# `set_reducibility`) are also free functions in the same modules, and counting
# those would be a false positive rather than a bypass.
CALL_RE = re.compile(r"(?:\.|[\w>]\s*::\s*)(" + _dot_alt + r")\s*\(")
DEFINITION_RE = re.compile(r"\bfn\s+(?:" + _dot_alt + r")\s*[(<]")
ASSOC_RE = re.compile(
    r"\bEnvironment\s*::\s*(" + "|".join(sorted(ASSOC_WATCHED, key=len, reverse=True)) + r")\s*\("
)
# Cheap prefilter: only files containing a watched name as a substring pay for
# noncode stripping + cfg(test) tracking. A file without the substring cannot
# contain a hit.
QUICK_RE = re.compile("|".join(sorted(WATCHED, key=len, reverse=True)))

CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\b")
# `[(<]` because a GENERIC declaration is still a declaration: audit r12
# M12-3 measured `fn widen_env_generic<D: Into<Declaration>>(..)` slipping
# past a `\\(`-only pattern while its non-generic twin was caught. The
# sibling scanners already spelled it this way.
TRAIT_FN_RE = re.compile(r"\bfn\s+([A-Za-z0-9_]+)\s*[(<]")

# AUDIT r16 M16-1 leg 2: `enclosing_fn` was the LAST `fn` name seen anywhere
# earlier in the file, never reset at fn end or impl end -- r12 residue that
# survived r15's rewrite. Measured: a free fn named exactly after a watched door,
# placed ABOVE `impl TrustedEnvExt for Environment`, was excused as that door's
# delegation and STOLE its cap slot, so the RED named the genuine, correctly
# commented forward at :453 and the plant did not appear at all. Applying the
# remediation that RED prescribes greens the tree with the bypass live. Three
# strictly worse variants followed from the same cause, including a second
# `pub trait ImportEnvExt` forwarding the same door without tripping trait drift,
# because `trait_methods()` collected `fn` names FILE-WIDE and never asked which
# trait owned them.
_TRAIT_IMPL_RE = re.compile(r"\bimpl\s+TrustedEnvExt\s+for\s+Environment\b")
_TRAIT_DECL_RE = re.compile(r"\b(?:pub(?:\([^)]*\))?\s+)?trait\s+TrustedEnvExt\b")


def _fn_context(lines):
    """Per-line `(fn_name, fn_line, inside_the_TrustedEnvExt_impl_or_trait)`.

    Derived by brace depth, so a fn ends where its body ends and the impl ends
    where its block ends -- which is what "inside `fn <method>` of `impl
    TrustedEnvExt for Environment`" means, and what the excuse asserts.
    """
    out = [(None, 0, False)]
    depth = 0
    fn_stack = []
    pending_fn = None
    block_depth = None
    for lineno, line in enumerate(lines, 1):
        opens = line.count("{")
        closes = line.count("}")
        if block_depth is None and opens and (
                _TRAIT_IMPL_RE.search(line) or _TRAIT_DECL_RE.search(line)):
            block_depth = depth
        fm = TRAIT_FN_RE.search(line)
        if fm:
            # a multi-line signature opens its body on a LATER line -- measured,
            # `fn upgrade_axiom_stubs_checked(` spans four lines, and requiring
            # the brace on the `fn` line lost it as a delegation
            pending_fn = (fm.group(1), lineno)
        if pending_fn:
            # AUDIT r17 R17-2: a BODY-LESS signature ends at its `;`, not at the
            # next `{`. The trait declaration block sits directly above the impl
            # block in this file, so `fn export_extension_states(..);` was armed
            # and then adopted by `impl TrustedEnvExt for Environment {` -- which
            # made that name the enclosing fn for the WHOLE impl, and every
            # genuine delegation stopped matching `enclosing_fn == <door>`. It
            # went unseen until an upstream edit shifted the file, because the
            # census only reds when the two happen to disagree.
            semi = line.find(";")
            brace = line.find("{")
            if semi != -1 and (brace == -1 or semi < brace):
                pending_fn = None
        if pending_fn and opens:
            fn_stack.append((pending_fn[0], pending_fn[1], depth))
            pending_fn = None
        out.append((
            fn_stack[-1][0] if fn_stack else None,
            fn_stack[-1][1] if fn_stack else 0,
            block_depth is not None,
        ))
        depth += opens - closes
        while fn_stack and depth <= fn_stack[-1][2]:
            fn_stack.pop()
        if block_depth is not None and depth <= block_depth:
            block_depth = None
    return out



def is_test_path(rel: Path) -> bool:
    """True for test FILES. Byte-identical to check_add_decl_ratchet.py /
    check_extend_constants_ratchet.py so the three bypass gates cannot drift
    into disagreeing about what a test is."""
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



# Rust non-code spans — same construction and rationale as
# check_add_decl_ratchet.py (ordered alternation; measured there: raw brace
# counting leaves 22 healthy files apparently unbalanced, stripping leaves 0).
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


def scan_file(path: Path, rel: Path) -> tuple[list[dict], list[dict]]:
    """(production hits, cfg(test) hits) for one file. Raises on unbalanced braces."""
    raw_text = path.read_text(errors="strict")
    if not QUICK_RE.search(raw_text):
        return [], []
    raw_lines = raw_text.splitlines()
    lines = strip_noncode(raw_text).splitlines()
    _caps = delegation_caps(_repo_root_of(path) or REPO_ROOT)
    prod: list[dict] = []
    tested: list[dict] = []
    in_cfg_test = False
    depth = 0
    pending_cfg = False
    _ctx = _fn_context(lines)
    prev_watched_call_line = 0
    for lineno, line in enumerate(lines, 1):
        enclosing_fn, enclosing_fn_line, in_trait_block = _ctx[lineno]
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
        # audit r12 M12-4/M12-3: blank definitions over the SPAN they occupy,
        # before matching, so a call sharing a line with a `fn` header still
        # counts and a definition never does.
        line = DEFINITION_RE.sub(lambda d: " " * len(d.group(0)), line)
        # AUDIT r13 M13-3: the r12 "shape rule" is DELETED. It excused a whole
        # LINE when the called door's name equalled `enclosing_fn` -- the most
        # recent `fn <name>` seen ANYWHERE earlier in the file, never reset at
        # fn/impl/EOF -- and when the first argument merely started with `self`.
        # Measured: ALL 35 watched doors go invisible behind a wrapper method
        # named after the door, on any type, in any production file; a door
        # nested in a genuine forward's arguments was skipped with it; a second
        # call to the same door on a different environment inside a real
        # delegation was dropped and never reached max_occurrences. That is a
        # strictly worse hole than the whole-file blanket it replaced, in the
        # sole gate for 31 of its doors. The 28 genuine forwards are accounted
        # the way the sibling ratchet already accounts its two: capped SITE
        # rows, checked below.
        for m in list(CALL_RE.finditer(line)) + list(ASSOC_RE.finditer(line)):
            # AUDIT r14 M14-3: a delegation is excused by a CAPPED ROW in the
            # census artifact plus the `// SOUNDNESS:` comment at the site --
            # never by a shape, and never by a position table living in this
            # gate's own source. Past the cap, or with the comment removed, the
            # call is COUNTED like any other.
            _key = (str(rel).replace("\\", "/"), m.group(1))
            _cap = _caps.get(_key)
            # AUDIT r15 M15-2 leg A: the excuse is DERIVED FROM THE SITE, not
            # granted by artifact coordinates.  Until now `delegation_caps` read
            # only {file, method, occurrences} and the scan matched on that
            # tuple, so ONE appended row excused a genuinely new production
            # bypass at any of the 35 watched doors in ANY production file --
            # measured in cmd_replacement/consts.rs, lsp/backend/navigation.rs
            # and server/handlers/env_merge.rs, each going from a named RED to
            # exit 0 with output byte-identical to pristine.  It also absorbed a
            # max_occurrences overflow at an already-baselined site, because the
            # excused hit `continue`s BEFORE the per-row accounting.  A row is a
            # CAP ON A PROVED DELEGATION now: the file must be the choke-point
            # trait's own file, the call must sit inside `fn <method>` of it, and
            # the method called must be the enclosing fn's own name.  A row that
            # cannot be proved is refused in run() below, never silently obeyed.
            _is_delegation = (
                rel == TRUSTED_EXT_REL
                and in_trait_block
                and enclosing_fn == m.group(1)
                and enclosing_fn_line > 0
            )
            if _cap is not None and _is_delegation and _has_soundness_comment(
                    raw_lines, lineno, prev_watched_call_line, enclosing_fn_line):
                if _DELEGATION_USE.get(_key, 0) < _cap:
                    _DELEGATION_USE[_key] = _DELEGATION_USE.get(_key, 0) + 1
                    # AUDIT r16 M16-1: record WHICH line spent the slot, so a
                    # COUNTED call whose cap is already exhausted can say who
                    # exhausted it. Without that, the RED named a line the
                    # reader had no reason to doubt and the plant appeared
                    # nowhere at all.
                    _DELEGATION_CONSUMERS.setdefault(_key, []).append(lineno)
                    prev_watched_call_line = lineno
                    continue
            prev_watched_call_line = lineno
            _spent = _DELEGATION_CONSUMERS.get(_key) or []
            hit = {
                "file": str(rel),
                "line": lineno,
                "cap_spent_by": _spent if (_cap is not None and _spent) else None,
                "method": m.group(1),
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


def measure(root: Path) -> tuple[list[dict], list[dict], list[str]]:
    # AUDIT r15 M15-1: the classification cache is keyed on the ROOT alone, so a
    # second measure() in one process answered from the first tree.  Production
    # calls measure() exactly once, so clearing here costs nothing there -- but
    # a selftest that mutates the tree between arms was silently re-reading the
    # first arm's answer, which makes every later arm vacuous.  Measured: an
    # eight-guard sweep reported the FIRST guard's verdict eight times.
    _CLASSIFY_CACHE.clear()
    _UNRESOLVED_EDGES.clear()
    _DELEGATION_USE.clear()
    _DELEGATION_CONSUMERS.clear()
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
        # AUDIT r12 M12-3: the whole-FILE blanket over env/trusted_ext.rs is
        # RETIRED here too. r11 retired it in the two sibling ratchets and this
        # scanner kept it though the commit said "everywhere" -- measured, a NEW
        # `self.add_skolem_axiom(..)` inserted INSIDE an existing delegation body
        # was byte-identical to baseline, i.e. a live bypass in the choke-point
        # file itself. Definitions are excluded by DEFINITION blanking; the
        # delegating CALLS are accounted by census rows like any other call.
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


def trait_methods(root: Path) -> tuple[set[str], str | None]:
    """Every named fn in trusted_ext.rs (trait decls + impl delegations — the
    same set). Returns (names, error)."""
    path = root / TRUSTED_EXT_REL
    try:
        text = strip_noncode(path.read_text(errors="strict"))
    except (OSError, UnicodeDecodeError) as exc:
        return set(), f"cannot read {TRUSTED_EXT_REL}: {exc} — the choke-point trait is unreadable"
    # AUDIT r16 M16-1 leg 2: file-wide `findall` counted a FREE fn, or a method
    # of a SECOND trait, as a TrustedEnvExt method -- so a free fn named
    # `anything` red as trait drift (a false positive that confounds any arm
    # aimed at the delegation predicate), and a second `pub trait ImportEnvExt`
    # forwarding a watched door satisfied the drift check that exists to notice
    # exactly that. Ask which block owns the fn.
    lines = text.splitlines()
    ctx = _fn_context(lines)
    names = set()
    for lineno, line in enumerate(lines, 1):
        m = TRAIT_FN_RE.search(line)
        if m and ctx[lineno][2]:
            names.add(m.group(1))
    return names, None


def load_census(root: Path) -> dict:
    path = root / CENSUS_REL
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        raise SystemExit(f"FAIL: cannot read {CENSUS_REL}: {exc}")


def run(root: Path, list_only: bool = False, require_complete: bool = True) -> int:
    # AUDIT r15 M15-2: the delegation-cap cache is keyed on the ROOT, exactly
    # like _CLASSIFY_CACHE was, so a second run() in one process answered from
    # the FIRST census it read.  Production runs once; a selftest that mutates
    # the artifact between arms was silently re-reading the old rows, which made
    # two arms below report green while asserting a refusal that does fire.
    _DELEGATION_CACHE.clear()
    census = load_census(root)
    prod, tested, errors = measure(root)

    if list_only:
        print(f"production sites ({len(prod)}):")
        for h in prod:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}")
        print(f"inline cfg(test) sites: {len(tested)}")
        return 0

    ok = True

    def red(msg: str) -> None:
        nonlocal ok
        ok = False
        print(msg, file=sys.stderr)

    if errors:
        red("FAIL: the env-bypass scanner could not classify part of the tree:")
        for e in errors:
            print(f"  {e}", file=sys.stderr)

    # ---- config sanity: rows may only name watched methods, once each -------
    rows = census.get("rows", []) or []
    method_to_row: dict[str, dict] = {}
    for row in rows:
        if not isinstance(row, dict) or not row.get("id") or not row.get("methods"):
            red(f"FAIL: {CENSUS_REL} has a malformed row (needs 'id' and 'methods'): {row!r}")
            continue
        for meth in row["methods"]:
            if meth in POINTER_METHODS:
                red(
                    f"FAIL: census row {row['id']!r} names {meth}, which is watched by a "
                    f"sibling scanner — it belongs in cross_references (one accounting "
                    f"point per site), never in a scanned row."
                )
            elif meth not in WATCHED:
                red(
                    f"FAIL: census row {row['id']!r} names {meth}, which this scanner does "
                    f"not watch. The watched list lives in code "
                    f"({Path(__file__).name}); widen it there, with review, first."
                )
            elif meth in method_to_row:
                red(
                    f"FAIL: {meth} appears in census rows {method_to_row[meth]['id']!r} and "
                    f"{row['id']!r} — one accounting point per method."
                )
            else:
                method_to_row[meth] = row

    if require_complete:
        unrowed = sorted(WATCHED - set(method_to_row))
        if unrowed:
            red(
                f"FAIL: watched method(s) with no census row: {unrowed}. Every watched "
                f"method needs a row in {CENSUS_REL} — an expect-zero row (empty sites) "
                f"if it has no production caller."
            )

    # ---- trait drift: the choke point cannot quietly widen ------------------
    tmethods, terr = trait_methods(root)
    if terr:
        red(f"FAIL: {terr}")
    for meth in sorted(tmethods - DOT_WATCHED - POINTER_METHODS):
        red(
            f"FAIL: TrustedEnvExt ({TRUSTED_EXT_REL}) has a method {meth!r} that no "
            f"scanner watches — a new cross-crate mutation hook must be added to "
            f"DOT_WATCHED here (plus a census row) before it can land."
        )

    # ---- delegation rows must NAME a provable delegation --------------------
    # AUDIT r15 M15-2 leg A.  A row is a cap on a proved forward, not a grant.
    # Refusing here rather than only via the zero-use staleness check keeps the
    # DIAGNOSIS right: a row naming a foreign file used to buy silence, and
    # would now read as merely "excused no call".
    for (dfile, dmethod), _cap in sorted(delegation_caps(root).items()):
        if dfile != str(TRUSTED_EXT_REL):
            red(
                f"FAIL: {DELEGATION_SITES_KEY} row {dfile}::{dmethod} names a file other "
                f"than the choke-point trait ({TRUSTED_EXT_REL}). A delegation row caps a "
                f"forward inside `impl TrustedEnvExt for Environment`; it is not a licence "
                f"to call a watched door somewhere else. Account that call with a census row."
            )
        elif tmethods and dmethod not in tmethods:
            red(
                f"FAIL: {DELEGATION_SITES_KEY} row {dfile}::{dmethod} names a method that is "
                f"not on the live TrustedEnvExt trait. The row can excuse nothing it can "
                f"prove -- delete it (the census only shrinks)."
            )

    # ---- cross-references: pointers must still point at something -----------
    for xref in census.get("cross_references", []) or []:
        for key in ("methods", "scanner", "ledger"):
            if not xref.get(key):
                red(f"FAIL: cross-reference row {xref.get('id')!r} lacks {key!r}")
        scanner = xref.get("scanner")
        if scanner and not (root / scanner).is_file():
            red(
                f"FAIL: cross-reference {xref.get('id')!r} points at {scanner}, which does "
                f"not exist — the sibling scanner this census delegates to is gone."
            )
        ledger = xref.get("ledger")
        if ledger:
            try:
                ledger_doc = json.loads((root / ledger).read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                red(f"FAIL: cross-reference {xref.get('id')!r}: cannot read {ledger}: {exc}")
                ledger_doc = None
            block = xref.get("ledger_key")
            if ledger_doc is not None and block and block not in ledger_doc:
                red(
                    f"FAIL: cross-reference {xref.get('id')!r}: {ledger} no longer has the "
                    f"{block!r} block it points at."
                )

    # ---- accounting: every production hit must land in its method's row -----
    def accounted(row: dict, file: str) -> bool:
        if any(site.get("file") == file for site in row.get("sites", []) or []):
            return True
        return any(file.startswith(p) for p in row.get("site_prefixes", []) or [])

    row_occurrences: dict[str, int] = {}
    unaccounted: list[dict] = []
    for h in prod:
        row = method_to_row.get(h["method"])
        if row is None or not accounted(row, h["file"]):
            unaccounted.append(h)
        else:
            row_occurrences[row["id"]] = row_occurrences.get(row["id"], 0) + 1
    if unaccounted:
        ok = False
        print(
            "FAIL: unaccounted environment-bypass call site(s) in production code:",
            file=sys.stderr,
        )
        for h in unaccounted:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}", file=sys.stderr)
            # AUDIT r16 M16-1: if this door HAS a capped delegation row and the
            # cap is already spent, say by which line. A reader who is not told
            # that reaches for the remediation the RED implies -- raise the cap,
            # or doubt the delegation the message names -- and either one greens
            # the tree with the bypass live.
            if h.get("cap_spent_by"):
                _lines = ", ".join(str(x) for x in h["cap_spent_by"])
                print(
                    f"     (its `trusted_ext_delegation_sites` cap was already spent by "
                    f"line(s) {_lines}; if one of those is not a genuine forward, THAT is "
                    f"the site to look at, not this one)",
                    file=sys.stderr,
                )
        print(
            "  -> a kernel-environment mutation/deserialization door outside the census. "
            f"Account for it in {CENSUS_REL} (the row watching that method), with its "
            "guard notes and R1-* disposition — or remove the call.",
            file=sys.stderr,
        )

    # ---- staleness: named sites and prefixes must still be live -------------
    live_by_row: dict[str, set[str]] = {}
    for h in prod:
        row = method_to_row.get(h["method"])
        if row is not None:
            live_by_row.setdefault(row["id"], set()).add(h["file"])
    for row in rows:
        if not isinstance(row, dict) or row.get("id") is None:
            continue
        live = live_by_row.get(row["id"], set())
        for site in row.get("sites", []) or []:
            f = site.get("file")
            if f and f not in live:
                red(
                    f"FAIL: census row {row['id']!r} names {f} and no production call to "
                    f"{'/'.join(row['methods'])} remains there. If the door was closed, "
                    f"remove the site row (the census only shrinks)."
                )
        for prefix in row.get("site_prefixes", []) or []:
            if not any(f.startswith(prefix) for f in live):
                red(
                    f"FAIL: census row {row['id']!r} carries site_prefix {prefix!r} with no "
                    f"live production call under it. Remove the prefix (stale class)."
                )

    # ---- staleness: a delegation row nothing excused is a dead excuse -------
    # AUDIT r14 M14-3: the r13 table could name a site that no longer existed
    # and nobody would know, because nothing read it back. A capped row that
    # excused ZERO calls in this pass is either a closed door (delete the row)
    # or a delegation that moved out from under its `// SOUNDNESS:` comment --
    # and in the second case the call is already being COUNTED, so the two
    # halves must be reported together or the RED reads as unexplained.
    for (dfile, dmethod), cap in sorted(delegation_caps(root).items()):
        if cap <= 0:
            red(
                f"FAIL: {DELEGATION_SITES_KEY} row {dfile}::{dmethod} caps occurrences at "
                f"{cap}. A row that excuses nothing is not an account -- delete it."
            )
            continue
        if _DELEGATION_USE.get((dfile, dmethod), 0) == 0:
            red(
                f"FAIL: {DELEGATION_SITES_KEY} row {dfile}::{dmethod} excused no call. "
                f"Either the delegation is gone (delete the row -- the census only "
                f"shrinks) or it lost the `// SOUNDNESS:` comment within "
                f"{SOUNDNESS_WINDOW} lines above it, in which case the call is being "
                f"COUNTED above and this is the reason why."
            )

    # ---- ratchet: a row cannot quietly grow occurrences ---------------------
    #
    # AUDIT r17 (2026-09-14). An ABSENT `max_occurrences` used to `continue`,
    # which made the row UNCAPPED: every call it already accounts for by file or
    # by `site_prefixes` was absorbed at exit 0, however many arrived. That is
    # the opposite of what this file's own "VERDICTS (all fail-closed)" contract
    # says, and it is the exact shape CLAUDE.md forbids -- "a sanctioned site is
    # never a blanket". The sibling scanner already had the right rule and said
    # so in its header: `occurrences` (default 1)
    # (scripts/check_extend_constants_ratchet.py:30,1010). So an absent key now
    # means ONE, not infinity.
    #
    # Measured before landing: all 18 live rows carry an explicit cap, so this
    # changes no live verdict. It was reproducible on this scanner's OWN fixture
    # -- the uncapped, prefix-accounted `builders` row took 1 -> 11 calls and
    # still printed "OK: ... all accounted for" -- and two of the three fixture
    # rows omit the key, so the hole was sitting inside the thing that is
    # supposed to prove the scanner works.
    UNCAPPED_DEFAULT = 1
    for row in rows:
        if not isinstance(row, dict) or row.get("id") is None:
            continue
        cap = row.get("max_occurrences")
        if cap is None:
            cap = UNCAPPED_DEFAULT
        seen = row_occurrences.get(row["id"], 0)
        if seen > cap:
            red(
                f"FAIL: census row {row['id']!r} measures {seen} production occurrences, "
                f"above its max_occurrences baseline {cap}. A new call through a watched "
                f"door must be justified and the baseline raised in review, never absorbed."
            )
        elif seen < cap:
            print(
                f"NOTE: census row {row['id']!r} measures {seen} production occurrences, "
                f"BELOW baseline {cap}; lower max_occurrences in {CENSUS_REL}."
            )

    if ok:
        total = sum(row_occurrences.values())
        print(
            f"OK: env-bypass census — {total} production call sites across "
            f"{len(rows)} census rows all accounted for; "
            f"{len(census.get('cross_references', []) or [])} cross-referenced ledger rows; "
            f"{len(tested)} inline cfg(test) sites excluded."
        )
        return 0
    return 1


# ---------------------------------------------------------------------------
# self-test: a gate that has never been shown to fail is not a gate
# ---------------------------------------------------------------------------

FAKE_TRUSTED_EXT = """\
pub trait TrustedEnvExt {
    fn init_quot(&mut self);
    fn add_decl_unchecked(&mut self, decl: Declaration);
    fn upgrade_axiom_stubs(&mut self, constants: C) -> usize;
}

impl TrustedEnvExt for Environment {
    fn init_quot(&mut self) {
        // SOUNDNESS: trait delegation only, capped in the census artifact.
        Environment::init_quot(self);
    }

    fn upgrade_axiom_stubs(&mut self, constants: C) -> usize {
        // SOUNDNESS: trait delegation only, capped in the census artifact.
        Environment::upgrade_axiom_stubs(self, constants)
    }
}
"""

FAKE_LIB = """\
pub fn wire(env: &mut E, s: S) {
    env.set_constant_source(s);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn t() {
        env.upgrade_axiom_stubs(d);
    }
}
"""

FAKE_KERNEL_BUILDER = """\
pub fn build(env: &mut E) {
    env.init_quot();
}
"""

FAKE_CENSUS = {
    "rows": [
        {
            "id": "stub-upgrade",
            "methods": ["upgrade_axiom_stubs"],
            "classification": "E",
            "disposition_job": "R1-STUB",
            "sites": [],
        },
        {
            "id": "lazy-source",
            "methods": ["set_constant_source"],
            "classification": "S/P",
            "disposition_job": "R1-LAZY",
            "sites": [{"file": "crates/c/src/lib.rs"}],
            "max_occurrences": 1,
        },
        {
            "id": "builders",
            "methods": ["init_quot"],
            "classification": "P",
            "disposition_job": "R1-EQREC",
            "sites": [],
            "site_prefixes": ["crates/k/"],
        },
    ],
    "cross_references": [],
    "trusted_ext_delegation_sites": [
        {
            "file": "crates/clean-kernel/src/env/trusted_ext.rs",
            "method": "init_quot",
            # AUDIT r15 M15-2: headroom ON PURPOSE. With the cap at 1 every
            # mis-nested call reds via the CAP, so an arm aimed at the
            # structural half cannot tell the two apart -- and three arms
            # written that way passed while proving nothing.
            "occurrences": 2,
            "trust": "selftest fixture row",
        },
        # AUDIT r15 M15-2: a SECOND delegation, 5 lines below the first, is what
        # makes the neighbour-comment leg exhibitable at all. With one
        # delegation the arm "its SOUNDNESS comment removed is RED" passed while
        # asserting a property the gate did not have.
        {
            "file": "crates/clean-kernel/src/env/trusted_ext.rs",
            "method": "upgrade_axiom_stubs",
            "occurrences": 1,
            "trust": "selftest fixture row",
        },
    ],
}


def _selftest_tree() -> Path:
    tmp = Path(tempfile.mkdtemp(prefix="env_bypass_selftest_"))
    # AUDIT r15 M15-1: without a `.git`, `_repo_root_of` returns None, so
    # `is_production_file` is False and `is_test_like` falls back to the NAME
    # predicate -- i.e. `classify_paths`, the whole target-side rule round 14
    # introduced, was reached by NO selftest arm in any of the three scanners.
    # One mkdir makes every arm below exercise it.
    (tmp / ".git").mkdir()
    (tmp / "data").mkdir()
    (tmp / "crates" / "c" / "src").mkdir(parents=True)
    (tmp / "crates" / "k" / "src").mkdir(parents=True)
    (tmp / TRUSTED_EXT_REL).parent.mkdir(parents=True)
    (tmp / TRUSTED_EXT_REL).write_text(FAKE_TRUSTED_EXT)
    (tmp / CENSUS_REL).write_text(json.dumps(FAKE_CENSUS, indent=2))
    (tmp / "crates" / "c" / "src" / "lib.rs").write_text(FAKE_LIB)
    (tmp / "crates" / "k" / "src" / "builder.rs").write_text(FAKE_KERNEL_BUILDER)
    return tmp


def _quiet_run(root: Path, require_complete: bool = False) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root, require_complete=require_complete)
    return rc, buf.getvalue()


def _arm(name: str, root: Path, expect: int, require_complete: bool = False) -> bool:
    rc, captured = _quiet_run(root, require_complete)
    good = rc == expect
    print(f"  [{'ok ' if good else 'FAIL'}] {name}: exit {rc} (expected {expect})")
    if not good and captured:
        print("    --- the arm's own output ---")
        for line in captured.rstrip("\n").splitlines():
            print(f"    {line}")
    return good


def _typed_param_selftest(check) -> None:
    """Typed successors add watched doors, not a new bypass or a larger cap."""
    typed = ("set_typed_param_names", "set_typed_param_infos")
    all_methods = ("set_param_names", "set_param_infos", *typed)
    root = _selftest_tree()
    te = root / TRUSTED_EXT_REL
    census_path = root / CENSUS_REL
    register = root / "crates/c/src/metadata.rs"
    extra = root / "crates/c/src/extra.rs"
    comment = "        // SOUNDNESS: this typed metadata forward alone.\n"
    declarations = "".join(f"    fn {method}(&mut self, name: N, values: V);\n" for method in typed)
    forwards = "".join(
        f"    fn {method}(&mut self, name: N, values: V) {{\n"
        + comment + f"        Environment::{method}(self, name, values);\n    }}\n"
        for method in typed
    )
    trait = FAKE_TRUSTED_EXT.replace("pub trait TrustedEnvExt {\n",
                                    "pub trait TrustedEnvExt {\n" + declarations)
    trait = trait.rstrip().removesuffix("}") + forwards + "}\n"
    registration = "pub fn register(env: &mut E) {\n" + (
        "    env.set_typed_param_infos(name, infos);\n" * 3
    ) + "}\n"
    doc = json.loads(json.dumps(FAKE_CENSUS))
    doc["rows"].append({
        "id": "param-binder-metadata", "methods": list(all_methods),
        "classification": "M", "disposition_job": "selftest typed migration",
        "sites": [{"file": "crates/c/src/metadata.rs"}], "max_occurrences": 3,
    })
    for method in typed:
        doc[DELEGATION_SITES_KEY].append({
            "file": str(TRUSTED_EXT_REL), "method": method,
            "occurrences": 1, "trust": "selftest typed forward only",
        })
    try:
        te.write_text(trait)
        register.write_text(registration)
        census_path.write_text(json.dumps(doc))
        check("typed metadata replaces exactly three legacy sites without a cap increase", root, 0)
        for method in typed:
            for form in (f"env.{method}(name, values)",
                         f"Environment::{method}(env, name, values)",
                         f"TrustedEnvExt::{method}(env, name, values)",
                         f"Self::{method}(env, name, values)",
                         f"Alias::{method}(env, name, values)",
                         f"<T as TrustedEnvExt>::{method}(env, name, values)"):
                extra.write_text(f"pub fn smuggle(env: &mut E) {{ {form}; }}\n")
                check(f"unaccounted typed metadata call {form} is RED", root, 1)
            extra.unlink()

            call = f"        Environment::{method}(self, name, values);\n"
            te.write_text(trait.replace(comment + call, call))
            check(f"{method} cannot borrow its neighbor's SOUNDNESS comment", root, 1)
            te.write_text(trait.replace(call, call + call))
            check(f"{method} second delegation exceeds its own one-call cap", root, 1)

            # Deliberate cap headroom isolates the structural ownership check:
            # a call in init_quot is not this typed method's delegation.
            expanded = json.loads(json.dumps(doc))
            next(row for row in expanded[DELEGATION_SITES_KEY]
                 if row["method"] == method)["occurrences"] = 2
            census_path.write_text(json.dumps(expanded))
            te.write_text(trait.replace(
                "        Environment::init_quot(self);\n",
                "        Environment::init_quot(self);\n" + comment + call,
            ))
            check(f"{method} in a different enclosing method is RED with cap headroom", root, 1)
            te.write_text(trait)
            census_path.write_text(json.dumps(doc))

        for method in all_methods:
            register.write_text(registration + f"pub fn fourth(env: &mut E) {{ env.{method}(name, values); }}\n")
            check(f"fourth aggregate metadata call through {method} is RED", root, 1)
        register.write_text(registration)
        extra.write_text("// env.set_typed_param_infos(name, values);\n"
                         'pub fn prose() { let _ = "env.set_typed_param_names(name, values)"; }\n')
        check("typed metadata names in comments and strings do not widen the census", root, 0)
    finally:
        shutil.rmtree(root, ignore_errors=True)


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
        print(f"  [ok  ] cfg lattice: {len(_CFG_LATTICE_CASES)} spellings, "
              f"including the five audit r15 M15-1 found inverted")
        passed += 1

    def check(name: str, root: Path, expect: int, require_complete: bool = False) -> None:
        nonlocal passed, failed
        if _arm(name, root, expect, require_complete):
            passed += 1
        else:
            failed += 1

    _typed_param_selftest(check)

    root = _selftest_tree()
    lib = root / "crates" / "c" / "src" / "lib.rs"
    baseline = FAKE_LIB
    try:
        # 1. pristine tree: an accounted prod call, a prefix-class call, and a
        #    cfg(test)-excluded call -> green
        check("pristine tree (accounted site + prefix class + cfg(test) exclusion) is green", root, 0)

        # 2. NEW unaccounted dot-call bypass -> RED
        lib.write_text(baseline + "\npub fn smuggle(env: &mut E, d: D) { env.upgrade_axiom_stubs(d); }\n")
        check("NEW unaccounted dot-call (upgrade_axiom_stubs) is RED", root, 1)

        # 3. plant removed -> green again
        lib.write_text(baseline)
        check("removing the planted call restores green", root, 0)

        # 4. Environment::-qualified call form is caught too
        lib.write_text(baseline + "\npub fn q(e: &mut E, v: V) { Environment::register_inductive(e, v); }\n")
        check("Environment::-qualified call (register_inductive) is RED", root, 1)

        # 5. trait-qualified call form is caught too
        lib.write_text(baseline + "\npub fn tq(e: &mut E, r: R) { TrustedEnvExt::register_recursor(e, r); }\n")
        check("TrustedEnvExt::-qualified call (register_recursor) is RED", root, 1)

        # 6. the associated deserialization entry points are caught
        lib.write_text(baseline + "\npub fn deser(s: &str) { let _ = Environment::from_json(s); }\n")
        check("Environment::from_json (env deserialization) is RED", root, 1)

        lib.write_text(baseline + "\nfn legacy_restore() { Environment::from_legacy_dag_bincode(bytes, epoch); }\n")
        check("Environment::from_legacy_dag_bincode is a watched data door", root, 1)
        lib.write_text(baseline)

        # 7. the same call inside a #[cfg(test)] mod is EXCLUDED
        lib.write_text(
            baseline
            + "\n#[cfg(test)]\nmod more_tests {\n    fn t2() { let _ = Environment::from_json(s); }\n}\n"
        )
        check("the same call inside #[cfg(test)] mod is excluded (green)", root, 0)

        # 8. a call in a tests/ dir file is EXCLUDED
        lib.write_text(baseline)
        tdir = root / "crates" / "c" / "tests"
        tdir.mkdir()
        (tdir / "t.rs").write_text("fn t() { env.add_skolem_axiom(n, ty); }\n")
        check("a call in a tests/ dir is excluded (green)", root, 0)
        shutil.rmtree(tdir)

        # 9. a call quoted in a comment is NOT a hit
        lib.write_text(baseline + "\n// see env.add_skolem_axiom(n, ty) for the door\n")
        check("a call quoted in a comment is not counted", root, 0)

        # 10. a named site with no live call left is RED (stale row)
        lib.write_text("pub fn clean() {}\n")
        check("a census site row with no live call is RED (stale)", root, 1)

        # 11. a second occurrence beyond max_occurrences is RED
        lib.write_text(
            baseline + "\npub fn wire2(env: &mut E, s: S) { env.set_constant_source(s); }\n"
        )
        check("a second call over the row's max_occurrences cap is RED", root, 1)

        # 11b. AUDIT r17: an UNCAPPED row admits ONE call, not infinity.
        #      `builders` carries no `max_occurrences` and is accounted by
        #      `site_prefixes: ["crates/k/"]`, so before the default existed it
        #      absorbed any number of new calls under that prefix at exit 0 --
        #      reproduced at 1 -> 11 with the gate still printing "all accounted
        #      for". Two of this fixture's three rows omit the key, which is why
        #      the hole lived inside the thing that proves the scanner works.
        #      The arm is TWO-WAY: one call (the baseline above) is green, and
        #      the second is red, so it cannot pass by the gate being broken.
        lib.write_text(baseline)
        builder = root / "crates" / "k" / "src" / "builder.rs"
        builder.write_text(
            FAKE_KERNEL_BUILDER
            + "\npub fn build2(env: &mut E) {\n    env.init_quot();\n}\n"
        )
        check("a SECOND call under an UNCAPPED row is RED (absent cap means 1)", root, 1)
        builder.write_text(FAKE_KERNEL_BUILDER)
        check("...and the uncapped row's single accounted call is still green", root, 0)

        # 12. a stale site_prefix (class with no live call under it) is RED
        lib.write_text(baseline)
        builder = root / "crates" / "k" / "src" / "builder.rs"
        builder.write_text("pub fn clean() {}\n")
        check("a site_prefix with no live call under it is RED (stale class)", root, 1)
        builder.write_text(FAKE_KERNEL_BUILDER)

        # 13. a NEW TrustedEnvExt method nobody watches is RED (trait drift)
        (root / TRUSTED_EXT_REL).write_text(
            FAKE_TRUSTED_EXT.replace(
                "}", "    fn brand_new_door(&mut self, d: D);\n}", 1
            )
        )
        check("a new unwatched TrustedEnvExt method is RED (trait drift)", root, 1)
        (root / TRUSTED_EXT_REL).write_text(FAKE_TRUSTED_EXT)

        # 13b-13e. AUDIT r14 M14-3: the delegation account is CAPPED, requires
        #          the `// SOUNDNESS:` comment, and refuses a row nothing uses.
        #          Rounds 12-13 excused these delegations by a shape and then by
        #          a hardcoded position table in this file, neither of which
        #          capped anything or could go stale.
        te = root / TRUSTED_EXT_REL
        te.write_text(FAKE_TRUSTED_EXT.replace("        // SOUNDNESS: trait delegation only, capped in the census artifact.\n", ""))
        check("a capped delegation with its SOUNDNESS comment removed is RED", root, 1)

        te.write_text(
            FAKE_TRUSTED_EXT.replace(
                "        Environment::init_quot(self);",
                "        Environment::init_quot(self);\n        Environment::init_quot(self);",
            )
        )
        check("a second delegation past the row's occurrences cap is RED", root, 1)

        te.write_text(
            FAKE_TRUSTED_EXT.replace(
                "        Environment::init_quot(self);",
                "        Environment::add_decl_unchecked(self, d);",
            )
        )
        check("a delegation to a door with no capped row is RED", root, 1)

        te.write_text(
            FAKE_TRUSTED_EXT[: FAKE_TRUSTED_EXT.index("\nimpl TrustedEnvExt")] + "\n"
        )
        check("a capped delegation row that excuses nothing is RED (stale)", root, 1)
        te.write_text(FAKE_TRUSTED_EXT)

        # 13f-13i. AUDIT r15 M15-2: the excuse is DERIVED FROM THE SITE. A row
        #          is a cap on a PROVED forward, and the comment scanned is the
        #          one that belongs to THIS call.
        te.write_text(
            FAKE_TRUSTED_EXT.replace(
                "    fn upgrade_axiom_stubs(&mut self, constants: C) -> usize {\n"
                "        // SOUNDNESS: trait delegation only, capped in the census artifact.\n",
                "    fn upgrade_axiom_stubs(&mut self, constants: C) -> usize {\n",
            )
        )
        check("the SECOND delegation's comment removed is RED (the first's does "
              "not cover it)", root, 1)

        te.write_text(FAKE_TRUSTED_EXT)

        # A row buys silence for a REAL new production bypass in a foreign file.
        # This is the capability leg: under the r14 predicate it exits 0 with
        # output byte-identical to pristine.
        extra = root / "crates" / "k" / "src" / "extra.rs"
        extra.write_text(
            "pub fn wire(env: &mut E, s: S) { env.set_constant_source(s); }\n"
        )
        check("a NEW production bypass in a foreign file is RED on its own",
              root, 1)
        doc = json.loads((root / CENSUS_REL).read_text())
        doc["trusted_ext_delegation_sites"].append(
            {"file": "crates/k/src/extra.rs", "method": "set_constant_source",
             "occurrences": 1, "trust": "selftest"}
        )
        (root / CENSUS_REL).write_text(json.dumps(doc, indent=2))
        check("...and a delegation row naming that foreign file does NOT buy it "
              "silence", root, 1)
        _rc, _out = _quiet_run(root)
        if "names a file other than the choke-point trait" in _out:
            passed += 1
            print("  [ok ] ...and the refusal names the real cause, not "
                  "'excused no call'")
        else:
            failed += 1
            print("  [FAIL] the foreign-file refusal did not name its cause")
        extra.unlink()
        (root / CENSUS_REL).write_text(json.dumps(FAKE_CENSUS, indent=2))

        # The STRUCTURAL half, isolated from the occurrences half by the cap
        # headroom above: a capped door called from inside a DIFFERENT
        # delegation is not that delegation.
        # The second door is placed AFTER the genuine forward and carries its
        # OWN comment, so neither the cap (headroom 2) nor the ownership floor
        # can red it -- only the structural predicate can. Written the other way
        # round, the arm passed under a mutation that deleted leg A entirely.
        te.write_text(
            FAKE_TRUSTED_EXT.replace(
                "        Environment::upgrade_axiom_stubs(self, constants)",
                "        Environment::upgrade_axiom_stubs(self, constants);\n"
                "        // SOUNDNESS: a SECOND door, called from a delegation "
                "that is not its own.\n"
                "        Environment::init_quot(self)",
            )
        )
        check("a capped door called from inside a DIFFERENT delegation is RED",
              root, 1)
        te.write_text(FAKE_TRUSTED_EXT)
        (root / CENSUS_REL).write_text(json.dumps(FAKE_CENSUS, indent=2))

        # 13j-13m. AUDIT r16 M16-1 leg 2: `enclosing_fn` was the last `fn` name
        #          seen ANYWHERE earlier in the file, never reset. Each shape
        #          below is a call that is NOT a delegation and was excused as
        #          one, stealing the genuine forward's cap slot -- so the RED
        #          named the genuine forward and the plant appeared nowhere.
        _thief = ("pub fn init_quot(env: &mut Environment) {\n"
                  "    // SOUNDNESS: not a delegation.\n"
                  "    Environment::init_quot(env);\n"
                  "}\n\n")
        te.write_text(FAKE_TRUSTED_EXT.replace(
            "impl TrustedEnvExt for Environment {", _thief + "impl TrustedEnvExt for Environment {"))
        check("a free fn ABOVE the impl, named after a capped door, is RED",
              root, 1)
        _rc, _out = _quiet_run(root)
        if "trusted_ext.rs:8" in _out or "trusted_ext.rs:9" in _out:
            passed += 1
            print("  [ok ] ...and the RED names the PLANT's line, not the genuine forward's")
        else:
            failed += 1
            print(f"  [FAIL] the RED did not name the plant's line: {_out.strip()[:200]}")

        te.write_text(FAKE_TRUSTED_EXT.replace(
            "impl TrustedEnvExt for Environment {",
            "impl SomethingElse {\n    fn init_quot(&mut self) {\n"
            "        // SOUNDNESS: not a delegation.\n"
            "        Environment::init_quot(self);\n    }\n}\n\n"
            "impl TrustedEnvExt for Environment {"))
        check("a same-named fn inside a DIFFERENT impl is RED", root, 1)

        te.write_text(FAKE_TRUSTED_EXT.replace(
            "impl TrustedEnvExt for Environment {",
            "pub trait ImportEnvExt {\n    fn init_quot(&mut self);\n}\n\n"
            "impl ImportEnvExt for Environment {\n    fn init_quot(&mut self) {\n"
            "        // SOUNDNESS: not a delegation.\n"
            "        Environment::init_quot(self);\n    }\n}\n\n"
            "impl TrustedEnvExt for Environment {"))
        check("a SECOND trait forwarding the same door is RED", root, 1)
        te.write_text(FAKE_TRUSTED_EXT)

        # 14. an unbalanced #[cfg(test)] mod fails CLOSED, never skips
        lib.write_text("#[cfg(test)]\nmod tests {\n    fn t() { env.upgrade_axiom_stubs(d); }\n")
        check("an unterminated cfg(test) block fails closed", root, 1)
        lib.write_text(baseline)

        # 15. census completeness: with require_complete (the real-run mode),
        #     the fake census's missing watched methods are RED
        check("an incomplete census is RED under the real-run completeness check", root, 1, True)

        # 16. an unreadable census fails closed
        (root / CENSUS_REL).write_text("{ not json")
        rc = 0
        try:
            _quiet_run(root)
        except SystemExit as exc:
            rc = 1 if exc.code else 0
        good = rc == 1
        print(f"  [{'ok ' if good else 'FAIL'}] an unparsable census fails closed: {good}")
        passed += 1 if good else 0
        failed += 0 if good else 1
    finally:
        shutil.rmtree(root, ignore_errors=True)

    print(f"selftest: {passed} passed, {failed} failed")
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    if "--selftest" in argv:
        return selftest()
    return run(REPO_ROOT, list_only="--list" in argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
