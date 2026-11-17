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
import types
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



# The Rust lexer and the test-code classifier -- which crates/**/*.rs files
# rustc compiles only under cfg(test) -- are check_add_decl_ratchet.py's, executed
# from its source (ignored bytecode is not an input) rather than re-typed, as
# check_extend_constants_ratchet.py does. Until 2026-11-16 this gate carried its
# own copy of both, ~920 lines kept in step by hand, and its classifier was still
# the beside-the-file rule the module-tree walk replaced (docs/DECISIONS.md,
# 2026-11-16); one copy is one rule by construction. check_gate_registry.py R7
# pins it through `--pinned-inputs`.
_reference = types.ModuleType("check_env_bypass_census_reference")
_reference.__file__ = str(Path(__file__).resolve().parent / "check_add_decl_ratchet.py")
exec(compile(Path(_reference.__file__).read_bytes(), _reference.__file__, "exec", dont_inherit=True),
     _reference.__dict__)

strip_noncode = _reference.strip_noncode
lexer_failures = _reference.lexer_failures
_LEXER_CASES = _reference._LEXER_CASES
_CFG_HEAD_CASES = _reference._CFG_HEAD_CASES
_CFG_LATTICE_CASES = _reference._CFG_LATTICE_CASES
_CLASSIFY_CACHE = _reference._CLASSIFY_CACHE
_EDGE_CASES = _reference._EDGE_CASES
_INCLUDE_CASES = _reference._INCLUDE_CASES
_MODULE_TREE_CASES = _reference._MODULE_TREE_CASES
_UNRESOLVED_EDGES = _reference._UNRESOLVED_EDGES
_repo_root_of = _reference._repo_root_of
cfg_lattice_failures = _reference.cfg_lattice_failures
edge_extractor_failures = _reference.edge_extractor_failures
is_production_file = _reference.is_production_file
is_test_like = _reference.is_test_like
module_tree_failures = _reference.module_tree_failures

ANSWERS_PINNED_INPUTS = True
PINNED_INPUTS = ("scripts/check_add_decl_ratchet.py",)


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
        print(f"  [ok  ] cfg lattice: {len(_CFG_LATTICE_CASES) + len(_CFG_HEAD_CASES)} spellings, "
              f"including the five audit r15 M15-1 found inverted and three tool paths")
        passed += 1
    _lexer_bad = lexer_failures()
    if _lexer_bad:
        print(f"  [FAIL] lexer: read differently from rustc: {_lexer_bad}")
        failed += 1
    else:
        print(f"  [ok  ] lexer: {len(_LEXER_CASES)} readings, nested comments, raw-string "
              f"prefixes and char escapes among them")
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

        # 3b. The 79a1983740 shape, end to end: a door call in a module the
        # compiler reaches only through a cfg(test) gate one file up -- through
        # an ordinary `chain.rs` that owns `chain/` -- is test code; the same
        # files with that gate removed are production and RED.
        chain = root / "crates" / "c" / "src" / "chain.rs"
        chain_dir = root / "crates" / "c" / "src" / "chain"
        chain_dir.mkdir()
        chain.write_text("mod deep;\n")
        (chain_dir / "deep.rs").write_text(
            "pub fn smuggle(env: &mut E, d: D) { env.upgrade_axiom_stubs(d); }\n"
        )
        for guard, want in (("#[cfg(test)]", 0), ("", 1)):
            lib.write_text(baseline + "\n" + guard + "\nmod chain;\n")
            check(
                f"a door call in chain/deep.rs under `{guard or '<no guard>'} mod chain;` is "
                f"{'RED' if want else 'green'}",
                root,
                want,
            )
        shutil.rmtree(chain_dir)
        chain.unlink()
        lib.write_text(baseline)

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

        # 14b-c. Test-ness a file carries (2026-11-16,
        # docs/issues/2026-11-16-python-rust-lexer-copies.md).
        src_dir = root / "crates" / "c" / "src"
        plant = "pub fn smuggle(env: &mut E, d: D) { env.upgrade_axiom_stubs(d); }\n"
        lib.write_text(baseline + "\nmod headed;\n")
        (src_dir / "headed.rs").write_text("// note\n\n#![cfg(test)]\n" + plant)
        check("a file headed #![cfg(test)] is test code, whatever declares it", root, 0)
        (src_dir / "headed.rs").write_text("// note\n\n#![cfg(any(test, feature = \"x\"))]\n" + plant)
        check("a file headed by any other cfg stays production", root, 1)
        (src_dir / "headed.rs").unlink()
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
    if "--pinned-inputs" in argv:
        print(*PINNED_INPUTS, sep="\n")
        return 0
    if "--selftest" in argv:
        return selftest()
    return run(REPO_ROOT, list_only="--list" in argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
