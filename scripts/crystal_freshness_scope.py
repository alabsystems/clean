#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Bind the crystal revalidation records to a clean-kernel SOURCE REV, and say
what HEAD's distance from it does and does not invalidate.

THE HOLE THIS FILLS (found 2026-08-19, at clean 891b7d153).

`scripts/crystal_fixture_freshness.py` compares a chain fixture to a LIVE
trustc dump.  It is the only thing that ever has.  But it needs the Trust
compiler, so it cannot run in the Rust suite, and its answer is therefore a
DATED RECORD -- `data/crystal_chain_revalidation_*.json` -- not a standing
claim.  Nothing bound those records to the clean-kernel source they were taken
from, so nothing could tell whether they still describe HEAD.

They did not.  Both committed records were measured with clean-kernel source
tree `214f8ffd0d` (clean revs f99b94e21 / f0846ade2).  At 891b7d153 the kernel
source tree is `a3ae6c21fc`: three files moved (+37 lines) in
`crates/clean-kernel/src/env/`, adding a field to `Environment`, three methods,
and a `Reducibility` match arm.  Every link-2a gate kept passing, because every
one of them reads a fixture.

WHAT THIS DECIDES, AND -- MORE IMPORTANTLY -- WHAT IT REFUSES TO DECIDE

Whether a chained BODY drifted is a question only trustc can answer.  This
script does not pretend otherwise.  What it can decide, with no compiler, is
the SCOPE the record's answer still covers:

  FRESH           the kernel source is byte-identical to the tree the record
                  was measured at.  The record's per-body answer covers HEAD.

  NUMBERING-SCOPE the kernel source moved, but NO chained body's own pinned
                  source moved.  Whole-crate `functy.N` / `enum.N` /
                  `struct.N` / `@func.N` indices have certainly renumbered --
                  adding one item to the crate does that with zero
                  instructions changed.  AMBER: printed, ledgered, and NOT a
                  failure.

  CONTENT-SCOPE   a chained body's own pinned source moved.  The body the spec
                  module transcribes may no longer be the body the producer
                  emits, and no fixture can tell you.  RED: re-derive with
                  `scripts/crystal_fixture_freshness.py` against a fresh dump
                  before trusting any link-2a verdict.

That split is the same one `crystal_fixture_freshness.py` makes between its
AMBER token classes and STRUCTURAL, lifted one level up -- from "which tokens
moved in the emitted text" to "which source could have moved them".  It is the
reason this gate is survivable: a gate that goes red every time an unrelated
crate item is added gets switched off inside a week, and then the CONTENT case
goes unnoticed with it.

It is NOT a claim that numbering-scope drift is harmless to the bodies.  It is
a claim that it is not evidence of body drift, and that the honest response is
a printed, ledgered revalidation DEBT rather than either a silent green or a
red nobody can act on.

WHAT "A BODY'S OWN PINNED SOURCE" IS -- THE ITEM, NOT THE FILE (2026-08-22)

The first cut of this check pinned each chained body's whole defining FILE.
That was the same mistake one level down: it asked a question wider than the
claim.  Commit cd10bf74a added two lines to `crates/clean-kernel/src/env/mod.rs`
-- a `mod inductive_rel_family;` declaration and a `pub use` re-export -- and
the check went CONTENT-SCOPE RED on `strict_monads`, whose def path is
`env::Environment::set_lean4_core_strict_monads` and whose body is one field
store.  A `mod` line cannot move that body's instructions.  `env/mod.rs` is one
of the most-edited files in the kernel and clearing a red here needs a live
trustc dump, so the steady state of a file-granular pin is a permanently
`--no-verify`'d pre-push gate -- which silently disables every other check that
shares it.  That is strictly worse than not having the gate.

So the pin is taken over ITEMS.  Each chained def_path names a list of Rust
items, located by anchor in the file and extracted by brace/`;` matching over a
STRING-, CHAR- AND COMMENT-MASKED copy of the source, and the digest is over
those item texts.  An unrelated edit elsewhere in the same file -- a `mod`
line, an import, another function, a doc comment -- no longer moves it.

THE ITEM LIST IS NOT JUST THE BODY.  Narrowing the pin to the defining function
alone would have been a real weakening: `set_lean4_core_strict_monads` stores
into a field of `Environment`, at an offset chosen by the LAYOUT of a struct
whose definition is a different item in the same file, so a field added to
`Environment` moves the emitted body with the function's own text unchanged.
Under a file pin that reddened; under a naive body pin it would not.  Each
def_path therefore pins its own item PLUS the items in that file whose layout
or signature its emitted code depends on -- the enum it matches on, the struct
whose field it reads, the callee it is composed with, the `impl Deref` it
derefs through.  Those are listed in `BODY_SOURCES` with the reason, and they
are recorded in the scope file, so what is and is not covered is readable
rather than assumed.

FAIL-CLOSED, WHICH IS THE ONLY WAY THIS IS WORTH HAVING

Extraction is a heuristic over text, so it is treated as one.  If any item of a
def_path cannot be located UNAMBIGUOUSLY -- not found, found twice, unbalanced
delimiters, a mask that will not terminate, a span that does not start on an
item keyword, a selector that no longer matches the one the scope file recorded
-- that def_path silently loses NOTHING: it falls back to the WHOLE-FILE digest
it used before, which is the stricter comparison, and the fallback is printed
with its reason on every run.  "Could not extract" is never read as
"unchanged".  A def_path under fallback reddens exactly as it used to.

WHAT CONTENT-SCOPE CAN MISS, STATED RATHER THAN LEFT TO BE DISCOVERED

A body's emitted instructions depend on its own MIR and on the LAYOUT of the
types it touches -- not only on the text of the items it is written in.  This
check pins named items and nothing else, so a layout change to a type defined
in ANOTHER FILE, or an inlined callee moving, would read NUMBERING-SCOPE.

The gap is bounded here rather than open, and the bound is READ FROM THE RECORD
rather than asserted -- the live census is printed with every AMBER verdict, so
do not trust this paragraph over that output:

  * 17 of the 19 chained bodies carry
    `calls: {resolved: 0, extern_decls: 0, unresolved: 0}` -- nothing can be
    inlined into them because nothing is called, so the pin on their own items
    is exact.
  * TWO are covered only approximately because they DO call:
    `has_loose_bvars` and `level_is_zero`.  `level_is_zero`'s 6 calls all go to
    `<LevelArc as Deref>::deref`, and both `LevelArc` and that `Deref` impl live
    in the pinned `src/level/mod.rs` and are named in its item list.
  * Where a body's own types are defined in the pinned file, they are NAMED as
    items (`CleanMode`, `Level`, `FlatFlags`, `ExprPathStep`, `LevelArc`,
    `Environment`).  Two rows -- `get_char_val_trunc` and `meta_tag_shl` -- name
    NO type at all; that is deliberate, because their bodies touch only
    primitives, and it is not the same claim as "their types are pinned".

An earlier revision of this paragraph listed `Expr` among the pinned items and
described `level_is_zero` as the only calling body.  Neither was true of the
runtime: `Expr` is in no item list, and the census prints two approximate rows.
Recorded because a docstring that overstates a gate's coverage is the same
defect as a gate that overstates its own health.

It is still an approximation.  That is exactly why the non-chained case is
AMBER and not green: the only thing that settles it is a dump.

THE MAPPING IS SELF-CHECKING.  Each chained def_path is mapped to one source
file AND to a pattern that must occur in it.  A mapping that no longer resolves
is a HARD failure (exit 2), not a skip -- otherwise a file rename would
silently empty the content-scope check and leave a green that checks nothing.
The item selectors are the softer layer beneath that: they narrow the pin when
they resolve and fall back to the file digest when they do not, so a selector
going stale costs precision and never coverage.

Usage:

    scripts/crystal_freshness_scope.py                 # check HEAD's tree
    scripts/crystal_freshness_scope.py --strict        # AMBER fails too
    scripts/crystal_freshness_scope.py --explain       # per-body detail
    scripts/crystal_freshness_scope.py --emit          # (re)write the scope file
    scripts/crystal_freshness_scope.py --emit --check  # is the committed file derivable?
    scripts/crystal_freshness_scope.py --json OUT

Exit codes: 0 fresh or amber, 1 CONTENT-SCOPE drift (or amber under --strict),
2 the scope file or a mapping is unusable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
KERNEL = Path("crates/clean-kernel")
SCOPE_FILE = REPO / "data" / "crystal_freshness_scope.json"
FIXTURE_SCRIPT = "scripts/crystal_fixture_freshness.py"
SCHEMA = "clean.crystal.freshness_scope/v2"

# The record whose scope this file binds. Dated records are never rewritten;
# this is a separate, derivable statement ABOUT the newest one.
#
# 2026-09-20 to 2026-10-07 it was an AT-HEAD record (`chain_revalidation_at_head/v1`,
# `--at-head`: NUMBERING-ONLY bodies against fixtures cut earlier, producer proved
# by a byte-for-byte control) -- the record kind that clears a CONTENT-SCOPE red
# without a rebaseline, which `crystal_a1_lineage/freshness_scope.rs` still admits.
# Since 2026-10-07 it is a STRICT v3 record again: `strict_monads` went STRUCTURAL
# (field 81 -> 83, two new `Environment` fields), was re-derived in 047ebd051, and
# the source-bound rebaseline at that rev re-cut all 21 fixtures from a live dump
# (trustc 321aaeda7), so the record covers the very rev it was measured at.
# Since 2026-10-18 it is an AT-HEAD record again, measured at bba5da779 (kernel
# source byte-identical to origin/main's): the committed measurement driver moved
# in 44b8ecded, the day after the strict record, and the newest dump must be taken
# by the driver committed now. Its control reproduced the 047ebd051 rebaseline's
# three artifacts byte for byte with that driver; the fixtures stay cut at 047ebd051.
# Since 2026-10-28 it is the at-head record measured at 1633a8e20: c1365ee61 added
# `cumulative_ever` to `pub struct Environment`, which strict_monads pins, so the
# 10-18 record's digest no longer matched; a fresh dump with the same compiler and
# driver found all 19 chains numbering-only or identical, zero structural.
RECORD = "data/crystal_chain_revalidation_2026-11-15_athead_35f090bb3.json"

# chain stem -> (defining source file, a pattern that must occur in it, the
# ITEMS pinned for that body, why those items).
#
# The pattern is what makes the mapping self-checking. `; #loc:` in the fixture
# carries only a whole-crate FILE INDEX, which is meaningless without the dump,
# so the mapping cannot be read off the artifact -- it is stated here and
# verified against the tree on every run.
#
# An ITEM is a tuple of anchors: each anchor is located inside the span of the
# previous one, so `("fn push_low_local", "const META_TAG")` means "the
# `META_TAG` const declared inside `push_low_local`" -- which is what makes the
# def path `LocalContext::push_low_local::META_TAG` addressable at all, since
# the file's `#[cfg(test)]` module declares two more consts of that name.
#
# The item list per body is the body's own item FIRST, then every item in the
# same file whose layout or signature its emitted code depends on. Dropping one
# of those would narrow the pin below the claim; see the module docstring.
BODY_SOURCES: dict[str, tuple[str, str, tuple[tuple[str, ...], ...], str]] = {
    "has_cubical_layer": (
        "src/mode.rs",
        "fn has_cubical_layer",
        (("fn has_cubical_layer",), ("enum CleanMode",)),
        "matches on CleanMode; the emitted body switches on the numeric discriminant",
    ),
    "from_source_system": (
        "src/mode.rs",
        "fn from_source_system",
        (("fn from_source_system",), ("enum CleanMode",), ("enum SourceSystem",)),
        "maps SourceSystem discriminants to CleanMode discriminants; both enums are load-bearing",
    ),
    "level_kind_ord": (
        "src/level/mod.rs",
        "fn kind_ord",
        (("fn kind_ord",), ("pub enum Level {",), ("struct LevelArc",)),
        "matches on Level; the emitted body switches on the numeric discriminant. "
        "`LevelArc` is pinned for the same reason its sibling `level_is_zero` pins "
        "it: `Level` is `Succ(LevelArc) | Max(LevelArc, LevelArc) | IMax(..)`, so "
        "Level's layout and niche depend on LevelArc, which lives in this same "
        "file. Without it an edit to `struct LevelArc` left this row silently "
        "green while `level_is_zero` reddened — a narrowing against the whole-file "
        "pin this replaced, and against this map's own doctrine of pinning the "
        "items whose layout the emitted code depends on.",
    ),
    "level_is_zero": (
        "src/level/mod.rs",
        "fn is_zero",
        (
            ("pub fn is_zero",),
            ("pub enum Level {",),
            ("struct LevelArc",),
            ("impl std::ops::Deref for LevelArc",),
        ),
        "the one chained body that calls: 6 calls into <LevelArc as Deref>::deref, "
        "which is inlinable and lives in this file",
    ),
    "flat_flags_contains": (
        "src/flat/types.rs",
        "fn contains",
        (("const fn contains",), ("struct FlatFlags",)),
        "reads FlatFlags' single field; the newtype's shape decides the emitted mask",
    ),
    "bvar_in_range": (
        "src/expr/mod.rs",
        "fn bvar_in_range",
        (("fn bvar_in_range",),),
        "three u32 primitives in, bool out; no kernel type in the signature",
    ),
    "is_valid_char": (
        "src/env/native_reducers_char.rs",
        "fn is_valid_char",
        (("fn is_valid_char",),),
        "one u64 in, bool out; no kernel type in the signature",
    ),
    "expr_path_step_clone": (
        "src/tc/expr_location.rs",
        "ExprPathStep",
        (("enum ExprPathStep",),),
        "a DERIVED Clone: the body is generated from the enum item and its derive list, "
        "so the enum item IS the body's source",
    ),
    "float_div": (
        "src/env/native_reducers_float.rs",
        "fn reduce_float_div",
        (("fn reduce_float_div",), ("fn float_binary_op",)),
        "the chained def path is the closure inside it; the closure's argument types come "
        "from float_binary_op's bound",
    ),
    "get_char_val_trunc": (
        "src/env/native_reducers_beq_shortcircuit.rs",
        "fn get_char_val",
        (("fn get_char_val",),),
        "the chained def path is the `map` closure inside it",
    ),
    "meta_tag_shl": (
        "src/tc/local_context.rs",
        "META_TAG",
        (("fn push_low_local", "const META_TAG"),),
        "a const item whose body is the shift itself; scoped to its enclosing fn because "
        "the test module declares two more consts of that name",
    ),
    "simp_priority_value": (
        "src/env/types.rs",
        "fn value",
        (("impl SimpPriority", "fn value"), ("enum SimpPriority",)),
        "matches on SimpPriority and reads its payload; `fn value` is not unique in the file",
    ),
    # Chains 12-14, the 2026-08-20 float tranche: three closures inside
    # float_binary_op's callers, one source line each.
    "float_add": (
        "src/env/native_reducers_float.rs",
        "fn reduce_float_add",
        (("fn reduce_float_add",), ("fn float_binary_op",)),
        "the chained def path is the closure inside it; the closure's argument types come "
        "from float_binary_op's bound",
    ),
    "float_sub": (
        "src/env/native_reducers_float.rs",
        "fn reduce_float_sub",
        (("fn reduce_float_sub",), ("fn float_binary_op",)),
        "the chained def path is the closure inside it; the closure's argument types come "
        "from float_binary_op's bound",
    ),
    "float_mul": (
        "src/env/native_reducers_float.rs",
        "fn reduce_float_mul",
        (("fn reduce_float_mul",), ("fn float_binary_op",)),
        "the chained def path is the closure inside it; the closure's argument types come "
        "from float_binary_op's bound",
    ),
    # Chains 15-17, the 2026-08-20 second tranche.
    "strict_monads": (
        "src/env/mod.rs",
        "fn set_lean4_core_strict_monads",
        (("fn set_lean4_core_strict_monads",), ("pub struct Environment",)),
        "one field store into Environment, at an offset chosen by that struct's layout -- "
        "a field added there moves this body with its own text unchanged",
    ),
    "flat_flags_with": (
        "src/flat/types.rs",
        "fn with",
        (("const fn with",), ("struct FlatFlags",)),
        "constructs a FlatFlags from its single field; the newtype's shape decides the emitted or",
    ),
    "node_id_index": (
        "src/cert/builder/state.rs",
        "fn index",
        (("fn index",), ("struct NodeId",)),
        "widens NodeId's single field; the newtype's shape decides the emitted cast",
    ),
    # Chain 18: BOTH halves of the call pair live in one file; the caller's own
    # source anchor is the composition site.
    "has_loose_bvars": (
        "src/expr/meta.rs",
        "fn has_loose_bvars",
        (
            ("fn has_loose_bvars",),
            ("fn loose_bvar_range",),
            ("const BVAR_RANGE_SHIFT",),
            ("struct ExprMeta",),
        ),
        "the composition site: it calls loose_bvar_range, which shifts by BVAR_RANGE_SHIFT "
        "out of ExprMeta's word -- all three are the emitted body's source",
    ),
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


# --------------------------------------------------------------------------
# item extraction
# --------------------------------------------------------------------------
#
# Everything below is deliberately paranoid. It exists to make the pin narrower
# than a whole file, and a narrower pin that is WRONG is worse than the wide one
# it replaced -- so every function here reports failure rather than a guess, and
# every failure routes the def_path back to the whole-file digest.


class ExtractError(Exception):
    """The item could not be located unambiguously. Always -> file fallback."""


_RAW_STRING = re.compile(r"(b?r)(#*)\"")
_IDENT_CHAR = re.compile(r"[0-9A-Za-z_]")
_ITEM_KEYWORDS = frozenset(
    {
        "pub",
        "const",
        "static",
        "unsafe",
        "async",
        "extern",
        "fn",
        "struct",
        "enum",
        "trait",
        "impl",
        "type",
        "mod",
        "union",
        "use",
        "default",
        "macro_rules",
    }
)


def mask_code(text: str, *, literals: bool = True) -> str:
    """A same-length copy of `text` with comments -- and, unless `literals` is
    False, string and char literals -- blanked to spaces (newlines kept, so
    offsets and line numbers are shared).

    Brace matching over the raw text would cut the wrong span the first time a
    `{` appeared inside a string or a `//` comment -- and this kernel is full of
    both, including a comment in `tc/local_context.rs` that names `META_TAG`
    precisely to warn a reader off it. Masking first is what makes the anchor
    search and the brace walk mean "in code".

    `literals=False` still SCANS every literal (so a `//` inside a string is
    never mistaken for a comment) but leaves its bytes alone. That mode is for
    the digest: a comment cannot move an emitted instruction and a string can.

    Raises `ExtractError` on anything it cannot close (an unterminated block
    comment or string literal), because a partial mask is a wrong mask.
    """
    out = list(text)
    n = len(text)

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    def blank_literal(a: int, b: int) -> None:
        if literals:
            blank(a, b)

    i = 0
    while i < n:
        c = text[i]
        prev_is_ident = i > 0 and _IDENT_CHAR.match(text[i - 1]) is not None

        if c == "/" and text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
            continue

        if c == "/" and text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if depth:
                raise ExtractError("unterminated block comment")
            blank(i, j)
            i = j
            continue

        if not prev_is_ident and (c == "r" or c == "b"):
            m = _RAW_STRING.match(text, i)
            if m is not None:
                close = '"' + m.group(2)
                j = text.find(close, m.end())
                if j < 0:
                    raise ExtractError("unterminated raw string literal")
                j += len(close)
                blank_literal(i, j)
                i = j
                continue

        if c == '"' or (c == "b" and not prev_is_ident and text.startswith('b"', i)):
            j = i + (2 if c == "b" else 1)
            closed = False
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    closed = True
                    break
                j += 1
            if not closed:
                raise ExtractError("unterminated string literal")
            blank_literal(i, j)
            i = j
            continue

        if c == "'" or (c == "b" and not prev_is_ident and text.startswith("b'", i)):
            q = i if c == "'" else i + 1  # index of the opening quote
            if text[q + 1 : q + 2] == "\\":
                j = q + 2
                if text[j : j + 1] == "u" and text[j + 1 : j + 2] == "{":
                    close = text.find("}", j)
                    if close < 0:
                        raise ExtractError("unterminated unicode char escape")
                    j = close + 1
                else:
                    j += 1
                if text[j : j + 1] != "'":
                    raise ExtractError("unterminated char literal")
                blank_literal(i, j + 1)
                i = j + 1
                continue
            if text[q + 2 : q + 3] == "'":
                blank_literal(i, q + 3)
                i = q + 3
                continue
            # Not a char literal: a lifetime (`'a`, `'static`, `'_`). Left alone.
            i += 1
            continue

        i += 1

    return "".join(out)


def _match_forward_brace(masked: str, i: int) -> int:
    """Index of the `}` closing the `{` at `i`, over already-masked text."""
    depth, n = 0, len(masked)
    while i < n:
        c = masked[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ExtractError("unbalanced braces after the anchor")


def _match_backward(masked: str, i: int, opener: str, closer: str) -> int:
    """Index of the `opener` matching the `closer` at `i`, scanning backwards."""
    depth = 0
    while i >= 0:
        c = masked[i]
        if c == closer:
            depth += 1
        elif c == opener:
            depth -= 1
            if depth == 0:
                return i
        i -= 1
    raise ExtractError("unbalanced brackets before the anchor")


def _item_start(text: str, masked: str, pos: int) -> int:
    """Start of the item whose anchor sits at `pos`: the anchor's line start,
    extended back over any `#[...]` / `#![...]` attributes.

    Attributes are absorbed because they are codegen input -- `#[inline]`,
    `#[derive(Clone)]`, `#[repr(u8)]` all change what is emitted, and the whole
    point of the derive chain (`expr_path_step_clone`) is that the item's body
    IS its derive list. Doc comments are already spaces in `masked`, so they are
    skipped over rather than absorbed: they cannot move an instruction.
    """
    start = text.rfind("\n", 0, pos) + 1
    while True:
        j = start
        while j > 0 and masked[j - 1] in " \t\r\n":
            j -= 1
        if j > 0 and masked[j - 1] == "]":
            k = _match_backward(masked, j - 1, "[", "]")
            m = k - 1 if k > 0 and masked[k - 1] == "!" else k
            if m > 0 and masked[m - 1] == "#":
                start = m - 1
                continue
        break
    line_start = text.rfind("\n", 0, start) + 1
    if masked[line_start:start].strip() == "":
        start = line_start
    return start


def _item_end(masked: str, start: int) -> int:
    """End (exclusive) of the item beginning at `start`.

    A braced item ends at the `}` matching its first depth-0 `{`; a `const` /
    `static` / tuple-struct / `use` item ends at its first depth-0 `;`. Round
    and square depth is tracked so that `#[derive(...)]`, `[u8; 4]` and an
    argument list cannot be mistaken for either terminator.
    """
    depth_round = depth_square = 0
    i, n = start, len(masked)
    while i < n:
        c = masked[i]
        if c == "(":
            depth_round += 1
        elif c == ")":
            depth_round -= 1
            if depth_round < 0:
                raise ExtractError("unbalanced parentheses in the item header")
        elif c == "[":
            depth_square += 1
        elif c == "]":
            depth_square -= 1
            if depth_square < 0:
                raise ExtractError("unbalanced brackets in the item header")
        elif c == "{" and depth_round == 0 and depth_square == 0:
            close = _match_forward_brace(masked, i)
            k = close + 1
            while k < n and masked[k] in " \t\r\n":
                k += 1
            # `const X: T = Foo { .. };` -- the braces close the initializer,
            # the item closes at the `;`.
            return k + 1 if k < n and masked[k] == ";" else close + 1
        elif c == ";" and depth_round == 0 and depth_square == 0:
            return i + 1
        i += 1
    raise ExtractError("no item terminator (`{...}` or `;`) after the anchor")


def _starts_on_an_item(masked_span: str) -> bool:
    """Does the span begin with attributes and then an item keyword?

    The last line of defence against an anchor that matched inside an
    expression: if the extracted span does not start where a Rust item can
    start, the span is not an item and the digest would be over the wrong text.
    """
    i, n = 0, len(masked_span)
    while i < n:
        while i < n and masked_span[i] in " \t\r\n":
            i += 1
        if i < n and masked_span[i] == "#":
            j = i + 1
            if j < n and masked_span[j] == "!":
                j += 1
            if j >= n or masked_span[j] != "[":
                return False
            depth = 0
            while j < n:
                if masked_span[j] == "[":
                    depth += 1
                elif masked_span[j] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= n:
                return False
            i = j + 1
            continue
        break
    m = re.match(r"[A-Za-z_][0-9A-Za-z_]*", masked_span[i:])
    return m is not None and m.group(0) in _ITEM_KEYWORDS


def _locate(text: str, masked: str, anchor: str, lo: int, hi: int) -> tuple[int, int]:
    """Span of the single item matching `anchor` inside `masked[lo:hi]`."""
    hits = []
    at = masked.find(anchor, lo, hi)
    while at >= 0:
        hits.append(at)
        if len(hits) > 1:
            break
        at = masked.find(anchor, at + 1, hi)
    if not hits:
        raise ExtractError("anchor `%s` occurs nowhere in code" % anchor)
    if len(hits) > 1:
        raise ExtractError("anchor `%s` occurs more than once in code" % anchor)
    start = _item_start(text, masked, hits[0])
    if start < lo:
        raise ExtractError("anchor `%s` starts outside its enclosing item" % anchor)
    end = _item_end(masked, start)
    if end > hi or end <= start:
        raise ExtractError("item for `%s` runs past its enclosing item" % anchor)
    if not _starts_on_an_item(masked[start:end]):
        raise ExtractError("the span for `%s` does not begin on a Rust item" % anchor)
    return start, end


def normalize_item(item: str) -> str:
    """The item's CODE text: comments blanked, blank lines dropped, trailing
    whitespace stripped.

    A comment cannot move an emitted instruction, so hashing raw bytes would
    make the pin reject a reworded doc comment as if it were a body change --
    and the pinned items include `Environment` (1,300+ documented fields) and
    `CleanMode`, where that is the common edit, not the rare one. String and
    char literals are left EXACTLY as written: those are data the compiler
    emits, so a changed byte in one is a real change.

    This is a narrowing of what the digest reacts to, so it is stated in the
    scope file's `body_digest_definition` rather than left implicit.
    """
    masked = mask_code(item, literals=False)
    return "\n".join(line.rstrip() for line in masked.split("\n") if line.strip())


def extract_items(text: str, selectors: tuple[tuple[str, ...], ...]) -> list[str]:
    """The item texts named by `selectors`, in order. Raises `ExtractError`."""
    masked = mask_code(text)
    if len(masked) != len(text):
        raise ExtractError("internal: the mask changed the source length")
    out: list[str] = []
    for path in selectors:
        lo, hi = 0, len(masked)
        for anchor in path:
            lo, hi = _locate(text, masked, anchor, lo, hi)
        out.append(text[lo:hi])
    return out


def body_digest_text(
    text: str, selectors: tuple[tuple[str, ...], ...]
) -> tuple[str | None, str]:
    """(digest over the pinned items of `text`, status).

    Status is `"item"` on success, or `"file-fallback: <reason>"` -- in which
    case the digest is `None` and the caller MUST compare whole files instead.
    Never returns a digest it is not sure of; that inversion is the one thing
    that would make this gate decoration.
    """
    try:
        items = extract_items(text, selectors)
    except ExtractError as exc:
        return None, "file-fallback: %s" % exc
    agg = hashlib.sha256()
    for path_anchors, item in zip(selectors, items):
        agg.update(("::".join(path_anchors)).encode("utf-8"))
        agg.update(b"\0")
        agg.update(normalize_item(item).encode("utf-8"))
        agg.update(b"\n")
    return agg.hexdigest(), "item"


def body_digest(
    path: Path, selectors: tuple[tuple[str, ...], ...]
) -> tuple[str | None, str]:
    """`body_digest_text` over a file, with unreadability as one more fallback."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return None, "file-fallback: unreadable as utf-8 (%s)" % exc
    return body_digest_text(text, selectors)


def kernel_files(root: Path) -> list[Path]:
    """The kernel source set, walked from the FILESYSTEM.

    Filesystem rather than git on purpose: the verdict must be the same in a
    detached worktree, in a pinned suite-runner checkout and in a tree with
    uncommitted edits, and it must not need git history at all. An untracked
    `.rs` under `src/` is therefore included -- conservative in the fail-closed
    direction, since a file that is present but unreferenced can only make the
    digest move earlier, never later.
    """
    base = root / KERNEL
    out = sorted(p for p in (base / "src").rglob("*.rs") if p.is_file())
    manifest = base / "Cargo.toml"
    if manifest.is_file():
        out.append(manifest)
    return out


def kernel_digest(root: Path) -> tuple[str, dict[str, str]]:
    """(aggregate digest, per-file digest) over the kernel source set."""
    per: dict[str, str] = {}
    agg = hashlib.sha256()
    for path in kernel_files(root):
        rel = path.relative_to(root).as_posix()
        digest = sha256_bytes(path.read_bytes())
        per[rel] = digest
        agg.update(rel.encode("utf-8"))
        agg.update(b"\0")
        agg.update(digest.encode("ascii"))
        agg.update(b"\n")
    return agg.hexdigest(), per


def check_mapping(root: Path) -> list[str]:
    """Every mapped file exists and still contains its item. Fail closed."""
    problems: list[str] = []
    for stem, (rel, pattern, _selectors, _why) in sorted(BODY_SOURCES.items()):
        path = root / KERNEL / rel
        if not path.is_file():
            problems.append(f"{stem}: {KERNEL / rel} does not exist")
            continue
        if pattern not in path.read_text(encoding="utf-8", errors="replace"):
            problems.append(
                f"{stem}: {KERNEL / rel} no longer contains `{pattern}` — the mapping is "
                "stale, so the content-scope check would silently cover nothing"
            )
    return problems


def call_census(record_rel: str) -> tuple[int, list[str]]:
    """(bodies making no calls, names of those that do) from the record.

    The content-scope check pins a body's own ITEMS, which is exact only while
    nothing is inlined into that body from another file. A zero-call body
    settles that directly, so the census is the honest measure of how much of
    the closure the pin actually covers -- and it is read live, so it cannot rot
    into a claim about a record that has moved on.
    """
    chains = json.loads((REPO / record_rel).read_text(encoding="utf-8"))["chains"]
    zero, called = 0, []
    for stem in sorted(BODY_SOURCES):
        row = chains.get(stem) or {}
        calls = (row.get("links_at_head") or {}).get("calls") or {}
        if calls.get("resolved") == 0:
            zero += 1
        else:
            called.append(stem)
    return zero, called


class ScopeUnusable(Exception):
    """The scope cannot be (re-)derived; the message says why."""


def is_commit(rev: str) -> bool:
    """Is `rev` a commit of this repository?"""
    probe = subprocess.run(
        ["git", "-C", str(REPO), "cat-file", "-e", rev + "^{commit}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return probe.returncode == 0


def tree_at(rev: str) -> Path:
    """Extract `crates/clean-kernel` at `rev` into a temp dir and return it."""
    if not is_commit(rev):
        raise ScopeUnusable("%s is not a commit in this repository" % rev)
    out = Path(tempfile.mkdtemp(prefix="crystal-scope-")) / "t"
    out.mkdir()
    archive = subprocess.run(
        ["git", "-C", str(REPO), "archive", rev, str(KERNEL)],
        stdout=subprocess.PIPE,
        check=True,
    ).stdout
    subprocess.run(["tar", "-x", "-C", str(out)], input=archive, check=True)
    return out


def moved_kernel_files(rev: str) -> list[str] | None:
    """Best-effort listing of which kernel files moved since `rev`.

    Compared against the WORKING TREE rather than against HEAD, so it agrees
    with the digest walk above on a tree with uncommitted edits. Reported for
    the operator, never for the verdict: the verdict is decided by the digests
    in the scope file, which need no git at all. A tree without git history
    still gets a correct verdict and loses only this listing.
    """
    try:
        done = subprocess.run(
            ["git", "-C", str(REPO), "diff", "--name-only", rev, "--", str(KERNEL)],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return sorted(line for line in done.stdout.splitlines() if line.strip())


def emit(rev: str, read_at: str, expect_digest: str | None, check: bool) -> int:
    """Write (or, with `check`, compare against) the scope file for `rev`.

    The kernel tree is READ at `read_at`: `rev` itself when it is a commit
    here, otherwise a pushed witness commit. Either way its kernel digest must
    be `expect_digest` -- the digest the record says it measured -- or nothing
    is written: a witness is only as good as that equality.
    """
    root = tree_at(read_at)
    try:
        problems = check_mapping(root)
        if problems:
            for p in problems:
                print("MAPPING UNUSABLE AT %s: %s" % (read_at, p), file=sys.stderr)
            return 2
        agg, per = kernel_digest(root)
        if expect_digest is not None and agg != expect_digest:
            print(
                "SCOPE UNUSABLE: the kernel at %s digests to %s, not the record's %s; "
                "that tree is not the one the record measured." % (read_at, agg, expect_digest),
                file=sys.stderr,
            )
            return 2
        bodies: dict[str, dict[str, object]] = {}
        fell_back: list[str] = []
        for stem, (rel, pattern, selectors, why) in sorted(BODY_SOURCES.items()):
            rel_posix = (KERNEL / rel).as_posix()
            digest, status = body_digest(root / KERNEL / rel, selectors)
            if status != "item":
                fell_back.append("%s: %s" % (stem, status))
            bodies[stem] = {
                "file": rel_posix,
                "sha256": per[rel_posix],
                "must_contain": pattern,
                "items": [list(p) for p in selectors],
                "items_why": why,
                "body_sha256": digest,
                "body_extraction": status,
            }
    finally:
        shutil.rmtree(root.parent, ignore_errors=True)
    doc = {
        "schema": SCHEMA,
        "what_this_is": (
            "The clean-kernel SOURCE the newest crystal revalidation record was measured "
            "at. Whether a chained BODY drifted is a question only trustc can answer, and "
            "the record is its DATED answer; this pins the tree that answer covers, so a "
            "pre-push gate and a suite row can decide -- with no Trust compiler and no "
            "dump -- whether it still covers the tree in front of them. Derivable: "
            "`scripts/crystal_freshness_scope.py --emit`, checked by `--emit --check`. "
            "When the record's rev is not a commit here, the kernel tree is read at "
            "`kernel_tree_read_at`, a pushed commit whose kernel source digests to the "
            "record's clean_kernel_src_sha256 (named once with --witness)."
        ),
        "record": RECORD,
        "covered_clean_rev": rev,
        "clean_kernel_src_sha256": agg,
        "clean_kernel_src_file_count": len(per),
        "digest_definition": (
            "sha256 over, in sorted path order, `<repo-relative path>\\0<sha256 of file "
            "bytes>\\n` for every crates/clean-kernel/src/**/*.rs plus "
            "crates/clean-kernel/Cargo.toml, walked from the filesystem."
        ),
        "body_digest_definition": (
            "Per chained def_path, sha256 over, in the order `items` lists them, "
            "`<anchors joined by ::>\\0<the item's CODE text>\\n`. An item is located by "
            "finding its anchor in a string-, char- and comment-MASKED copy of the file "
            "(so a brace in a literal or a comment cannot cut the span), taking the "
            "anchor's line start extended back over any #[...] attributes, and ending at "
            "the `}` matching the first depth-0 `{` or at the first depth-0 `;`. The item's "
            "CODE text is that span with COMMENTS blanked, blank lines dropped and trailing "
            "whitespace stripped -- a comment cannot move an emitted instruction -- while "
            "string and char literals are kept byte-for-byte, because those are data the "
            "compiler emits. `items` "
            "pins the body's own item plus the items in that file whose layout or "
            "signature its emitted code depends on; `items_why` says which and why. If "
            "any item cannot be located UNAMBIGUOUSLY the entry records "
            "body_sha256: null and body_extraction: \"file-fallback: <reason>\", and the "
            "check compares `sha256` -- the whole FILE -- for that def_path instead."
        ),
        "chained_body_sources": bodies,
        "how_to_re_derive": (
            "A CONTENT-SCOPE failure is not refreshed by re-emitting this file. Produce a "
            "fresh dump and run " + FIXTURE_SCRIPT + ", commit the new revalidation "
            "record, point `record` at it, then --emit."
        ),
    }
    if read_at != rev:
        doc["kernel_tree_read_at"] = read_at
    text = json.dumps(doc, indent=1) + "\n"
    if check:
        committed = SCOPE_FILE.read_text(encoding="utf-8") if SCOPE_FILE.is_file() else ""
        if committed == text:
            print("SCOPE_EMIT=reproduced %s (kernel read at %s)" % (SCOPE_FILE.name, read_at))
            return 0
        print(
            "SCOPE_EMIT=differs: re-deriving %s at %s does not reproduce the committed "
            "file; it is not derivable as committed." % (SCOPE_FILE.name, read_at),
            file=sys.stderr,
        )
        return 1
    SCOPE_FILE.write_text(text, encoding="utf-8")
    print("wrote %s" % SCOPE_FILE)
    print("  covered_clean_rev        %s" % rev)
    print("  clean_kernel_src_sha256  %s" % agg)
    print("  files                    %d" % len(per))
    print(
        "  bodies pinned at ITEM granularity  %d of %d"
        % (len(BODY_SOURCES) - len(fell_back), len(BODY_SOURCES))
    )
    for line in fell_back:
        print("    FILE-GRANULAR (extraction failed) %s" % line)
    return 0


def compare_bodies(
    scope: dict, per: dict[str, str]
) -> tuple[list[str], list[str], list[dict[str, str]]]:
    """(drifted, item-granular stems, printed fallback notes).

    A def_path is compared at ITEM granularity only when BOTH sides extracted
    cleanly AND the recorded selector is the one this script would use now.
    Anything else compares the whole FILE, which is the check this replaced --
    strictly stronger, never weaker.
    """
    drifted: list[str] = []
    item_granular: list[str] = []
    notes: list[dict[str, str]] = []
    for stem, entry in sorted(scope["chained_body_sources"].items()):
        rel_posix = entry["file"]
        live_file = per.get(rel_posix)
        mapped = BODY_SOURCES.get(stem)
        recorded_items = entry.get("items")
        recorded_body = entry.get("body_sha256")

        reason: str | None = None
        if mapped is None:
            reason = "the scope file pins a def_path this script no longer maps"
        elif recorded_items is None or recorded_body is None:
            reason = (
                "the scope file predates item granularity (no body_sha256); re-emit at "
                "the SAME covered_clean_rev to re-pin at item granularity"
            )
        elif [list(p) for p in mapped[2]] != recorded_items:
            reason = (
                "the recorded item selector is not the one this script uses now; re-emit "
                "at the SAME covered_clean_rev to re-pin"
            )
        elif (KERNEL / mapped[0]).as_posix() != rel_posix:
            # An item digest carries no path, so a body that MOVED FILE with its
            # text intact would compare equal against the old file's pin. The
            # file is part of the claim; a disagreement is settled by the file
            # digest, which reads the recorded path and so reports ABSENT.
            reason = (
                "this script now maps the def_path to %s, not the recorded %s"
                % ((KERNEL / mapped[0]).as_posix(), rel_posix)
            )

        if reason is None and mapped is not None:
            live_body, status = body_digest(REPO / KERNEL / mapped[0], mapped[2])
            if status != "item":
                reason = status.replace("file-fallback: ", "", 1)
            else:
                item_granular.append(stem)
                if live_body != recorded_body:
                    drifted.append(
                        "%s: pinned items moved (%s -> %s) in %s"
                        % (
                            stem,
                            str(recorded_body)[:12],
                            str(live_body or "ABSENT")[:12],
                            rel_posix,
                        )
                    )
                continue

        notes.append({"def_path": stem, "file": rel_posix, "reason": reason})
        if live_file != entry["sha256"]:
            drifted.append(
                "%s: %s moved (%s -> %s) [file granularity: %s]"
                % (
                    stem,
                    rel_posix,
                    entry["sha256"][:12],
                    (live_file or "ABSENT")[:12],
                    reason,
                )
            )
    return drifted, item_granular, notes


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--emit", action="store_true", help="(re)write the scope file")
    ap.add_argument(
        "--at",
        default=None,
        help="with --emit, the clean rev to pin (default: the record's clean_worktree_rev)",
    )
    ap.add_argument(
        "--witness",
        default=None,
        help="with --emit, a pushed commit to READ the kernel tree at when the covered "
        "rev is not a commit here; its kernel digest must equal the record's",
    )
    ap.add_argument(
        "--check",
        action="store_true",
        help="with --emit, compare the re-derived scope file with the committed one "
        "instead of writing it",
    )
    ap.add_argument(
        "--strict", action="store_true", help="NUMBERING-SCOPE drift fails too"
    )
    ap.add_argument(
        "--explain",
        action="store_true",
        help="print per-body granularity, pinned items and digests",
    )
    ap.add_argument("--json", type=Path, default=None, help="write the verdict here")
    args = ap.parse_args()

    if args.emit:
        record = json.loads((REPO / RECORD).read_text(encoding="utf-8"))
        provenance = record.get("provenance") or {}
        pinned = provenance.get("clean_source_rev") or provenance.get(
            "clean_worktree_rev"
        )
        rev = args.at
        if rev is None:
            rev = pinned
            if not rev:
                print(
                    "SCOPE UNUSABLE: %s carries neither provenance.clean_source_rev nor "
                    "provenance.clean_worktree_rev." % RECORD,
                    file=sys.stderr,
                )
                return 2
        elif pinned and rev != pinned:
            # The default --emit re-derives at the RECORD's own rev, so it can
            # only ever re-state the same measurement -- at finer granularity,
            # say, which is a legitimate reason to re-emit. `--at` is the only
            # way to move the pin, and moving the pin without a fresh dump would
            # convert a CONTENT-SCOPE red into a green that measured nothing.
            print(
                "WARNING: --at %s is NOT the rev %s was measured at (%s). Moving the pin\n"
                "         does not revalidate anything: a CONTENT-SCOPE red is cleared by a\n"
                "         fresh %s dump and a NEW record, never by re-emitting."
                % (rev, RECORD, pinned, FIXTURE_SCRIPT),
                file=sys.stderr,
            )
        read_at = rev
        if not is_commit(rev):
            if rev != pinned:
                print(
                    "SCOPE UNUSABLE: --at %s is not a commit in this repository, and only "
                    "the record's own rev has a measured kernel digest a witness could be "
                    "checked against." % rev,
                    file=sys.stderr,
                )
                return 2
            read_at = args.witness
            if read_at is None and SCOPE_FILE.is_file():
                committed = json.loads(SCOPE_FILE.read_text(encoding="utf-8"))
                if committed.get("covered_clean_rev") == rev:
                    read_at = committed.get("kernel_tree_read_at")
            if not read_at:
                print(
                    "SCOPE UNUSABLE: %s is not a commit in this repository, so its kernel "
                    "tree cannot be read. Name a pushed commit whose kernel source digests "
                    "to the record's clean_kernel_src_sha256: --witness <rev>." % rev,
                    file=sys.stderr,
                )
                return 2
        elif args.witness is not None:
            print(
                "SCOPE UNUSABLE: --witness %s given, but %s is a commit here; the tree is "
                "read at the rev itself." % (args.witness, rev),
                file=sys.stderr,
            )
            return 2
        expect = provenance.get("clean_kernel_src_sha256") if rev == pinned else None
        try:
            return emit(rev, read_at, expect, args.check)
        except ScopeUnusable as exc:
            print("SCOPE UNUSABLE: %s" % exc, file=sys.stderr)
            return 2

    if not SCOPE_FILE.is_file():
        print("SCOPE UNUSABLE: %s is missing." % SCOPE_FILE, file=sys.stderr)
        print("  Re-derive it: scripts/crystal_freshness_scope.py --emit", file=sys.stderr)
        return 2
    scope = json.loads(SCOPE_FILE.read_text(encoding="utf-8"))
    if not (REPO / scope["record"]).is_file():
        print(
            "SCOPE UNUSABLE: it names %s, which is not in the tree." % scope["record"],
            file=sys.stderr,
        )
        return 2

    problems = check_mapping(REPO)
    if problems:
        for p in problems:
            print("MAPPING UNUSABLE: %s" % p, file=sys.stderr)
        return 2

    agg, per = kernel_digest(REPO)
    moved_bodies, item_granular, fallback_notes = compare_bodies(scope, per)

    verdict = (
        "CONTENT-SCOPE"
        if moved_bodies
        else ("FRESH" if agg == scope["clean_kernel_src_sha256"] else "NUMBERING-SCOPE")
    )

    total = len(scope["chained_body_sources"])
    print("== crystal revalidation scope ==")
    print("record                 %s" % scope["record"])
    print("covered_clean_rev      %s" % scope["covered_clean_rev"])
    print("covered kernel digest  %s" % scope["clean_kernel_src_sha256"][:24])
    print("live kernel digest     %s" % agg[:24])
    print(
        "body pin granularity   %d of %d def_paths at ITEM level, %d at FILE level"
        % (len(item_granular), total, total - len(item_granular))
    )
    print("verdict                %s" % verdict)

    if fallback_notes:
        print(
            "\nFILE-GRANULAR def_paths — the item could not be located, so the WHOLE FILE is\n"
            "compared for these (the check this replaced; strictly stronger, never weaker).\n"
            "An unextractable item is never read as an unchanged one:"
        )
        grouped: dict[str, list[str]] = {}
        for note in fallback_notes:
            grouped.setdefault(note["reason"], []).append(
                "%s (%s)" % (note["def_path"], note["file"])
            )
        for reason, wheres in sorted(grouped.items()):
            print("  %s" % reason)
            for where in wheres:
                print("      %s" % where)

    if args.explain:
        print("\n== per-body pin ==")
        for stem, entry in sorted(scope["chained_body_sources"].items()):
            mapped = BODY_SOURCES.get(stem)
            live_body, status = (
                body_digest(REPO / KERNEL / mapped[0], mapped[2])
                if mapped
                else (None, "file-fallback: unmapped")
            )
            print(
                "  %-22s %-14s recorded %s live %s"
                % (
                    stem,
                    "ITEM" if status == "item" else "FILE",
                    str(entry.get("body_sha256"))[:12],
                    str(live_body)[:12],
                )
            )
            if mapped:
                for path_anchors in mapped[2]:
                    print("      item  %s" % " :: ".join(path_anchors))
                print("      why   %s" % mapped[3])

    if args.json:
        args.json.write_text(
            json.dumps(
                {
                    "schema": "clean.crystal.freshness_scope_verdict/v2",
                    "verdict": verdict,
                    "record": scope["record"],
                    "covered_clean_rev": scope["covered_clean_rev"],
                    "covered_kernel_src_sha256": scope["clean_kernel_src_sha256"],
                    "live_kernel_src_sha256": agg,
                    "chained_body_sources_moved": moved_bodies,
                    "item_granular_def_paths": sorted(item_granular),
                    "file_granular_def_paths": sorted(
                        set(scope["chained_body_sources"]) - set(item_granular)
                    ),
                    "file_granular_reasons": fallback_notes,
                },
                indent=1,
            )
            + "\n",
            encoding="utf-8",
        )
        print("verdict written to %s" % args.json)

    if verdict == "CONTENT-SCOPE":
        print("\nRED — a chained body's own pinned source moved:")
        for m in moved_bodies:
            print("  %s" % m)
        print(
            "\nThe body the spec module transcribes may no longer be the body the producer\n"
            "emits, and NO fixture in this tree can tell you: every link-2a gate reads the\n"
            "fixture. Re-DERIVE against a live dump (%s) and commit a\n"
            "new revalidation record. Do not re-emit the scope file to clear this." % FIXTURE_SCRIPT
        )
        return 1

    if verdict == "NUMBERING-SCOPE":
        print(
            "\nAMBER — the kernel source moved, but no chained body's own pinned items did.\n"
            "  Whole-crate functy.N / enum.N / struct.N / @func.N indices have renumbered:\n"
            "  adding one crate item does that with zero instructions changed. That is NOT\n"
            "  evidence a body drifted, and it is NOT a claim that none did — only a fresh\n"
            "  dump can say. It is a revalidation DEBT, and it is printed rather than\n"
            "  smoothed."
        )
        zero, called = call_census(scope["record"])
        print(
            "  closure note: %d of %d chained bodies make ZERO calls in the record, so nothing\n"
            "  can be inlined into them and the pin on their own items is exact. %s"
            % (
                zero,
                zero + len(called),
                (
                    "Covered only approximately: "
                    + ", ".join(called)
                    + " (calls, so an inlined callee could move instructions with the pinned "
                    "items unchanged)."
                    if called
                    else "No calling body is left, so the pin is exact throughout."
                ),
            )
        )
        listing = moved_kernel_files(scope["covered_clean_rev"])
        if listing is None:
            print("  (which files moved is unavailable here — no usable git history)")
        else:
            print("  kernel files moved since %s: %d" % (scope["covered_clean_rev"][:9], len(listing)))
            for rel in listing[:12]:
                print("    %s" % rel)
            if len(listing) > 12:
                print("    ... and %d more" % (len(listing) - 12))
        print("  Re-derive: %s <dump-dir>, then --emit." % FIXTURE_SCRIPT)
        if args.strict:
            print("\n--strict: a revalidation debt is a failure in this mode.")
            return 1
        return 0

    print("\nFRESH: the record's per-body answer covers this tree byte-for-byte.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
