#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Compare every chain fixture against a LIVE trustc dump. **The check nothing did.**

THE HOLE THIS FILLS, stated as it was found (2026-08-19).

Each of the ten complete five-link chains pins its body's emitted trust-ir
VERBATIM in `crates/clean-verify/tests/fixtures/<chain>.trust-ir.txt`, and link
2a (`crystal_a1_lineage`) asserts that the registered spec module encodes the
same control-flow graph.  The gate reads the FIXTURE.  It has never read a dump.
So if the producer stopped emitting what the fixture records, every one of those
gates would keep passing --- comparing the spec to a file, while the shipped
kernel was built from something else.

Nothing else closed it either.  The only trustc-invoking scripts in this repo are
`trust_ir_build.sh` (whole-crate axis ratchet; touches no fixture) and
`trust_verify_ratchet.sh` (a different mechanism).  The perturbation batteries
and `crystal_lane_matrix_battery.sh` MUTATE the fixtures to prove the lanes
discriminate, but never re-derive them.  `verify_runner` has no trustc row.
`crystal_a1_lineage.rs`'s own module doc already said the lineage digest is
RECORDED and not recomputed; the emitted IR TEXT had no such statement anywhere.

This script is that comparison, and it is deliberately NOT a unit test: deriving
the answer needs the Trust compiler, which the Rust suite does not run.  It is a
re-measurement duty with a command.

WHAT IT DECIDES, AND WHAT IT REFUSES TO DECIDE

Every line that differs is classified, and only one class is RED:

  STRUCTURAL         an instruction, block, operand or count changed.  The body
                     the spec module describes is not the body being shipped.
                     RED, always.

  functy-index       the `functy.N` in the function header.  A whole-crate
                     function-TYPE table index.
                     NO LONGER UNREAD, as of 2026-08-20, and for the same reason
                     `callee-index` stopped being unread: the gap WAS the defect.
                     `FuncTy` is `{ params, returns, is_vararg }`, and a printed
                     body shows its parameter types in the entry block header,
                     its return types only through a `ret` an execution reaches,
                     and `is_vararg` nowhere at all --- so two texts differing
                     only in this numeral are a variadic and a non-variadic
                     function, and `ir_mint::project` accepted both.  It is now
                     pinned in `generated/ir_<chain>.tags.json`'s
                     `interface.functy` and compared.
                     It stays AMBER here because the index still MOVES with the
                     whole-crate table --- measured over the three producer
                     dumps, 9 of the 11 chained bodies moved theirs, the same
                     drift rate as `@func.N` --- and a move is a reviewed re-pin
                     of that table, which is what the M10 lane reports.  Both
                     designated chains are in the 2 that did NOT move
                     (`has_cubical_layer` and `level_is_zero` are `[0, 0, 0]`).
                     What is no longer true of it is `read by NO gate lane`.
  type-table-index   `enum.N` / `struct.N` / `tuple.N` / `array.N`.  Read by the
                     `const_tys` lane when it sits on a `const`, and by nothing
                     when it sits on a `load` or an entry parameter.
  callee-index       `@func.N` in a `call`.  Only `level_is_zero` has one, and
                     its link 2a is measured-OPEN.
                     NO LONGER UNREAD, as of 2026-08-20.  This class was AMBER
                     partly because no gate lane consulted it, and that gap was
                     itself the defect: the core form interned callee ids in a
                     namespace SEPARATE from the function's own id, both
                     starting at 0, so one numeral denoted two functions and
                     swapping the two `@func.N` literals in this very fixture
                     produced a byte-identical core module for a different
                     program.  `crystal_a2_mint`'s M8 lane now reads the index
                     --- against `generated/ir_lz.tags.json`'s `funcs` lane,
                     which pins both the crate id and the NAME reader A read for
                     it, and against reader A's `crate_func_ids_seen` record.
                     It stays AMBER here because the index still MOVES with the
                     whole-crate table (measured: 4914/4925 -> 3884/3895 across
                     the three producer dumps) while the names do not; a move is
                     a reviewed re-pin of that table, which is what M8 reports.
                     What is no longer true of it is `read by NO gate lane`.
  global-index       `@global.N` in a `global_addr`.  The exact analogue of
                     `callee-index`, and found the same way it was: on 2026-08-19,
                     the FIRST run that ever compared `level_is_zero_deref_callee`
                     to a dump.  That body is intact --- six instructions, same
                     opcodes, same operands, and the `const u64 34` that carries
                     the addressed string's LENGTH byte-identical --- while three
                     whole-crate tables moved under it (`functy` 53->45, `@func`
                     8369->7170 and 7675->6477, `@global` 4527->4524).
                     LIMITATION, stated rather than left to be found: like
                     `@func.N`, a `@global.N` is an INDEX and the module text
                     carries no declaration under that name (globals print as
                     `@__trust_promoted_N`), so this comparison does not re-derive
                     WHICH global is addressed.  What it does establish is that
                     the instruction, its operand shape and the accompanying
                     length constant are unchanged, and that no gate lane reads
                     the index.  It is AMBER for exactly that reason and for no
                     stronger one --- and unlike `callee-index`, which acquired
                     a gate lane on 2026-08-20, this one still has none.  It is
                     row `global-index` of `data/crystal_mint_blind_slots.json`,
                     which is where the finite list of such slots now lives.
  loc-file-index     the `; #loc:` file index.  Excluded from
                     `Module::stable_digest`; the CFG parser strips it.

The three index classes are WHOLE-CRATE NUMBERING.  They renumber whenever
clean-kernel gains or loses an item, and also whenever the producer changes how
many bodies it lowers --- so they go stale by construction and say nothing about
whether a proof still describes the artifact.  They are reported as AMBER, with
the fixture and the live value printed, and they do not fail the run unless
`--strict` is passed.  One LINE can carry several classes at once -- a `const
enum.N { k }` line also carries the `; #loc:` comment -- so classification
COMPOSES the normalisers and a line is STRUCTURAL only if the fully
index-normalised texts still differ (see `classify()`; this was a measured
defect until 2026-08-20).

That split is a measurement, not an opinion.  `ir_const_agg_eval` consults an
aggregate type only through `ir_ty_is_agg`, and `ir_ty_is_agg_enum_any` /
`ir_ty_is_agg_struct_any` (`spec/core_spec/eval_ir_ops.rs`) PROVE
`ir_ty_is_agg (IRTy.enum_ n) = true` for every `n` --- so the index cannot reach
the value the machine computes.

IT ALSO RE-DERIVES THE PER-BUILD PINS, because a fixture whose IR text still
matches can still be describing a different build: `lineage`, `def_index`,
`func_id`, `instr_count`, the derived-MIR verdict, `markers_exact`,
`unsupported`, the call counts, and whether a flip event fired and carries the
coverage row's lineage.

Usage:

    scripts/crystal_fixture_freshness.py <dump-dir> [--strict] [--json OUT]

It compares the ELEVEN chained bodies plus every fixture in `EXTRA_BODIES` --- a
fixture that is committed and asserted against but is not a chain.  A `*.trust-ir.txt`
in the fixtures directory that appears in NEITHER table is a fixture nothing checks;
`crystal_a1_lineage/freshness.rs` fails closed on exactly that.

It ALSO compares every MODULE-TABLE fixture in `EXTRA_ROWS` (suffix
`.trust-ir-rows.txt`): rows of the emitted module that are not a function body
--- a `global ... @<name> ...` line and the `type ty.N = ...` alias its element
type names.  Those rows have no coverage body, so they get ONLY the text verdict
(IDENTICAL / NUMBERING-ONLY / STRUCTURAL) and are written under the report's
`rows` key --- an addition to schema v1, never a change to `bodies`, whose set
`crystal_fixture_rebaseline.py` and `crystal_chain_revalidation.py` both pin.
`crystal_a1_lineage/freshness_closure.rs` closes the rows suffix over that table.

`<dump-dir>` is a `TRUST_IR_BUILD_DUMP` directory --- it must contain
`clean_kernel.trust-ir.txt` and `clean_kernel.coverage.json`, and
`clean_kernel.build.log` if flip events are to be checked.  Produce one with:

    TRUST_IR_BUILD_DUMP=<dir> TRUSTC=<sealed tc> scripts/trust_ir_build.sh --print-only

SEAL THE DRIVER FIRST.  macOS resolves `DYLD_LIBRARY_PATH` by dylib LEAF NAME
even for absolute load commands, so an unsealed snapshot silently becomes
whatever the newest build is.  `trust/scripts/seal_driver.sh seal|guard|selftest`.

Exit codes: 0 fresh (or amber without --strict), 1 STRUCTURAL drift or a missing
body, 2 the dump is unusable.
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
FIXTURES = REPO / "crates" / "clean-verify" / "tests" / "fixtures"

# fixture stem -> the def_path the coverage row carries.  `level_is_zero` is the
# designated target rather than a chain; it is checked here too, because its
# fixture is pinned the same way and its gate hard-codes a callee index.
BODIES: dict[str, str] = {
    "has_cubical_layer": "mode::CleanMode::has_cubical_layer",
    "level_kind_ord": "level::Level::kind_ord",
    "from_source_system": "mode::CleanMode::from_source_system",
    "flat_flags_contains": "flat::types::FlatFlags::contains",
    "bvar_in_range": "expr::bvar_in_range",
    "is_valid_char": "env::native_reducers_char::is_valid_char",
    "expr_path_step_clone": "<tc::expr_location::ExprPathStep as std::clone::Clone>::clone",
    "float_div": "env::native_reducers_float::reduce_float_div::{closure#0}",
    "get_char_val_trunc": "env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}",
    "meta_tag_shl": "tc::local_context::LocalContext::push_low_local::META_TAG",
    "level_is_zero": "level::Level::is_zero",
    # The 2026-08-20 float tranche — post-record pins (see freshness.rs's
    # POST_RECORD_PINS): pinned against local stage1 trustc 10130575c, owed an
    # entry in the NEXT revalidation record.
    "float_add": "env::native_reducers_float::reduce_float_add::{closure#0}",
    "float_sub": "env::native_reducers_float::reduce_float_sub::{closure#0}",
    "float_mul": "env::native_reducers_float::reduce_float_mul::{closure#0}",
    # Chains 15-17, the 2026-08-20 second tranche (same dump cohort, same
    # reproduction trio as the floats).
    "strict_monads": "env::Environment::set_lean4_core_strict_monads",
    "flat_flags_with": "flat::types::FlatFlags::with",
    "node_id_index": "cert::builder::state::NodeId::index",
    # Chain 18, 2026-08-21 — the FIRST call-bearing chain, pinned from the
    # c4e667ca51 producer era (the prior 19 fixtures stay at their own eras;
    # NUMBERING-ONLY against this producer, verified).
    "has_loose_bvars": "expr::meta::ExprMeta::has_loose_bvars",
    # The ELEVENTH chain, 2026-08-20 -- the first chained body that computes an
    # address and dereferences it.  Its fixture was taken from a live dump on
    # the day it was committed, and it enters this table so the NEXT lane
    # re-derives it like every other.
    "simp_priority_value": "env::types::SimpPriority::value",
}

# Fixtures that are NOT chains but whose emitted text is committed and asserted
# against anyway.  `level_is_zero_deref_callee` is read verbatim by
# `crystal_a1_lineage/level_is_zero.rs:76` -- it is the callee whose own
# `unsupported` verdict is the recorded reason `is_zero` cannot be transcribed --
# and until 2026-08-19 nothing compared it to a dump.  That is the same hole this
# script exists to close, one level down from where it was looking.
#
# They are a SEPARATE table because `crystal_a1_lineage/freshness.rs` asserts
# `BODIES == the chained set` and that assertion must keep its exact meaning; a
# second test there asserts that every committed `*.trust-ir.txt` appears in one
# table or the other, so a thirteenth fixture cannot arrive uncompared.
EXTRA_BODIES: dict[str, str] = {
    "level_is_zero_deref_callee": "<level::LevelArc as std::ops::Deref>::deref",
    # Chain 18's SUPPORTING callee: its emitted IR is transcribed into the
    # two-function reflected module and gated by has_loose_bvars.rs, so it must
    # be compared against live dumps like every other committed fixture.
    "loose_bvar_range_callee": "expr::meta::ExprMeta::loose_bvar_range",
}

# MODULE-TABLE fixtures: fixture stem -> the stem of the BODY fixture that
# reaches the row through `global_addr` (a key of EXTRA_BODIES / BODIES).
# These are rows of the module that are not function bodies.
# `level_is_zero_deref_globals` is the promoted string constant the deref
# body's panic path reaches through `global_addr` -- the `type ty.N = u8`
# alias line and the `global internal @__trust_promoted_N [ty.N x 34] =
# array[...]` line, both copied verbatim from the dump (2026-09-09,
# dump-control, rev18 producer).
#
# The value is a BODY STEM and not the global's name on purpose.
# `@__trust_promoted_N` is a per-BUILD number: at the 2026-09-09 HEAD dump the
# deref body's string had moved 4557 -> 4567 and `@__trust_promoted_4557` was a
# DIFFERENT 17-byte global, so a table that pinned the number was red on the
# CONTROL (a "STRUCTURAL" verdict for a whole-crate renumbering, which is the
# exact 2026-08-20 failure `classify`'s docstring records).  The rows loop
# therefore DERIVES the live name: it finds the referencing body by its
# signature, reads the one `global_addr @global.N` it carries, and compares the
# fixture against `@__trust_promoted_N` -- so a renumbered name is
# NUMBERING-ONLY (`global-index`) and only changed BYTES are STRUCTURAL.
#
# A THIRD table, not a widening of EXTRA_BODIES, for three measured reasons:
# a global has no `clean_kernel.coverage.json` body row, so the bodies loop's
# `rows.get(def_path)` half would be red by construction; its first line is not
# a `rustcc fn` header, so `signature_of` would SystemExit on it; and
# `crystal_fixture_rebaseline.py::validate_body_set` and
# `crystal_chain_revalidation.py` both refuse a report whose `bodies` set is
# not exactly BODIES | EXTRA_BODIES.  So these rows are compared by their own
# loop below, which runs ONLY the text verdict and writes report["rows"].
#
# The fixture suffix is `.trust-ir-rows.txt`, NOT `.trust-ir.txt`: that keeps
# it out of `check_crystal_fixture_pins.py`'s glob and out of the 21-row
# rebaseline record that gate reads, and `crystal_a1_lineage/freshness_closure.rs`
# closes the rows suffix over THIS table the way it closes bodies over the two
# tables above -- a `*.trust-ir-rows.txt` that appears here in no row fails
# that test (it reads the KEYS only; the value is this script's business).
EXTRA_ROWS: dict[str, str] = {
    "level_is_zero_deref_globals": "level_is_zero_deref_callee",
}
ROWS_SUFFIX = ".trust-ir-rows.txt"

# The emitted signature each body is found by in the dump text.  Derived from the
# fixture's own first line rather than hard-coded, so a rename fails loudly.
LINEAGE_FIXTURE = {"level_is_zero": "level_is_zero.a0.json"}

AMBER_CLASSES = (
    "functy-index",
    "type-table-index",
    "callee-index",
    "global-index",
    "loc-file-index",
)


def _norm_functy(s: str) -> str:
    return re.sub(r"functy\.\d+", "functy.X", s)


def _norm_tytable(s: str) -> str:
    # `ty.N` is the module's type-ALIAS table (`type ty.N = ...`, and the
    # `[ty.N x LEN]` element type of a global row); it renumbers with the
    # crate exactly as the aggregate tables do.  No function-body fixture
    # carries a `ty.N` token (measured 2026-09-09 over every *.trust-ir.txt),
    # so widening the class here changes no body verdict.
    return re.sub(r"\b(enum|struct|tuple|array|ty)\.\d+", r"\1.X", s)


def _norm_callee(s: str) -> str:
    return re.sub(r"@func\.\d+", "@func.X", s)


def _norm_global(s: str) -> str:
    # Two spellings of a global index, kept DISTINCT under normalisation: a
    # numbered `@global.N` reference and a promoted constant's
    # `@__trust_promoted_N` name (note the underscore before the digits --
    # `@__trust_promoted_4557` in the dump).  A row that moves from one
    # spelling to the other is a real change, not renumbering.
    s = re.sub(r"@global\.\d+", "@global.X", s)
    return re.sub(r"@__trust_promoted_\d+", "@__trust_promoted_X", s)


def _strip_loc(s: str) -> str:
    return s.split("; #")[0].rstrip()


def classify(old: str, new: str) -> tuple[str, ...]:
    """Name the drift classes of one changed line, or ("STRUCTURAL",) if real.

    COMPOSITIONAL, and it was not (fixed 2026-08-20).  The first shape of this
    function tried each normaliser ALONE, so a line carrying TWO index classes
    at once -- `const enum.181 { 0 }  ; #loc: 425` going to
    `const enum.174 { 0 }  ; #loc: 422` -- matched no single normaliser and
    fell through to STRUCTURAL.  At the 2026-08-20 producer that is not a
    corner case, it is the CONTROL: an unchanged clean main read STRUCTURAL on
    four bodies (expr_path_step_clone enum+loc, level_is_zero callee+loc,
    simp_priority_value enum+loc, level_is_zero_deref_callee func/global+loc),
    so a clean revalidation record could not be minted on an UNCHANGED tree.
    Fail-loud, so safe -- but a gate that is red on the control cannot say
    anything about a subject.

    Now every applicable normaliser is applied to BOTH lines and the verdict is
    taken on the composition; a line is STRUCTURAL exactly when the fully
    index-normalised texts still differ.  The returned classes are the
    normalisers that were NEEDED -- those whose omission from the composition
    leaves the lines unequal -- so a single-class line reports exactly what it
    always did, and a composed line reports each class it carries.  The caller
    ledgers the line under every class it returns; the five class names are
    pinned by `crystal_a1_lineage/freshness.rs`, which is why this returns
    plural known names rather than minting a composite name.
    """
    norms: list[tuple[str, object]] = []
    if old.startswith("rustcc fn @") and new.startswith("rustcc fn @"):
        norms.append(("functy-index", _norm_functy))
    norms.extend(
        [
            ("type-table-index", _norm_tytable),
            ("callee-index", _norm_callee),
            ("global-index", _norm_global),
            ("loc-file-index", _strip_loc),
        ]
    )

    def compose(line: str, skip: str | None = None) -> str:
        for name, fn in norms:
            if name != skip:
                line = fn(line)  # type: ignore[operator]
        return line

    if compose(old) != compose(new):
        return ("STRUCTURAL",)
    needed = tuple(
        name for name, _fn in norms if compose(old, skip=name) != compose(new, skip=name)
    )
    if needed:
        return needed
    # Degenerate guard: old != new yet no single omission breaks equality.
    # Possible only if two normalisers' patterns overlap on the same span (e.g.
    # a differing token inside the `; #`-stripped region that another regex
    # also rewrites).  Refuse to return an empty class set -- name every
    # normaliser that touches either line, and if none does, the difference is
    # real and unclassified: STRUCTURAL.
    touched = tuple(name for name, fn in norms if fn(old) != old or fn(new) != new)  # type: ignore[operator]
    return touched or ("STRUCTURAL",)


def selftest_classifier() -> None:
    """Fail closed if composed renumbering or a real edit is misclassified."""
    cases = [
        (
            "%2 = load enum.181, ptr %0  ; #loc: 425 20 16",
            "%2 = load enum.182, ptr %0  ; #loc: 426 28 16",
            ("type-table-index", "loc-file-index"),
        ),
        (
            "%12 = call @func.4914(%9)  ; #loc: 389 528 34",
            "%12 = call @func.3890(%9)  ; #loc: 390 548 34",
            ("callee-index", "loc-file-index"),
        ),
        (
            "%2 = global_addr @global.4527  ; #loc: 389 61 20",
            "%2 = global_addr @global.4556  ; #loc: 390 61 20",
            ("global-index", "loc-file-index"),
        ),
        (
            "%3 = extractfield u8 %2, 0  ; #loc: 425 20 16",
            "%3 = extractfield u8 %2, 0  ; #loc: 426 28 16",
            ("loc-file-index",),
        ),
        # A changed payload or argument remains structural even alongside an
        # otherwise admissible table/location renumbering.
        (
            "%4 = const enum.181 { 0 }  ; #loc: 425 20 16",
            "%4 = const enum.182 { 1 }  ; #loc: 426 28 16",
            ("STRUCTURAL",),
        ),
        (
            "%12 = call @func.4914(%9)  ; #loc: 389 528 34",
            "%12 = call @func.3890(%10)  ; #loc: 390 548 34",
            ("STRUCTURAL",),
        ),
        # Module-table rows (EXTRA_ROWS): a promoted constant's name and the
        # `ty.N` alias of its element type are both whole-crate numbering, and
        # the classes compose in normaliser order.
        (
            "global internal @__trust_promoted_4557 [ty.0 x 34] = array[ 108, 105 ]",
            "global internal @__trust_promoted_4601 [ty.2 x 34] = array[ 108, 105 ]",
            ("type-table-index", "global-index"),
        ),
        (
            "type ty.0 = u8",
            "type ty.2 = u8",
            ("type-table-index",),
        ),
        # The element count or a payload byte is the row's CONTENT.
        (
            "global internal @__trust_promoted_4557 [ty.0 x 34] = array[ 108, 105 ]",
            "global internal @__trust_promoted_4601 [ty.0 x 35] = array[ 108, 105 ]",
            ("STRUCTURAL",),
        ),
        # A promoted name is not a numbered global: the spelling is kept.
        (
            "%2 = global_addr @global.4557  ; #loc: 389 61 20",
            "%2 = global_addr @__trust_promoted_4557  ; #loc: 389 61 20",
            ("STRUCTURAL",),
        ),
    ]
    for old, new, expected in cases:
        got = classify(old, new)
        if got != expected:
            raise RuntimeError(
                f"classifier selftest failed: expected {expected}, got {got}: "
                f"{old!r} -> {new!r}"
            )


def signature_of(fixture_text: str) -> str:
    """`rustcc fn @NAME(functy.N) {` -> `rustcc fn @NAME(`."""
    head = fixture_text.splitlines()[0]
    cut = head.rfind("(functy.")
    if cut < 0:
        raise SystemExit("fixture head is not a rustcc fn header: %r" % head)
    return head[: cut + 1]


def extract(dump_text: str, sig: str) -> list[str]:
    """Every body in the dump whose header starts with `sig`."""
    out: list[str] = []
    buf: list[str] | None = None
    for line in dump_text.splitlines(keepends=True):
        if line.startswith("rustcc fn "):
            buf = [line] if line.startswith(sig) else None
            continue
        if buf is not None:
            buf.append(line)
            if line.rstrip("\n") == "}":
                out.append("".join(buf))
                buf = None
    return out


def extract_rows(dump_text: str, name: str) -> list[str]:
    """Every module-table global row `global ... @<name> ...` in the dump.

    Each hit is returned as text in FIXTURE order: the `type ty.N = ...` alias
    line that the row's `[ty.N x LEN]` element type names FIRST, then the
    global line itself, each newline-terminated.  The dump prints its type
    table before its globals and the fixture is a verbatim copy of both lines,
    so this order is byte-identical to the fixture's.  A hit whose alias line
    is absent or ambiguous is returned as the global line alone, which the
    caller then reads as a line-count STRUCTURAL drift rather than as a match.
    """
    lines = dump_text.splitlines()
    aliases: dict[str, list[str]] = {}
    for line in lines:
        m = re.match(r"type (ty\.\d+) = ", line)
        if m:
            aliases.setdefault(m.group(1), []).append(line)
    pat = re.compile(r"\s@" + re.escape(name) + r"(?=\s|$)")
    out: list[str] = []
    for line in lines:
        if not line.startswith("global ") or not pat.search(line):
            continue
        m = re.search(r"\[(ty\.\d+) x \d+\]", line)
        alias = aliases.get(m.group(1), []) if m else []
        parts = ([alias[0]] if len(alias) == 1 else []) + [line]
        out.append("".join(f"{p}\n" for p in parts))
    return out


def drift_classes(fx: str, live: str) -> dict[str, list[str]]:
    """Line-by-line drift ledger of a fixture against its live text.

    A line-count change is STRUCTURAL outright; otherwise every differing line
    is ledgered under each class `classify` returns for it.  Shared by the
    bodies loop and the module-table rows loop so both hand out the same
    IDENTICAL / NUMBERING-ONLY / STRUCTURAL verdict.
    """
    fl, ll = fx.splitlines(), live.splitlines()
    classes: dict[str, list[str]] = {}
    if len(fl) != len(ll):
        classes["STRUCTURAL"] = [f"line count {len(fl)} -> {len(ll)}"]
        return classes
    for a, b in zip(fl, ll):
        if a != b:
            for cls in classify(a, b):
                classes.setdefault(cls, []).append(f"{a.strip()}  ->  {b.strip()}")
    return classes


_GLOBAL_REF = re.compile(r"global_addr @global\.(\d+)")
_PROMOTED_NAME = re.compile(r"@(__trust_promoted_\d+)(?=\s|$)")


def promoted_global_refs(body_text: str) -> list[str]:
    """The `@global.N` indices a body reaches through `global_addr`, in order."""
    return _GLOBAL_REF.findall(body_text)


def compare_rows_fixture(
    dump_text: str, stem: str, body_stem: str, fx: str, body_fixture_text: str
) -> tuple[dict[str, object], list[str], list[str]]:
    """The module-table verdict for ONE `EXTRA_ROWS` fixture.

    Returns `(entry, red, amber)`.  The row's identity anchor is DERIVED from
    the live dump, never read off the fixture: the referencing body is found by
    its signature, the single `global_addr @global.N` it carries names the live
    row, and the fixture is compared against `@__trust_promoted_N`.  Every way
    that derivation can fail is its OWN verdict (`NO REFERENCING BODY`,
    `AMBIGUOUS REFERENCING BODY`, `NO GLOBAL REFERENCE`, `AMBIGUOUS GLOBAL
    REFERENCE`, `ABSENT FROM DUMP`, `AMBIGUOUS IN DUMP`) -- red, but named as a
    lookup failure so it can never be mistaken for the STRUCTURAL verdict,
    which is reserved for a genuine content change in a row that WAS found.
    `entry["global"]` is the live name compared against; `entry["fixture_global"]`
    is the name the fixture pins, so the JSON says which row was compared.
    """
    red: list[str] = []
    amber: list[str] = []
    pinned = _PROMOTED_NAME.findall(fx)
    entry: dict[str, object] = {
        "referencing_body": body_stem,
        "fixture_global": pinned[0] if len(pinned) == 1 else None,
        "global": None,
        "at_head": None,
        "at_head_reason": "module-table row, no coverage body",
    }
    if len(pinned) != 1:
        entry["verdict"] = "MALFORMED FIXTURE"
        red.append(f"{stem}: the fixture names {len(pinned)} promoted globals, expected 1")
        return entry, red, amber
    live_bodies = extract(dump_text, signature_of(body_fixture_text))
    if len(live_bodies) != 1:
        entry["verdict"] = (
            "NO REFERENCING BODY" if not live_bodies else "AMBIGUOUS REFERENCING BODY"
        )
        red.append(
            f"{stem}: {entry['verdict']} -- the dump carries {len(live_bodies)} bodies with "
            f"the signature of {body_stem}, expected 1; the row cannot be located"
        )
        return entry, red, amber
    refs = promoted_global_refs(live_bodies[0])
    if len(refs) != 1:
        entry["verdict"] = "NO GLOBAL REFERENCE" if not refs else "AMBIGUOUS GLOBAL REFERENCE"
        red.append(
            f"{stem}: {entry['verdict']} -- the live {body_stem} body carries {len(refs)} "
            f"`global_addr @global.N` instructions, expected 1; the row cannot be located"
        )
        return entry, red, amber
    gname = f"__trust_promoted_{refs[0]}"
    entry["global"] = gname
    found = extract_rows(dump_text, gname)
    if len(found) != 1:
        entry["verdict"] = "ABSENT FROM DUMP" if not found else "AMBIGUOUS IN DUMP"
        red.append(
            f"{stem}: {entry['verdict']} -- the dump carries {len(found)} global rows named "
            f"@{gname} (derived from the live {body_stem} body), expected 1"
        )
        return entry, red, amber
    live = found[0]
    if fx == live:
        entry["verdict"] = "IDENTICAL"
        entry["classes"] = []
        return entry, red, amber
    classes = drift_classes(fx, live)
    entry["classes"] = sorted(classes)
    entry["detail"] = classes
    entry["diff"] = "".join(
        difflib.unified_diff(
            fx.splitlines(keepends=True),
            live.splitlines(keepends=True),
            fromfile=f"fixture {stem}{ROWS_SUFFIX}",
            tofile="live dump",
        )
    )
    if "STRUCTURAL" in classes:
        entry["verdict"] = "STRUCTURAL"
        red.append(
            f"{stem}: STRUCTURAL drift (row @{gname}) -- " + "; ".join(classes["STRUCTURAL"][:3])
        )
    else:
        entry["verdict"] = "NUMBERING-ONLY"
        amber.append(f"{stem}: {', '.join(sorted(classes))} (row @{gname})")
    return entry, red, amber


def selftest_rows_loop() -> None:
    """END-TO-END selftest of the module-table rows lane, run on every invocation.

    Not a `classify` pair: this drives `compare_rows_fixture` over a synthetic
    dump snippet, so the verdicts the loop can actually hand out are the ones
    pinned.  The row whose fixture-pinned number is also a DIFFERENT live
    global (the 2026-09-09 HEAD shape) must read NUMBERING-ONLY, because the
    name is derived from the referencing body and not looked up by number.
    """
    body_fx = (
        "rustcc fn @<level::LevelArc as std::ops::Deref>::deref(functy.45) {\n"
        "  bb0:\n"
        "    %2 = global_addr @global.4557  ; #loc: 391 61 20\n"
        "}\n"
    )
    rows_fx = (
        "type ty.0 = u8\n"
        "global internal @__trust_promoted_4557 [ty.0 x 3] = array[ 1, 2, 3 ]\n"
    )

    def dump(ty: str, n: str, payload: str, *, body: bool = True, decoy: bool = False) -> str:
        text = f"type {ty} = u8\ntype ty.9 = u16\n"
        if decoy:
            # The fixture's OLD number is now a different global entirely.
            text += "global internal @__trust_promoted_4557 [ty.9 x 2] = array[ 7, 7 ]\n"
        text += f"global internal @__trust_promoted_{n} [{ty} x 3] = array[ {payload} ]\n"
        if body:
            text += "rustcc fn @<other::Thing>::f(functy.1) {\n  bb0:\n    ret\n}\n"
            text += body_fx.replace("@global.4557", f"@global.{n}")
        return text

    cases: list[tuple[str, str, str, list[str], str]] = [
        # (label, dump, expected verdict, expected classes, expected colour)
        ("control", dump("ty.0", "4557", "1, 2, 3"), "IDENTICAL", [], "green"),
        (
            "renumbered",
            dump("ty.2", "4601", "1, 2, 3", decoy=True),
            "NUMBERING-ONLY",
            ["global-index", "type-table-index"],
            "amber",
        ),
        (
            "bytes changed",
            dump("ty.2", "4601", "1, 2, 4", decoy=True),
            "STRUCTURAL",
            ["STRUCTURAL", "type-table-index"],
            "red",
        ),
        ("no body", dump("ty.0", "4557", "1, 2, 3", body=False), "NO REFERENCING BODY", [], "red"),
        (
            "absent row",
            dump("ty.0", "4557", "1, 2, 3").replace("@__trust_promoted_4557 [", "@__trust_promoted_4558 ["),
            "ABSENT FROM DUMP",
            [],
            "red",
        ),
    ]
    for label, text, verdict, classes, colour in cases:
        entry, red, amber = compare_rows_fixture(
            text, "rows_selftest", "rows_selftest_callee", rows_fx, body_fx
        )
        got = (entry.get("verdict"), list(entry.get("classes") or []))
        want = (verdict, classes)
        if got != want:
            raise RuntimeError(f"rows-lane selftest {label!r}: expected {want}, got {got}")
        got_colour = "red" if red else ("amber" if amber else "green")
        if got_colour != colour:
            raise RuntimeError(
                f"rows-lane selftest {label!r}: expected {colour}, got {got_colour} "
                f"(red={red!r}, amber={amber!r})"
            )
        if colour == "red" and verdict != "STRUCTURAL" and any("STRUCTURAL" in r for r in red):
            raise RuntimeError(f"rows-lane selftest {label!r}: a lookup failure was labelled STRUCTURAL")
    # The derived name, not the fixture's number, is what the JSON reports.
    entry, _r, _a = compare_rows_fixture(
        dump("ty.2", "4601", "1, 2, 3", decoy=True), "s", "c", rows_fx, body_fx
    )
    if (entry["global"], entry["fixture_global"]) != ("__trust_promoted_4601", "__trust_promoted_4557"):
        raise RuntimeError(f"rows-lane selftest: derived/pinned names wrong: {entry!r}")


def dump_provenance(path: Path) -> str:
    """Return a stable directory label, never a machine-local path.

    Preserve the spelling of an ordinary final component (including a symlink
    name).  `.` has no final component in `pathlib`, so use the absolute
    directory's basename for that one relative spelling.  A filesystem root
    has no basename even after absolutizing and therefore receives an explicit
    sentinel instead of leaking `/`, a drive root, or another host-specific
    absolute spelling into a committed report.
    """
    return path.name or path.absolute().name or "filesystem-root"


def selftest_dump_provenance() -> None:
    assert dump_provenance(Path("/private/tmp/agent-session/irdumpB")) == "irdumpB"
    assert dump_provenance(Path("relative/dump_O3")) == "dump_O3"
    root = Path(Path.cwd().anchor)
    assert dump_provenance(root) == "filesystem-root"
    for label in (
        dump_provenance(Path("/private/tmp/agent-session/irdumpB")),
        dump_provenance(root),
    ):
        assert not Path(label).is_absolute(), label


def main() -> int:
    selftest_classifier()
    selftest_rows_loop()
    selftest_dump_provenance()
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("dump", type=Path, help="a TRUST_IR_BUILD_DUMP directory")
    ap.add_argument(
        "--strict",
        action="store_true",
        help="fail on whole-crate NUMBERING drift too, not only on STRUCTURAL drift",
    )
    ap.add_argument("--json", type=Path, default=None, help="also write the full report here")
    args = ap.parse_args()

    ir = args.dump / "clean_kernel.trust-ir.txt"
    cov = args.dump / "clean_kernel.coverage.json"
    log = args.dump / "clean_kernel.build.log"
    for p in (ir, cov):
        if not p.is_file():
            print("FRESHNESS UNUSABLE: %s is missing." % p, file=sys.stderr)
            print("  A dump directory needs clean_kernel.trust-ir.txt and", file=sys.stderr)
            print("  clean_kernel.coverage.json. See this file's header.", file=sys.stderr)
            return 2

    dump_text = ir.read_text(encoding="utf-8", errors="replace")
    rows = {
        b.get("def_path"): b
        for b in json.loads(cov.read_text(encoding="utf-8"))["bodies"]
    }
    flips: dict[int, str] = {}
    if log.is_file():
        for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
            if "trust-ir-flip:" in line and "compiled from trust-ir" in line:
                m = re.search(r"did=DefId\(0:(\d+)", line)
                if m:
                    flips[int(m.group(1))] = line.strip()

    report: dict[str, object] = {
        "schema": "clean.crystal.fixture_freshness/v1",
        # The dump directory's NAME, never its absolute path. A per-session
        # scratch path under someone's home or temp directory tells a reader
        # nothing they can reproduce — that directory exists on exactly one
        # machine, for one session — and it is precisely the agent-session and
        # personal-path residue the publication boundary refuses outright,
        # which is how a committed one blocked a release. Nothing reads this
        # field; it is provenance for a human, so record what identifies the
        # dump rather than where it briefly sat.
        "dump": dump_provenance(args.dump),
        "bodies": {},
    }
    red: list[str] = []
    amber: list[str] = []

    for stem, def_path in {**BODIES, **EXTRA_BODIES}.items():
        fx_path = FIXTURES / f"{stem}.trust-ir.txt"
        entry: dict[str, object] = {"def_path": def_path}
        report["bodies"][stem] = entry  # type: ignore[index]

        if not fx_path.is_file():
            red.append(f"{stem}: fixture {fx_path} is missing")
            entry["verdict"] = "MISSING FIXTURE"
            continue
        fx = fx_path.read_text(encoding="utf-8")
        found = extract(dump_text, signature_of(fx))
        if len(found) != 1:
            red.append(
                f"{stem}: the dump carries {len(found)} bodies with this signature, expected 1"
            )
            entry["verdict"] = "ABSENT FROM DUMP" if not found else "AMBIGUOUS IN DUMP"
            continue
        live = found[0]

        if fx == live:
            entry["verdict"] = "IDENTICAL"
            entry["classes"] = []
        else:
            classes = drift_classes(fx, live)
            entry["classes"] = sorted(classes)
            entry["detail"] = classes
            entry["diff"] = "".join(
                difflib.unified_diff(
                    fx.splitlines(keepends=True),
                    live.splitlines(keepends=True),
                    fromfile=f"fixture {stem}.trust-ir.txt",
                    tofile="live dump",
                )
            )
            if "STRUCTURAL" in classes:
                entry["verdict"] = "STRUCTURAL"
                red.append(
                    f"{stem}: STRUCTURAL drift — "
                    + "; ".join(classes["STRUCTURAL"][:3])
                )
            else:
                entry["verdict"] = "NUMBERING-ONLY"
                amber.append(f"{stem}: {', '.join(sorted(classes))}")

        row = rows.get(def_path)
        if row is None:
            red.append(f"{stem}: no coverage row for {def_path}")
            continue
        dm = (row.get("differentials") or {}).get("derived_mir") or {}
        idx = row.get("def_index")
        entry["at_head"] = {
            "lineage": row.get("lineage"),
            "def_index": idx,
            "func_id": row.get("func_id"),
            "instr_count": row.get("instr_count"),
            "lowered": row.get("lowered"),
            "spliced": row.get("spliced"),
            "unsupported": row.get("unsupported"),
            "calls": row.get("calls"),
            "derived_mir_verdict": dm.get("verdict"),
            "markers_exact": dm.get("markers_exact"),
            "flip_event": flips.get(idx),
        }
        lf = FIXTURES / LINEAGE_FIXTURE.get(stem, f"{stem}.lineage.json")
        if lf.is_file():
            evidence = json.loads(lf.read_text(encoding="utf-8"))
            # Historical top-level measurements remain queryable forever.  A
            # reviewed source-bound fixture rebaseline adds a complete current
            # pin instead of mixing new lineage fields into that old build
            # record.  Strict freshness compares against the current pin when
            # present and falls back to the historical schema for old records.
            pinned = evidence.get("current_source_bound_pin") or evidence
            entry["pinned"] = {
                "lineage": pinned.get("lineage"),
                "def_index": pinned.get("def_index"),
                "func_id": pinned.get("func_id"),
                "instr_count": pinned.get("instr_count"),
            }
            if pinned.get("instr_count") not in (None, row.get("instr_count")):
                red.append(
                    "%s: instr_count moved %s -> %s — that is not numbering, it is the body"
                    % (stem, pinned.get("instr_count"), row.get("instr_count"))
                )
            if pinned.get("lineage") and pinned["lineage"] != row.get("lineage"):
                amber.append(f"{stem}: lineage digest moved (per-BUILD identity, expected)")

    # MODULE-TABLE rows: text verdict only.  Never `signature_of` (no `rustcc
    # fn` header), never `rows.get` (no coverage body), never report["bodies"]
    # (its set is pinned by two other scripts).  `at_head` is recorded as null
    # with the reason, so a reader of the JSON sees an absence stated rather
    # than a field forgotten.
    report["rows"] = {}
    for stem, body_stem in EXTRA_ROWS.items():
        fx_path = FIXTURES / f"{stem}{ROWS_SUFFIX}"
        body_path = FIXTURES / f"{body_stem}.trust-ir.txt"
        if not fx_path.is_file():
            red.append(f"{stem}: fixture {fx_path} is missing")
            report["rows"][stem] = {  # type: ignore[index]
                "referencing_body": body_stem,
                "verdict": "MISSING FIXTURE",
                "at_head": None,
                "at_head_reason": "module-table row, no coverage body",
            }
            continue
        if (body_stem not in BODIES and body_stem not in EXTRA_BODIES) or not body_path.is_file():
            red.append(
                f"{stem}: NO REFERENCING BODY -- EXTRA_ROWS names {body_stem!r}, which is not a "
                f"committed body fixture ({body_path})"
            )
            report["rows"][stem] = {  # type: ignore[index]
                "referencing_body": body_stem,
                "verdict": "NO REFERENCING BODY",
                "at_head": None,
                "at_head_reason": "module-table row, no coverage body",
            }
            continue
        rentry, r_red, r_amber = compare_rows_fixture(
            dump_text,
            stem,
            body_stem,
            fx_path.read_text(encoding="utf-8"),
            body_path.read_text(encoding="utf-8"),
        )
        report["rows"][stem] = rentry  # type: ignore[index]
        red.extend(r_red)
        amber.extend(r_amber)

    print("== crystal chain fixture freshness ==")
    print("dump: %s" % args.dump)
    for stem, e in report["bodies"].items():  # type: ignore[union-attr]
        head = e.get("at_head") or {}
        print(
            "  %-22s %-16s %s"
            % (
                stem,
                e.get("verdict", "?"),
                ("classes=" + (",".join(e.get("classes") or []) or "-"))
                + "  instr=%s verdict=%s markers_exact=%s flip=%s"
                % (
                    head.get("instr_count"),
                    head.get("derived_mir_verdict"),
                    head.get("markers_exact"),
                    "yes" if head.get("flip_event") else "no",
                ),
            )
        )
    for stem, e in report["rows"].items():  # type: ignore[union-attr]
        print(
            "  %-22s %-16s %s"
            % (
                stem,
                e.get("verdict", "?"),
                ("classes=" + (",".join(e.get("classes") or []) or "-"))
                + "  module-table row (live @%s, fixture @%s, via %s; no coverage body)"
                % (e.get("global"), e.get("fixture_global"), e.get("referencing_body")),
            )
        )
    if args.json:
        args.json.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
        print("report: %s" % args.json)

    if amber:
        print("\nAMBER — whole-crate NUMBERING drift (no instruction moved):")
        for a in amber:
            print("  %s" % a)
        print(
            "  These indices renumber on any clean-kernel or producer change. They are NOT\n"
            "  read by the semantics: ir_ty_is_agg_enum_any / ir_ty_is_agg_struct_any prove\n"
            "  the type index cannot reach the machine's answer. Do not copy a live body over\n"
            "  the fixture: that can break a registered proof/tag binding. A reviewed strict\n"
            "  re-pin uses scripts/crystal_fixture_rebaseline.py, which requires every such\n"
            "  binding before it writes and preserves the old identity in an append-only ledger."
        )
    if red:
        print("\nRED:")
        for r in red:
            print("  %s" % r)
        structural = [r for r in red if "STRUCTURAL drift" in r or "instr_count moved" in r]
        if structural:
            print(
                "\nA STRUCTURAL drift means the spec module and its refinement theorem may no\n"
                "longer describe the emitted program. Re-DERIVE — do not re-record the fixture."
            )
        if len(structural) != len(red):
            print(
                "\nA lookup failure (MISSING / ABSENT FROM DUMP / AMBIGUOUS / NO REFERENCING BODY /\n"
                "no coverage row) means the fixture could not be COMPARED at all: it says nothing\n"
                "about whether an instruction moved. Check the dump is a complete clean-kernel\n"
                "dump from the producer this script's header names before reading it as drift."
            )
        return 1
    if amber and args.strict:
        print("\n--strict: numbering drift is a failure in this mode.")
        return 1
    print("\nFRESH: no chained body's instructions have moved.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
