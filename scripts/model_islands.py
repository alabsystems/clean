#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The self-verification MODEL as Clean islands, and the accounting that keeps it honest.

Embed memo `designs/2026-08-28-embedding-the-kernel-model.md`, owner ruling 5,
decided for IN-PLACE ISLANDS. `crates/clean-kernel/src/model_islands.rs` uses
Trust's OUT-OF-LINE island form, `#[path = "..."] clean mod <unit>;`, which loads
a `.clean` file from disk BYTE FOR BYTE at expansion time. The compiler parses it
with the real Clean parser and registers every declaration through `add_decl`, so
the CIC kernel type-checks the model during the Rust build and a rejected unit
fails that build. The unit files ARE the islands: nothing is copied or generated.

## The accounting, and why it is the whole point

The island registers into the compiler PRELUDE's environment; `clean-verify`
builds the model on an EMPTY one. Six of the model's declarations (43 at the
2026-09-15 --check: 37 registered, 6 agreed, 0 refused, 0 blocked -- read that line,
not this one) are names the prelude already owns and cannot be honestly re-declared:

  * an `inductive` re-declaration naming a SUBSET of the prelude's constructors
    is SILENTLY ACCEPTED -- it reports the name as registered while registering
    nothing that was written (measured on `Eq`, whose whole unit was a false
    green). Under trustc 0.11.0+g20565c325 (measured 2026-10-28) it is refused
    instead, as Lean refuses it, so a unit declaring one cannot be loaded at all;
    and
  * a `def` re-declaration is refused outright (OWNED_RE names both wordings).

So every model declaration must be in exactly one of three states, and `--verify`
refuses if any is in none of them:

  REGISTERED  the name is free; the island registers it, and the compiler's own
              note says so.
  AGREED      the prelude owns it; `crates/clean-verify/spec/foundation_agreement.clean`
              states the model's DEFINING EQUATIONS for it, each held by
              `Eq.refl` so the kernel decides it by computation.
  REFUSED     the island cannot elaborate it. The reason is recorded AND
              re-measured on every --verify, in the environment the module
              provides -- never in isolation, which is how three declarations
              came to be recorded refused while elaborating perfectly well.
  BLOCKED     it is free, but its unit also declares a prelude-owned name, so the
              unit cannot be embedded whole without that name being aliased.

The ownership split is PROBED against the live compiler on every run, never read
from a list, so a new collision cannot appear unnoticed.

  scripts/model_islands.py --check     # the module and the accounting agree
  scripts/model_islands.py --verify    # compile the islands with trustc
  scripts/model_islands.py --self-test
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MODEL_SPEC_DIR = os.path.join("crates", "clean-verify", "spec")
MODEL_CENSUS = os.path.join("data", "model_unit_declarations.json")
ISLAND_SPEC_DIR = os.path.join("crates", "clean-kernel", "spec")
ISLAND_MODULE = os.path.join("crates", "clean-kernel", "src", "model_islands.rs")
CFG = "clean_trust_islands"

# Units the island module loads, and the declarations each must register.
EMBEDDED = {
    "foundation_agreement": [
        "fa_nat_zero", "fa_nat_succ", "fa_nat_add_zero", "fa_nat_add_succ",
        "fa_nat_pred_zero", "fa_nat_pred_succ", "fa_nat_sub_zero", "fa_nat_sub_succ",
        "fa_nat_rec", "fa_eq_refl", "fa_eq_rec",
        "fa_bool_true", "fa_bool_false", "fa_bool_rec", "fa_empty_elim",
        "fa_nat_sort", "fa_bool_sort", "fa_empty_sort", "fa_eq_is_prop",
    ],
    "expr_model_core": [
        "Name", "Level", "ListType", "KExpr", "lift_bvar_at", "lift_at", "lift",
        "instantiate_bvar_geq", "instantiate_bvar_at", "instantiate_at", "instantiate",
    ],
    "expr_model_spine": ["kapp_fn", "kapp_arg_count", "is_const_app"],
    "foundation_order": ["Lt", "Le"],
    "foundation_prod": ["ProdType"],
}

# A prelude-owned declaration and the agreement witnesses that stand for it.
# Probed, not assumed: --verify refuses if the live ownership set stops matching
# these keys in either direction.
AGREEMENT_COVERS = {
    "Nat": ["fa_nat_zero", "fa_nat_succ", "fa_nat_rec", "fa_nat_sort"],
    "Nat.add": ["fa_nat_add_zero", "fa_nat_add_succ"],
    "Nat.pred": ["fa_nat_pred_zero", "fa_nat_pred_succ"],
    "Nat.sub": ["fa_nat_sub_zero", "fa_nat_sub_succ"],
    "Eq": ["fa_eq_refl", "fa_eq_rec", "fa_eq_is_prop"],
    "Empty": ["fa_empty_elim", "fa_empty_sort"],
}

# Names the model USES but never DECLARES, so they are supplied by whichever
# environment it is elaborated in. Measured: exactly these, reached through
# `is_const_app : KExpr -> Bool`. They are not in the declaration census (they are
# not the model's declarations), so they cannot be accounted by AGREEMENT_COVERS;
# they need witnesses for the same reason a prelude-owned declaration does.
# SCOPE, stated because the obvious reading is wrong: this set is the ambient
# interface of the MODEL over the SPEC's environment. The island environment is a
# strict superset (the whole compiler prelude), so a name the model resolves to a
# model declaration here may resolve to a prelude declaration there. What the
# witnesses establish is agreement on the six owned names and these ambient ones;
# they do not enumerate the island environment's own surface.
#
# The set is DERIVED FROM THE KERNEL, not listed here: data/model_unit_declarations.json
# carries it under `ambient`, computed by walking the elaborated type and value of
# every census declaration for constant references and subtracting everything the
# model brings in (its declarations plus the constructors and recursors the kernel
# generates from them). --check requires every recorded ambient name to appear
# below, so a NEW ambient dependency introduced by a future unit fails the gate
# instead of passing unnoticed. A text scan could not compute this: it cannot tell
# a binder from a constant.
AMBIENT_AGREED = {
    "Bool": ["fa_bool_rec", "fa_bool_sort"],
    "Bool.rec": ["fa_bool_rec"],
    "Bool.true": ["fa_bool_true"],
    "Bool.false": ["fa_bool_false"],
}

# Model declarations the island cannot elaborate, mapped to the unit that declares
# them and the measured reason, RE-MEASURED on every --verify by cmd_verify in the
# SAME environment the module provides -- never in isolation. EMPTY as of
# 2026-09-13: the three that sat here (kapp_fn, kapp_arg_count, is_const_app) were
# never refused by anything. They had been measured by compiling `expr_model_spine`
# as the ONLY unit in its crate, which leaves `KExpr` out of the environment; the
# elaborator's Lean-compatible auto-bound-implicit rule then turns the binder type
# into an implicit `{KExpr : Sort u}` whose `match` has no nameable type
# constructor. Loaded beside `expr_model_core`, as the module does, all three
# register: a refusal reproduced outside the environment the declaration lives in
# tells you about the harness. The entry stays as a slot because a genuine refusal
# must be recorded, not silently dropped from the accounting.
REFUSED: dict[str, tuple[str, str]] = {}

# Free declarations the island could register, blocked by their UNIT-MATE: the
# island loads whole units, and a unit that also declares a prelude-owned name
# cannot be embedded without that name being silently aliased. Splitting the unit
# to fit the gate would fork the model's source of truth, so the declaration is
# recorded here instead. Each entry falls the day its unit-mate stops colliding
# -- i.e. the day the foundation is transported.
# History. `AndType` sat here while the rule was "never embed a unit that declares a
# prelude-owned name": an alias to an unmeasured declaration is a false green. From
# 2026-09-13 to 2026-10-28 it was embedded instead, because the kernel's
# add_inductive guard returned before any mutation, so re-declaring the
# prelude-owned `Empty` was a pure no-op, and `Empty`'s defining property is
# witnessed by `fa_empty_elim` (`_embedded_unit_declarations_are_accounted` below
# still enforces that an embedded unit's aliased names are AGREED). That premise no
# longer holds: the Trust toolchain 0.11.0+g20565c325 refuses the re-declaration
# outright, as Lean does ("`Empty` did not elaborate: `Empty` has already been
# declared (Lean 4.8.0 core)"), so the unit cannot be loaded at all and every
# island failed to compile. `foundation_empty_and` is therefore not embedded, and
# `AndType` is recorded here again; `Empty` stays AGREED.
BLOCKED_BY_UNITMATE: dict[str, str] = {
    "AndType": (
        "its unit foundation_empty_and also declares the prelude-owned Empty, whose "
        "re-declaration the island compiler refuses (measured 2026-10-28, trustc "
        "0.11.0+g20565c325: `Empty` has already been declared (Lean 4.8.0 core))"
    ),
}

# Witnesses that must FAIL. Without these the agreement class could be vacuous:
# a witness that cannot go red proves nothing about the prelude.
# Each control is (label, island body, why, expected-substring-of-stderr). The
# EXPECTED SUBSTRING is load-bearing: requiring only a non-zero exit lets a
# control that has decayed into a syntax error count as "correctly refused",
# which would make the agreement class vacuous while the leg stayed green.
# Each substring is the ELABORATOR's own wording as built into the Trust toolchain from
# its first-party/clean submodule, so it moves when that pin moves and the control then
# reds for the toolchain's reason, not its own. Where each is rendered (grep 2026-09-15):
# two pin the `Type mismatch` lead, three its `expected <their equation>` (2026-11-16), one the `Unknown identifier` lead of ElabError's
# thiserror strings in crates/clean-elab/src/error.rs (TypeMismatch, UnknownIdent); the
# two recursor pins are TypeMismatch's `expected {expected}, got {actual}` frame around
# the unifier's `cannot unify <kind> with <kind>` (unify/unifier/unify_expr.rs), kinds
# named by error_render.rs `kind_name`; the `error: `x` did not elaborate:` line is
# clean-elab's too (module_batch/render.rs). Remedy when a stamp moves a wording:
# re-measure and pin the tightest substring naming the stated reason (old wording, stamp
# and why beside the tuple).
def _control_message_matches(expect, stderr: str) -> bool:
    """Does the refusal name its stated reason, in ANY dialect this repo has measured?

    `expect` is either one substring, or a list of ALTERNATIVES where each
    alternative is one substring or a tuple of substrings that must ALL appear.
    An alternative is a whole dialect; the conjunction inside it is what keeps
    the pin tight, so a control decayed into a syntax error still fails.

    WHY ALTERNATIVES EXIST (measured 2026-09-15). These substrings are the
    ELABORATOR's wording as built into the Trust toolchain -- a different
    program from this repo's clean-elab -- so the control's verdict is a
    function of the OPERATOR'S TOOLCHAIN, not of this tree. The two recursor
    controls were pinned to the post-`888e9c09a` (2026-08-30) rendering,
    measured under a toolchain stamped `43f8b339f 2026-09-12` on another box.
    This box's `rustc +trust` is `c4e667ca5 2026-08-21` -- NINE DAYS BEFORE
    that commit -- so its embedded Clean still prints the older
    `cannot unify expressions of different shape: Discriminant(N) vs
    Discriminant(M)` and debug-formats the expected type as
    `Const(Name { .. suffix: ["Nat"] .. })`. Both controls still REFUSE, and
    refuse for exactly their stated reason; only the rendering differs.

    Re-pinning to one box's wording cannot fix that -- it just moves the red to
    the other box. `scripts/check_fmt_changed.py` ARM 3b was the same class
    earlier the same day: an arm that measured the toolchain's DIALECT rather
    than the code. So the pin is made dialect-INDEPENDENT instead, and a new
    rendering is added here beside its stamp rather than replacing the old one.
    """
    alts = expect if isinstance(expect, list) else [expect]
    for alt in alts:
        needles = alt if isinstance(alt, tuple) else (alt,)
        if all(n in stderr for n in needles):
            return True
    return False


NEGATIVE_CONTROLS = [
    ("add_recurses_left",
     "def bad_add (n : Nat) : @Eq Nat (Nat.add Nat.zero n) n := @Eq.refl Nat n",
     "Nat.add recursing on its LEFT argument would make this hold", "Type mismatch: expected Nat.add Nat.zero"),
    ("pred_zero_wrong",
     "def bad_pred : @Eq Nat (Nat.pred Nat.zero) (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)",
     "Nat.pred Nat.zero must be Nat.zero, not a successor", "Type mismatch: expected Nat.pred Nat.zero = Nat.succ Nat.zero"),
    ("sub_drops_pred",
     "def bad_sub (a : Nat) (b : Nat) : @Eq Nat (Nat.sub a (Nat.succ b)) (Nat.sub a b) := @Eq.refl Nat (Nat.sub a b)",
     "Nat.sub must peel the right operand THROUGH pred", "Type mismatch: expected Nat.sub"),
    ("succ_wrong_arity",
     "def bad_succ : Nat -> Nat -> Nat := Nat.succ",
     "Nat.succ must be unary", "Type mismatch"),
    ("nat_rec_three_minors",
     "def bad_nat_rec (C : Nat -> Type) (z : C Nat.zero) (s : (n : Nat) -> C n -> C (Nat.succ n)) (x : C Nat.zero) (n : Nat) : C n := @Nat.rec C z s x n",
     "Nat.rec takes one minor premise per constructor, so a third would mean a third constructor",
     # Was "Discriminant" -- never a kernel word: clean-elab's unifier
     # (unify/unifier/unify_expr.rs) printed a shape mismatch as `{:?}` of
     # std::mem::discriminant(kind) until 888e9c09a (2026-08-30) put `cannot unify <kind>
     # with <kind>: <term> vs <term>` there, so the toolchain's embedded Clean is at or
     # past that commit. Re-measured 2026-09-15 under `rustc 1.99.0-dev (43f8b339f
     # 2026-09-12)`, the verbatim `rustc +trust --version` line: the TOOLCHAIN BUILD's
     # stamp (atpkg seal at ~/.rustup/toolchains/trust, built from $HOME/trust
     # per its PROVENANCE), not a git anchor -- 43f8b339f resolves to no commit in this
     # repo or ../trust. Message: `Type mismatch: expected Nat, got cannot unify an
     # application with a constant: fvar#0 Nat.zero vs Nat`. That IS the stated reason:
     # after the minors `z s` the next `Nat.rec` slot is the major premise `t : Nat`, and
     # the extra minor `x : C Nat.zero` (an application; `C` is fvar#0) lands in it.
     # Measured both ways: the body minus `x` registers (rc=0); with a THIRD constructor
     # it fails `expected fvar#0 Three.third, got const mismatch: Three.zero vs
     # Three.third`, which this pin rejects and a bare "Type mismatch" would accept. The
     # `fvar#0 ... vs Nat` tail is NOT pinned: fvar#N is error_render::fvar's no-context
     # fallback, likeliest to move next, and only repeats the two kinds already named.
     # Second alternative MEASURED on this box 2026-09-15 at trust `c4e667ca5`
     # (2026-08-21), verbatim: `Type mismatch: expected Const(Name { depth: 1,
     # suffix: ["Nat"], lean4_hash: 9ecc0d3a68dfdd9b }, []), got cannot unify
     # expressions of different shape: Discriminant(4) vs Discriminant(3)`. The
     # conjunction names the TYPE and the UNIFICATION FAILURE separately, so a
     # decayed syntax error matches neither half. The Discriminant NUMBERS are
     # deliberately not pinned -- they are `{:?}` of a std::mem::discriminant
     # and carry no stable meaning.
     ["expected Nat, got cannot unify an application with a constant",
      ('suffix: ["Nat"]', "got cannot unify expressions of different shape")]),
    ("bool_rec_three_minors",
     "def bad_bool_rec (C : Bool -> Type) (f : C Bool.false) (t : C Bool.true) (x : C Bool.false) (b : Bool) : C b := @Bool.rec C f t x b",
     "Bool.rec takes one minor premise per constructor, so a third would mean a third constructor",
     # Was "Discriminant"; same provenance, mechanism and measurements as
     # `nat_rec_three_minors` above, over Bool (`expected Bool, got cannot unify
     # an application with a constant: fvar#0 Bool.false vs Bool`; the two-minor
     # body registers; a third constructor `Tri.third` fails `const mismatch`).
     # Second alternative MEASURED on this box 2026-09-15 at trust `c4e667ca5`:
     # `expected Const(Name { depth: 1, suffix: ["Bool"], lean4_hash:
     # b2c7c3b8d8c62cfa }, []), got cannot unify expressions of different
     # shape: Discriminant(4) vs Discriminant(3)`. Same mechanism as the Nat
     # control above.
     ["expected Bool, got cannot unify an application with a constant",
      ('suffix: ["Bool"]', "got cannot unify expressions of different shape")]),
    ("empty_wrong_sort",
     "def bad_empty_sort : Prop := Empty",
     "Empty must live at the model's sort; the constructor and eliminator witnesses alone do not pin it",
     "Type mismatch"),
    ("empty_has_ctor",
     "def bad_empty : Empty := Empty.mk",
     "Empty must have no constructors", "Unknown identifier"),
]

DECL_RE = re.compile(
    r'#\[path\s*=\s*"(?P<path>[^"]+)"\]\s*\n\s*clean\s+mod\s+(?P<unit>[A-Za-z_][A-Za-z0-9_]*)\s*;'
)
TOPLEVEL_RE = re.compile(r"^(inductive|def)\s+([A-Za-z_][\w.]*)", re.M)


class IslandError(Exception):
    """Fail-closed: anything we cannot account for aborts the run."""


def strip_clean_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return "\n".join(line.split("--")[0] for line in text.splitlines())


def model_declarations() -> dict[str, list[str]]:
    """Every top-level declaration of every model unit, by unit.

    Read from the committed census rather than parsed here. This script must not
    parse Clean source: a regex that misses a declaration the real parser accepts
    would make that declaration invisible to the whole accounting, which is the
    one way a "nothing unaccounted" claim could be false while reading green. The
    census is re-derived from the units by the REAL parser
    (`declarations_of_source`, the production loader's own function) in
    `crates/clean-verify/src/spec/model_units/agreement.rs`, which refuses any
    disagreement in either direction.
    """
    path = os.path.join(REPO, MODEL_CENSUS)
    if not os.path.exists(path):
        raise IslandError(
            f"{MODEL_CENSUS} is missing -- it is the declaration census this gate accounts "
            "against, re-derived by the Clean parser in clean-verify's agreement tests"
        )
    doc = json.loads(open(path, encoding="utf-8").read())
    units = doc.get("units")
    if not isinstance(units, dict) or not units:
        raise IslandError(f"{MODEL_CENSUS} carries no `units` map")
    on_disk = {
        os.path.basename(p)[: -len(".clean")]
        for p in glob.glob(os.path.join(REPO, MODEL_SPEC_DIR, "*.clean"))
    }
    if set(units) != on_disk:
        raise IslandError(
            f"{MODEL_CENSUS} covers {sorted(units)} but {MODEL_SPEC_DIR} holds {sorted(on_disk)} -- "
            "a model unit added or removed without re-minting the census would be outside the "
            "accounting entirely"
        )
    return {u: list(v) for u, v in units.items()}


def module_units() -> list[tuple[str, str]]:
    path = os.path.join(REPO, ISLAND_MODULE)
    if not os.path.exists(path):
        raise IslandError(f"{ISLAND_MODULE} is missing")
    text = open(path, encoding="utf-8").read()
    return [(m.group("unit"), m.group("path")) for m in DECL_RE.finditer(text)]


def unit_source(unit: str) -> str:
    for base in (MODEL_SPEC_DIR, ISLAND_SPEC_DIR):
        candidate = os.path.join(REPO, base, f"{unit}.clean")
        if os.path.exists(candidate):
            return candidate
    raise IslandError(f"unit {unit!r} has no .clean file under {MODEL_SPEC_DIR} or {ISLAND_SPEC_DIR}")


def cmd_check() -> int:
    """The module declares exactly the embedded units, each loading its own file."""
    declared = module_units()
    names = [u for u, _ in declared]
    if sorted(names) != sorted(EMBEDDED):
        raise IslandError(
            f"{ISLAND_MODULE} declares {sorted(names)} but this script accounts for "
            f"{sorted(EMBEDDED)} -- a unit embedded without an accounting entry is a "
            "declaration nothing checks for prelude aliasing, and an accounting entry "
            "with no `clean mod` is a claim nothing compiles"
        )
    if len(names) != len(set(names)):
        raise IslandError(f"{ISLAND_MODULE} declares a unit twice: {names}")
    module_dir = os.path.dirname(os.path.join(REPO, ISLAND_MODULE))
    for unit, rel in declared:
        resolved = os.path.normpath(os.path.join(module_dir, rel))
        expected = os.path.normpath(unit_source(unit))
        if resolved != expected:
            raise IslandError(
                f"`clean mod {unit}` loads {resolved}, not {expected} -- the island "
                "must BE the committed unit, not a copy of it"
            )
    # An embedded unit's every declaration must be accounted: either claimed
    # REGISTERED for that unit, or AGREED (aliased to a prelude declaration whose
    # defining property is witnessed). Anything else would ride into the island
    # unnoticed -- the compiler's note names a silently aliased declaration as
    # registered, so the note cannot be the accounting.
    model = model_declarations()
    for unit, claimed in EMBEDDED.items():
        if unit not in model:
            continue  # the agreement unit itself is not a model unit
        for name in model[unit]:
            if name in claimed or name in AGREEMENT_COVERS:
                continue
            raise IslandError(
                f"embedded unit {unit!r} declares {name!r}, which is neither claimed as "
                f"registered for that unit nor AGREED. An embedded unit's declarations all "
                f"enter the island: one that is prelude-owned is silently aliased and the "
                f"compiler still names it registered, so it must be covered by an agreement "
                f"witness before the unit may be embedded."
            )
    embedded_names = {n for v in EMBEDDED.values() for n in v}
    unaccounted = [
        f"{unit}::{name}"
        for unit, decls in model.items()
        for name in decls
        if name not in embedded_names
        and name not in AGREEMENT_COVERS
        and name not in REFUSED
        and name not in BLOCKED_BY_UNITMATE
    ]
    if unaccounted:
        raise IslandError(
            "these model declarations are in NO state -- not registered by an "
            "embedded unit, not covered by an agreement witness, not recorded as "
            f"refused, not blocked by a unit-mate: {', '.join(unaccounted)}. A model declaration the island "
            "neither checks nor accounts for is exactly the gap this gate exists to "
            "close; add it to EMBEDDED, to AGREEMENT_COVERS, to REFUSED, or to "
            "BLOCKED_BY_UNITMATE with its measured reason"
        )
    # Every ambient name the kernel found must carry a witness. An ambient name is
    # supplied by the environment, not by the model, so one without a witness is a
    # dependency on the ambient environment that nothing checks.
    census = json.loads(open(os.path.join(REPO, MODEL_CENSUS), encoding="utf-8").read())
    ambient = census.get("ambient")
    if not isinstance(ambient, list):
        raise IslandError(
            f"{MODEL_CENSUS} records no `ambient` list -- it is derived from the kernel by "
            "clean-verify's agreement tests and is what pins the model's dependencies on "
            "whatever environment it is elaborated in"
        )
    unwitnessed = [n for n in ambient if n not in AMBIENT_AGREED and n not in AGREEMENT_COVERS]
    if unwitnessed:
        raise IslandError(
            f"these AMBIENT names have no agreement witness: {', '.join(unwitnessed)}. The model "
            "references them and declares none of them, so in an island they come from the "
            "compiler prelude with nothing checking that the prelude's version is the one the "
            "model's proofs are about"
        )

    total = sum(len(v) for v in model.values())
    print(
        f"MODEL_ISLANDS=ok {ISLAND_MODULE} loads {len(declared)} unit(s) byte-verbatim; "
        f"all {total} model declaration(s) accounted "
        f"({len(embedded_names & {n for v in model.values() for n in v})} registered, "
        f"{len(AGREEMENT_COVERS)} agreed, {len(REFUSED)} refused, "
        f"{len(BLOCKED_BY_UNITMATE)} blocked by a unit-mate)"
    )
    return 0


# The compiler's note is the gate's evidence channel, and rustc renders the unit's
# OWN SOURCE into the same stderr underneath it. A free-form scan of that stream
# therefore lets the artifact under audit write into the record that audits it:
# measured, a `.clean` unit whose prose contains the words "registered (ghost_one,
# ghost_two)" injects both names, and one such sentence is enough to mask a
# declaration deleted from the model -- defeating this gate's own demonstration
# arm while it reports OK.
#
# So the harvest is ANCHORED to the note line (column 0; an echoed source line is
# prefixed "N | ") and CROSS-CHECKED against the count the note states about
# itself. A note that names a different number of declarations than it claims is
# refused rather than parsed.
NOTE_RE = re.compile(
    r"^note: Clean island kernel-checked: (\d+) declaration\(s\) registered \(([^)]*)\)$"
)


# How the compiler says a probed name is already declared: a free name registers,
# an owned one is refused, in the wording of the toolchain that runs:
#   "Duplicate declaration: X"                              (through 2026-10)
#   "`X` did not elaborate: `X` has already been declared"  (trustc 0.11.0+g20565c325,
#                                                            measured 2026-10-28)
# Both are read, and nothing else. A probe that reads neither takes the owned set as
# EMPTY and reports all six declarations "no longer owned" -- a fact about the
# wording, not about the prelude (the class trustc_available's docstring records).
OWNED_RE = re.compile(
    r"Duplicate declaration: ([A-Za-z_][A-Za-z0-9_.]*)"
    r"|`([A-Za-z_][A-Za-z0-9_.]*)` did not elaborate: `\2` has already been declared"
)


def owned_names(stderr: str) -> set[str]:
    """The probed names the COMPILER refused as already declared."""
    return {old or new for old, new in OWNED_RE.findall(stderr)}


def harvest_registered(stderr: str) -> set[str]:
    """The declarations the COMPILER said it registered, and nothing else."""
    out: set[str] = set()
    for line in stderr.splitlines():
        m = NOTE_RE.match(line)
        if m is None:
            continue
        claimed = int(m.group(1))
        names = [x.strip() for x in m.group(2).split(",") if x.strip()]
        if len(names) != claimed:
            raise IslandError(
                f"a kernel-checked note claims {claimed} declaration(s) but names "
                f"{len(names)}: {line!r}. The note is this gate's evidence channel; a note "
                "that disagrees with itself is not evidence."
            )
        out.update(names)
    return out


def trustc_available() -> bool:
    """Does `trustc` resolve to a compiler with the CLEAN FRONT END?

    Resolving the alias is not enough, and accepting it cost a waiver. On a host
    where `+trust` falls back to upstream stable, `--print sysroot` exits 0 and
    prints a stable sysroot, so this returned True, `cmd_verify` proceeded, and
    upstream rustc answered the ownership probe with ``missing `struct` for
    struct definition`` — a message carrying no `Duplicate declaration` line, so
    the probe read the prelude-owned set as EMPTY and the leg reported six model
    declarations "no longer owned". That verdict was a fact about the alias, not
    about the prelude or any committed byte (gate-legs.txt, WAIVED 2026-09-12).

    So the probe is the thing it is a probe FOR: compile a one-line island and
    require it to build. A compiler without the front end cannot, and the caller
    takes its documented skip instead of minting a claim from a compiler that
    never ran Clean.

    THAT SENTENCE WAS TRUE OF THE WRONG FORM, and the defect recurred one level
    down (2026-09-14). The probe compiled an INLINE island, `clean { ... }`,
    while `model_islands.rs` declares every unit OUT OF LINE,
    `#[path = "...clean"] clean mod <unit>;`. The live stage2 on this host
    (trust `10f221fbe`, 2026-08-08) accepts the first and not the second, so the
    probe passed, `cmd_verify` proceeded, and the compiler answered the
    out-of-line form with a plain Rust parse error -- `expected one of `!` or
    `::`, found keyword `mod`` -- which the leg reported as "the islands do not
    kernel-check". That is a fact about the TOOLCHAIN, not about any committed
    byte, and it is the same class as the waiver above: a capability probe that
    does not test the capability the gate depends on.

    Both forms are required now. A host that can run one and not the other takes
    the skip, because the gate needs both.
    """
    probe = subprocess.run(
        ["trustc", "--print", "sysroot"], capture_output=True, text=True
    )
    if probe.returncode != 0 or not probe.stdout.strip():
        return False
    body = "def model_islands_probe : Nat := 0"
    with tempfile.TemporaryDirectory() as work:
        if _island(body, work, "probe").returncode != 0:
            return False
        return _island_mod(body, work, "probe_mod").returncode == 0


def _rustc(args: list[str], cwd: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["trustc", "--edition", "2021", "--crate-type", "lib", "--emit", "metadata", *args],
        capture_output=True, text=True, cwd=cwd,
    )


def _island_mod(body: str, work: str, stem: str) -> subprocess.CompletedProcess:
    """The OUT-OF-LINE island form, which is the one `model_islands.rs` uses.

    `#[path = "<unit>.clean"] clean mod <unit>;` loads the unit from disk byte
    for byte at expansion time. A front end that supports only the inline
    `clean { }` form parses this as Rust and fails on the `mod` keyword.
    """
    unit = f"{stem}_unit"
    with open(os.path.join(work, f"{unit}.clean"), "w", encoding="utf-8") as handle:
        handle.write(body + "\n")
    path = os.path.join(work, f"{stem}.rs")
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(f'#[path = "{unit}.clean"]\nclean mod {unit};\n')
    return _rustc(["--out-dir", work, os.path.basename(path)], work)


def _island(body: str, work: str, stem: str) -> subprocess.CompletedProcess:
    path = os.path.join(work, f"{stem}.rs")
    with open(path, "w", encoding="utf-8") as handle:
        handle.write("clean {\n" + body + "\n}\n")
    return _rustc(["--out-dir", work, path], work)


def cmd_verify() -> int:
    """Compile the islands with Trust and read the COMPILER's own verdict."""
    if not trustc_available():
        print(
            "MODEL_ISLANDS=skipped this host's `trustc` cannot compile a Clean "
            "island in BOTH forms (inline `clean { }` and out-of-line "
            "`#[path] clean mod`); the alias may still resolve -- see trustc_available"
        )
        return 0
    model = model_declarations()
    all_model = [n for decls in model.values() for n in decls]
    ambient_names = json.loads(
        open(os.path.join(REPO, MODEL_CENSUS), encoding="utf-8").read()
    ).get("ambient", [])
    expected = [n for unit in sorted(EMBEDDED) for n in EMBEDDED[unit]]
    module_dir = os.path.dirname(os.path.join(REPO, ISLAND_MODULE))

    with tempfile.TemporaryDirectory(prefix="model-islands-") as work:
        # 1. The islands themselves, compiled from the module's OWN directory so
        #    its `#[path]` attributes resolve exactly as in a real build.
        got = _rustc(["--out-dir", work, os.path.basename(ISLAND_MODULE)], module_dir)
        if got.returncode != 0:
            errs = [ln for ln in got.stderr.splitlines() if ln.startswith("error")][:4]
            print("MODEL_ISLANDS=fail the islands do not kernel-check:\n  " + "\n  ".join(errs),
                  file=sys.stderr)
            return 1
        registered = harvest_registered(got.stderr)

        # 2. Ownership FIRST, PROBED against the live compiler. A name the prelude owns
        #    is refused as already declared (OWNED_RE); a free one registers.
        owned_probe = _island(
            "".join(f"    def {n} : Nat := Nat.zero\n" for n in all_model), work, "ownership")
        owned = owned_names(owned_probe.stderr) & set(all_model)
        if owned != set(AGREEMENT_COVERS):
            new = sorted(owned - set(AGREEMENT_COVERS))
            gone = sorted(set(AGREEMENT_COVERS) - owned)
            print(
                "MODEL_ISLANDS=fail the set of PRELUDE-OWNED model declarations moved. "
                + (f"Newly owned (must gain agreement witnesses, and must NOT be embedded -- "
                   f"an inductive re-declaration would be silently aliased): {', '.join(new)}. "
                   if new else "")
                + (f"No longer owned (the witnesses are now vacuous; embed the unit instead): "
                   f"{', '.join(gone)}." if gone else ""),
                file=sys.stderr)
            return 1

        # 3. No embedded declaration may be prelude-owned: that is the false green.
        aliased = sorted(set(expected) & owned)
        if aliased:
            print("MODEL_ISLANDS=fail these embedded declarations are PRELUDE-OWNED, so the "
                  f"island green is the prelude's and not the model's: {', '.join(aliased)}.",
                  file=sys.stderr)
            return 1

        # 3b. Completeness FIRST: a renamed declaration is both missing and
        #     surprising, and naming what was LOST is the more useful diagnosis.
        missing = [n for n in expected if n not in registered]
        if missing:
            print(
                "MODEL_ISLANDS=fail the compiler did not report these declarations as "
                f"registered: {', '.join(missing)}. Either a unit changed or a declaration "
                "was dropped -- a dropped declaration is exactly the silent failure this "
                "check exists for.", file=sys.stderr)
            return 1

        # 3c. The other direction: every name the COMPILER registered must be a
        # name the census knows. Without this the accounting is one-way -- a
        # declaration added to an embedded unit and not re-minted into the census
        # is invisible to every check here, including the prelude-alias probe,
        # because all of them iterate the census. A surprise registration is
        # exactly how an unaccounted (and possibly aliased) declaration would ride
        # into the island while every leg stayed green.
        surprise = sorted(registered - set(all_model))
        if surprise:
            raise IslandError(
                f"the islands registered declarations the census does not know: "
                f"{', '.join(surprise)}. Every check in this gate iterates "
                f"{MODEL_CENSUS}, so an unrecorded declaration is outside the accounting "
                "entirely -- re-mint the census (and let clean-verify's parser-derived test "
                "confirm it) before this can pass."
            )


        # 4. The agreement witnesses must all have registered.
        uncovered = [
            w
            for ws in list(AGREEMENT_COVERS.values()) + list(AMBIENT_AGREED.values())
            for w in ws
            if w not in registered
        ]
        if uncovered:
            print("MODEL_ISLANDS=fail these agreement witnesses did not register, so the "
                  f"prelude-owned declarations they stand for are unchecked: {', '.join(uncovered)}",
                  file=sys.stderr)
            return 1

        # 4b. Every recorded refusal must STILL be a refusal, re-measured in the
        # environment the module provides rather than in isolation.
        for name, (unit, reason) in sorted(REFUSED.items()):
            if name in registered:
                print(f"MODEL_ISLANDS=fail {name!r} is recorded REFUSED but the island registered "
                      "it. A refusal that has stopped being true is debt the accounting is "
                      "carrying for nothing; move it to EMBEDDED.", file=sys.stderr)
                return 1
            probe_src = open(os.path.join(REPO, ISLAND_MODULE), encoding="utf-8").read()
            probe_src += f'\n#[path = "../../clean-verify/spec/{unit}.clean"]\nclean mod {unit};\n'
            probe_path = os.path.join(module_dir, f"_refusal_probe_{unit}.rs")
            try:
                with open(probe_path, "w", encoding="utf-8") as handle:
                    handle.write(probe_src)
                got_ref = _rustc(["--out-dir", work, os.path.basename(probe_path)], module_dir)
            finally:
                if os.path.exists(probe_path):
                    os.remove(probe_path)
            if got_ref.returncode == 0 or reason not in got_ref.stderr:
                print(f"MODEL_ISLANDS=fail the recorded refusal of {name!r} no longer reproduces "
                      f"with the module's own units loaded: expected a failure mentioning "
                      f"{reason!r}. Either it now elaborates (move it to EMBEDDED) or it fails for "
                      "a different reason (record that reason).", file=sys.stderr)
                return 1

        # 5. Negative controls: a witness class that cannot go red proves nothing.
        for stem, body, why, expect in NEGATIVE_CONTROLS:
            control = _island("    " + body, work, f"neg_{stem}")
            if control.returncode == 0:
                print(f"MODEL_ISLANDS=fail negative control {stem!r} was ACCEPTED -- {why}. "
                      "The agreement witnesses are vacuous: they cannot distinguish a prelude "
                      "that matches the model from one that does not.", file=sys.stderr)
                return 1
            if not _control_message_matches(expect, control.stderr):
                print(f"MODEL_ISLANDS=fail negative control {stem!r} failed, but NOT for its "
                      f"stated reason ({why}): expected {expect!r} in the compiler's message. "
                      "A control that has decayed into a syntax error still exits non-zero and "
                      "would count as 'correctly refused' while proving nothing.", file=sys.stderr)
                return 1

    print(
        f"MODEL_ISLANDS=ok {len(registered)} declaration(s) kernel-checked in a Rust build; "
        f"{len(all_model)} model declaration(s) accounted -- "
        f"{len([n for n in all_model if n in registered and n not in AGREEMENT_COVERS])} registered, "
        f"{len(AGREEMENT_COVERS)} prelude-owned and AGREED by "
        f"{sum(len(v) for v in AGREEMENT_COVERS.values())} witness(es), "
        f"{len(ambient_names)} ambient name(s) agreed by "
        f"{sum(len(v) for v in AMBIENT_AGREED.values())} witness(es), "
        f"{len(REFUSED)} refused (each re-measured), "
        f"{len(BLOCKED_BY_UNITMATE)} blocked by a unit-mate; "
        f"{len(NEGATIVE_CONTROLS)} negative control(s) correctly refused"
    )
    return 0


def cmd_self_test() -> int:
    arms: list[tuple[str, bool]] = []
    real = open(os.path.join(REPO, ISLAND_MODULE), encoding="utf-8").read()
    model = model_declarations()
    all_model = {n for decls in model.values() for n in decls}

    arms.append(("the module parses as out-of-line `clean mod` units",
                 len(DECL_RE.findall(real)) == len(EMBEDDED)))
    arms.append(("the module is the out-of-line form, so nothing is copied",
                 not re.search(r"^\s*clean\s*\{", real, re.M)))
    arms.append(("every embedded unit has a committed .clean file",
                 all(os.path.exists(unit_source(u)) for u in EMBEDDED)))
    arms.append(("every model declaration is in exactly one state",
                 all(sum([n in {x for v in EMBEDDED.values() for x in v},
                          n in AGREEMENT_COVERS, n in REFUSED,
                          n in BLOCKED_BY_UNITMATE]) == 1 for n in all_model)))
    arms.append(("every agreed declaration is a real model declaration",
                 set(AGREEMENT_COVERS) <= all_model))
    arms.append(("every ambient name is NOT a model declaration (that is what makes it ambient)",
                 not (set(AMBIENT_AGREED) & all_model)))
    # The evidence channel must not be writable by the artifact under audit.
    injected = harvest_registered(
        "note: Clean island kernel-checked: 1 declaration(s) registered (real_one)\n"
        "1 | / /-! prose that says registered (ghost_one, ghost_two) -/\n"
    )
    owned_text = (
        "error: Duplicate declaration: Nat\n"
        "error: error: `Empty` did not elaborate: `Empty` has already been declared "
        "(Lean 4.8.0 core)\n"
        "3 |     def AndType : Nat := Nat.zero\n"
        "error: error: `Eq` did not elaborate: `Le` has already been declared\n"
    )
    arms.append(("the ownership probe reads both compiler wordings, and only for the name refused",
                 owned_names(owned_text) == {"Nat", "Empty"}))
    arms.append(("an echoed source line cannot inject a registered name",
                 injected == {"real_one"}))
    try:
        harvest_registered("note: Clean island kernel-checked: 3 declaration(s) registered (a, b)\n")
        miscount_refused = False
    except IslandError:
        miscount_refused = True
    arms.append(("a note that disagrees with its own count is refused", miscount_refused))
    arms.append(("every kernel-derived ambient name carries a witness",
                 all(n in AMBIENT_AGREED or n in AGREEMENT_COVERS
                     for n in json.loads(open(os.path.join(REPO, MODEL_CENSUS),
                                              encoding="utf-8").read()).get("ambient", []))))
    arms.append(("the agreement unit supplies every ambient witness",
                 {w for ws in AMBIENT_AGREED.values() for w in ws}
                 <= set(EMBEDDED["foundation_agreement"])))
    arms.append(("every refused declaration is a real model declaration",
                 set(REFUSED) <= all_model))
    arms.append(("every unit-mate-blocked declaration is a real model declaration",
                 set(BLOCKED_BY_UNITMATE) <= all_model))
    arms.append(("no agreed declaration is also embedded",
                 not (set(AGREEMENT_COVERS) & {x for v in EMBEDDED.values() for x in v})))
    arms.append(("the agreement unit supplies every witness the cover map names",
                 {w for ws in AGREEMENT_COVERS.values() for w in ws}
                 <= set(EMBEDDED["foundation_agreement"])))
    arms.append(("every embedded unit's declarations are all claimed or agreed",
                 all(n in EMBEDDED[u] or n in AGREEMENT_COVERS
                     for u in EMBEDDED if u in model for n in model[u])))
    arms.append(("there is a negative control for the arithmetic, the arity and the empty type",
                 len(NEGATIVE_CONTROLS) >= 5))
    # The DIALECT axis (2026-09-15). A control pinned to one toolchain's exact
    # wording is a toolchain-version detector: the two recursor controls were
    # pinned under trust `43f8b339f` (2026-09-12) on another box and were RED on
    # this one at `c4e667ca5` (2026-08-21), which renders the same refusal
    # differently. These arms pin the matcher in BOTH directions, because a pin
    # loosened to clear a red is worth nothing unless it still rejects a control
    # that has decayed into a syntax error.
    _nat = [c for c in NEGATIVE_CONTROLS if c[0] == "nat_rec_three_minors"][0][3]
    arms.append(("a recursor control accepts the post-888e9c09a wording",
                 _control_message_matches(
                     _nat, "Type mismatch: expected Nat, got cannot unify an "
                           "application with a constant: fvar#0 Nat.zero vs Nat")))
    arms.append(("a recursor control accepts the pre-888e9c09a wording (measured at c4e667ca5)",
                 _control_message_matches(
                     _nat, 'Type mismatch: expected Const(Name { depth: 1, suffix: '
                           '["Nat"], lean4_hash: 9ecc }, []), got cannot unify '
                           'expressions of different shape: Discriminant(4) vs Discriminant(3)')))
    arms.append(("a control decayed into a SYNTAX error is still refused",
                 not _control_message_matches(_nat, "error: expected identifier, found `)`")))
    arms.append(("naming the type without the unification failure is refused",
                 not _control_message_matches(
                     _nat, 'expected Const(Name { suffix: ["Nat"] }, []), got something else')))
    arms.append(("a unification failure against the WRONG type is refused",
                 not _control_message_matches(
                     _nat, "got cannot unify expressions of different shape: "
                           "Discriminant(1) vs Discriminant(2)")))
    arms.append(("a single-substring pin still behaves as one",
                 _control_message_matches("Type mismatch", "x Type mismatch y")
                 and not _control_message_matches("Type mismatch", "nope")))

    arms.append(("every negative control pins the compiler message it expects",
                 all(len(c) == 4 and c[3] for c in NEGATIVE_CONTROLS)))
    try:
        cmd_check()
        arms.append(("--check accepts the committed tree", True))
    except IslandError:
        arms.append(("--check accepts the committed tree", False))

    failed = [name for name, ok in arms if not ok]
    for name, ok in arms:
        print(f"  [{'ok' if ok else 'FAIL'}] {name}")
    if failed:
        print(f"MODEL_ISLANDS_SELFTEST=fail {len(failed)}/{len(arms)}", file=sys.stderr)
        return 1
    print(f"MODEL_ISLANDS_SELFTEST=ok {len(arms)}/{len(arms)} arms")
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true", help="the module and the accounting agree")
    group.add_argument("--verify", action="store_true", help="compile the islands with trustc")
    group.add_argument("--self-test", action="store_true", help="run the mutation arms")
    args = parser.parse_args(argv[1:])
    try:
        if args.check:
            return cmd_check()
        if args.verify:
            return cmd_verify()
        return cmd_self_test()
    except IslandError as exc:
        print(f"MODEL_ISLANDS=fail {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
