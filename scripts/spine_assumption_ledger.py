#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Mint the §3.6 assumption ledger — `data/spine_assumption_ledger.json`.

designs/2026-08-22-spine-and-lattice-program.md §3.6 and standing rule R8
require one artifact holding "every unproved thing a chain stands on", each
entry carrying a statement, a probe command, a discharge condition, a date and
an owning job; `spine_gate` prints it and G-SCORE ratchets its count downward.
The file did not exist, which is why `scripts/spine_scoreboard.py` reported
`assumption_ledger.count` as UNKNOWN. This script COLLECTS it from committed
sources; it does not invent assumptions.

WHAT THIS LEDGER IS NOT. It is an inventory of STATED assumptions, not evidence
that any of them is safe. A row's presence is a debt, not a discharge, and a
row that carries a `witness` is a bounded assumption, not a discharged one.
Long-form: docs/analysis/spine-assumption-ledger-2026-08-27.md.

--------------------------------------------------------------------- derived

Re-derived from committed artifacts on every run; nothing here is typed by
hand, so a change in the source moves the ledger and `--check` says so.

  class `crystal-erasure-slot`  one row per slot in
        data/crystal_mint_blind_slots.json — the complete list of fields the
        crystal-A2 mint does not fold into the committed core module. That
        file's own words: "Each row below is a claim boundary." A slot closed
        at ACCEPTANCE (a comparison, a refusal) is still an erasure in the
        ENCODING, which is why closing one does not remove its row; deleting
        the slot does. Statement, defence and residual are quoted from the
        slot, never paraphrased.

  class `evalir-declared-delta` one row per `kind: "delta"` row in
        data/evalir_adequacy_grid.json — a measured divergence between EvalIR's
        executable semantics and the pinned trust-ir reference interpreter that
        the encoding DECLARES rather than closes.

------------------------------------------------------------- seeded (SEEDED)

Declared in `SEEDED_ENTRIES` below, each with its citation, because no
machine-readable artifact carries them: they live in prose in the status page,
the decision memo, the program doc and the recon. THIS IS THE PART A CHECKER
CANNOT RE-DERIVE. `--check` can only verify that each seeded row's cited
anchor still occurs verbatim in the cited file; it cannot verify that the row
is complete, and it cannot notice an assumption nobody wrote down. Adding a
seeded row is a human act, and R8 makes omitting one a gate failure rather than
a tidy ledger.

  class `core-callee-model`     1 — C-LZ's deref residual.
  class `layout-obligation`     3 — the undischarged layout obligations the
                                designated target stands on: the two `Level`
                                ones, plus the `Arc` data offset the deref
                                model geps by (which replaced a
                                `core-callee-model` row when that clause was
                                discharged rather than restated).
  class `operational-contract`  3 — PROSPECTIVE. The psm/`stack_safe` FFI
                                bracket (§3.3, T-CTRL) and the two per-cache
                                contracts (§3.2, T-HASH (a) memos / (b)
                                union-finds). §3.6 names all three, but the
                                jobs that would make them live have not run and
                                no chain stands on them today. They carry
                                `status: "prospective"` and are EXCLUDED from
                                `count`, so a planned assumption never
                                masquerades as a live one.

--------------------------------------------------- one accounting point each

data/verdict_io_contracts.json already carries Ring R2 lane (b)'s own 44-row
§3.6 ledger with its own ratchet. Those rows are CROSS-REFERENCED here (a
pointer plus its count), never copied — the rule the env-bypass census follows.
A derived or seeded row whose id collides with a lane-(b) row id aborts the
run. Likewise the adequacy grid's three `audit-pin` rows (load/store/alloca
`align`) are NOT separate rows: the grid itself names
`data/crystal_mint_blind_slots.json` slot `align` as "the R8 ledger row", so
they are folded onto that slot as `restated_in` and the grid's audit-pin total
is cross-checked against them.

Fail-closed: schema drift in any input, a cited anchor that no longer occurs
verbatim in its file, a row missing its probe/statement/discharge/owning job, a
derived row whose source id has vanished, an id colliding with lane (b),
arithmetic that does not close — any of these aborts with a nonzero exit and
writes NOTHING.

Output is deterministic (content-derived provenance: input sha256s, no
timestamps), so re-running on an unchanged tree is a no-op diff.

Usage:
  python3 scripts/spine_assumption_ledger.py              # derive + write the artifact
  python3 scripts/spine_assumption_ledger.py --check      # derive + fail if committed file is stale
  python3 scripts/spine_assumption_ledger.py --self-test  # mutation arms
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

BLIND_SLOTS_PATH = "data/crystal_mint_blind_slots.json"
ADEQUACY_GRID_PATH = "data/evalir_adequacy_grid.json"
VERDICT_IO_PATH = "data/verdict_io_contracts.json"
OUTPUT_PATH = "data/spine_assumption_ledger.json"
SCHEMA = "clean.spine.assumption-ledger/1"

PROGRAM_DOC = "designs/2026-08-22-spine-and-lattice-program.md"
STATUS_DOC = "docs/CRYSTAL_STATUS.md"
LZ_MEMO = "designs/2026-08-22-is-zero-model-vs-minted-decision.md"
RECON_DOC = "docs/analysis/spine-lattice-recon-2026-08-22.md"

STATUSES = ("measured", "prospective")
CLASSES = (
    "crystal-erasure-slot",
    "evalir-declared-delta",
    "core-callee-model",
    "layout-obligation",
    "operational-contract",
)
REQUIRED_KEYS = (
    "id", "class", "origin", "status", "statement", "probe", "probe_kind",
    "discharge", "date", "owning_job", "sources",
)
PROBE_KINDS = ("measurement", "citation")

UNDATED = "UNDATED"
_ISO_DATE = re.compile(r"(20\d\d-\d\d-\d\d)")
_UNDERSCORE_DATE = re.compile(r"(20\d\d)_(\d\d)_(\d\d)")

# The blind-slot lane's own test module, used to spell each slot's probe.
BLIND_SLOT_TEST = "targo --unverified test --locked -p clean-verify --test crystal_a2_mint blind_slots::%s"
BLIND_SLOT_ANCHOR_TEST = "m9_every_blind_slot_is_anchored_in_live_source"
GRID_PROBE = "python3 scripts/evalir_adequacy_grid.py --check"


class LedgerError(Exception):
    """Fail-closed: any input we cannot fully account for aborts the run."""


# --------------------------------------------------------------------- seeded
#
# Every row below is prose somewhere in the tree and nowhere in a machine-
# readable artifact. `sources` is the citation and IS checked (the anchor must
# occur verbatim); the row's completeness is not and cannot be.

SEEDED_ENTRIES = [
    {
        "id": "A-CLZ-DEREF-MODEL",
        "class": "core-callee-model",
        "origin": "seeded",
        "status": "measured",
        "date": "2026-08-26",
        "owning_job": "C-LZ",
        "statement": (
            "The designated target's link-4 theorems hold over a module whose "
            "second function is AUTHORED, not minted. `ir_lzb_correct` (A4) and "
            "`ir_lzb_machine_sound` (A5) are stated over `ir_lzb_module` = the "
            "minted `ir_lz_func` at function 0 (pinned by name, kernel-checked, "
            "`ir_lzb_func0_is_minted`) PLUS a hand-authored model of "
            "`<LevelArc as Deref>::deref` at function 1. That model is an "
            "ASSUMPTION about `Option::as_deref` + `Option::expect`, whose "
            "bodies no artifact here can carry: rustc has no cross-crate THIR "
            "(`thir_body` takes a `LocalDefId`; there is no `thir_of_instance`). "
            "Measured 2026-08-26, the scope was an undercount in both "
            "directions: the reachable closure is six or seven functions, not "
            "two, it includes the higher-order `Option::map`, and its DATA path "
            "bottoms out at `NonNull::as_ref`'s `&*ptr` — a language primitive "
            "with no body at all, which unreachability cannot excuse because "
            "dereferencing is what `is_zero` is there to do. Every chain that "
            "reads through an `Arc` inherits this floor."
        ),
        "probe": "targo --unverified test --locked -p clean-verify --test crystal_a1_lineage level_is_zero",
        "probe_kind": "measurement",
        "discharge": (
            "replace the authored model with a DERIVED one via cross-crate "
            "lowering (designs/2026-08-26-cross-crate-lowering-for-a0.md). Note "
            "what that buys, in the currency the status page states: it does "
            "not REMOVE the assumption, it converts a bespoke one (\"`deref` "
            "does load + null-check + assert\", this chain only) into shared "
            "instruction semantics (\"EvalIR's `load` models `&*ptr`\") that all "
            "eighteen chains already rest on. This row closes only when the "
            "deref's own callees are bodyful — A0's bodyful reachable closure, "
            "architecturally blocked today."
        ),
        "sources": [
            {"path": STATUS_DOC, "anchor": "The deref model is an **ASSUMPTION** about"},
            {"path": LZ_MEMO, "anchor": "The residual is unchanged and is not discharged."},
        ],
    },
    {
        "id": "A-CLZ-LEVELARC-FIELD-OFFSETS",
        "class": "layout-obligation",
        "origin": "seeded",
        "status": "measured",
        "date": "2026-08-26",
        "owning_job": "C-LZ",
        "statement": (
            "The field-addressed representation relation `EncodesLevelArcF` "
            "assumes that a represented `Level` has its `LevelArc` fields "
            "reachable at cells `a+8` and `a+16`. The OFFSETS are read off the "
            "committed artifact; that the representation PLACES anything there "
            "is an assumption about `repr(Rust)` field placement, which is not "
            "guaranteed by the language. Not discharged."
        ),
        "probe": "grep -n 'fields reachable at cells' docs/CRYSTAL_STATUS.md",
        "probe_kind": "citation",
        "discharge": (
            "derive the field offsets from a committed layout descriptor the "
            "way `data/crystal_enum_layout_census_2026-08-21.json` derives the "
            "tag encoding, and pin them the way the tag census is pinned — or "
            "pin the layout at the source with a stated repr."
        ),
        "sources": [
            {"path": STATUS_DOC, "anchor": "fields reachable at cells `a+8` and `a+16`"},
            {"path": LZ_MEMO, "anchor": "`LevelArc` fields at cells `a+8` and `a+16`"},
        ],
    },
    {
        "id": "A-CLZ-DEREF-ARC-DATA-OFFSET",
        "class": "layout-obligation",
        "origin": "seeded",
        "status": "measured",
        "date": "2026-09-09",
        "owning_job": "C-LZ",
        "statement": (
            "`ir_lzb_deref` geps the pointer it loads out of a `LevelArc` field "
            "by SIXTEEN, and `EncodesLevelArcF` places every child `Level` at "
            "`Nat.add b ir_d16` to match, because `<Arc<T> as Deref>::deref` "
            "yields the address of the Arc's DATA — past `ArcInner`'s strong "
            "and weak counts. The 16 is MEASURED on this target (stable rustc "
            "1.97.1 aarch64-apple-darwin, `Level` size 40 / align 8: "
            "`stored=0x105459bf0`, `deref_result=0x105459c00`).\n"
            "NARROWED 2026-09-10, and one clause of it REFUTED. This row used to "
            "end 'not guaranteed: `ArcInner` is private `alloc` internals with "
            "NO STATED REPR, and another target or another smart pointer would "
            "move it.' The no-stated-repr half is FALSE, measured two ways. "
            "rustc's own layout descriptor for this instance reports `repr=c` "
            "for `ArcInner` (the same extraction reports `repr=transparent` for "
            "`NonNull` and no repr at all for `Arc`, so it is not defaulting), "
            "and the sysroot source declares `#[repr(C, align(2))] struct "
            "ArcInner<T: ?Sized> { strong: Atomic<usize>, weak: Atomic<usize>, "
            "data: T }`. Under `repr(C)` the field ORDER is guaranteed, so 16 is "
            "not a layout-algorithm accident: it is two pointer-sized atomic "
            "counts, and what survives is the POINTER WIDTH, not the layout "
            "algorithm. The second half stands unchanged: another target moves "
            "it, and another smart pointer has a different header entirely.\n"
            "The row's own second discharge route — 'make the deref's own "
            "callees bodyful, at which point the offset comes from the emitted "
            "code' — is now AVAILABLE and taken as far as evidence goes. The "
            "callee sidecar derives `<Arc<Level> as Deref>::deref` from its own "
            "monomorphized MIR, and that body geps by a `const i64 16`. So the "
            "16 is no longer a difference between two runtime addresses: it is "
            "the compiler's own constant for this instance. "
            "`scripts/crystal_lzd_readiness.py` RECOMPUTES the offset from "
            "rustc's field sizes (`ArcInner` size 56, fields Atomic(8), "
            "Atomic(8), Level, so data at 16 and a 40-byte payload — the same 40 "
            "this row already recorded) and REFUSES unless the recomputed "
            "offset, the emitted gep constant and the authored model's constant "
            "all agree. Demonstrated: planting 24 as the authored constant "
            "fails closed with 'ledger row A-CLZ-DEREF-ARC-DATA-OFFSET is now "
            "false of the machine it models'. CLOSING the row is still an owner "
            "act, and it should not close alone: its route says it closes "
            "together with `A-CLZ-DEREF-MODEL`, which needs the derived module "
            "MINTED and A4/A5 re-proved over it, not merely measured mintable. \n"
            "WHAT THIS ROW IS NOT. Audit r16 M16-6 (2026-09-02) opened it as a "
            "`core-callee-model` row recording something strictly worse — the "
            "model returned the loaded word UNCHANGED, computing `x` where the "
            "machine computes `&*x`, which did not weaken the relation but made "
            "it UNSATISFIABLE by any real `Level` heap at exactly the "
            "`Succ`/`Max`/`IMax` nodes link 4 is about. That clause is "
            "DISCHARGED: the model carries the gep, the relation moved with it, "
            "and the two `Eq.refl` cost equations it re-derived are "
            "kernel-checked at their new values (`ir_lzb_cost_halts_max` 41, "
            "`ir_lzb_cost_halts_imax` 22). What survives is the layout "
            "obligation above, in the same family as the field offsets and the "
            "niche tag — a smaller and honest debt in place of a false clause."
        ),
        "probe": (
            "targo --unverified test --locked -p clean-verify --test crystal_a1_lineage "
            "deref_model_arc_data_offset"
        ),
        "probe_kind": "measurement",
        "discharge": (
            "derive the Arc data offset from a committed layout descriptor the "
            "way `data/crystal_enum_layout_census_2026-08-21.json` derives the "
            "tag encoding, rather than from a constant stated in two places and "
            "held in step by a test; or make the deref's own callees bodyful, "
            "at which point the offset comes from the emitted code and this row "
            "and `A-CLZ-DEREF-MODEL` close together."
        ),
        "sources": [
            {"path": STATUS_DOC, "anchor": "the Arc's DATA address, sixteen bytes past the stored word"},
            {"path": LZ_MEMO, "anchor": "the deref model geps by the Arc header"},
        ],
    },
    {
        "id": "A-CLZ-LEVEL-NICHE-TAG",
        "class": "layout-obligation",
        "origin": "seeded",
        "status": "measured",
        "date": "2026-08-21",
        "owning_job": "C-LZ",
        "statement": (
            "The niche-encoding obligation, the older of the designated "
            "target's two layout obligations. Measured from the BINARY dumps "
            "(data/crystal_enum_layout_census_2026-08-21.json, two sealed "
            "producers, control/subject/iso arms, all six agreeing), `Level` is "
            "NICHE-encoded — `Niche{untagged=4 (Param), niche_variants=0..=3, "
            "niche_start=3, niche_offset=0, niche_ty=u64}`, size 40, align 8, "
            "`repr=None`. The model side's `u8` tag exists only through "
            "`canonical_tag_repr()`'s `smallest_for` fallback, and the emitted "
            "`Level` bodies read `extractfield u8 %v, 0` and switch on "
            "discriminant VALUES 0..4 — so the text form and the layout "
            "descriptor disagree about where that number lives. The "
            "disagreement is printed, not smoothed; the chain still stands on "
            "the model's tag encoding for `Level`, unproved. Stage 2 made the "
            "assumption source-guaranteed for the three FIELDLESS enums (a "
            "`repr(u8)` fieldless enum IS a `u8`); `Level` is not one of them, "
            "and its repr flip stays a separate differentially-gated change."
        ),
        "probe": "grep -n 'is NICHE-encoded' docs/CRYSTAL_STATUS.md",
        "probe_kind": "citation",
        "discharge": (
            "land the `Level` repr flip as a differentially-gated subject "
            "change (R4: it ships as the kernel, passes corpus verdict-parity "
            "and re-earns every affected chain), or prove the niche encoding "
            "and the model's tag agree at every constructor."
        ),
        "sources": [
            {"path": STATUS_DOC, "anchor": "beside the niche-encoding one"},
            {"path": STATUS_DOC,
             "anchor": "`Niche{untagged=4 (Param), niche_variants=0..=3, niche_start=3, niche_offset=0,"},
        ],
    },
    {
        "id": "A-PSM-STACK-SAFE-BRACKET",
        "class": "operational-contract",
        "origin": "seeded",
        "status": "prospective",
        "date": "2026-08-22",
        "owning_job": "T-CTRL / K-STACK (§3.3)",
        "statement": (
            "PROSPECTIVE — planned, not live. §3.3 adopts K-STACK's "
            "single-bracket route for `stack_safe` and rules that either way "
            "\"the psm boundary is a named ledger entry, never silently inside "
            "a proof\"; T-CTRL's exit requires the entry to exist with its "
            "probe, stating `stack_safe(f) ≡ f()` at the bracket, "
            "differentially probed. The surface it will cover, measured at the "
            "recon: 15 non-test spine `stack_safe` sites (infer.rs:259,305,778, "
            "825,829; whnf.rs:194,342; whnf_proj.rs:46,56,99,117; "
            "def_eq/mod.rs:237,254; proof_irrel.rs:129), which are "
            "`stacker::maybe_grow` → psm FFI stack switching. NO CHAIN STANDS "
            "ON THIS CONTRACT TODAY: the job has not run, no spine body with a "
            "`stack_safe` site is chained, and the contract's exact statement "
            "is fixed by K-STACK's outcome, not by this row. Excluded from "
            "`count` for exactly that reason."
        ),
        "probe": "grep -n 'stacker::maybe_grow' crates/clean-kernel/src/expr/mod.rs",
        "probe_kind": "citation",
        "discharge": (
            "K-STACK lands and this row is REPLACED by the live entry its exit "
            "mints (statement fixed by the route taken, probe differential) — "
            "which raises `count` by the number of live rows minted and lowers "
            "`prospective_count`. That is a rebase, and it is progress."
        ),
        "sources": [
            {"path": PROGRAM_DOC, "anchor": "`stack_safe(f) ≡ f()` at the bracket"},
            {"path": PROGRAM_DOC,
             "anchor": "the psm boundary is a named ledger entry, never silently inside a proof."},
            {"path": RECON_DOC, "anchor": "`stacker::maybe_grow` → **psm FFI** stack switching"},
            {"path": "crates/clean-kernel/src/expr/mod.rs",
             "anchor": "stacker::maybe_grow(MIN_STACK_RED_ZONE, STACK_GROWTH_SIZE, f)"},
        ],
    },
    {
        "id": "A-CACHE-MEMO-CONTRACT",
        "class": "operational-contract",
        "origin": "seeded",
        "status": "prospective",
        "date": "2026-08-22",
        "owning_job": "T-HASH(a) (§3.2)",
        "statement": (
            "PROSPECTIVE — planned, not live. §3.2 adopts Route B (model the "
            "caches, do not chase hashbrown/ahash) and T-HASH(a) fixes the "
            "contract for the PURE MEMOS — type_cache, infer_arc_memo (keyed on "
            "`Arc::as_ptr`), whnf_cache + whnf_core_cache, def_eq_cache, "
            "proj_type_cache, unfold_cache, quick_infer_cache, "
            "args_failure_cache — as \"hit ⇒ previously-computed value; miss ⇒ "
            "recompute\", to be discharged by a layer-2 memo-soundness theorem "
            "with a per-cache differential probe. T-HASH's exit is one ledger "
            "entry PER CACHE, so this single row is a placeholder for a set "
            "whose size the classification decides. NO CHAIN STANDS ON IT "
            "TODAY: no cache-touching spine body is chained. Excluded from "
            "`count`."
        ),
        "probe": "grep -n 'infer_arc_memo: RefCell::new(Default::default())' crates/clean-kernel/src/tc/config.rs",
        "probe_kind": "citation",
        "discharge": (
            "T-HASH classifies every spine cache (a)/(b) and mints one live "
            "ledger entry per cache with its differential probe; this row is "
            "replaced by that set."
        ),
        "sources": [
            {"path": PROGRAM_DOC, "anchor": "hit ⇒ previously-computed value; miss ⇒ recompute"},
            {"path": RECON_DOC, "anchor": "4. **Hash caches** — 10 on TypeChecker (type_cache, infer_arc_memo keyed on"},
            {"path": "crates/clean-kernel/src/tc/config.rs",
             "anchor": "infer_arc_memo: RefCell::new(Default::default())"},
        ],
    },
    {
        "id": "A-CACHE-UNIONFIND-CONTRACT",
        "class": "operational-contract",
        "origin": "seeded",
        "status": "prospective",
        "date": "2026-08-22",
        "owning_job": "T-HASH(b) (§3.2)",
        "statement": (
            "PROSPECTIVE — planned, not live. T-HASH(b) separates the "
            "equiv/sliding-equiv managers, which are UNION-FINDS and not memos, "
            "with the contract \"merge only on accepted def-eq; queries answer "
            "the reflexive-symmetric-transitive closure\". The spec-side "
            "theorem is closure soundness over semantic DefEq, and it is "
            "nontrivial for a stated reason: the budget makes the ACCEPT set "
            "non-transitive, so the theorem is about the semantic relation, not "
            "the accept set. NO CHAIN STANDS ON IT TODAY. Excluded from "
            "`count`."
        ),
        "probe": "grep -n 'Union-find equivalence manager' crates/clean-kernel/src/tc/equiv_manager.rs",
        "probe_kind": "citation",
        "discharge": (
            "T-HASH(b) discharges closure soundness over semantic DefEq for the "
            "equiv and sliding-equiv managers and mints the live entry (or "
            "closes the row outright if the theorem covers the managers "
            "whole)."
        ),
        "sources": [
            {"path": PROGRAM_DOC,
             "anchor": "only on accepted def-eq; queries answer the reflexive-symmetric-transitive"},
            {"path": RECON_DOC, "anchor": "**equiv_manager — a union-find, not a memo**"},
            {"path": "crates/clean-kernel/src/tc/equiv_manager.rs",
             "anchor": "Union-find equivalence manager for definitional equality caching."},
        ],
    },
]


# ------------------------------------------------------------------- plumbing


def _read_json(root, rel):
    path = os.path.join(root, rel)
    if not os.path.isfile(path):
        raise LedgerError("input missing: %s" % rel)
    try:
        with open(path, encoding="utf-8") as fh:
            doc = json.load(fh)
    except (OSError, ValueError) as exc:
        raise LedgerError("%s: unreadable (%s)" % (rel, exc))
    if not isinstance(doc, dict):
        raise LedgerError("%s: top level is not an object (schema drift)" % rel)
    return doc


def _sha256(root, rel):
    h = hashlib.sha256()
    with open(os.path.join(root, rel), "rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def _first_date(row):
    """The row's own date, from its text and its key names. Never invented."""
    haystack = []
    for key, val in row.items():
        haystack.append(key)
        if isinstance(val, str):
            haystack.append(val)
    joined = " ".join(haystack)
    m = _ISO_DATE.search(joined)
    if m:
        return m.group(1)
    m = _UNDERSCORE_DATE.search(joined)
    if m:
        return "%s-%s-%s" % m.groups()
    return UNDATED


def _anchors_of(row, rel):
    """`anchors: [{file, text}]` from a source artifact, as ledger sources."""
    anchors = row.get("anchors")
    if anchors is None:
        return []
    if not isinstance(anchors, list):
        raise LedgerError("%s: row %r has a non-list `anchors` (schema drift)"
                          % (rel, row.get("id")))
    out = []
    for a in anchors:
        if not isinstance(a, dict) or not isinstance(a.get("file"), str) \
                or not isinstance(a.get("text"), str):
            raise LedgerError(
                "%s: row %r has an anchor that is not {file, text} (schema drift)"
                % (rel, row.get("id")))
        out.append({"path": a["file"], "anchor": a["text"]})
    return out


# -------------------------------------------------------- derived: blind slots


def _validate_blind_slots(doc):
    slots = doc.get("slots")
    if not isinstance(slots, list) or not slots:
        raise LedgerError("%s: `slots` missing or empty (schema drift)" % BLIND_SLOTS_PATH)
    ids = []
    for slot in slots:
        if not isinstance(slot, dict):
            raise LedgerError("%s: a slot is not an object (schema drift)" % BLIND_SLOTS_PATH)
        for key in ("id", "kind", "slot", "artifact_carries", "core_carries",
                    "consequence", "read_by"):
            if not isinstance(slot.get(key), str) or not slot[key]:
                raise LedgerError("%s: slot %r has no usable `%s` (schema drift)"
                                  % (BLIND_SLOTS_PATH, slot.get("id"), key))
        ids.append(slot["id"])
    if len(ids) != len(set(ids)):
        raise LedgerError("%s: duplicate slot ids" % BLIND_SLOTS_PATH)
    return slots


def _erasure_entries(slots, align_restatements):
    entries = []
    for slot in slots:
        witness = slot.get("witness")
        residual = slot.get("residual")
        statement = (
            "The crystal-A2 mint erases this slot from the projected core "
            "module, and every chain minted through that projection stands, "
            "unproved, on the erasure being invisible to the value the module "
            "computes. SLOT: %s ARTIFACT CARRIES: %s CORE CARRIES: %s "
            "STATE IN THE OWNING ARTIFACT (%s): %s"
            % (slot["slot"], slot["artifact_carries"], slot["core_carries"],
               slot["kind"], slot["consequence"])
        )
        if isinstance(residual, str) and residual:
            statement += " RESIDUAL: %s" % residual
        if isinstance(witness, str) and witness:
            probe = BLIND_SLOT_TEST % witness
            defence = "witnessed — a test constructs the indistinguishable pair"
        else:
            probe = BLIND_SLOT_TEST % BLIND_SLOT_ANCHOR_TEST
            defence = ("unwitnessed — no test constructs the pair; the row's "
                       "only defence is the quoted source it anchors to")
        discharge = (
            "close the erasure in the ENCODING, not only at acceptance, and "
            "delete the slot from %s — a comparison or a refusal BOUNDS the "
            "slot, it does not remove it, which is why a slot recorded CLOSED "
            "still holds a ledger row." % BLIND_SLOTS_PATH
        )
        if isinstance(residual, str) and residual:
            discharge += " The slot's own residual states what that needs."
        entry = {
            "id": "A-ERASE-%s" % slot["id"],
            "class": "crystal-erasure-slot",
            "origin": "derived",
            "status": "measured",
            "statement": statement,
            "probe": probe,
            "probe_kind": "measurement",
            "discharge": discharge,
            "date": _first_date(slot),
            "owning_job": "crystal_a2_mint::blind_slots",
            "sources": _anchors_of(slot, BLIND_SLOTS_PATH),
            "derived_from": {"path": BLIND_SLOTS_PATH, "slot_id": slot["id"]},
            "slot_kind": slot["kind"],
            "defence": defence,
            "read_by": slot["read_by"],
            "live_on_chains": slot.get("live_on_chains", "UNSTATED"),
        }
        if entry["date"] == UNDATED:
            entry["date_reason"] = (
                "the slot carries no ISO date in any of its text or key names; "
                "a date is never invented here")
        if slot["id"] in align_restatements:
            entry["restated_in"] = align_restatements[slot["id"]]
        entries.append(entry)
    return entries


# --------------------------------------------------------- derived: the grid


def _validate_grid(doc):
    totals = doc.get("totals")
    rows = doc.get("rows")
    if not isinstance(totals, dict) or not isinstance(rows, list):
        raise LedgerError("%s: `totals` or `rows` missing (schema drift)" % ADEQUACY_GRID_PATH)
    for key in ("rows", "declared-delta", "audit-pin"):
        if not isinstance(totals.get(key), int):
            raise LedgerError("%s: totals.%s missing or not an int (schema drift)"
                              % (ADEQUACY_GRID_PATH, key))
    if totals["rows"] != len(rows):
        raise LedgerError("%s: totals.rows=%d but len(rows)=%d"
                          % (ADEQUACY_GRID_PATH, totals["rows"], len(rows)))
    deltas = [r for r in rows if isinstance(r, dict) and r.get("kind") == "delta"]
    pins = [r for r in rows if isinstance(r, dict) and r.get("state") == "audit-pin"]
    if len(deltas) != totals["declared-delta"]:
        raise LedgerError("%s: totals.declared-delta=%d but %d rows carry kind=delta"
                          % (ADEQUACY_GRID_PATH, totals["declared-delta"], len(deltas)))
    if len(pins) != totals["audit-pin"]:
        raise LedgerError("%s: totals.audit-pin=%d but %d rows carry state=audit-pin"
                          % (ADEQUACY_GRID_PATH, totals["audit-pin"], len(pins)))
    for row in deltas:
        for key in ("id", "constructor", "clean", "e2", "measured"):
            if not isinstance(row.get(key), str) or not row[key]:
                raise LedgerError("%s: delta row %r has no usable `%s` (schema drift)"
                                  % (ADEQUACY_GRID_PATH, row.get("id"), key))
    ids = [r["id"] for r in deltas]
    if len(ids) != len(set(ids)):
        raise LedgerError("%s: duplicate declared-delta ids" % ADEQUACY_GRID_PATH)
    return deltas, pins


_PIN_SLOT = re.compile(r"crystal_mint_blind_slots\.json slot id `([^`]+)`")


def _fold_audit_pins(pins, slot_ids):
    """The grid's audit-pin rows are RESTATEMENTS of a blind slot, not rows.

    Each must name the slot it defers to, and that slot must exist — otherwise
    an assumption would have two accounting points, or none.
    """
    folded = {}
    for row in pins:
        ledger = row.get("ledger")
        if not isinstance(ledger, str):
            raise LedgerError(
                "%s: audit-pin row %s.%s carries no `ledger` field naming its "
                "accounting point (schema drift) — an audit-pin row must defer "
                "to a blind slot or be a ledger row in its own right"
                % (ADEQUACY_GRID_PATH, row.get("constructor"), row.get("name")))
        m = _PIN_SLOT.search(ledger)
        if not m:
            raise LedgerError(
                "%s: audit-pin row %s.%s names no `crystal_mint_blind_slots.json "
                "slot id` in its `ledger` field: %r"
                % (ADEQUACY_GRID_PATH, row.get("constructor"), row.get("name"), ledger))
        slot_id = m.group(1)
        if slot_id not in slot_ids:
            raise LedgerError(
                "%s: audit-pin row %s.%s defers to blind slot %r, which does not "
                "exist in %s — the assumption would have NO accounting point"
                % (ADEQUACY_GRID_PATH, row.get("constructor"), row.get("name"),
                   slot_id, BLIND_SLOTS_PATH))
        folded.setdefault(slot_id, []).append({
            "path": ADEQUACY_GRID_PATH,
            "constructor": row.get("constructor"),
            "field": row.get("name"),
            "state": "audit-pin",
            "pinned_by": row.get("pinned_by", "UNSTATED"),
        })
    return folded


def _delta_entries(deltas):
    entries = []
    for row in deltas:
        statement = (
            "EvalIR's executable semantics and the pinned trust-ir reference "
            "interpreter DIVERGE on `%s`, and the encoding DECLARES the "
            "divergence rather than closing it. CLEAN: %s E2: %s MEASURED: %s"
            % (row["constructor"], row["clean"], row["e2"], row["measured"])
        )
        residue = row.get("residue")
        if isinstance(residue, str) and residue:
            statement += " RESIDUE: %s" % residue
        entries.append({
            "id": "A-DELTA-%s" % row["id"],
            "class": "evalir-declared-delta",
            "origin": "derived",
            "status": "measured",
            "statement": statement,
            "probe": GRID_PROBE,
            "probe_kind": "measurement",
            "discharge": (
                "close the divergence — model the refused fragment, or align "
                "the fault class — and delete the row from %s. The ratcheted "
                "count is `totals.declared-delta` there, published as the "
                "scoreboard row `evalir.adequacy.declared_delta` (direction "
                "down)." % ADEQUACY_GRID_PATH
            ),
            "date": _first_date(row),
            "owning_job": "B-SEM (§4(c) adequacy grid)",
            "sources": _anchors_of(row, ADEQUACY_GRID_PATH),
            "derived_from": {"path": ADEQUACY_GRID_PATH, "delta_id": row["id"]},
            "recorded_in": row.get("recorded_in", "UNSTATED"),
        })
    return entries


# ---------------------------------------------------------- cross-references


def _lane_b_reference(doc):
    ledger = doc.get("ledger")
    if not isinstance(ledger, dict):
        raise LedgerError("%s: no `ledger` block (schema drift)" % VERDICT_IO_PATH)
    count = ledger.get("row_count")
    rows = ledger.get("rows")
    if not isinstance(count, int) or not isinstance(rows, list):
        raise LedgerError("%s: ledger.row_count is not an int or ledger.rows is "
                          "not a list (schema drift)" % VERDICT_IO_PATH)
    if len(rows) != count:
        raise LedgerError("%s: ledger.row_count=%d but len(ledger.rows)=%d"
                          % (VERDICT_IO_PATH, count, len(rows)))
    ids = []
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("id"), str):
            raise LedgerError("%s: a ledger row carries no string `id` (schema drift)"
                              % VERDICT_IO_PATH)
        ids.append(row["id"])
    if len(ids) != len(set(ids)):
        raise LedgerError("%s: duplicate ledger row ids" % VERDICT_IO_PATH)
    ref = {
        "id": "XREF-VERDICT-IO-LANE-B",
        "path": VERDICT_IO_PATH,
        "block": "ledger",
        "row_count": count,
        "direction": ledger.get("direction", "UNSTATED"),
        "rows_by_class": ledger.get("rows_by_class", "UNSTATED"),
        "why_not_copied": (
            "Ring R2 lane (b) mints and ratchets its own §3.6 rows in its own "
            "artifact. Copying them here would give each assumption two "
            "accounting points and two ratchets; the env-bypass census follows "
            "the same rule. They are counted in the scoreboard by the separate "
            "row `assumption_ledger.verdict_io_lane_b`, which is disjoint from "
            "`assumption_ledger.count` by construction — this generator aborts "
            "if any id here collides with one there."
        ),
    }
    return ref, set(ids)


# ------------------------------------------------------------------ validation


def validate_entries(entries, root, slot_ids, delta_ids, lane_b_ids):
    """Fail-closed structural + citation + accounting checks on the row set."""
    if not entries:
        raise LedgerError("the ledger derived ZERO rows — that is schema drift, "
                          "not an empty ledger")
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise LedgerError("an entry is not an object (schema drift)")
        eid = entry.get("id")
        for key in REQUIRED_KEYS:
            val = entry.get(key)
            if key == "sources":
                if not isinstance(val, list) or not val:
                    raise LedgerError("entry %r has no `sources` — R8 requires "
                                      "every row to trace to a committed source" % eid)
            elif not isinstance(val, str) or not val:
                raise LedgerError("entry %r is missing `%s` — §3.6 requires "
                                  "statement, probe, discharge, date and owning "
                                  "job on every row" % (eid, key))
        if entry["class"] not in CLASSES:
            raise LedgerError("entry %r has class %r, which is not one this "
                              "ledger knows" % (eid, entry["class"]))
        if entry["status"] not in STATUSES:
            raise LedgerError("entry %r has status %r, which is not one this "
                              "ledger knows (%s)" % (eid, entry["status"],
                                                     "/".join(STATUSES)))
        if entry["probe_kind"] not in PROBE_KINDS:
            raise LedgerError("entry %r has probe_kind %r, which is not one this "
                              "ledger knows" % (eid, entry["probe_kind"]))
        if entry["origin"] not in ("derived", "seeded"):
            raise LedgerError("entry %r has origin %r (schema drift)"
                              % (eid, entry["origin"]))
        if eid in seen:
            raise LedgerError("duplicate ledger id %r" % eid)
        seen.add(eid)
        if eid in lane_b_ids:
            raise LedgerError(
                "ledger id %r collides with a row id in %s's lane-(b) ledger — "
                "one accounting point per assumption; cross-reference it, never "
                "copy it" % (eid, VERDICT_IO_PATH))
        _check_sources(entry, root)

    _check_derived_ids(entries, slot_ids, delta_ids)
    return seen


def _check_sources(entry, root):
    for src in entry["sources"]:
        if not isinstance(src, dict) or not isinstance(src.get("path"), str) \
                or not isinstance(src.get("anchor"), str) or not src["anchor"]:
            raise LedgerError("entry %r has a source that is not {path, anchor}"
                              % entry.get("id"))
        path = os.path.join(root, src["path"])
        if not os.path.isfile(path):
            raise LedgerError("entry %r cites %s, which does not exist — a row "
                              "whose source has vanished is not a row"
                              % (entry.get("id"), src["path"]))
        try:
            with open(path, encoding="utf-8") as fh:
                text = fh.read()
        except OSError as exc:
            raise LedgerError("entry %r cites %s, which is unreadable (%s)"
                              % (entry.get("id"), src["path"], exc))
        if src["anchor"] not in text:
            raise LedgerError(
                "entry %r cites %s for %r, which no longer occurs there VERBATIM "
                "— the row's citation has rotted"
                % (entry.get("id"), src["path"], src["anchor"][:80]))


def _check_derived_ids(entries, slot_ids, delta_ids):
    """A derived row must correspond to a live id in its source artifact."""
    for entry in entries:
        if entry["origin"] != "derived":
            continue
        origin = entry.get("derived_from")
        if not isinstance(origin, dict):
            raise LedgerError("derived entry %r carries no `derived_from` "
                              "(schema drift)" % entry.get("id"))
        if entry["class"] == "crystal-erasure-slot":
            key, universe, rel = "slot_id", slot_ids, BLIND_SLOTS_PATH
        elif entry["class"] == "evalir-declared-delta":
            key, universe, rel = "delta_id", delta_ids, ADEQUACY_GRID_PATH
        else:
            raise LedgerError("derived entry %r has class %r, which no producer "
                              "derives" % (entry.get("id"), entry["class"]))
        src_id = origin.get(key)
        if src_id not in universe:
            raise LedgerError(
                "derived entry %r claims to come from %s %s=%r, which is not in "
                "%s — a planted row, or a source row that vanished"
                % (entry.get("id"), rel, key, src_id, rel))


def check_arithmetic(doc):
    """The ledger's own counts must close, or none of it is quotable."""
    entries = doc.get("entries")
    if not isinstance(entries, list):
        raise LedgerError("`entries` is not a list (schema drift)")
    for key in ("count", "prospective_count", "row_count"):
        if not isinstance(doc.get(key), int):
            raise LedgerError("`%s` missing or not an int (schema drift)" % key)
    if doc["row_count"] != len(entries):
        raise LedgerError("row_count=%d but len(entries)=%d"
                          % (doc["row_count"], len(entries)))
    stray = [e.get("id") for e in entries
             if not isinstance(e, dict) or e.get("status") not in STATUSES]
    if stray:
        raise LedgerError("entries carry a status outside the vocabulary (%s): "
                          "%s — such a row would be counted by neither `count` "
                          "nor `prospective_count`"
                          % ("/".join(STATUSES), ", ".join(str(s) for s in stray)))
    live = sum(1 for e in entries if e.get("status") == "measured")
    prospective = sum(1 for e in entries if e.get("status") == "prospective")
    if doc["count"] != live:
        raise LedgerError("count=%d but %d entries carry status=measured"
                          % (doc["count"], live))
    if doc["prospective_count"] != prospective:
        raise LedgerError("prospective_count=%d but %d entries carry "
                          "status=prospective" % (doc["prospective_count"], prospective))
    if live + prospective != len(entries):
        raise LedgerError("count + prospective_count = %d != len(entries) %d — an "
                          "entry carries a status outside the vocabulary"
                          % (live + prospective, len(entries)))
    by_class = doc.get("counts_by_class")
    if not isinstance(by_class, dict) or sum(by_class.values()) != len(entries):
        raise LedgerError("counts_by_class missing, or its values do not sum to "
                          "len(entries) %d" % len(entries))
    by_origin = doc.get("counts_by_origin")
    if not isinstance(by_origin, dict) or sum(by_origin.values()) != len(entries):
        raise LedgerError("counts_by_origin missing, or its values do not sum to "
                          "len(entries) %d" % len(entries))


# --------------------------------------------------------------------- derive


def derive(root):
    slots_doc = _read_json(root, BLIND_SLOTS_PATH)
    grid_doc = _read_json(root, ADEQUACY_GRID_PATH)
    verdict_doc = _read_json(root, VERDICT_IO_PATH)

    slots = _validate_blind_slots(slots_doc)
    slot_ids = set(s["id"] for s in slots)
    deltas, pins = _validate_grid(grid_doc)
    delta_ids = set(d["id"] for d in deltas)
    folded = _fold_audit_pins(pins, slot_ids)
    lane_b_ref, lane_b_ids = _lane_b_reference(verdict_doc)

    entries = _erasure_entries(slots, folded)
    entries.extend(_delta_entries(deltas))
    entries.extend(copy.deepcopy(SEEDED_ENTRIES))

    validate_entries(entries, root, slot_ids, delta_ids, lane_b_ids)

    by_class = {}
    by_origin = {}
    by_status = {}
    for entry in entries:
        by_class[entry["class"]] = by_class.get(entry["class"], 0) + 1
        by_origin[entry["origin"]] = by_origin.get(entry["origin"], 0) + 1
        by_status[entry["status"]] = by_status.get(entry["status"], 0) + 1

    doc = {
        "schema": SCHEMA,
        "what": (
            "The §3.6 assumption ledger: every unproved thing a spine chain "
            "stands on, one row each, with a statement, a probe command, a "
            "discharge condition, a date and an owning job. "
            "designs/2026-08-22-spine-and-lattice-program.md §3.6 and standing "
            "rule R8."
        ),
        "not_claimed": (
            "This file is an INVENTORY OF STATED ASSUMPTIONS, not evidence that "
            "any of them is safe. A row's presence is a debt, not a discharge. "
            "A row carrying a witness is a BOUNDED assumption, not a closed "
            "one. And the ledger cannot be complete by construction: the "
            "derived classes are as complete as their source artifacts, and the "
            "seeded classes are as complete as the humans who wrote them down. "
            "docs/analysis/spine-assumption-ledger-2026-08-27.md states this at "
            "length."
        ),
        "counting_rule": (
            "`count` counts rows with status=measured — the debt standing "
            "today, and the number G-SCORE ratchets DOWN. `prospective_count` "
            "counts rows for assumptions of jobs that have NOT RUN; they are "
            "listed so §3.6's named contracts are visible, and excluded from "
            "`count` so a planned assumption never masquerades as a live one. "
            "A prospective row becoming live is a rebase of `count` upward, and "
            "it is progress."
        ),
        "count": by_status.get("measured", 0),
        "prospective_count": by_status.get("prospective", 0),
        "row_count": len(entries),
        "counts_by_class": by_class,
        "counts_by_origin": by_origin,
        "counts_by_status": by_status,
        "cross_references": [lane_b_ref],
        "entries": entries,
        "provenance": {
            "derived_by": "scripts/spine_assumption_ledger.py",
            "rule": (
                "derived rows: one per slot in %s (class crystal-erasure-slot) "
                "and one per kind=delta row in %s (class evalir-declared-delta), "
                "with statement, defence and residual quoted from the source and "
                "the date read off the source row's own text and key names, "
                "never invented. The grid's audit-pin rows are FOLDED onto the "
                "blind slot they name as `restated_in`, because the grid itself "
                "calls that slot 'the R8 ledger row' — one accounting point per "
                "assumption. seeded rows: SEEDED_ENTRIES in the generator, each "
                "with a citation whose anchor must occur verbatim; a checker "
                "cannot re-derive them and cannot notice a missing one. "
                "Fail-closed on schema drift, a rotted citation, a row missing "
                "its probe, a derived row with no live source id, an id "
                "colliding with the lane-(b) ledger, or arithmetic that does "
                "not close." % (BLIND_SLOTS_PATH, ADEQUACY_GRID_PATH)
            ),
            "derived_classes": ["crystal-erasure-slot", "evalir-declared-delta"],
            "seeded_classes": ["core-callee-model", "layout-obligation",
                               "operational-contract"],
            "inputs": [
                {"path": rel, "sha256": _sha256(root, rel)}
                for rel in (BLIND_SLOTS_PATH, ADEQUACY_GRID_PATH, VERDICT_IO_PATH)
            ],
            "consumers": [
                "scripts/spine_scoreboard.py (assumption_ledger.count, direction down)",
                "scripts/spine_gate.sh (S4 gate: printed with every entry probed) — not yet written",
            ],
        },
    }
    check_arithmetic(doc)
    return doc


def render(doc):
    return json.dumps(doc, indent=2, sort_keys=False) + "\n"


# ------------------------------------------------------------------ self-test


def self_test(root):
    failures = 0

    def arm(name, fn):
        nonlocal failures
        try:
            fn()
        except LedgerError as exc:
            print("  self-test ARM ok: %s -> detected (%s)" % (name, str(exc)[:150]))
            return
        print("  self-test ARM FAILED: %s -> mutation NOT detected" % name)
        failures += 1

    def ok(name, fn):
        nonlocal failures
        try:
            fn()
        except LedgerError as exc:
            print("  self-test ARM FAILED: %s -> unexpected refusal (%s)" % (name, exc))
            failures += 1
            return
        print("  self-test ARM ok: %s -> accepted" % name)

    slots_doc = _read_json(root, BLIND_SLOTS_PATH)
    grid_doc = _read_json(root, ADEQUACY_GRID_PATH)
    verdict_doc = _read_json(root, VERDICT_IO_PATH)
    slots = _validate_blind_slots(slots_doc)
    slot_ids = set(s["id"] for s in slots)
    deltas, pins = _validate_grid(grid_doc)
    delta_ids = set(d["id"] for d in deltas)
    lane_b_ref, lane_b_ids = _lane_b_reference(verdict_doc)

    baseline = derive(root)

    def entries_copy():
        return copy.deepcopy(baseline["entries"])

    def validate(entries):
        validate_entries(entries, root, slot_ids, delta_ids, lane_b_ids)

    # 1. A PLANTED EXTRA ROW: well-formed, cites a real anchor, claims to be
    #    derived from a slot that does not exist.
    def planted_extra():
        entries = entries_copy()
        template = copy.deepcopy(entries[0])
        template["id"] = "A-ERASE-planted-extra"
        template["derived_from"] = {"path": BLIND_SLOTS_PATH,
                                    "slot_id": "planted-extra"}
        entries.append(template)
        validate(entries)

    arm("planted extra derived row (no such slot)", planted_extra)

    # 1b. A planted extra SEEDED row is caught by the same door only if it lies
    #     about being derived; a genuinely new seeded row is a human act, and
    #     the ledger says so rather than pretending to detect it. What IS
    #     detected: a seeded row with a class no producer knows.
    def planted_unknown_class():
        entries = entries_copy()
        template = copy.deepcopy(entries[-1])
        template["id"] = "A-PLANTED-UNKNOWN-CLASS"
        template["class"] = "invented-class"
        entries.append(template)
        validate(entries)

    arm("planted row with an unknown class", planted_unknown_class)

    # 2. A ROW WHOSE CITED SOURCE VANISHED — both halves: the file is gone, and
    #    the file is there but the anchor text is not.
    def vanished_file():
        entries = entries_copy()
        entries[0]["sources"] = [{"path": "docs/NO_SUCH_FILE_HERE.md",
                                  "anchor": "anything"}]
        validate(entries)

    arm("cited source file vanished", vanished_file)

    def vanished_anchor():
        entries = entries_copy()
        entries[0]["sources"] = [{"path": STATUS_DOC,
                                  "anchor": "this sentence is not in the status page"}]
        validate(entries)

    arm("cited anchor no longer occurs verbatim", vanished_anchor)

    def no_sources():
        entries = entries_copy()
        entries[0]["sources"] = []
        validate(entries)

    arm("row with no cited source at all", no_sources)

    # 3. A ROW MISSING ITS PROBE (and, by the same door, its discharge/date).
    for missing in ("probe", "discharge", "date", "owning_job", "statement"):
        def drop(key=missing):
            entries = entries_copy()
            del entries[0][key]
            validate(entries)

        arm("row missing its `%s`" % missing, drop)

    def bad_probe_kind():
        entries = entries_copy()
        entries[0]["probe_kind"] = "vibes"
        validate(entries)

    arm("row with an unrecognised probe_kind", bad_probe_kind)

    # 4. COUNT / LEN DISAGREEMENT, in each of its shapes.
    def count_drift():
        doc = copy.deepcopy(baseline)
        doc["count"] += 1
        check_arithmetic(doc)

    arm("count != number of status=measured rows", count_drift)

    def row_count_drift():
        doc = copy.deepcopy(baseline)
        doc["row_count"] += 1
        check_arithmetic(doc)

    arm("row_count != len(entries)", row_count_drift)

    def prospective_drift():
        doc = copy.deepcopy(baseline)
        doc["prospective_count"] -= 1
        check_arithmetic(doc)

    arm("prospective_count != number of status=prospective rows", prospective_drift)

    def status_outside_vocabulary():
        doc = copy.deepcopy(baseline)
        doc["entries"][0]["status"] = "sort-of-measured"
        check_arithmetic(doc)

    arm("a row whose status is outside the vocabulary", status_outside_vocabulary)

    def class_split_drift():
        doc = copy.deepcopy(baseline)
        first = sorted(doc["counts_by_class"])[0]
        doc["counts_by_class"][first] += 1
        check_arithmetic(doc)

    arm("counts_by_class does not sum to len(entries)", class_split_drift)

    # 5. DOUBLE COUNTING against the lane-(b) ledger.
    def lane_b_collision():
        entries = entries_copy()
        entries[0]["id"] = sorted(lane_b_ids)[0]
        validate(entries)

    arm("id collides with a lane-(b) ledger row (double count)", lane_b_collision)

    def duplicate_id():
        entries = entries_copy()
        entries.append(copy.deepcopy(entries[0]))
        validate(entries)

    arm("duplicate ledger id", duplicate_id)

    # 6. THE AUDIT-PIN FOLD: a grid audit-pin row that defers to a slot which
    #    does not exist would leave its assumption with NO accounting point.
    def orphan_audit_pin():
        mutated = copy.deepcopy(pins)
        mutated[0]["ledger"] = ("data/crystal_mint_blind_slots.json slot id "
                                "`no-such-slot` — the R8 ledger row")
        _fold_audit_pins(mutated, slot_ids)

    arm("audit-pin row defers to a slot that does not exist", orphan_audit_pin)

    def unaccounted_audit_pin():
        mutated = copy.deepcopy(pins)
        del mutated[0]["ledger"]
        _fold_audit_pins(mutated, slot_ids)

    arm("audit-pin row names no accounting point", unaccounted_audit_pin)

    # 7. SOURCE-ARTIFACT SCHEMA DRIFT.
    def grid_total_drift():
        doc = copy.deepcopy(grid_doc)
        doc["totals"]["declared-delta"] += 1
        _validate_grid(doc)

    arm("grid totals.declared-delta disagrees with its rows", grid_total_drift)

    def slots_empty():
        doc = copy.deepcopy(slots_doc)
        doc["slots"] = []
        _validate_blind_slots(doc)

    arm("blind-slots artifact carries no slots", slots_empty)

    def lane_b_self_disagreement():
        doc = copy.deepcopy(verdict_doc)
        doc["ledger"]["row_count"] += 1
        _lane_b_reference(doc)

    arm("lane-(b) ledger disagrees with itself", lane_b_self_disagreement)

    # 8. The unmutated pipeline must pass every door.
    ok("baseline: the committed tree derives and validates", lambda: validate(entries_copy()))
    ok("baseline: the committed arithmetic closes", lambda: check_arithmetic(baseline))

    print("  self-test baseline: %d rows (%d measured, %d prospective); "
          "by class %s; by origin %s; lane (b) cross-referenced at %d rows"
          % (baseline["row_count"], baseline["count"],
             baseline["prospective_count"],
             json.dumps(baseline["counts_by_class"], sort_keys=True),
             json.dumps(baseline["counts_by_origin"], sort_keys=True),
             lane_b_ref["row_count"]))

    if failures:
        print("self-test: %d arm(s) FAILED" % failures, file=sys.stderr)
        return 1
    print("self-test: all arms green")
    return 0


# ----------------------------------------------------------------------- main


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="derive and fail if the committed artifact is stale")
    ap.add_argument("--self-test", action="store_true",
                    help="run the mutation arms")
    args = ap.parse_args(argv)

    if args.self_test:
        try:
            return self_test(REPO_ROOT)
        except LedgerError as exc:
            print("spine_assumption_ledger: self-test FAIL-CLOSED: %s" % exc,
                  file=sys.stderr)
            return 1

    try:
        doc = derive(REPO_ROOT)
    except LedgerError as exc:
        print("spine_assumption_ledger: FAIL-CLOSED: %s" % exc, file=sys.stderr)
        return 1

    out_path = os.path.join(REPO_ROOT, OUTPUT_PATH)
    rendered = render(doc)
    if args.check:
        try:
            with open(out_path, encoding="utf-8") as fh:
                committed = fh.read()
        except OSError:
            print("spine_assumption_ledger: --check: %s missing; run without "
                  "--check to mint it" % OUTPUT_PATH, file=sys.stderr)
            return 1
        if committed != rendered:
            print("spine_assumption_ledger: --check: %s is STALE; regenerate"
                  % OUTPUT_PATH, file=sys.stderr)
            return 1
        print("spine_assumption_ledger: %s up to date: %d rows "
              "(%d measured, %d prospective)"
              % (OUTPUT_PATH, doc["row_count"], doc["count"],
                 doc["prospective_count"]))
        return 0

    with open(out_path, "w", encoding="utf-8") as fh:
        fh.write(rendered)
    print("spine_assumption_ledger: wrote %s: %d rows (%d measured, %d "
          "prospective); by class %s"
          % (OUTPUT_PATH, doc["row_count"], doc["count"],
             doc["prospective_count"],
             json.dumps(doc["counts_by_class"], sort_keys=True)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
