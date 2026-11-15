#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Crystal link 3, per-call-site reconciliation: a fail-closed RATCHET.

WHAT IT MEASURES
    Link 3 is "the escaping edges close". The producer's manifest
    (`<dump>/callees/clean_kernel.callees.manifest.json`) reported 31 escaping
    rows, and that number rested on a check that could never fail: the
    intrinsic fold promoted every intrinsic call to a "terminal" when the
    module text did not contain `call @core::intrinsics::` (callee_sidecar.rs
    ~1174-1176 in the trust tree), a spelling the bridge never emits. The
    bridge lowers a missing callee as `assert false; undef` plus a
    `[trust-absent-callee-assumption]` obligation, so 111 of the 180 "promoted"
    intrinsic instances are havocs. See
    docs/handoff/2026-09-23-crystal-decision-memo.md, sections 1, 2 (B6) and 5.

    This script re-derives the ledger from the ARTIFACT, one MIR Call
    terminator at a time. It never trusts a count that the manifest reports.

HOW A SITE IS KEYED: (member, MIR basic block)
    * The manifest lists each member's calls in MIR block order, one row per
      Call/TailCall terminator (`extract_member` in callee_sidecar.rs pushes
      one MonoEdge per block, and the walk skips non-call blocks).
    * The module holds one `fn` per member, in `sidecar_func_id` order. Its
      block labels are the MIR block indices. Both facts are checked on every
      run, and a mismatch is a refusal.
    * Positive per-site EVIDENCE comes from the parsed module:
        - a `call @func.K` instruction in block bbN;
        - `call_indirect`;
        - a native op;
        - an obligation whose `source` is `mir-assert:<fn>:bbN:terminator`.
          The obligation's `function` index, the function NAME inside its
          `source`, the payload's `source_id` and any `site fK/bbN#j` must all
          agree, or the artifact is refused.
    * A v2 manifest's ordered call list is aligned to the ordered evidence
      sites by a longest-common-subsequence match over callee identity. Two
      outcomes are failures, never guesses:
        - a module site with strong evidence that no manifest row explains
          (counted in `unreconciled`);
        - a manifest row with no evidence anywhere. It stays ESCAPING and
          UNKEYED, with the admissible bb range reported.
    * Rule /3: a v3 manifest carries each row's MIR `bb`, and the row is KEYED
      by it. It must be explained by the evidence at exactly that block;
      evidence no row claims, and evidence at a row's block the row does not
      explain, are unreconciled. A row with no module trace at all (cold_path)
      is keyed by the producer's bb ALONE (`sites_keyed_by_producer_bb_only`):
      the ratchet accepts a producer KEY, checked for consistency, never a
      producer VERDICT.
    * Rule /4: the module may carry, AFTER its one `fn` per member, bodiless
      DECLARATIONS (`fn @<name>(functy.N) {` immediately followed by `}`): the
      bridge's `premise-decls` lane lowers a FOREIGN premise as a call to one
      instead of `assert false; undef` (memo D2). So #functions = #members +
      #declarations. Every declaration must be bodiless, unique by name, an
      `{extern#N}` foreign item, and called by at least one member; a body among
      the declarations or a bodiless member is a refusal, and so is any
      declaration in a module whose manifest's producer block does not name the
      `premise_decls` lane. A `call @func.K` whose K is a declaration is
      evidence `call_decl:<name>`, never a member call.
    * Rule /5: the bridge's "untypeable callable receiver" spelling of an absent-callee
      obligation (`[trust-absent-callee-assumption] indirect call `X` through an
      untypeable callable receiver (dyn/erased Fn*; callee unknown) may panic`, minted for
      a call through a dyn/erased `Fn*` receiver) names its callee `X` and is read exactly
      as `call to absent callee `X``. Before /5 an artifact carrying one was REFUSED as an
      unmodelled assumption; the MIR-encoded D3 arm is the first to reach one
      (`<&mut dyn FnMut() as FnOnce<()>>::call_once`, stacker's callback).
    * Rule /5: a native `cmpxchg` is evidence for the intrinsic of its OWN strength
      only: `cmpxchg weak` (trust-ir's `weak` flag) for `atomic_cxchgweak`, a plain
      `cmpxchg` for `atomic_cxchg`. A weak CAS modelled as strong deletes its
      spurious-failure executions, so neither may stand in for the other. The
      producer's evidence spelling (`native-op:cmpxchg`) does not distinguish them
      and is compared as before.
    * Rule /7 (crystal E3, 2026-09-24): a producer that ran the trust bridge's
      `abort-cleanup` lane (named in its producer block, `abort_cleanup`) lowers no
      unwind cleanup block, so a member's block labels -- still the MIR block indices,
      strictly increasing -- may SKIP, and the member's `mir_blocks` may exceed the blocks
      the module carries. Only such a manifest may carry a skipped label; no call row and
      no obligation may name a skipped block; a label past `mir_blocks` or a repeated one
      is refused as before. Every figure of an artifact with no skipped label is unchanged,
      so the rule version is not moved.
    * Rule /8 (crystal plan step 19, 2026-09-25): a producer that ran the trust bridge's
      `intrinsic-arms` lane (named in its producer block, `intrinsic_arms`) lowers a call to a
      modelled compiler intrinsic as its EXACT ARM instead of `assert false; undef`. Every
      instruction of an arm carries `custom(1900000+k)`, k the head's index in
      INTRINSIC_ARM_HEADS (the bridge's `ARM_HEADS`, same order). Such a site is
      `intrinsic-modelled` with evidence `exact-arm:<head>` only when, AT ITS BLOCK: the tagged
      instructions are one contiguous run carrying the tag of the row's OWN head; their opcode
      sequence is exactly that head's template at the run's width (`arm_template`); every
      opcode has a Clean image; no absent-callee obligation names the callee; a CHARGED head
      (`ctlz_nonzero`, `cttz_nonzero`, `exact_div`, `typed_swap_nonoverlapping`) also carries
      its `[trust-intrinsic-precondition] `X` requires ..` obligation; and `compare_bytes`'s one
      tagged instruction calls a SUPPLIED body. A tag anywhere else, a template that does not
      match, a missing charge, and a tag from a producer that does not name the lane are
      unreconciled or refused, never credited. The module may then carry, after the members and
      before any declaration, SUPPLIED intrinsic bodies (`; #producer: trust-intrinsic-arm`):
      each named exactly a core intrinsic whose body the lane supplies (`compare_bytes`),
      unique, called by a member, with no call, no obligation and only projectable opcodes.
      Such a body is neither a member nor a declaration, and a call to it is evidence
      `call_supplied`. A /7 artifact carries no tag, no supplied body and no lane, so it
      measures identically.
    * Rule /9 (crystal D10, decision memo §15, 2026-09-25): a NATIVE atomic op the Clean
      projector images by SEQUENTIAL EXPANSION (`scripts/crystal_a2_project` `fn
      seq_atomic_image`: atomicrmw xchg/add/sub/and/or/xor, strong cmpxchg, atomic_load,
      atomic_store, fence) is exact only under the ENVIRONMENT premise SEQ (`SEQ_PREMISE`): its
      site is classified `atomic-seq-premise` -- a PREMISE site, counted like a foreign
      terminal under `closed_under(P)` and never under `closed` -- instead of escaping as
      `intrinsic-unprojectable`. An atomic the image does not compute (a max/min rmw, a weak
      cmpxchg) stays `intrinsic-unprojectable`. This moves sites on EVERY artifact, so it is not
      a pure refinement: the /8 -> /9 migration is a DECLARED RECLASSIFICATION
      (`RULE_RECLASSIFICATIONS`), accepted only when the baseline's own artifact reproduces its
      site table EXACTLY once the declared move is undone, and no ratcheted figure rises.
    * Rule /10 (crystal D1, 2026-09-25): a markerless `call_indirect` (rule /6) is admitted only
      when, in addition, the member's indirect rows name the SAME targets by an unambiguous tiling
      of member names (names contain ", ", so a split is never trusted), every target is declared
      at the call's own functy DEFINITION and the call passes that functy's arity -- the bridge's
      exactness claim, re-derived, since EvalIR binds arguments positionally. A call shaped as the
      trust sidecar's `shim-adapter` (the unit environment `const () phantomdata`, then the
      argument tuple as one `insertfield` per lane over a typed `const (..) {..}` seed, each lane
      written once) is admitted only from a producer naming that lane, and counted in the
      informational `indirect_sites_dispatched_through_shim_adapter`. A manifest's `tls_cells` rows
      (lane `tls-cells`, decision D11) are validated -- the lane named, `certified` the conjunction
      of its three facts -- and the TLS INPUT premise's ops counted (information: the op is not a
      call site). A /9 artifact carries the marker before every call_indirect and no rows, so /10
      is a pure refinement on it.
    * Rule /11 (decision memo §18, 2026-09-25): (a) a `ub-terminal` row is evidenced only when the
      bridge's `reaching `X` is undefined behavior` obligation SITES (`site f<fn>/bb<k>#<i>`) the
      halting `assert` of a `const bool false` bound before it in that block -- the node the Clean
      projector's `fn ub_halt_image` images as `unreachable` (ub; E2's sanctioned-panic arm refuses
      it), never the sanctioned-panic `assert` a false assert elsewhere in the block would be.
      (b) Crystal D13: SUPPLIED ABI thunks (`; #producer: "trust-abi-thunk"`, the trust sidecar's
      `fnptr-thunks` lane) may follow the supplied intrinsic bodies, admitted only from a producer
      naming the lane, each checked to be EXACTLY the rust-call spread of one member shim
      (`_check_abi_thunk`); a markerless call_indirect whose enumerated targets are such shims is
      admitted THROUGH their thunks when every thunk is declared at the call's functy and no
      `fndef<func.K>` names a shim K as a value, and counted in the informational
      `indirect_sites_dispatched_through_abi_thunk`. A /10 artifact carries no thunk and the bridge
      sites every UB halt obligation at its halting assert, so /11 is a pure refinement on it.
    * Rule /3: when the producer declares `call_evidence`, every intrinsic
      row's `evidence` is RE-DERIVED here from the module (`derived_site_evidence`)
      and a disagreement is unreconciled; its `Intrinsic` escaping rows must be
      exactly the trust-ir-rule set the sites give, and are never counted on top
      of the site-derived intrinsic figures. A `subsumed: reached from <parent>`
      root is credited only after `_subsumed_root_defect` verifies it (member
      id, Item body, instance path, uniqueness, and the parent's member edge).

SYMBOLS (C-M0, 2026-09-27; decision memo §21)
    A `fn` header's name is read by `scripts/crystal_trust_ir_symbols.py`, the ONE symbol reader
    this script shares with link 4. trust-ir's WS4.3 printer (first in a crystal dump at trust-ir
    `dcc5b9a3`, Trust main `909cd903f0`) prints a non-bare name QUOTED (`fn @"..."`, with its own
    escapes) and a bare-alphabet one bare; every earlier producer printed every name raw. A module
    holding both a quoted and a raw (unquoted, non-bare) name is REFUSED -- no trust-ir printer
    writes one. This changes no rule: a legacy module reads byte-for-byte as before, and the same
    bundle printed either way measures identically (self-test arms 125-129). Before it, all three
    M0 arms were REFUSED, exit 2 (`function 0 is '"clean_kernel::...`).

CLASSIFICATION (each Call terminator is exactly one of)
    member-call       `call @func.K` naming the manifest's resolved member
    panic-terminal    obligation "panic call `X` must be unreachable" at the
                      site, and the block ends `assert false; unreachable`
    ub-terminal       (rule /5) the same halt for a call whose EXECUTION is undefined
                      behavior (`unreachable_unchecked`): obligation "reaching `X` is
                      undefined behavior; this program point must be proven
                      unreachable" plus the halting `assert false`. The trust sidecar
                      and bridge decide both halts with ONE predicate,
                      `trust_types::callee_class::call_site_halt`, over the same
                      name and the same site divergence; the manifest lists both
                      kinds in `panic_terminals`
    foreign-terminal  absent-callee obligation naming an entry of
                      `foreign_terminals` whose def path is an `{extern#N}`
                      foreign item (the manifest's word alone is never a
                      premise). This is a PREMISE. While it is
                      lowered as `assert false; undef` rather than as a
                      declared bodiless call (memo D2), it is also counted in
                      `premise_sites_lowered_as_havoc`. Rule /4: the site is a
                      premise LOWERED AS A CALL (`premise_sites_lowered_as_call`,
                      info) only when its block ALSO holds `call @func.K` to the
                      bodiless declaration of that same name and NO halting
                      `assert <const false>`; the obligation is still required,
                      because it is what names and keys the premise. A declared
                      call without the obligation is no premise at all.
    foreign-callback-terminal  (rule /5) a foreign-terminal site whose manifest row is
                      classed `foreign-callback-terminal: <callee>` -- the trust
                      sidecar's `foreign-callback` lane: the callee is a foreign
                      item whose SIGNATURE takes a function pointer, so it
                      re-enters the Rust program. Same evidence as a foreign
                      terminal (the absent-callee obligation; rule /4's declared
                      call), and additionally: the manifest's `foreign_callbacks`
                      row for the callee carries a CONTRACT (data, not proved),
                      the row names this site (member, bb), and every callback it
                      lists is a member. Counted SEPARATELY from
                      `foreign-terminal`: its premise is weaker than a plain
                      foreign symbol's, because the bundle's own code runs inside
                      it. A callee the producer kept escaping (no contract) is an
                      escaping `foreign` row, never a premise.
    intrinsic-modelled  an intrinsic whose site carries a recognised native
                      lowering AND every opcode of that lowering has a Clean
                      IRInst image. The positive evidence must be at that
                      site. A missing obligation is NEVER evidence, and no
                      text match is evidence either.
    escaping          with a class:
        mir-unavailable / virtual / other: read from the manifest row the
                          site reconciles to;
        indirect:         `call_indirect` plus its obligation. Rule /6: a
                          `call_indirect` whose block holds NO `assert <const
                          false>` dispatches BY VALUE (the trust sidecar's
                          `indirect-by-value` lane). It stays `indirect` and is
                          additionally counted in the informational
                          `indirect_sites_dispatched_by_value`, and it is admitted
                          only from a manifest whose producer names that lane and
                          whose indirect row(s) for the member state an all-member,
                          scan-complete enumeration; anything else is REFUSED;
        intrinsic-havoc:  an absent-callee obligation names the intrinsic;
        intrinsic-unprojectable: a native op models it in trust-ir (the
                          atomics), but the op has no Clean IRInst image;
        intrinsic-unevidenced: no instruction at the site at all (for
                          example `cold_path`).
    A SILENT HAVOC is an escaping site whose only trace is an unannotated
    `undef` with no obligation. The three `String::clone` sites are this.

ESCAPING ROWS, three rules, all derived and all reported
    per_instance (THE RATCHET): the manifest's escaping rows, plus every
        intrinsic INSTANCE that has at least one site without Clean-projectable
        positive evidence.
    module_wide: the documented fail-closed rule ("one survivor refuses the
        whole promotion"). All intrinsic instances escape if any intrinsic site
        anywhere lacks that evidence.
    reviewers' rules (informational only):
        - an instance escapes only if an absent-callee obligation names it
          (this reproduces 142);
        - native trust-ir lowering counts as modelled, and an unevidenced
          site does not.

RATCHET SEMANTICS
    * Every figure in RATCHETED is a bad count: higher is worse.
    * Measured > baseline on any figure gives exit 1. So does an escaping
      callee absent from the baseline's pinned set, because a one-for-one swap
      leaves every count flat.
    * THE PIN IS KEYED MODULO IDENTITY HASHES (C-M0, 2026-09-27; memo §19 item 6,
      measured at §20). Rebuilding the sysroot renames every `__trust_args@<hex>`,
      `__trust_crate@<hex>::` and `<crate>[<hex>]` token while the program is the
      same, and the raw-name pin read each rename as a new escaping callee (33 on
      `m0off`, 18 on `m0on`, every one a rename). A callee is now compared by
      `crystal_trust_ir_symbols.canonical_identity`, which blanks the hex of exactly
      those three tokens and nothing else, and as a MULTISET: a name that
      canonicalises onto one the baseline already pins still fails if it raises
      that name's count, so an escape swapped for a second instance of a pinned
      callee is caught, not absorbed. What the key cannot see is by construction a
      swap between two instances printed identically but for their hashes. The
      same-artifact reproduction check still compares the RAW set, exactly.
    * The baseline carries a SEAL: a sha256 over its own canonical content.
      A hand edit that does not re-seal is refused.
    * The baseline records the artifact's sha256s. If the artifact is the same
      one, every figure and the site-table digest must REPRODUCE EXACTLY, so a
      re-sealed hand edit is refused in either direction.
    * Measured < baseline passes, with a PROGRESS line. `--rebase --reason ...`
      locks the new figures in, and it refuses to raise anything.
    * `--init --reason ...` writes a baseline only where none exists.

REVIEW 2026-09-23 (adversarial: "can it report FEWER escaping sites than the truth?")
    Three holes, each demonstrated on the real artifact before the fix, and the
    self-test arms 44-51 that pin them:
    * SUBJECT PIN. The baseline records the crate, the filter and the roots
      multiset. Another subject, or a lost root, FAILS. A roots list that had
      lost its six refused closures read as `refused_roots 6 -> 0` PROGRESS,
      and --rebase locked it in.
    * A silent-havoc block that no manifest row claims is unreconciled. A
      producer that forgot one String::clone call row read as PROGRESS.
    * A foreign terminal must be an `{extern#N}` item. Before this, relabelling
      an escaping callee as foreign dropped the headline figures, and it was
      caught only incidentally by premise_sites_lowered_as_havoc.
    Also: an unknown `[trust-*-assumption]` obligation is a refusal, never
    skipped. And `drop_glue_assumption_sites` is ratcheted SEPARATELY, outside
    the row figures: MIR Drop terminators are calls to drop glue that the walk
    never follows (extract_member records only Call/TailCall), and unproven glue
    lowers to a halting `assert false`.
    Residual limits (manifest-only knowledge, not derivable from the module):
    a call row with no module trace at all (cold_path); an escaping row with no
    call site (a reified fn pointer); a Drop lowered with no obligation; a
    panic terminal rests on the bridge's own panic obligation.

EXIT CODES
    0   pass, or progress that is not yet locked in
    1   ratchet failure: a regression, a swap, a baseline that does not
        reproduce or reseal, a rule-version mismatch, or a refused
        --rebase/--init
    2   refusal: a malformed or truncated artifact, or a missing or malformed
        baseline
    64  usage

USAGE
    python3.14 scripts/crystal_link3_reconcile.py
        uses the artifact paths recorded in the baseline
    python3.14 scripts/crystal_link3_reconcile.py --manifest M.json [--report R.json]
    python3.14 scripts/crystal_link3_reconcile.py --rebase --reason "why"
    python3.14 scripts/crystal_link3_reconcile.py --init --reason "why" --manifest M.json
    python3.14 scripts/crystal_link3_reconcile.py --self-test

Reads no Rust or Lean source. Its inputs are the manifest JSON and the
trust-ir TEXT module that the manifest names. It does not grep-count: it
parses both, with a full tokenizer for obligation lines.
"""
from __future__ import annotations

import argparse
import contextlib
import datetime as _dt
import hashlib
import io
import json
import os
import re
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
# The ONE reader of trust-ir's definition-site symbols (quoted since WS4.3), shared with link 4.
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports), and its registry row
# pins them, so a change to the shared symbol reader is R7-stale until the arms replay over it.
ANSWERS_PINNED_INPUTS = True
DEFAULT_BASELINE = REPO_ROOT / "data" / "crystal_link3_reconcile_baseline.json"

RULE_VERSION = "crystal-link3-reconcile/11"
BASELINE_SCHEMA = "crystal-link3-reconcile-baseline/2"
REPORT_SCHEMA = "crystal-link3-reconcile-report/3"
# A rule change changes what a figure MEANS, so a baseline cut under another rule is refused.
# The one sanctioned way across is a MIGRATION named here: `--rebase` re-measures the baseline's
# OWN artifact under this rule and requires every figure, the pinned escaping-callee set and the
# site-table digest to REPRODUCE EXACTLY -- the rule change is then a pure refinement on the old
# artifact, and the new artifact is compared as an ordinary ratchet. Anything else still needs
# `git rm` + `--init`, visible in review.
RULE_MIGRATIONS = {
    "crystal-link3-reconcile/2": (
        "/3 keys a v3 manifest's sites by the producer's MIR `bb` (verified against the block's "
        "module evidence), re-derives and cross-checks the producer's per-site intrinsic "
        "`evidence`, stops counting a manifest `Intrinsic` escaping row twice, and credits a "
        "`subsumed:` root only after verifying it; on a v2 manifest (the /2 baseline's artifact) "
        "none of these applies, so the old artifact must measure identically. The /4 step (see its "
        "own entry) applies to a /2 artifact exactly as to a /3 one: it has no declarations. The /5 step "
        "(see the /4 entry) likewise: a /2 artifact has no foreign-callback row and no weak cmpxchg"
    ),
    "crystal-link3-reconcile/3": (
        "/4 admits bodiless DECLARATIONS after the members (#functions = #members + #declarations; "
        "each bodiless, unique, an {extern#N} foreign item, called by a member) -- the trust bridge's "
        "`premise-decls` lane lowers a FOREIGN premise as `call @decl` instead of `assert false; undef` "
        "-- and counts a foreign-terminal site whose block holds that call and no halting assert as a "
        "premise lowered as a CALL, not in premise_sites_lowered_as_havoc. The site's classification "
        "is unchanged (foreign-terminal), so the site table is too. A /3 artifact carries no "
        "declaration, so it must measure identically. The /5 step (see the /4 entry) applies too: a /3 "
        "artifact has no foreign-callback row and no weak cmpxchg"
    ),
    "crystal-link3-reconcile/4": (
        "/5 admits the trust sidecar's `foreign-callback` lane -- a call row classed "
        "`foreign-callback-terminal: <callee>` (a foreign item whose signature takes a function pointer) "
        "is a PREMISE counted separately from `foreign-terminal`, only when the manifest's "
        "`foreign_callbacks` row carries a contract, names the site and lists member callbacks -- and "
        "keys native `cmpxchg` evidence by strength (`cmpxchg weak` is evidence for `atomic_cxchgweak` "
        "only, plain `cmpxchg` for `atomic_cxchg` only). A /4 artifact carries no foreign-callback row "
        "and no weak cmpxchg, and its strong cmpxchg sites are evidence exactly as before; /5 also reads "
        "the bridge's `indirect call `X` through an untypeable callable receiver` absent-callee spelling "
        "as naming X (a /4 run REFUSED an artifact carrying one, so no /4 baseline holds one), and reads "
        "a `ub-terminal` row (the sidecar's undefined-behavior halt, one predicate with the bridge's) "
        "evidenced by the bridge's `reaching `X` is undefined behavior` obligation, which /4 did not "
        "collect, so a /4 artifact holding one gains evidence and cannot reproduce. So a /4 "
        "artifact must measure identically. The /6 step (see the /5 entry) applies too: a /4 artifact "
        "carries no call_indirect without its marker"
    ),
    "crystal-link3-reconcile/5": (
        "/6 reads the trust sidecar's VALUE lanes (crystal plan step 18). A `call_indirect` whose block "
        "carries no `assert` of a `const bool false` (the bridge's fail-closed marker) dispatches BY "
        "VALUE, and it is admitted only from a manifest whose producer block names the "
        "`indirect-by-value` lane AND whose indirect row for that member states an enumeration that is "
        "all members and unmarked by the crate-wide scan; anything else is REFUSED. Such a site keeps "
        "its `indirect` classification (it is still escaping for `closed`) and is also counted in the "
        "informational `indirect_sites_dispatched_by_value`. Every /5 artifact carries the marker in "
        "front of every call_indirect (memo B6, measured), so it must measure identically"
    ),
    "crystal-link3-reconcile/6": (
        "/7 admits a module whose block labels SKIP (crystal E3): the trust bridge's `abort-cleanup` "
        "lane lowers no unwind cleanup edge, so a member's cleanup blocks are unreachable and are not "
        "lowered, and the labels (still MIR block indices) may then have holes. /7 accepts such a "
        "module only from a manifest whose producer block names `abort_cleanup`, and no row may be "
        "keyed to a skipped label; anything else is REFUSED. A /6 artifact has dense labels and no "
        "such lane, so it must measure identically"
    ),
    "crystal-link3-reconcile/7": (
        "/8 reads the trust sidecar's `intrinsic-arms` lane (crystal plan step 19): an intrinsic site "
        "lowered as its exact arm (instructions tagged custom(1900000+k), the head's template, only "
        "projectable opcodes, a charged precondition carried as its `[trust-intrinsic-precondition]` "
        "obligation, `compare_bytes` calling a supplied body) is `intrinsic-modelled` with evidence "
        "`exact-arm:<head>`, admitted only from a manifest whose producer names the lane; the module "
        "may carry supplied intrinsic bodies between the members and the declarations. /8 also images "
        "`ctpop` (the projector's U::CtPop). A /7 artifact carries no tag, no supplied body, no "
        "precondition obligation, no ctpop op and no lane, so it must measure identically"
    ),
    "crystal-link3-reconcile/8": (
        "/9 is crystal D10 (decision memo §15): a native atomic the Clean projector images by sequential "
        "expansion under the ENVIRONMENT premise SEQ is an `atomic-seq-premise` site (a premise, not "
        "escaping). NOT a pure refinement -- it is the declared reclassification in RULE_RECLASSIFICATIONS, "
        "checked on the baseline's own artifact"
    ),
    "crystal-link3-reconcile/9": (
        "/10 is crystal D1: a markerless call_indirect (rule /6) is admitted only when, in addition, every "
        "target its member's indirect row enumerates -- read by an UNAMBIGUOUS tiling of member names -- is "
        "a function whose declared functy DEFINITION equals the call's and the call passes that functy's "
        "arity (the bridge's exactness claim, re-derived); a call shaped as the trust sidecar's "
        "`shim-adapter` (the unit environment `const () phantomdata`, then the argument tuple as one "
        "`insertfield` per lane over a typed `const (..) {..}` seed, each lane written once) is admitted "
        "only from a producer naming that lane, and counted in `indirect_sites_dispatched_through_shim_"
        "adapter`; a manifest's `tls_cells` rows (lane `tls-cells`, decision D11) are validated and the "
        "TLS input premise's ops counted, information only. Every /9 artifact carries the marker in front "
        "of every call_indirect and no `tls_cells` rows, so it must measure identically"
    ),
    "crystal-link3-reconcile/10": (
        "/11 is decision memo §18. (a) A `ub-terminal` row's evidence moves to what the Clean projector "
        "images: the bridge's `reaching `X` is undefined behavior` obligation must SITE the halting "
        "`assert` of a `const bool false` bound before it in that block -- the node the projector's `fn "
        "ub_halt_image` images as `unreachable` (ub, refused by E2's sanctioned-panic arm), not merely "
        "stand beside some false assert. (b) Crystal D13: SUPPLIED ABI thunks (`; #producer: "
        "trust-abi-thunk`, the trust sidecar's `fnptr-thunks` lane) may follow the supplied intrinsic "
        "bodies, each checked to be EXACTLY the rust-call spread of one member shim, and a markerless "
        "call_indirect whose enumerated targets are shims is admitted through their thunks when each "
        "thunk is declared at the call's functy and no constant names a shim as a value; counted in "
        "`indirect_sites_dispatched_through_abi_thunk`. Every /10 artifact carries no thunk, and the "
        "bridge sites every UB halt obligation at its halting assert, so it must measure identically"
    ),
}
# A rule step that MOVES sites between classes cannot reproduce its predecessor's figures, so it is
# declared here: target rule -> the classification it introduces -> the (classification,
# escaping_class) that site had under the rule before. `migration_check` then requires the baseline's
# OWN artifact, re-measured, to reproduce the baseline's site-table digest EXACTLY once each declared
# move is undone -- every site that did not move is identical, and every site that moved was exactly
# the declared old class -- and no ratcheted figure may rise. Anything else still needs git rm + --init.
RULE_RECLASSIFICATIONS = {
    "crystal-link3-reconcile/9": {"atomic-seq-premise": ("escaping", "intrinsic-unprojectable")},
}
# The callee-sidecar manifest schemas this script reads, keyed on the manifest's own
# `schema` field. v3 (trust callee_sidecar.rs, 2026-09-24) adds a `bb` on every call row
# (the MIR basic block of the call terminator), a `mir_digest` on every member, and the
# top-level `fuel` / `fuel_exhausted`; v2 stays readable for the artifacts cut before it.
# A manifest that CLAIMS v3 and lacks one of those, or carries it malformed, is REFUSED.
# Rule /3 READS the v3 `bb`: every call row of a v3 manifest is keyed by its own bb and must be
# explained by the module evidence AT that block; module evidence no row claims, and evidence
# at a row's block the row does not explain, are unreconciled. A row with no module trace at
# all (`cold_path`) is keyed by the producer's bb alone -- the ratchet accepts a producer KEY,
# checked for consistency, but never a producer VERDICT (see `sites_keyed_by_producer_bb_only`).
# A v3 manifest whose producer block declares `call_evidence` carries a per-site `evidence` on
# every `intrinsic-terminal` call row; this script RE-DERIVES each one and fails on any
# disagreement, so the producer does not certify itself.
MANIFEST_SCHEMA_V2 = "trust-ir-callee-sidecar-v2"
MANIFEST_SCHEMA_V3 = "trust-ir-callee-sidecar-v3"
MANIFEST_SCHEMAS = (MANIFEST_SCHEMA_V2, MANIFEST_SCHEMA_V3)
# `ProofDigest`'s display form. The all-zero digest is Trust's "no digest" value (and the
# placeholder its own layout fixture carries), so it is refused as a member's digest.
_MIR_DIGEST_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_ZERO_MIR_DIGEST = "sha256:" + "0" * 64
# The producer's per-site intrinsic evidence vocabulary (trust callee_sidecar.rs `SiteEvidence`).
_EVIDENCE_RE = re.compile(r"^(?:native-op:[a-z_]+|exact-arm:[a-z_]+|absent-callee-havoc|no-trace|member-not-lowered|block-map-unavailable)$")
SUBSUMED_PREFIX = "subsumed: reached from "
MODULE_HEADER = "; TrustIr text format v1"

EXIT_OK, EXIT_FAIL, EXIT_REFUSE, EXIT_USAGE = 0, 1, 2, 64

# Bad counts. Each one is compared <= baseline.
RATCHETED = (
    "escaping_rows_per_instance",
    "escaping_rows_module_wide",
    "escaping_call_sites",
    "silent_havoc_call_sites",
    "unkeyed_call_sites",
    "refused_roots",
    "premise_sites_lowered_as_havoc",
    "unreconciled",
    # Review 2026-09-23: MIR `Drop` terminators are calls to `drop_in_place::<T>` that the
    # walk never follows (extract_member pushes MonoEdge::None for every non-Call
    # terminator), and the bridge lowers unproven glue as a HALTING `assert false`. They are
    # outside the 142/211 row figures by definition, so they are ratcheted separately
    # instead of being silently absent.
    "drop_glue_assumption_sites",
)

# Text opcodes that have a Clean IRInst image. Provenance: the match arms of
# scripts/crystal_a2_project/src/main.rs (~1051-1260), whose fallback is
# "no Clean IRInst image for trust_ir::Inst::{}", together with IRInst in
# crates/clean-verify/src/spec/core_spec/eval_ir_syntax.rs.
# Used only to decide whether a recognised native intrinsic lowering can be
# projected. An opcode missing from this list counts as NOT projectable,
# which fails closed.
CLEAN_PROJECTABLE_OPS = frozenset(
    {
        "const", "br", "condbr", "switch", "ret", "unreachable", "call", "call_indirect",
        "load", "store", "alloca", "gep", "borrow", "copy", "extractfield", "insertfield",
        "extractelement", "global_addr", "undef", "assert", "select", "icmp", "fcmp",
        "ptr_data", "ptr_metadata", "ptr_from_parts",
        "bitcast", "zext", "sext", "trunc", "inttoptr", "ptrtoint",
        "add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "and", "or", "xor",
        "band", "bor", "shl", "lshr", "ashr", "not", "neg",
        # Rule /8: the projector images `U::CtPop => "ctpop"` (scripts/crystal_a2_project/src/ops.rs),
        # onto Clean's IRUnOp.ctpop (eval_ir_ops.rs `ir_ctpop_eval`).
        "ctpop",
    }
)
ATOMIC_OPS = frozenset({"atomicrmw", "cmpxchg", "fence", "atomic_load", "atomic_store"})
# Rule /8 (crystal plan step 19): the trust bridge's `intrinsic-arms` lane. The tag of head k is
# `custom(INTRINSIC_ARM_TAG_BASE + k)`; this tuple is trust-ir-bridge `lower/intrinsic_arms.rs`
# `ARM_HEADS`, in the SAME order (appending is the only safe edit on either side).
INTRINSIC_ARM_TAG_BASE = 1_900_000
INTRINSIC_ARM_HEADS = (
    "saturating_add", "saturating_sub", "rotate_left", "ctpop", "ctlz", "ctlz_nonzero", "cttz",
    "cttz_nonzero", "exact_div", "select_unpredictable", "assert_inhabited", "cold_path",
    "compare_bytes", "typed_swap_nonoverlapping", "size_of_val", "align_of_val",
)
# Heads whose undefined-behaviour precondition an arm CHARGES (`udiv T 1, m`), each with its
# `[trust-intrinsic-precondition]` obligation at the site. `size_of_val` is charged only in its
# slice-tail form (`arm_charged`): a sized `T`'s size is a constant with nothing to violate.
CHARGED_ARM_HEADS = frozenset({"ctlz_nonzero", "cttz_nonzero", "exact_div", "typed_swap_nonoverlapping"})
# Heads whose body the lane SUPPLIES as a module function (`; #producer: trust-intrinsic-arm`).
SUPPLIED_ARM_HEADS = frozenset({"compare_bytes"})
# As the trust-ir printer spells `Producer::Other("trust-intrinsic-arm")` (quoted, unlike the
# stable vocabulary's bare `trust-ir`).
SUPPLIED_PRODUCER = '"trust-intrinsic-arm"'
# Rule /11 (crystal D13): a SUPPLIED ABI thunk's producer stamp and name suffix (trust-ir-bridge
# `lower/abi_thunks.rs`).
THUNK_PRODUCER = '"trust-abi-thunk"'
THUNK_SUFFIX = "#trust-abi-thunk"
_ARM_TAG_RE = re.compile(r"\bcustom\((\d+)\)")
_PRECOND_RE = re.compile(r"^\[trust-intrinsic-precondition\] `([^`]*)` requires ")
_ARM_WIDTH = {"u8": 8, "u16": 16, "u32": 32, "u64": 64, "usize": 64}
# Rule /9 (crystal D10, decision memo §15): the native atomics the Clean projector images by
# SEQUENTIAL expansion (scripts/crystal_a2_project `fn seq_atomic_image`), and the premise under which
# that image is exact. An atomicrmw is imaged only for these ops; a weak cmpxchg never.
SEQ_IMAGED_ATOMIC_OPS = frozenset({"atomicrmw", "cmpxchg", "atomic_load", "atomic_store", "fence"})
SEQ_RMW_OPS = frozenset({"xchg", "add", "sub", "and", "or", "xor"})
SEQ_PREMISE = ("SEQ: no other thread writes a memory cell that a native atomic instruction of the "
               "projected bodies reads or writes while the projected run is live, so each atomic "
               "instruction computes exactly its sequential image and every ordering and fence is vacuous")
# Decision D11 (memo §17): the INPUT premise under which the Clean projector images a certified
# `trust_rust.thread_local_addr` as the address of an input cell. The projector's `TLS_PREMISE`,
# verbatim in substance; information only here (the op is not a call site).
TLS_PREMISE = ("TLS: each distinct symbol of a trust_rust.thread_local_addr op names ONE thread-local static, "
               "certified by the callee sidecar's tls_cells row (unique symbol, pointer-free type, definitely "
               "!Sync); every evaluation during the projected run yields that static's instance on the running "
               "thread (non-null, dereferenceable, live, disjoint from every other allocation); its content "
               "when the run starts is an INPUT quantified over every value of its type, never its "
               "initializer; and no agent outside the run writes it while the run is live")
_ATOMICRMW_OP_RE = re.compile(r"^(?:%\d+(?:, %\d+)* = )?atomicrmw ([a-z]+) ")
# A foreign terminal is a PREMISE, and the bridge lowers it with the same
# `[trust-absent-callee-assumption]` obligation as a MIR-unavailable callee. So the manifest's
# `foreign_terminals` list would otherwise be the ONLY thing separating a premise from an
# escaping edge. A foreign item's def path has an `{extern#N}` segment right before its name
# (DefPathData::ForeignMod); a name without one is never accepted as a premise.
_FOREIGN_ITEM_RE = re.compile(r"\{extern#\d+\}::[^:]+$")
# Any `[trust-...-assumption]` obligation this script does not recognise is a refusal: a new
# assumption class must never be silently skipped by the parse.
_ASSUMPTION_TAG_RE = re.compile(r"^\[trust-[a-z0-9-]+-assumption\]")
_DROP_UNPROVEN_RE = re.compile(r"^\[trust-drop-glue-assumption\] drop glue for (?P<ty>.*) has unproven panic-freedom")


# Rule /5: trust-ir's `cmpxchg weak` spelling (display.rs `write_inst`: `cmpxchg weak <ty> ptr ..`).
_CMPXCHG_WEAK_RE = re.compile(r"^(?:%\d+(?:, %\d+)* = )?cmpxchg weak ")


def native_evidence_kind(head: str) -> str:
    """Rule /5: the evidence kind a native lowering of this intrinsic head must carry. A weak
    compare-exchange intrinsic is evidenced ONLY by a `cmpxchg weak`, and every other head only
    by a strong instruction: modelling a weak CAS as strong deletes its spurious failures."""
    return "native_op_weak" if head.startswith("atomic_cxchgweak") else "native_op"


def native_intrinsic_ops(head: str) -> frozenset[str] | None:
    """The native trust-ir opcode that lowers an intrinsic of this head, or None.

    A site counts as a native lowering only when its block carries exactly
    this opcode. The table is deliberately small. Any head that is not listed
    has no recognised lowering, and its sites stay unevidenced.
    """
    if head.startswith("atomic_cxchg"):
        return frozenset({"cmpxchg"})
    if head in ("atomic_fence", "atomic_singlethreadfence"):
        return frozenset({"fence"})
    if head == "atomic_load":
        return frozenset({"atomic_load"})
    if head == "atomic_store":
        return frozenset({"atomic_store"})
    if head in (
        "atomic_xadd", "atomic_xsub", "atomic_xchg", "atomic_and", "atomic_nand",
        "atomic_or", "atomic_xor", "atomic_max", "atomic_min", "atomic_umax", "atomic_umin",
    ):
        return frozenset({"atomicrmw"})
    return None


class Refusal(Exception):
    """The artifact or baseline cannot be read as what it claims to be. Exit 2."""


# ─────────────────────────────── artifact parsing ───────────────────────────────


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise Refusal(msg)


def load_manifest(path: Path) -> dict:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise Refusal(f"cannot read manifest {path}: {exc}") from exc
    try:
        m = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise Refusal(f"manifest {path} is not JSON (truncated?): {exc}") from exc
    _require(isinstance(m, dict), "manifest top level is not an object")
    _require(m.get("schema") in MANIFEST_SCHEMAS,
             f"manifest schema {m.get('schema')!r} is not one of {MANIFEST_SCHEMAS!r}")
    # Every key the verdict reads must be PRESENT and well typed. An absent key
    # is a refusal and never an empty list: "no `escaping` key" does not mean
    # "zero escaping".
    for key, ty in (
        ("roots", list), ("members", list), ("panic_terminals", list),
        ("foreign_terminals", list), ("escaping", list), ("closed", bool),
        ("closed_modulo_foreign", bool), ("lowering", str), ("artifacts", dict),
        ("crate", str), ("filter", str),
    ):
        _require(key in m, f"manifest has no `{key}` key (refusing; absent is not empty)")
        _require(isinstance(m[key], ty), f"manifest `{key}` is {type(m[key]).__name__}, "
                                         f"expected {ty.__name__}")
    _require(all(isinstance(r, str) for r in m["escaping"]), "manifest `escaping` holds a non-string")
    art = m["artifacts"]
    for key, ty in (("text", str), ("text_bytes", int)):
        _require(key in art and isinstance(art[key], ty), f"manifest artifacts.{key} missing or mistyped")
    _require(m["lowering"] == "ok",
             f"manifest lowering={m['lowering']!r}: the module does not carry every member, "
             f"so a per-site reconciliation keyed on sidecar_func_id is impossible (refusing)")
    v3 = m["schema"] == MANIFEST_SCHEMA_V3
    producer = m.get("producer")
    # The producer DECLARES per-site evidence by naming it; its presence is what separates a
    # manifest that carries `evidence` from an earlier v3 one that does not.
    has_evidence = v3 and isinstance(producer, dict) and "call_evidence" in producer
    m["_has_site_evidence"] = has_evidence
    # Rule /4: a producer that ran the trust bridge's `premise-decls` lane NAMES it in its producer
    # block (callee_sidecar.rs `PREMISE_DECLS_MEANING`); a module carrying declarations is admitted
    # only from such a manifest.
    m["_premise_decls"] = isinstance(producer, dict) and isinstance(producer.get("premise_decls"), str)
    # Rule /5: the `foreign-callback` lane is NAMED in the producer block, and exactly then the
    # manifest carries `foreign_callbacks` rows. Either without the other is a malformed artifact.
    fc_lane = isinstance(producer, dict) and isinstance(producer.get("foreign_callback"), str)
    _require(fc_lane == ("foreign_callbacks" in m),
             "manifest `foreign_callbacks` rows and the producer's `foreign_callback` lane must come "
             "together (one is present without the other) -- refusing")
    fc_rows: dict[str, dict] = {}
    if fc_lane:
        _require(isinstance(m["foreign_callbacks"], list), "manifest `foreign_callbacks` is not a list")
        for k, row in enumerate(m["foreign_callbacks"]):
            _require(isinstance(row, dict) and isinstance(row.get("callee"), str)
                     and isinstance(row.get("callback_param_types"), list)
                     and all(isinstance(t, str) for t in row["callback_param_types"])
                     and (row.get("contract") is None or isinstance(row.get("contract"), str))
                     and "contract" in row and isinstance(row.get("sites"), list),
                     f"foreign_callbacks row {k} is malformed")
            for site in row["sites"]:
                _require(isinstance(site, dict) and isinstance(site.get("member"), str)
                         and type(site.get("bb")) is int and isinstance(site.get("callbacks"), list)
                         and all(isinstance(c, str) for c in site["callbacks"]),
                         f"foreign_callbacks row {k} has a malformed site")
            _require(row["callee"] not in fc_rows, f"foreign_callbacks row {k} repeats its callee")
            fc_rows[row["callee"]] = row
    m["_foreign_callback_lane"] = fc_lane
    m["_foreign_callbacks"] = fc_rows
    # Rule /6: the trust sidecar's VALUE lanes are NAMED in the producer block (callee_sidecar.rs
    # `value_lanes_meaning`) whenever one was on; a call_indirect lowered without its marker is
    # admitted only when the named set includes `indirect-by-value`.
    value_lanes = producer.get("value_lanes") if isinstance(producer, dict) else None
    _require(value_lanes is None or isinstance(value_lanes, str),
             "manifest producer `value_lanes` is not a string -- refusing")
    m["_indirect_by_value_lane"] = isinstance(value_lanes, str) and "indirect-by-value:" in value_lanes
    # Rule /10 (crystal D1): the `shim-adapter` lane admits the call-site adapter; the `tls-cells`
    # lane writes the `tls_cells` rows D11's TLS input premise rests on. Rows without the lane
    # named, or malformed, are refused.
    m["_shim_adapter_lane"] = isinstance(value_lanes, str) and "shim-adapter:" in value_lanes
    # Rule /11 (crystal D13): the `fnptr-thunks` lane supplies ABI thunks.
    m["_fnptr_thunks_lane"] = isinstance(value_lanes, str) and "fnptr-thunks:" in value_lanes
    tls_rows = m.get("tls_cells")
    _require(tls_rows is None or (isinstance(value_lanes, str) and "tls-cells:" in value_lanes),
             "manifest carries `tls_cells` rows but its producer does not name the `tls-cells` lane -- refusing")
    tls_certified: set[str] = set()
    if tls_rows is not None:
        _require(isinstance(tls_rows, list), "manifest `tls_cells` is not a list")
        for k, row in enumerate(tls_rows):
            _require(isinstance(row, dict) and isinstance(row.get("symbol"), str)
                     and all(type(row.get(f)) is bool for f in
                             ("certified", "unique_symbol", "pointer_free", "definitely_not_sync")),
                     f"manifest tls_cells row {k} is malformed")
            _require(row["certified"] == (row["unique_symbol"] and row["pointer_free"]
                                          and row["definitely_not_sync"]),
                     f"manifest tls_cells row {k}: `certified` is not the conjunction of its three facts")
            if row["certified"]:
                tls_certified.add(row["symbol"])
    m["_tls_certified"] = tls_certified
    # Rule /7 (crystal E3): a producer that ran the trust bridge's `abort-cleanup` lane NAMES it in
    # its producer block (callee_sidecar.rs `ABORT_CLEANUP_MEANING`). That lane models no unwind
    # cleanup edge, so a member's cleanup blocks are unreachable and the bridge does not lower
    # them: the module's block labels (still the MIR block indices) may then SKIP. Only such a
    # manifest may carry a module with a skipped label, and no row may be keyed to one.
    m["_abort_cleanup"] = isinstance(producer, dict) and isinstance(producer.get("abort_cleanup"), str)
    # Rule /8 (crystal plan step 19): the `intrinsic-arms` lane is NAMED in the producer block
    # (callee_sidecar.rs `INTRINSIC_ARMS_MEANING`); only such a manifest may carry `exact-arm:`
    # evidence, and only its module may carry arm tags or supplied intrinsic bodies.
    m["_intrinsic_arms"] = isinstance(producer, dict) and isinstance(producer.get("intrinsic_arms"), str)
    if v3:
        # `type(x) is int` and not isinstance: a JSON `true` is a Python bool, which IS an int.
        _require(type(m.get("fuel")) is int and m["fuel"] >= 1,
                 "v3 manifest has no well-typed `fuel` (the member cap in effect) -- refusing")
        _require(type(m.get("fuel_exhausted")) is bool,
                 "v3 manifest has no well-typed `fuel_exhausted` -- refusing")
        _require(not (m["fuel_exhausted"] and m["closed"]),
                 "v3 manifest says `closed` with its member fuel exhausted -- contradictory, refusing")
    for i, mem in enumerate(m["members"]):
        _require(isinstance(mem, dict), f"member {i} is not an object")
        for key, ty in (("sidecar_func_id", int), ("name", str), ("mir_blocks", int),
                        ("extracted_blocks", int), ("calls", list)):
            _require(key in mem and isinstance(mem[key], ty), f"member {i} lacks `{key}`")
        _require(mem["sidecar_func_id"] == i, f"member {i} has sidecar_func_id {mem['sidecar_func_id']}")
        _require(mem["mir_blocks"] == mem["extracted_blocks"],
                 f"member {i} extracted {mem['extracted_blocks']} of {mem['mir_blocks']} MIR blocks")
        if v3:
            d = mem.get("mir_digest")
            _require(isinstance(d, str) and bool(_MIR_DIGEST_RE.match(d)) and d != _ZERO_MIR_DIGEST,
                     f"v3 member {i} has no well-formed `mir_digest` (sha256:<64 hex>, non-zero): {d!r}")
        prev_bb = -1
        for j, c in enumerate(mem["calls"]):
            _require(isinstance(c, dict) and all(isinstance(c.get(k), str) for k in ("site", "resolved", "class")),
                     f"member {i} call {j} is malformed")
            _require(fc_lane or not c["class"].startswith("foreign-callback-terminal"),
                     f"member {i} call {j} is classed foreign-callback-terminal, but the producer does not "
                     f"declare the `foreign_callback` lane -- refusing")
            if has_evidence and c["class"].startswith("intrinsic-terminal"):
                _require(isinstance(c.get("evidence"), str) and _EVIDENCE_RE.match(c["evidence"]) is not None,
                         f"member {i} call {j} is an intrinsic site of a manifest whose producer declares "
                         f"`call_evidence`, and carries no well-formed `evidence`: {c.get('evidence')!r} -- refusing")
                _require(not c["evidence"].startswith("exact-arm:") or m["_intrinsic_arms"],
                         f"member {i} call {j} carries `exact-arm:` evidence, but the producer does not "
                         f"declare the `intrinsic_arms` lane -- refusing")
            else:
                _require("evidence" not in c,
                         f"member {i} call {j} carries `evidence` where it has no meaning (not an intrinsic "
                         f"site, or the producer declares no `call_evidence`) -- refusing")
            if v3:
                # One call per MIR block and rows in block order, so the bbs strictly
                # increase and each names a block the member has.
                bb = c.get("bb")
                _require(type(bb) is int and prev_bb < bb < mem["mir_blocks"],
                         f"v3 member {i} call {j} has no `bb` in ({prev_bb}, {mem['mir_blocks']}): {bb!r}")
                prev_bb = bb
    for i, r in enumerate(m["roots"]):
        _require(isinstance(r, dict) and "outcome" in r and "resolved" in r
                 and isinstance(r.get("callee_def_path"), str) and isinstance(r.get("caller"), str),
                 f"root {i} is malformed")
        if isinstance(r["outcome"], str) and r["outcome"].startswith(SUBSUMED_PREFIX):
            _require(v3, f"root {i} is `subsumed` in a pre-v3 manifest -- refusing")
    return m


_OBL_KINDS_BAREWORD = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def _tokenize_obligation(line: str) -> list[tuple[str, bool]]:
    """Split an obligation line into (token, was_quoted). Quoted strings honour escapes."""
    toks: list[tuple[str, bool]] = []
    i, n = 0, len(line)
    while i < n:
        if line[i] == " ":
            i += 1
            continue
        if line[i] == '"':
            j = i + 1
            buf = []
            while True:
                if j >= n:
                    raise Refusal(f"unterminated quoted string in obligation line: {line[:120]!r}")
                ch = line[j]
                if ch == "\\":
                    if j + 1 >= n:
                        raise Refusal(f"dangling escape in obligation line: {line[:120]!r}")
                    nxt = line[j + 1]
                    buf.append({"n": "\n", "t": "\t", "r": "\r"}.get(nxt, nxt))
                    j += 2
                    continue
                if ch == '"':
                    break
                buf.append(ch)
                j += 1
            toks.append(("".join(buf), True))
            i = j + 1
            if i < n and line[i] != " ":
                raise Refusal(f"junk after quoted string in obligation line: {line[:120]!r}")
        else:
            j = line.find(" ", i)
            j = n if j < 0 else j
            toks.append((line[i:j], False))
            i = j
    return toks


_SRC_SITE_RE = re.compile(r"^mir-assert:(?P<fn>.*):(?P<bb>bb\d+):terminator$")
_SITE_FIELD_RE = re.compile(r"^f(?P<f>\d+)/(?P<bb>bb\d+)#(?P<k>\d+)$")
_ABSENT_RE = re.compile(r"call to absent callee `([^`]*)`")
# Rule /5: the bridge's OTHER spelling of the same absent-callee obligation, minted for a call
# through a dyn/erased `Fn*` receiver it cannot type (trust-ir-bridge lower.rs, the
# "untypeable callable receiver" arm: `assert false`, a havoc result, and this row under either
# absent-callee prefix). It names its callee exactly as the first spelling does, so it is read
# as that; any other `indirect call ..` wording under an assumption tag still refuses.
_ABSENT_DYN_RE = re.compile(r"^\[trust-(?:expected-)?absent-callee-assumption\] indirect call `([^`]*)` "
                            r"through an untypeable callable receiver \(dyn/erased Fn\*; callee unknown\) may panic$")
_PANIC_RE = re.compile(r"^panic call `([^`]*)` must be unreachable")
# Rule /5: the bridge's wording for the same halt at an undefined-behavior callee
# (trust-ir-bridge lower.rs, `CallHalt::UndefinedBehavior`).
_UB_RE = re.compile(r"^reaching `([^`]*)` is undefined behavior; this program point must be proven unreachable$")
_INDIRECT_RE = re.compile(r"^indirect call through fn-pointer ")


def parse_obligation(line: str) -> dict:
    """Grammar (every clause checked; an unknown clause is a refusal):

        obligation <int> <word> <word> "<desc>" function <int>
            formula "<format>" "<payload>" [smtlib "<s>" sort "<s>"]
            source "<source>" assertion "<assertion>" range <int> x5 [site f<int>/bb<int>#<int>]
    """
    t = _tokenize_obligation(line)
    pos = 0

    def take_word(word: str) -> None:
        nonlocal pos
        _require(pos < len(t) and t[pos] == (word, False),
                 f"obligation: expected `{word}` at token {pos}, got "
                 f"{t[pos][0][:40] if pos < len(t) else '<end>'!r}: {line[:120]!r}")
        pos += 1

    def take_quoted() -> str:
        nonlocal pos
        _require(pos < len(t) and t[pos][1], f"obligation: expected a quoted string at token {pos}: {line[:120]!r}")
        pos += 1
        return t[pos - 1][0]

    def take_int() -> int:
        nonlocal pos
        _require(pos < len(t) and not t[pos][1] and t[pos][0].isdigit(),
                 f"obligation: expected an integer at token {pos}: {line[:120]!r}")
        pos += 1
        return int(t[pos - 1][0])

    def take_bareword() -> str:
        nonlocal pos
        _require(pos < len(t) and not t[pos][1] and _OBL_KINDS_BAREWORD.match(t[pos][0]) is not None,
                 f"obligation: expected a bareword at token {pos}: {line[:120]!r}")
        pos += 1
        return t[pos - 1][0]

    take_word("obligation")
    oid = take_int()
    kind = take_bareword()
    status = take_bareword()
    desc = take_quoted()
    take_word("function")
    fid = take_int()
    take_word("formula")
    formula = take_quoted()
    payload = take_quoted()
    if pos < len(t) and t[pos] == ("smtlib", False):
        take_word("smtlib")
        take_quoted()
        take_word("sort")
        take_quoted()
    take_word("source")
    source = take_quoted()
    take_word("assertion")
    take_quoted()
    take_word("range")
    for _ in range(5):
        take_int()
    site = None
    site_index = None
    if pos < len(t):
        take_word("site")
        _require(pos < len(t) and not t[pos][1], f"obligation: site value missing: {line[:120]!r}")
        sm = _SITE_FIELD_RE.match(t[pos][0])
        _require(sm is not None, f"malformed site field {t[pos][0]!r}")
        site = (int(sm.group("f")), sm.group("bb"))
        site_index = int(sm.group("k"))
        pos += 1
    _require(pos == len(t), f"obligation: {len(t) - pos} trailing token(s): {line[:120]!r}")
    return {"id": oid, "kind": kind, "status": status, "desc": desc, "function": fid,
            "formula": formula, "payload": payload, "source": source, "site": site,
            "site_index": site_index}


# A `fn` header takes no calling-convention word here: any other prefix is an unrecognised line.
_FN_PREFIX = re.compile(r"")
_FUNCTY_DEF_RE = re.compile(r"^functy\.(?P<id>\d+) = (?P<def>.+)$")
_CALL_INDIRECT_FULL_RE = re.compile(
    r"^(?:(?P<res>%\d+(?:, %\d+)*) = )?call_indirect (?P<callee>%\d+)\(functy\.(?P<sig>\d+)\)"
    r"\((?P<args>(?:%\d+(?:, %\d+)*)?)\)(?: cc=\S+)?$")
_TLS_OP_PREFIX = ('dialect_op trust_rust.thread_local_addr() -> ptr '
                  '[schema=str:"trust-rust.thread-local-addr/v1"] [symbol=str:"')
_BLOCK_RE = re.compile(r"^bb(?P<n>\d+)(?:\(.*\))?:$")
_TOPLEVEL_OK = re.compile(
    r'^(?:;.*|module ".*"|file \d+ .*|struct .*|enum .*|global .*|type .*|closure_ty .*|functy\.\d+ .*)$'
)
_OPNAME_RE = re.compile(r"^(?:%\d+(?:, %\d+)* = )?([a-z_]+)\b")
_CALL_RE = re.compile(r"^(?:%\d+(?:, %\d+)* = )?call @(?P<callee>[^(]+)\(")
_CALL_INDIRECT_RE = re.compile(r"^(?:%\d+(?:, %\d+)* = )?call_indirect\b")
_UNDEF_RE = re.compile(r"^(?P<v>%\d+) = undef (?P<ty>.+)$")
_STORE_RE = re.compile(r"^store \S+ (?P<v>%\d+), ptr ")


def split_annotation(ins: str) -> tuple[str, str]:
    code, _sep, ann = ins.partition("  ; ")
    return code.strip(), ann.strip()


def opname(code: str) -> str | None:
    m = _OPNAME_RE.match(code)
    return m.group(1) if m else None


def parse_module(path: Path, expected_bytes: int) -> dict:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise Refusal(f"cannot read module {path}: {exc}") from exc
    _require(len(raw) == expected_bytes,
             f"module {path.name} is {len(raw)} bytes, the manifest records {expected_bytes} "
             f"(truncated or replaced; refusing)")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise Refusal(f"module is not UTF-8: {exc}") from exc
    lines = text.split("\n")
    _require(lines and lines[0] == MODULE_HEADER, f"module header is not {MODULE_HEADER!r}")
    funcs: list[dict] = []
    obligations: list[dict] = []
    functys: dict[int, str] = {}
    cur = None
    block = None
    spellings = tir_symbols.Spellings()
    for ln, line in enumerate(lines, 1):
        if cur is not None:
            if line == "}":
                # Rule /4: a function with no blocks is a bodiless DECLARATION. Whether one may
                # stand where it stands (only after the members, only for a foreign premise) is
                # decided in `reconcile`, which knows the member count; here it is only recorded.
                cur["decl"] = not cur["blocks"]
                cur = None
                block = None
                continue
            bm = _BLOCK_RE.match(line)
            if bm:
                block = int(bm.group("n"))
                if block == 0:
                    # Rule /11: the entry block's parameters, read by the ABI-thunk check.
                    cur["entry_params"] = re.findall(r"(%\d+):", line)
                # The labels ARE the MIR block indices, strictly increasing. A SKIPPED index is
                # a block the bridge did not lower; it is held as `None` and admitted only for a
                # manifest whose producer ran the `abort-cleanup` lane (rule /7, `reconcile`).
                _require(block >= len(cur["blocks"]),
                         f"line {ln}: block bb{block} out of order in {cur['name'][:80]} "
                         f"(labels must be the MIR block indices, increasing)")
                cur["blocks"].extend([None] * (block - len(cur["blocks"])))
                cur["blocks"].append([])
                continue
            _require(line.startswith("    "), f"line {ln}: unexpected text inside a function: {line[:100]!r}")
            s = line.strip()
            if s.startswith("; #producer:"):
                # Rule /8: the stamp separates a SUPPLIED intrinsic body from a member.
                cur["producer"] = s[len("; #producer:"):].strip()
                continue
            if not s or s.startswith(";"):
                continue
            _require(block is not None, f"line {ln}: instruction before the first block label")
            cur["blocks"][block].append(s)
            continue
        try:
            fh = tir_symbols.parse_fn_header(line, _FN_PREFIX)
            if fh is not None:
                spellings.note(fh[2], f"line {ln}")
        except tir_symbols.SymbolRefusal as exc:
            raise Refusal(f"line {ln}: {exc}") from exc
        if fh is not None:
            cur = {"name": fh[0], "blocks": [], "line": ln, "functy": fh[1]}
            funcs.append(cur)
            block = None
            continue
        fym = _FUNCTY_DEF_RE.match(line)
        if fym:
            _require(int(fym.group("id")) not in functys, f"line {ln}: functy.{fym.group('id')} defined twice")
            functys[int(fym.group("id"))] = fym.group("def")
        if line.startswith("obligation "):
            obligations.append(parse_obligation(line))
            continue
        if line == "":
            continue
        _require(_TOPLEVEL_OK.match(line) is not None, f"line {ln}: unrecognised top-level line {line[:100]!r}")
    _require(cur is None, f"module ends inside function {cur['name'][:80] if cur else ''} (truncated)")
    _require(funcs, "module has no functions")
    ids = [o["id"] for o in obligations]
    _require(ids == list(range(len(ids))), "obligation ids are not 0..n-1 (lines lost or reordered)")
    # Rule /11: every function a `fndef<func.K>` constant names as a VALUE, anywhere in the module.
    fndef_named = {int(k) for k in re.findall(r"\bfndef<func\.(\d+)>", text)}
    return {"funcs": funcs, "obligations": obligations, "sha256": hashlib.sha256(raw).hexdigest(),
            "bytes": len(raw), "functys": functys, "fndef_named": fndef_named}


# ─────────────────────────────── reconciliation ────────────────────────────────


def classify_row(row: str) -> tuple[str, str]:
    """(class, subject) of a manifest escaping row. Names themselves contain ': '."""
    if row.endswith(": bodyless instance kind Intrinsic"):
        # An intrinsic INSTANCE the producer kept escaping. Its sites are classified from the
        # module like every other intrinsic's, so the row is CROSS-CHECKED against the site
        # derivation (rule /3) and never counted on top of it.
        return "intrinsic", row[: -len(": bodyless instance kind Intrinsic")]
    if row.endswith(": MIR unavailable"):
        return "mir-unavailable", row[: -len(": MIR unavailable")]
    k = row.find(": indirect call (")
    if k >= 0:
        return "indirect", row[:k]
    k = row.find(": bodyless instance kind Virtual")
    if k >= 0:
        return "virtual", row[:k]
    k = row.find(": foreign item")
    if k >= 0:
        return "foreign", row[:k]
    return "other", row


def intrinsic_head(name: str) -> str:
    return name.split("::<", 1)[0].rsplit("::", 1)[-1]


def _obligation_site(o: dict, funcs: list[dict], what: str) -> tuple[int, int]:
    """(sidecar_func_id, bb) of a per-site obligation, every redundant field cross-checked."""
    fid = o["function"]
    _require(0 <= fid < len(funcs), f"obligation {o['id']} names function {fid} of {len(funcs)}")
    sm = _SRC_SITE_RE.match(o["source"])
    _require(sm is not None, f"{what} obligation {o['id']} has no per-site source: {o['source'][:120]!r}")
    _require(sm.group("fn") == funcs[fid]["name"],
             f"obligation {o['id']} source names {sm.group('fn')[:80]!r}, "
             f"function {fid} is {funcs[fid]['name'][:80]!r}")
    bb = int(sm.group("bb")[2:])
    _require(bb < len(funcs[fid]["blocks"]), f"obligation {o['id']} names bb{bb}, function {fid} has "
                                             f"{len(funcs[fid]['blocks'])} blocks")
    _require(funcs[fid]["blocks"][bb] is not None,
             f"obligation {o['id']} names bb{bb} of function {fid}, which the module does not carry")
    if o["site"] is not None:
        _require(o["site"] == (fid, f"bb{bb}"), f"obligation {o['id']} site field {o['site']} "
                                                f"disagrees with its source (f{fid}/bb{bb})")
    if o["formula"] == "trust.trust_ir.obligation-source.v1":
        try:
            payload = json.loads(o["payload"])
        except json.JSONDecodeError as exc:
            raise Refusal(f"obligation {o['id']} payload is not JSON: {exc}") from exc
        _require(payload.get("source_id") == o["source"],
                 f"obligation {o['id']} payload source_id disagrees with its source")
    return fid, bb


def call_site_obligations(module: dict) -> dict:
    funcs = module["funcs"]
    by_site: dict[tuple[int, int], list[tuple[str, str, int]]] = defaultdict(list)
    for o in module["obligations"]:
        desc = o["desc"]
        a = _ABSENT_RE.search(desc) or _ABSENT_DYN_RE.match(desc)
        p = _PANIC_RE.match(desc)
        u = _UB_RE.match(desc)
        ind = _INDIRECT_RE.match(desc)
        pc = _PRECOND_RE.match(desc)
        if not (a or p or u or ind or pc):
            _require(not _ASSUMPTION_TAG_RE.match(desc) or _DROP_UNPROVEN_RE.match(desc) is not None,
                     f"obligation {o['id']} carries an assumption tag this script does not model "
                     f"(refusing; an unmodelled assumption is never skipped): {desc[:160]!r}")
            continue
        kind = ("absent" if a else "panic" if p else "ub" if u else "precond" if pc else "indirect")
        fid, bb = _obligation_site(o, funcs, "call-site")
        subject = (a.group(1) if a else p.group(1) if p else u.group(1) if u
                   else pc.group(1) if pc else "")
        by_site[(fid, bb)].append((kind, subject, o["id"], o.get("site_index")))
    return by_site


def drop_glue_sites(module: dict) -> dict[tuple[int, int], list[str]]:
    """Per-site UNPROVEN drop-glue assumptions: MIR `Drop` terminators whose glue the bridge
    lowers as a halting `assert false`. Keyed (sidecar_func_id, bb), validated like a call-site
    obligation; a non-per-site one is a refusal."""
    funcs = module["funcs"]
    out: dict[tuple[int, int], list[str]] = defaultdict(list)
    for o in module["obligations"]:
        dm = _DROP_UNPROVEN_RE.match(o["desc"])
        if dm is None:
            continue
        out[_obligation_site(o, funcs, "drop-glue")].append(dm.group("ty"))
    return out


def _arm_width(code: str, op: str) -> int | None:
    """The unsigned width of `op`'s type in `code` (`%5 = ctpop u64 %4` -> 64), or None."""
    toks = code.split(" = ", 1)[-1].split()
    if not toks or toks[0] != op:
        return None
    ty = toks[2] if op == "icmp" and len(toks) > 2 else (toks[1] if len(toks) > 1 else "")
    return _ARM_WIDTH.get(ty)


def arm_template(head: str, codes: list[str]) -> str | None:
    """Rule /8: None when `codes` -- one contiguous run of instructions tagged with `head`'s arm
    tag, annotations stripped -- is EXACTLY that head's arm (trust-ir-bridge
    `lower/intrinsic_arms.rs`, `emit`); otherwise why not. The check is the opcode SEQUENCE at the
    run's own width, plus a Clean image for every opcode."""
    ops = [opname(c) for c in codes]
    if any(op not in CLEAN_PROJECTABLE_OPS for op in ops):
        return f"an arm opcode has no Clean image: {sorted({o for o in ops if o not in CLEAN_PROJECTABLE_OPS})}"

    def width(op: str) -> int | None:
        for c in codes:
            w = _arm_width(c, op)
            if w is not None:
                return w
        return None

    def to_u32(w: int) -> list[str]:
        return [] if w == 32 else (["trunc"] if w > 32 else ["zext"])

    charge = ["const", "icmp", "const", "select", "const", "udiv"]
    want: list[str] | None
    if head == "saturating_add":
        want = ["add", "icmp", "const", "select"]
    elif head == "saturating_sub":
        want = ["sub", "icmp", "const", "select"]
    elif head == "rotate_left":
        w = width("shl")
        want = None if w is None else (["const", "and"] + ([] if w == 32 else ["zext"] if w > 32 else ["trunc"])
                                       + ["shl", "const", "sub", "const", "and", "lshr", "or"])
    elif head in ("ctpop", "ctlz", "ctlz_nonzero", "cttz", "cttz_nonzero"):
        w = width("ctpop")
        if w is None:
            want = None
        else:
            core = {"ctpop": [],
                    "ctlz": ["const", "lshr", "or"] * (w.bit_length() - 1) + ["not"],
                    "cttz": ["const", "sub", "not", "and"]}[head.removesuffix("_nonzero")]
            want = (charge if head.endswith("_nonzero") else []) + core + ["ctpop"] + to_u32(w)
    elif head == "exact_div":
        want = ["udiv", "urem", "const", "icmp", "const", "select", "const", "udiv"]
    elif head == "select_unpredictable":
        want = ["select"]
    elif head in ("assert_inhabited", "cold_path"):
        return None if len(codes) == 1 and re.fullmatch(r"%\d+ = const bool true", codes[0]) else \
            f"a no-op arm is exactly one `const bool true` marker, got {codes}"
    elif head == "compare_bytes":
        want = ["call"]
    elif head == "typed_swap_nonoverlapping":
        want = ["icmp", "const", "const", "select", "const", "udiv", "load", "load", "store", "store"]
    elif head == "size_of_val":
        # A sized T: its size, a constant. A slice / str tail: len * elem_size, the fits-isize
        # bound charged first.
        want = (["const"] if ops == ["const"] else
                ["ptr_metadata", "const", "icmp", "const", "const", "select", "const", "udiv", "const",
                 "mul"])
    elif head == "align_of_val":
        want = ["const"]
    else:
        return f"no template for head {head!r}"
    if want is None:
        return f"the {head} arm names no supported unsigned width: {codes}"
    return None if ops == want else f"the {head} arm spells {ops}, its template is {want}"


def arm_charged(head: str, codes: list[str]) -> bool:
    """Rule /8: whether this arm CHARGES a precondition (and so needs its obligation at the site)."""
    return head in CHARGED_ARM_HEADS or (head == "size_of_val" and len(codes) > 1)


def block_arm(block: list[str]) -> dict | None:
    """Rule /8: the instructions of `block` tagged with an `intrinsic-arms` tag, or None. A tag in
    the lane's range that names no head, two heads' tags in one block, and a tagged run that is not
    contiguous are DEFECTS the caller refuses to credit (`defect`)."""
    idx: list[int] = []
    heads: set[str] = set()
    for k, ins in enumerate(block):
        _code, ann = split_annotation(ins)
        for t in _ARM_TAG_RE.findall(ann):
            off = int(t) - INTRINSIC_ARM_TAG_BASE
            if not 0 <= off < 1000:
                continue
            _require(off < len(INTRINSIC_ARM_HEADS),
                     f"an arm tag custom({t}) names no head of the lane's table -- refusing")
            heads.add(INTRINSIC_ARM_HEADS[off])
            idx.append(k)
    if not idx:
        return None
    idx = sorted(set(idx))
    head = min(heads)
    codes = [split_annotation(block[k])[0] for k in idx]
    defect = None
    if len(heads) > 1:
        defect = f"tags of {sorted(heads)} in one block"
    elif idx != list(range(idx[0], idx[-1] + 1)):
        defect = "the tagged run is not contiguous"
    else:
        defect = arm_template(head, codes)
    return {"head": head, "first": idx[0], "codes": codes, "defect": defect,
            "charged": arm_charged(head, codes)}


def block_evidence(fid: int, block: list[str], funcs: list[dict], obl: list, n_members: int,
                   n_supplied: int = 0) -> dict:
    """Strong and weak evidence that a MIR Call terminator lowered into this block."""
    strong: list[tuple[str, str]] = []
    seq_unimaged: set[int] = set()
    arm = block_arm(block)
    for k_ins, ins in enumerate(block):
        code, _ann = split_annotation(ins)
        if arm is not None and k_ins == arm["first"]:
            # Rule /8: the arm is ONE piece of evidence, placed before its own instructions'.
            strong.append(("exact_arm", arm["head"]))
        cm = _CALL_RE.match(code)
        if cm:
            callee = cm.group("callee")
            fm = re.fullmatch(r"func\.(\d+)", callee)
            if fm:
                k = int(fm.group(1))
                _require(k < len(funcs), f"call @func.{k} out of range in function {fid}")
                # Rule /4: a call to a bodiless DECLARATION (every function past the members and
                # the supplied bodies is one; `reconcile` verified that) is its own kind of
                # evidence, so it can never stand in for a member call and a member call can never
                # stand in for it. Rule /8: likewise a call to a SUPPLIED intrinsic body.
                kind = ("call" if k < n_members else
                        "call_supplied" if k < n_members + n_supplied else "call_decl")
                strong.append((kind, funcs[k]["name"]))
            else:
                strong.append(("call_external", callee))
        elif _CALL_INDIRECT_RE.match(code):
            strong.append(("call_indirect", ""))
        else:
            op = opname(code)
            if op in ATOMIC_OPS:
                # Rule /5: a WEAK compare-exchange is its own kind of evidence (see
                # `native_evidence_kind`); its op name stays `cmpxchg`, the producer's spelling.
                weak = op == "cmpxchg" and _CMPXCHG_WEAK_RE.match(code) is not None
                strong.append(("native_op_weak" if weak else "native_op", op))
                # Rule /9: whether the projector's SEQ image computes THIS instruction.
                rmw = _ATOMICRMW_OP_RE.match(code)
                if weak or (rmw is not None and rmw.group(1) not in SEQ_RMW_OPS):
                    seq_unimaged.add(len(strong) - 1)
    for kind, subject, oid, _k in obl:
        strong.append(("obl_" + kind, subject))
    # Rule /11: every undefined-behaviour halt obligation of this block SITES a halting `assert` of
    # a `const bool false` bound before it in the block -- the node the projector images as
    # `unreachable` (`fn ub_halt_image`), never the sanctioned-panic `assert`.
    ub_ks = [k_ for kind, _s, _o, k_ in obl if kind == "ub"]
    ub_sited_halt = bool(ub_ks) and all(k_ is not None and _is_halting_assert_at(block, k_) for k_ in ub_ks)
    weak = None
    # SILENT havoc: the block ends in `%v = undef T`, which carries no
    # annotation, is optionally followed by `store T %v, ptr ...`, and then
    # `br`. It has no obligation. It is weak evidence, used only to KEY a row
    # that has no other trace.
    if block and opname(split_annotation(block[-1])[0]) == "br" and not obl:
        body = block[:-1]
        if body:
            last_code, _ = split_annotation(body[-1])
            sm = _STORE_RE.match(last_code)
            cand = body[-2] if (sm and len(body) >= 2) else (None if sm else body[-1])
            if cand is not None:
                ccode, cann = split_annotation(cand)
                um = _UNDEF_RE.match(ccode)
                if um and not cann and (not sm or sm.group("v") == um.group("v")):
                    weak = ("silent_undef", um.group("ty"))
    ends_unreachable = bool(block) and opname(split_annotation(block[-1])[0]) == "unreachable"
    has_false_assert = _has_false_assert(block)
    return {"strong": strong, "weak": weak, "ends_unreachable": ends_unreachable,
            "false_assert": has_false_assert, "ub_sited_halt": ub_sited_halt,
            "arm_defect": arm["defect"] if arm else None,
            "arm_charged": bool(arm and arm["charged"]),
            "seq_unimaged": seq_unimaged}


# Rule /6: the two facts an indirect escaping row states (trust callee_sidecar.rs) that the
# `indirect-by-value` lane rests on.
_INDIRECT_EXACT_MEMBERS = "(every enumerated target is a member)"
_INDIRECT_SCAN_COMPLETE = "(crate-wide address-taken scan: no body of this crate could take an address at this type unseen"


def _tile_targets(content: str, n: int, names) -> list[str] | None:
    """Rule /10: the member names whose sorted `", "`-join is EXACTLY `content` (n of them), or None
    when no unique tiling exists. Names contain ", " themselves, so a split is never trusted."""
    cands = sorted(nm for nm in names if nm in content)
    sols: list[list[str]] = []

    def go(i: int, acc: list[str]) -> None:
        if len(sols) > 1:
            return
        if i == len(content):
            if len(acc) == n:
                sols.append(list(acc))
            return
        for nm in cands:
            if content.startswith(nm, i):
                j = i + len(nm)
                if j == len(content):
                    go(j, acc + [nm])
                elif content.startswith(", ", j):
                    go(j + 2, acc + [nm])
    go(0, [])
    if len(sols) != 1 or sols[0] != sorted(sols[0]):
        return None
    return sols[0]


def _functy_arity(defn: str) -> int | None:
    """Parameter count of a `functy.N = (P, ..) -> (R..)` definition, or None when unparsed."""
    if not defn.startswith("("):
        return None
    depth = 0
    for j, ch in enumerate(defn):
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>":
            depth -= 1
            if depth == 0:
                inner = defn[1:j]
                if not inner.strip():
                    return 0
                d, n = 0, 1
                for c in inner:
                    if c in "([{<":
                        d += 1
                    elif c in ")]}>":
                        d -= 1
                    elif c == "," and d == 0:
                        n += 1
                return n
    return None


def _check_abi_thunk(t: dict, k: int, all_funcs: list[dict], n_members: int, functys: dict) -> str:
    """Rule /11 (crystal D13): function k must be EXACTLY the supplied ABI thunk of one member shim
    -- named `<shim>#trust-abi-thunk`; one block `bb0(%p0..%pn-1)`: `const () phantomdata`, a typed
    `const (T..) {..}` seed, an insertfield chain writing param i to lane i, `call @func.<shim>(env,
    tuple)`, `ret` of its result -- at the shim's signature with the environment and the tuple
    spread (shim `((), (T..)) -> R`, thunk `(T..) -> R`). Returns the shim's name."""
    name = t["name"]
    _require(name.endswith(THUNK_SUFFIX), f"ABI thunk {k} ({name[:120]!r}) is not named `<shim>{THUNK_SUFFIX}`")
    shim = name[:-len(THUNK_SUFFIX)]
    idx = [j for j in range(n_members) if all_funcs[j]["name"] == shim]
    _require(len(idx) == 1, f"ABI thunk {k} ({name[:120]!r}) names no member shim, or several")
    bad = f"ABI thunk {k} ({name[:120]!r}) is not the exact rust-call spread of its shim -- refusing"
    _require(len(t["blocks"]) == 1 and t["blocks"][0] is not None, bad)
    params = t.get("entry_params") or []
    code = [split_annotation(i)[0] for i in t["blocks"][0]]
    n = len(params)
    _require(n >= 1 and len(code) == n + 4, bad)
    em = re.match(r"^(%\d+) = const \(\) phantomdata$", code[0])
    sm = re.match(r"^(%\d+) = const (\(.*\)) \{.*\}$", code[1])
    _require(em is not None and sm is not None and _functy_arity(sm.group(2) + " -> ()") == n, bad)
    tup, cur = sm.group(2), sm.group(1)
    for i in range(n):
        im = re.match(r"^(%\d+) = insertfield (\(.*\)) (%\d+), (\d+), (%\d+)$", code[2 + i])
        _require(im is not None and im.group(2) == tup and im.group(3) == cur and int(im.group(4)) == i
                 and im.group(5) == params[i], bad)
        cur = im.group(1)
    cm = re.match(r"^(?:(%\d+) = )?call @func\.(\d+)\((%\d+), (%\d+)\)$", code[2 + n])
    _require(cm is not None and int(cm.group(2)) == idx[0] and cm.group(3) == em.group(1)
             and cm.group(4) == cur, bad)
    _require(code[3 + n] == (f"ret {cm.group(1)}" if cm.group(1) else "ret"), bad)
    sdef = functys.get(all_funcs[idx[0]]["functy"]) or ""
    tdef = functys.get(t["functy"]) or ""
    _require(sdef.startswith("((), ") and sdef[len("((), "):].startswith(tup)
             and tdef == tup + sdef[len("((), ") + len(tup) + 1:], bad)
    return shim


def _is_shim_adapter(block: list[str], args: list[str]) -> bool:
    """Rule /10: the trust sidecar's `shim-adapter` shape -- two arguments, the first a
    `const () phantomdata` of this block, the second the last link of an `insertfield` chain
    rooted at a typed `const (..) {..}` seed of this block, writing each lane exactly once."""
    if len(args) != 2:
        return False
    defs = {}
    for ins in block:
        code = split_annotation(ins)[0]
        m = re.match(r"^(%\d+) = (.*)$", code)
        if m:
            defs[m.group(1)] = m.group(2)
    if defs.get(args[0]) != "const () phantomdata":
        return False
    lanes: list[int] = []
    cur = args[1]
    tuple_ty = None
    while True:
        d = defs.get(cur, "")
        im = re.match(r"^insertfield (\(.*\)) (%\d+), (\d+), %\d+$", d)
        if im:
            if tuple_ty is not None and im.group(1) != tuple_ty:
                return False
            tuple_ty = im.group(1)
            lanes.append(int(im.group(3)))
            cur = im.group(2)
            continue
        cm = re.match(r"^const (\(.*\)) \{.*\}$", d)
        if not cm or tuple_ty is None or cm.group(1) != tuple_ty:
            return False
        arity = _functy_arity(tuple_ty + " -> ()")
        return arity is not None and sorted(lanes) == list(range(arity))


def _is_halting_assert_at(block: list[str], k: int) -> bool:
    """Rule /11: is instruction k of the block `assert %v`, %v a `const bool false` bound before it?"""
    if not 0 <= k < len(block):
        return False
    m = re.match(r"^assert (%\d+)$", split_annotation(block[k])[0])
    return m is not None and any(
        re.match(r"^" + re.escape(m.group(1)) + r" = const bool false$", split_annotation(i)[0])
        for i in block[:k])


def _has_false_assert(block: list[str]) -> bool:
    false_vals = set()
    for ins in block:
        code, _ = split_annotation(ins)
        m = re.match(r"^(%\d+) = const bool false$", code)
        if m:
            false_vals.add(m.group(1))
        m = re.match(r"^assert (%\d+)$", code)
        if m and m.group(1) in false_vals:
            return True
    return False


def compat(edge: dict, ev: dict, foreign: set[str],
           callbacks: dict | None = None) -> tuple[str, set] | None:
    """If manifest row `edge` can stand at a site with evidence `ev`, return
    (verdict, consumed-evidence). Otherwise return None. `callbacks` is the manifest's
    `foreign_callbacks` rows by callee (rule /5)."""
    cls, r = edge["class"], edge["resolved"]
    strong = ev["strong"]

    def find(kind, subject=None):
        return {i for i, (k, s) in enumerate(strong) if k == kind and (subject is None or s == subject)}

    if cls == "member":
        hit = find("call", r)
        return ("member-call", {min(hit)}) if hit else None
    if cls == "panic-terminal":
        # Positive evidence is the per-site obligation plus a HALTING `assert <const false>`
        # in the block. EvalIR halts on a false assert (eval_ir_machine.rs `ir_assert_b`).
        # Whether the block then ends in `unreachable` or in a dead `br` is recorded
        # separately (`panic_terminal_sites_not_ending_unreachable`).
        hit = find("obl_panic", r)
        if hit and ev["false_assert"]:
            return ("panic-terminal", {min(hit)})
        return None
    if cls == "ub-terminal":
        # Rule /5: the same halting shape, keyed by the bridge's undefined-behavior wording.
        # Neither wording is evidence for the other class. Rule /11: the obligation must SITE the
        # halting assert itself -- the node the Clean projector images as `unreachable`.
        hit = find("obl_ub", r)
        if hit and ev.get("ub_sited_halt"):
            return ("ub-terminal", {min(hit)})
        return None
    if cls.startswith("foreign-callback-terminal"):
        # Rule /5. The foreign-terminal evidence, and the premise it stands on: a recorded
        # CONTRACT in the manifest's `foreign_callbacks` row. A callee the producer kept escaping
        # (not in `foreign_terminals`, or no contract) is an escaping site, never a premise.
        hit = find("obl_absent", r)
        if not hit:
            return None
        decl = find("call_decl", r)
        row = (callbacks or {}).get(r)
        if r in foreign and _FOREIGN_ITEM_RE.search(r) and row is not None and row.get("contract"):
            if decl:
                verdict = "foreign-callback-terminal" if ev["false_assert"] else "foreign-callback-terminal-call"
                return (verdict, {min(hit), min(decl)})
            return ("foreign-callback-terminal", {min(hit)})
        return ("foreign-callback-escaping", {min(hit)} | ({min(decl)} if decl else set()))
    if cls.startswith("foreign-terminal"):
        hit = find("obl_absent", r)
        if hit and r in foreign and _FOREIGN_ITEM_RE.search(r):
            # Rule /4: the obligation names and keys the premise either way. The site is a premise
            # LOWERED AS A CALL only when its block also calls the bodiless declaration of THIS
            # callee and holds no halting `assert <const false>`; a declared call beside a halting
            # assert still halts, so it stays counted as a havoc lowering.
            decl = find("call_decl", r)
            if decl:
                verdict = "foreign-terminal" if ev["false_assert"] else "foreign-terminal-call"
                return (verdict, {min(hit), min(decl)})
            return ("foreign-terminal", {min(hit)})
        return None
    if cls.startswith("intrinsic-terminal"):
        hit = find("obl_absent", r)
        if hit:
            return ("intrinsic-havoc", {min(hit)})
        # Rule /8: the site's block holds the EXACT ARM of this row's own head, with its template,
        # its charge (a charged head) and its supplied body (compare_bytes). Any defect: no verdict,
        # so the row's evidence is unexplained and the site is unreconciled.
        head = intrinsic_head(r)
        arm = find("exact_arm", head)
        if arm:
            if ev.get("arm_defect"):
                return None
            consumed = {min(arm)}
            if ev.get("arm_charged"):
                pre = find("obl_precond", r)
                if not pre:
                    return None
                consumed.add(min(pre))
            if head in SUPPLIED_ARM_HEADS:
                call = find("call_supplied", r)
                if not call:
                    return None
                consumed.add(min(call))
            return ("intrinsic-modelled", consumed)
        ops = native_intrinsic_ops(intrinsic_head(r))
        if ops:
            want = native_evidence_kind(intrinsic_head(r))
            hit = {i for i, (k, s) in enumerate(strong) if k == want and s in ops}
            if hit:
                # Rule /9: a native atomic the projector images under SEQ is a premise site.
                verdict = ("intrinsic-modelled" if ops <= CLEAN_PROJECTABLE_OPS
                           else "intrinsic-modelled-seq"
                           if ops <= SEQ_IMAGED_ATOMIC_OPS and not (hit & ev.get("seq_unimaged", set()))
                           else "intrinsic-unprojectable")
                return (verdict, hit)
        if ev["weak"] and not strong:
            return ("silent-havoc", set())
        return None
    if cls.startswith("escaping: indirect call"):
        ci, oi = find("call_indirect"), find("obl_indirect")
        if ci and oi:
            return ("indirect", {min(ci), min(oi)})
        return None
    if cls.startswith("escaping"):
        if r:
            hit = find("obl_absent", r)
            if hit:
                # Rule /4: a foreign callee the producer's fold kept ESCAPING may still be lowered
                # as a call to its declaration; that call is the same site, not extra evidence.
                decl = find("call_decl", r)
                return ("escaping-absent", {min(hit)} | ({min(decl)} if decl else set()))
        if ev["weak"] and not strong:
            return ("silent-havoc", set())
        return None
    return None


def derived_site_evidence(rec: dict) -> str:
    """The producer's per-site `evidence` vocabulary, re-derived from THIS script's verdict at the
    site (rule /3). The producer's value must equal it, or the site is unreconciled."""
    v = rec["verdict"]
    if v == "intrinsic-havoc":
        return "absent-callee-havoc"
    if v in ("intrinsic-modelled", "intrinsic-modelled-seq", "intrinsic-unprojectable"):
        if "arm_head" in rec:
            return "exact-arm:" + rec["arm_head"]
        return "native-op:" + rec["native_op"]
    if v in ("silent-havoc", "unevidenced"):
        return "no-trace"
    return f"<no producer spelling for verdict {v}>"


def _instance_path(name: str, crate: str) -> str:
    """A path comparable across the two spellings a local closure carries: a member's instance
    name (`clean_kernel::tc::..::{closure#0}::<__trust_args@..>`, lifetimes `'_`) and a local
    root's def path (`tc::..::{closure#0}`, lifetimes named)."""
    base = re.sub(r"::<__trust_args@[0-9a-f]+>$", "", name)
    base = base.replace(crate + "::", "")
    return re.sub(r"'[A-Za-z_][A-Za-z0-9_]*", "'_", base)


def _subsumed_root_defect(r: dict, members: list[dict], crate: str) -> str | None:
    """None when a `subsumed: reached from <parent>` root is INDEPENDENTLY verified: a local
    root; its `sidecar_func_id` names the member `resolved` names; that member is an `Item`
    body; its instance path equals the root's def path and no other Item member's does; and
    `<parent>` is a member with a `member` call row to it. Otherwise the reason. The producer
    matched on `DefId`; this matches on the rendered path AND the parent edge, so the two
    derivations are independent."""
    if r.get("caller") != "<local root>":
        return "not a local root"
    sid = r.get("sidecar_func_id")
    if not (type(sid) is int and 0 <= sid < len(members)):
        return f"no member id ({sid!r})"
    mem = members[sid]
    if mem["name"] != r.get("resolved"):
        return "the member at sidecar_func_id is not the one `resolved` names"
    if mem.get("instance_kind") != "Item":
        return f"the member is a {mem.get('instance_kind')!r}, not an Item body"
    want = _instance_path(r["callee_def_path"], crate)
    if _instance_path(mem["name"], crate) != want:
        return f"the member's instance path is not the root's ({want[:120]!r})"
    same = [m for m in members if m.get("instance_kind") == "Item" and _instance_path(m["name"], crate) == want]
    if len(same) != 1:
        return f"{len(same)} Item members carry the root's path"
    parent = r["outcome"][len(SUBSUMED_PREFIX):]
    pm = [m for m in members if m["name"] == parent]
    if len(pm) != 1:
        return "the named parent is not (exactly one) member"
    if not any(c["class"] == "member" and c["resolved"] == mem["name"] for c in pm[0]["calls"]):
        return "the named parent has no `member` call row to it"
    return None


_STRONG_WEIGHT = 1 << 20  # one strong match outweighs any number of weak ones


def align_member(edges: list[dict], sites: list[tuple[int, dict]], foreign: set[str],
                 callbacks: dict | None = None):
    """An order-preserving match of manifest rows against evidence sites that is
    maximal LEXICOGRAPHICALLY: first by matches on strong evidence (a call, an
    obligation, a native op), then by matches on weak evidence (a silent undef).
    A plain pair count is wrong. It lets a weak match displace a strong one on a
    tie, which self-test arm 33c measured: a cold_path row stole a silent block
    and left a `call_indirect` unexplained."""
    n, m = len(edges), len(sites)
    ok = [[compat(edges[i], sites[j][1], foreign, callbacks) for j in range(m)] for i in range(n)]
    w = [[0 if ok[i][j] is None else (_STRONG_WEIGHT if ok[i][j][1] else 1) for j in range(m)]
         for i in range(n)]
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n - 1, -1, -1):
        row, nxt, wi = dp[i], dp[i + 1], w[i]
        for j in range(m - 1, -1, -1):
            best = nxt[j] if nxt[j] >= row[j + 1] else row[j + 1]
            if wi[j] and wi[j] + nxt[j + 1] > best:
                best = wi[j] + nxt[j + 1]
            row[j] = best
    pairs = []
    i = j = 0
    while i < n and j < m:
        if w[i][j] and dp[i][j] == w[i][j] + dp[i + 1][j + 1]:
            pairs.append((i, j, ok[i][j]))
            i += 1
            j += 1
        elif dp[i + 1][j] >= dp[i][j + 1]:
            i += 1
        else:
            j += 1
    return pairs


def reconcile(manifest: dict, module: dict) -> dict:
    all_funcs = module["funcs"]
    members = manifest["members"]
    n_members = len(members)
    # Rule /4: #functions = #members + #declarations. The members come first, one `fn` each in
    # sidecar_func_id order; everything after them must be a bodiless declaration of a FOREIGN
    # item. A declaration is never a member, and a member is never bodiless.
    _require(len(all_funcs) >= n_members,
             f"module has {len(all_funcs)} functions, manifest has {n_members} members")
    funcs = all_funcs[:n_members]
    # Rule /8: SUPPLIED intrinsic bodies (the `intrinsic-arms` lane) sit between the members and the
    # declarations, each stamped `; #producer: trust-intrinsic-arm`; everything after them is a
    # declaration, checked as before (a bodied function there is still refused).
    rest = all_funcs[n_members:]
    n_supplied = 0
    while n_supplied < len(rest) and not rest[n_supplied].get("decl") \
            and rest[n_supplied].get("producer") == SUPPLIED_PRODUCER:
        n_supplied += 1
    supplied = rest[:n_supplied]
    # Rule /11 (crystal D13): SUPPLIED ABI thunks (`; #producer: "trust-abi-thunk"`) follow them.
    n_thunks = 0
    while n_supplied + n_thunks < len(rest) and not rest[n_supplied + n_thunks].get("decl") \
            and rest[n_supplied + n_thunks].get("producer") == THUNK_PRODUCER:
        n_thunks += 1
    thunks = rest[n_supplied:n_supplied + n_thunks]
    decls = rest[n_supplied + n_thunks:]
    for i, (f, mem) in enumerate(zip(funcs, members)):
        _require(f["name"] == mem["name"], f"function {i} is {f['name'][:80]!r}, member is {mem['name'][:80]!r}")
        _require(not f.get("decl"), f"function {i} ({f['name'][:80]!r}) is a MEMBER and has no blocks")
        # Rule /7: with the `abort-cleanup` lane the module may omit blocks (trailing ones too, so
        # the label list is padded to the member's MIR block count); without it, every MIR block
        # is lowered and the count is exact, as before.
        _require(len(f["blocks"]) <= mem["mir_blocks"],
                 f"function {i} has {len(f['blocks'])} blocks, the member records {mem['mir_blocks']} MIR blocks")
        f["blocks"].extend([None] * (mem["mir_blocks"] - len(f["blocks"])))
        holes = sum(1 for b in f["blocks"] if b is None)
        _require(holes == 0 or manifest.get("_abort_cleanup"),
                 f"function {i} ({f['name'][:80]!r}) omits {holes} of its {mem['mir_blocks']} MIR blocks, "
                 f"but the manifest's producer does not declare the `abort_cleanup` lane that prunes "
                 f"cleanup blocks -- refusing")
    _require(not decls or manifest.get("_premise_decls"),
             f"module carries {len(decls)} bodiless declaration(s) after the members, but the manifest's "
             f"producer does not declare the `premise_decls` lane that mints them -- refusing")
    _require(not supplied or manifest.get("_intrinsic_arms"),
             f"module carries {len(supplied)} supplied intrinsic bod(y/ies) after the members, but the "
             f"manifest's producer does not declare the `intrinsic_arms` lane that supplies them -- refusing")
    _require(not thunks or manifest.get("_fnptr_thunks_lane"),
             f"module carries {len(thunks)} supplied ABI thunk(s), but the manifest's producer does not "
             f"name the `fnptr-thunks` lane that supplies them -- refusing")
    supplied_names: set[str] = set()
    obl_fns = {o["function"] for o in module["obligations"]}
    thunk_of: dict[str, int] = {}
    for j, t in enumerate(thunks):
        k = n_members + n_supplied + j
        shim = _check_abi_thunk(t, k, all_funcs, n_members, module.get("functys", {}))
        _require(shim not in thunk_of, f"shim {shim[:120]!r} has two ABI thunks")
        _require(k not in obl_fns, f"ABI thunk {k} carries an obligation; a thunk is exact and owes none")
        thunk_of[shim] = k
    for j, b in enumerate(supplied):
        k = n_members + j
        stem = b["name"].split("::<", 1)[0]
        _require(stem.startswith("core::intrinsics::") and intrinsic_head(b["name"]) in SUPPLIED_ARM_HEADS
                 and stem.count("::") == 2,
                 f"supplied body {k} ({b['name'][:120]!r}) is not a core intrinsic whose body the lane "
                 f"supplies ({sorted(SUPPLIED_ARM_HEADS)})")
        _require(b["name"] not in supplied_names, f"supplied body {k} ({b['name'][:120]!r}) appears twice")
        supplied_names.add(b["name"])
        _require(k not in obl_fns, f"supplied body {k} ({b['name'][:120]!r}) carries an obligation; a "
                                   f"supplied body is exact and owes none")
        for bb_, blk in enumerate(b["blocks"]):
            _require(blk is not None, f"supplied body {k} skips block label bb{bb_}")
            for ins in blk:
                op = opname(split_annotation(ins)[0])
                _require(op in CLEAN_PROJECTABLE_OPS and op not in ("call", "call_indirect"),
                         f"supplied body {k} ({b['name'][:80]!r}) holds `{op}`: a supplied body may call "
                         f"nothing and use only opcodes with a Clean image")
    # Rule /8: an arm tag is evidence only from a producer that declares the lane.
    if not manifest.get("_intrinsic_arms"):
        for f in funcs:
            for blk in f["blocks"]:
                _require(blk is None or not any(
                    int(t) - INTRINSIC_ARM_TAG_BASE in range(1000)
                    for ins in blk for t in _ARM_TAG_RE.findall(split_annotation(ins)[1])),
                    f"member {f['name'][:80]!r} carries an intrinsic-arm tag, but the producer does not "
                    f"declare the `intrinsic_arms` lane -- refusing")
    decl_names: set[str] = set()
    for j, d in enumerate(decls):
        k = n_members + n_supplied + n_thunks + j
        _require(d.get("decl"), f"function {k} ({d['name'][:80]!r}) is past the {n_members} members and has "
                                f"a body: module has {len(all_funcs)} functions, manifest has {n_members} members")
        _require(_FOREIGN_ITEM_RE.search(d["name"]) is not None,
                 f"declaration {k} ({d['name'][:120]!r}) is not an {{extern#N}} foreign item; rule /4 admits a "
                 f"bodiless declaration only as a FOREIGN premise")
        _require(d["name"] not in decl_names, f"declaration {k} ({d['name'][:120]!r}) is declared twice")
        decl_names.add(d["name"])
    # Rule /6: a call_indirect with NO fail-closed marker in its block dispatches BY VALUE. The
    # producer must name the `indirect-by-value` lane, and the member's indirect row(s) must state
    # the exact enumeration that lane rests on -- every target a member, the crate-wide scan
    # unmarked at the pointer's type. Anything else is a markerless call the ratchet cannot
    # explain, so it is refused rather than counted.
    by_value_sites: list[tuple[int, int]] = []
    adapter_sites: list[tuple[int, int]] = []
    thunk_sites: list[tuple[int, int]] = []
    functys = module.get("functys", {})
    member_names = {f["name"]: k for k, f in enumerate(funcs)}
    esc_rows = manifest["escaping"]
    for fid, f in enumerate(funcs):
        for bb, block in enumerate(f["blocks"]):
            # A block pruned by the `abort-cleanup` lane (rule /7) holds no instruction.
            if block is None or not any(_CALL_INDIRECT_RE.match(split_annotation(ins)[0]) for ins in block):
                continue
            if _has_false_assert(block):
                continue
            _require(manifest.get("_indirect_by_value_lane"),
                     f"function {fid} bb{bb}: a call_indirect with no `assert false` marker, but the "
                     f"producer does not name the `indirect-by-value` lane -- refusing")
            rows = [r for r in esc_rows if classify_row(r) == ("indirect", f["name"])]
            _require(rows and all(_INDIRECT_EXACT_MEMBERS in r and _INDIRECT_SCAN_COMPLETE in r
                                  for r in rows),
                     f"function {fid} bb{bb}: a call_indirect dispatched by value, but the member's "
                     f"indirect row does not state an all-member, scan-complete enumeration -- refusing")
            # Rule /10: the enumerated targets, and each one's signature against the call's.
            tsets = set()
            for r in rows:
                tm = re.search(r"; enumerated targets (\d+) \[(.*)\] " + re.escape(_INDIRECT_EXACT_MEMBERS), r)
                tiled = _tile_targets(tm.group(2), int(tm.group(1)), member_names) if tm else None
                _require(tiled is not None,
                         f"function {fid} bb{bb}: the indirect row's target list is not an unambiguous "
                         f"tiling of member names -- refusing")
                tsets.add(tuple(tiled))
            _require(len(tsets) == 1, f"function {fid} bb{bb}: the member's indirect rows enumerate "
                                      f"different target sets -- refusing")
            targets = next(iter(tsets))
            for ins in block:
                cm = _CALL_INDIRECT_FULL_RE.match(split_annotation(ins)[0])
                if not _CALL_INDIRECT_RE.match(split_annotation(ins)[0]):
                    continue
                _require(cm is not None, f"function {fid} bb{bb}: unparsed call_indirect {ins[:120]!r}")
                call_def = functys.get(int(cm.group("sig")))
                args = re.findall(r"%\d+", cm.group("args") or "")
                _require(call_def is not None and _functy_arity(call_def) == len(args),
                         f"function {fid} bb{bb}: a by-value call_indirect whose functy is undefined or "
                         f"whose arity it does not pass -- refusing")
                # Rule /11 (crystal D13): targets that are shims with ABI thunks dispatch THROUGH
                # the thunks -- every value naming such a shim at a functy names its thunk -- when
                # each thunk is at the call's functy and no constant names a shim as a value.
                through_thunks = (bool(thunk_of) and all(t in thunk_of for t in targets)
                                  and not any(member_names[t] in module.get("fndef_named", ())
                                              for t in targets)
                                  and all(functys.get(all_funcs[thunk_of[t]]["functy"]) == call_def
                                          for t in targets)
                                  and not all(functys.get(all_funcs[member_names[t]]["functy"]) == call_def
                                              for t in targets))
                if through_thunks:
                    thunk_sites.append((fid, bb))
                for t in targets if not through_thunks else ():
                    tf = all_funcs[member_names[t]]
                    _require(functys.get(tf["functy"]) == call_def,
                             f"function {fid} bb{bb}: by-value target {t[:120]!r} is declared at "
                             f"functy.{tf['functy']} = {functys.get(tf['functy'])!r}, the call at "
                             f"{call_def!r}: a positional mismatch -- refusing")
                if _is_shim_adapter(block, args):
                    _require(manifest.get("_shim_adapter_lane"),
                             f"function {fid} bb{bb}: a call_indirect shaped as the shim adapter, but the "
                             f"producer does not name the `shim-adapter` lane -- refusing")
                    adapter_sites.append((fid, bb))
            by_value_sites.append((fid, bb))
    # Rule /10 (D11): the thread-local address ops of the members, certified or not.
    tls_ops = {"certified": 0, "uncertified": 0}
    tls_cert = manifest.get("_tls_certified") or set()
    for f in funcs:
        for blk in f["blocks"]:
            for ins in blk or ():
                code = split_annotation(ins)[0]
                rhs = code.split(" = ", 1)[1] if " = " in code else code
                if rhs.startswith(_TLS_OP_PREFIX) and rhs.endswith('"]'):
                    tls_ops["certified" if rhs[len(_TLS_OP_PREFIX):-2] in tls_cert else "uncertified"] += 1
    foreign = set(manifest["foreign_terminals"])
    fc_rows: dict[str, dict] = manifest.get("_foreign_callbacks") or {}
    obl_sites = call_site_obligations(module)
    drops = drop_glue_sites(module)

    unreconciled: list[dict] = []
    # Every declaration must be CALLED by a member: one no member calls stands for no site.
    called_past_members = {all_funcs[int(m_.group(1))]["name"]
                           for f in funcs for block in f["blocks"] if block is not None for ins in block
                           if (m_ := re.match(r"^(?:%\d+(?:, %\d+)* = )?call @func\.(\d+)\(",
                                              split_annotation(ins)[0]))
                           and n_members <= int(m_.group(1)) < len(all_funcs)}
    for name in sorted(decl_names - called_past_members):
        unreconciled.append({"kind": "declaration-never-called", "name": name[:200]})
    # Rule /8: a supplied body no member calls stands for no site.
    for name in sorted(supplied_names - called_past_members):
        unreconciled.append({"kind": "supplied-body-never-called", "name": name[:200]})
    sites_out: list[dict] = []  # one record per manifest Call terminator
    # Rule /3: a v3 manifest carries each call's MIR `bb`, and the site is KEYED by it. The
    # row must be explained by the module evidence at exactly that block; evidence no row
    # claims, and evidence at a row's block the row does not explain, are unreconciled. A v2
    # manifest keeps the order-preserving alignment below, unchanged.
    v3_keyed = manifest["schema"] == MANIFEST_SCHEMA_V3
    for fid, (f, mem) in enumerate(zip(funcs, members)):
        evs = []
        ev_at: dict[int, dict] = {}
        for bb, block in enumerate(f["blocks"]):
            if block is None:
                continue
            ev = block_evidence(fid, block, all_funcs, obl_sites.get((fid, bb), []), n_members, n_supplied)
            ev_at[bb] = ev
            if ev["strong"] or ev["weak"]:
                evs.append((bb, ev))
        edges = mem["calls"]
        if v3_keyed:
            claimed: set[int] = set()
            for i, e in enumerate(edges):
                bb = e["bb"]
                _require(bb in ev_at, f"member {fid} ({f['name'][:80]!r}): a call row is keyed to bb{bb}, "
                                      f"which the module does not carry (rule /7: a pruned block holds "
                                      f"no call the producer may report)")
                ev = ev_at[bb]
                claimed.add(bb)
                rec = {"member": fid, "member_name": f["name"], "call_index": i, "bb": bb,
                       "manifest_class": e["class"], "resolved": e["resolved"], "site": e["site"]}
                if "evidence" in e:
                    rec["producer_evidence"] = e["evidence"]
                ok = compat(e, ev, foreign, fc_rows)
                if ok is not None:
                    verdict, consumed = ok
                    rec["verdict"] = verdict
                    rec["keyed_by"] = "module-evidence"
                    rec["evidence"] = ([f"{k}:{s_}" for n_, (k, s_) in enumerate(ev["strong"]) if n_ in consumed]
                                       or ([f"{ev['weak'][0]}:{ev['weak'][1]}"] if ev["weak"] else []))
                    if verdict in ("panic-terminal", "ub-terminal"):
                        rec["panic_tail_unreachable"] = ev["ends_unreachable"]
                    if verdict in ("intrinsic-modelled", "intrinsic-modelled-seq", "intrinsic-unprojectable"):
                        k0, s0 = ev["strong"][min(consumed)]
                        if k0 == "exact_arm":
                            rec["arm_head"] = s0  # rule /8
                            rec["arm_charged"] = ev.get("arm_charged", False)
                        else:
                            rec["native_op"] = s0
                    extra = [f"{k}:{s_}" for n_, (k, s_) in enumerate(ev["strong"]) if n_ not in consumed]
                    if extra:
                        unreconciled.append({"kind": "extra-evidence-at-matched-site", "member": fid,
                                             "name": f["name"], "bb": bb, "evidence": extra})
                else:
                    rec["verdict"] = "unevidenced"
                    rec["evidence"] = []
                    # No module trace at all: the site is located by the producer's bb ALONE.
                    rec["keyed_by"] = "producer-bb"
                    if ev["strong"] or ev["weak"]:
                        unreconciled.append({
                            "kind": "row-bb-holds-evidence-the-row-does-not-explain", "member": fid,
                            "name": f["name"], "bb": bb, "manifest_class": e["class"],
                            "evidence": ([f"{k}:{s_}" for k, s_ in ev["strong"]]
                                         or [f"{ev['weak'][0]}:{ev['weak'][1]}"])})
                sites_out.append(rec)
            for bb, ev in evs:
                if bb in claimed:
                    continue
                if ev["strong"]:
                    unreconciled.append({"kind": "module-site-without-manifest-row", "member": fid,
                                         "name": f["name"], "bb": bb,
                                         "evidence": [f"{k}:{s_}" for k, s_ in ev["strong"]]})
                else:
                    unreconciled.append({"kind": "module-silent-havoc-without-manifest-row", "member": fid,
                                         "name": f["name"], "bb": bb,
                                         "evidence": [f"{ev['weak'][0]}:{ev['weak'][1]}"]})
            continue
        pairs = align_member(edges, evs, foreign, fc_rows)
        matched_e = {p[0]: p for p in pairs}
        matched_s = {p[1] for p in pairs}
        # Every site with strong evidence must be explained by a manifest row.
        for j, (bb, ev) in enumerate(evs):
            if ev["strong"] and j not in matched_s:
                unreconciled.append({"kind": "module-site-without-manifest-row", "member": fid,
                                     "name": f["name"], "bb": bb,
                                     "evidence": [f"{k}:{s}" for k, s in ev["strong"]]})
            elif ev["weak"] and j not in matched_s:
                # Review 2026-09-23: a SILENT havoc (an unannotated `undef` standing for a call)
                # that no manifest row claims is a call the producer did not list. Before this,
                # a manifest that forgot the row made the site vanish and read as PROGRESS.
                unreconciled.append({"kind": "module-silent-havoc-without-manifest-row", "member": fid,
                                     "name": f["name"], "bb": bb,
                                     "evidence": [f"{ev['weak'][0]}:{ev['weak'][1]}"]})
        for i, j, (verdict, consumed) in pairs:
            bb, ev = evs[j]
            extra = [f"{k}:{s}" for n_, (k, s) in enumerate(ev["strong"]) if n_ not in consumed]
            if extra:
                unreconciled.append({"kind": "extra-evidence-at-matched-site", "member": fid,
                                     "name": f["name"], "bb": bb, "evidence": extra})
        matched_bbs = [(i, evs[j][0]) for i, j, _ in pairs]
        for i, e in enumerate(edges):
            rec = {"member": fid, "member_name": f["name"], "call_index": i,
                   "manifest_class": e["class"], "resolved": e["resolved"], "site": e["site"]}
            if i in matched_e:
                _i, j, (verdict, consumed) = matched_e[i]
                bb, ev = evs[j]
                rec["bb"] = bb
                rec["verdict"] = verdict
                rec["evidence"] = ([f"{k}:{s}" for n_, (k, s) in enumerate(ev["strong"]) if n_ in consumed]
                                   or ([f"{ev['weak'][0]}:{ev['weak'][1]}"] if ev["weak"] else []))
                if verdict in ("panic-terminal", "ub-terminal"):
                    rec["panic_tail_unreachable"] = ev["ends_unreachable"]
                if verdict == "silent-havoc":
                    # Weak evidence keys a row only when the candidate is unique.
                    lo = max([b for k, b in matched_bbs if k < i] or [-1]) + 1
                    hi = min([b for k, b in matched_bbs if k > i] or [len(f["blocks"])]) - 1
                    cands = [bb2 for bb2, ev2 in evs if lo <= bb2 <= hi and ev2["weak"] and not ev2["strong"]]
                    if len(cands) != 1:
                        rec["bb"] = None
                        rec["bb_range"] = [lo, hi]
                        rec["ambiguous_candidates"] = cands
            else:
                lo = max([b for k, b in matched_bbs if k < i] or [-1]) + 1
                hi = min([b for k, b in matched_bbs if k > i] or [len(f["blocks"])]) - 1
                rec["bb"] = None
                rec["bb_range"] = [lo, hi]
                rec["verdict"] = "unevidenced"
                rec["evidence"] = []
            sites_out.append(rec)

    # ── classify every site, and reconcile the escaping sites to manifest rows ──
    rows = manifest["escaping"]
    row_info = [classify_row(r) for r in rows]
    callee_rows: dict[str, set] = defaultdict(set)  # subject -> distinct row strings (non-indirect)
    indirect_rows: dict[str, list[int]] = defaultdict(list)
    for idx, (rc, subj) in enumerate(row_info):
        if rc == "indirect":
            indirect_rows[subj].append(idx)
        else:
            callee_rows[subj].add(idx)
    row_sites: Counter = Counter()

    def attach_row(rec: dict) -> str | None:
        if rec["verdict"] == "indirect" or rec["manifest_class"].startswith("escaping: indirect call"):
            pool = indirect_rows.get(rec["member_name"], [])
            if pool:
                idx = pool.pop(0)
                row_sites[idx] += 1
                rec["row_index"] = idx
                return "indirect"
            return None
        idxs = callee_rows.get(rec["resolved"], set())
        if idxs:
            # Rows with an identical subject are identical strings; any one of them will do.
            idx = min(idxs)
            row_sites[idx] += 1
            rec["row_index"] = idx
            return row_info[idx][0]
        return None

    for rec in sites_out:
        v, mc = rec["verdict"], rec["manifest_class"]
        if v == "member-call":
            rec["classification"] = "member-call"
        elif v in ("panic-terminal", "ub-terminal"):
            rec["classification"] = v
        elif v == "foreign-terminal":
            rec["classification"] = "foreign-terminal"
            rec["premise_lowered_as_havoc"] = True
        elif v == "foreign-terminal-call":
            # Rule /4: the same PREMISE, lowered as a call to its bodiless declaration. The
            # classification (and so the site table) is unchanged; only the lowering differs.
            rec["classification"] = "foreign-terminal"
            rec["premise_lowered_as_call"] = True
        elif v == "foreign-callback-terminal":
            # Rule /5: a foreign PREMISE whose callee re-enters the bundle, under its contract.
            rec["classification"] = "foreign-callback-terminal"
            rec["premise_lowered_as_havoc"] = True
        elif v == "foreign-callback-terminal-call":
            rec["classification"] = "foreign-callback-terminal"
            rec["premise_lowered_as_call"] = True
        elif v == "foreign-callback-escaping":
            # The producer kept this foreign callback ESCAPING (no contract, or a site without a
            # member callback): its escaping `foreign` row accounts for it.
            rec["classification"] = "escaping"
            rc = attach_row(rec)
            if rc is None:
                rec["escaping_class"] = "other"
                unreconciled.append({"kind": "escaping-site-without-manifest-row", "member": rec["member"],
                                     "name": rec["member_name"], "bb": rec["bb"], "resolved": rec["resolved"]})
            else:
                rec["escaping_class"] = rc
        elif v == "intrinsic-modelled":
            rec["classification"] = "intrinsic-modelled"
        elif v == "intrinsic-modelled-seq":
            # Rule /9 (D10): exact only under the ENVIRONMENT premise SEQ -- a PREMISE site.
            rec["classification"] = "atomic-seq-premise"
        elif mc.startswith("intrinsic-terminal"):
            rec["classification"] = "escaping"
            rec["escaping_class"] = {"intrinsic-havoc": "intrinsic-havoc",
                                     "intrinsic-unprojectable": "intrinsic-unprojectable",
                                     "silent-havoc": "intrinsic-havoc",
                                     "unevidenced": "intrinsic-unevidenced"}[v]
        elif mc.startswith("escaping"):
            rec["classification"] = "escaping"
            rc = attach_row(rec)
            if rc is None:
                rec["escaping_class"] = "other"
                unreconciled.append({"kind": "escaping-site-without-manifest-row", "member": rec["member"],
                                     "name": rec["member_name"], "bb": rec["bb"], "resolved": rec["resolved"]})
            else:
                rec["escaping_class"] = rc
            if v == "unevidenced":
                rec["escaping_class_note"] = "no module evidence at any site"
        else:
            # member / panic / foreign rows the module does not back up.
            rec["classification"] = "escaping"
            rec["escaping_class"] = "other"
            unreconciled.append({"kind": "manifest-row-contradicted-by-module", "member": rec["member"],
                                 "name": rec["member_name"], "bb": rec["bb"], "manifest_class": mc,
                                 "resolved": rec["resolved"]})
        if v == "silent-havoc":
            rec["silent_havoc"] = True

    # ── roots ──
    # Rule /3: a `subsumed: reached from <parent>` root (the producer's closure root whose body is
    # a member by instance identity) is credited only after `_subsumed_root_defect` verifies it
    # independently; an unverified one is refused AND unreconciled.
    subsumed_roots: list[dict] = []
    refused_roots: list[dict] = []
    for r in manifest["roots"]:
        oc = r.get("outcome")
        if oc == "resolved" and r.get("resolved"):
            continue
        if isinstance(oc, str) and oc.startswith(SUBSUMED_PREFIX):
            defect = _subsumed_root_defect(r, members, manifest["crate"])
            if defect is None:
                subsumed_roots.append(r)
                continue
            unreconciled.append({"kind": "subsumed-root-not-verified", "root": r.get("callee_def_path"),
                                 "why": defect})
        refused_roots.append(r)
    for r in manifest["roots"]:
        if r in refused_roots or r in subsumed_roots:
            continue
        sid = r.get("sidecar_func_id")
        if not (isinstance(sid, int) and 0 <= sid < len(members) and members[sid]["name"] == r["resolved"]):
            unreconciled.append({"kind": "resolved-root-not-a-member", "root": r.get("callee_def_path")})

    def _norm(p: str) -> str:
        return re.sub(r"\b(?:[a-z_][a-z0-9_]*::)+", "", p)

    member_defpaths = {_norm(m.get("def_path", "")) for m in members}
    refused_with_member = [r for r in refused_roots if _norm(r.get("callee_def_path", "")) in member_defpaths]

    # ── manifest self-consistency against what the module shows ──
    not_foreign = sorted(n_ for n_ in foreign if not _FOREIGN_ITEM_RE.search(n_))
    if not_foreign:
        unreconciled.append({"kind": "foreign-terminal-not-a-foreign-item", "names": not_foreign})
    foreign_seen = {s["resolved"] for s in sites_out if s["classification"] == "foreign-terminal"}
    if foreign_seen - foreign:
        unreconciled.append({"kind": "foreign-site-not-listed", "names": sorted(foreign_seen - foreign)})
    # Rule /5: every foreign-callback premise site must be LISTED by the callee's
    # `foreign_callbacks` row at exactly (member, bb), with member callbacks; a row site no
    # premise site backs is unreconciled too; and a foreign-callback callee must be promoted.
    member_names = {mem["name"] for mem in members}
    fc_seen = {s["resolved"] for s in sites_out if s["classification"] == "foreign-callback-terminal"}
    if fc_seen - foreign:
        unreconciled.append({"kind": "foreign-site-not-listed", "names": sorted(fc_seen - foreign)})
    fc_premises = []
    for callee in sorted(fc_seen):
        row = fc_rows.get(callee)
        if row is None or not row.get("contract"):
            unreconciled.append({"kind": "foreign-callback-without-contract", "name": callee[:200]})
            continue
        listed = {(st["member"], st["bb"]): st["callbacks"] for st in row["sites"]}
        seen_sites = {(s["member_name"], s["bb"]) for s in sites_out
                      if s["classification"] == "foreign-callback-terminal" and s["resolved"] == callee}
        for key in sorted(seen_sites - set(listed), key=str):
            unreconciled.append({"kind": "foreign-callback-site-not-in-its-row", "name": callee[:200],
                                 "member": key[0][:200], "bb": key[1]})
        for key in sorted(set(listed) - seen_sites, key=str):
            unreconciled.append({"kind": "foreign-callback-row-site-without-premise-site", "name": callee[:200],
                                 "member": key[0][:200], "bb": key[1]})
        cbs = sorted({c for key in seen_sites & set(listed) for c in listed[key]})
        if any(not listed[key] for key in seen_sites & set(listed)):
            unreconciled.append({"kind": "foreign-callback-site-without-callback", "name": callee[:200]})
        missing = [c for c in cbs if c not in member_names]
        if missing:
            unreconciled.append({"kind": "foreign-callback-callback-not-a-member", "name": callee[:200],
                                 "callbacks": [c[:200] for c in missing]})
        fc_premises.append({"callee": callee[:200], "contract": row["contract"], "sites": len(seen_sites),
                            "callbacks": [c[:200] for c in cbs]})
    panic_seen = {s["resolved"] for s in sites_out if s["classification"] in ("panic-terminal", "ub-terminal")}
    if panic_seen - set(manifest["panic_terminals"]):
        unreconciled.append({"kind": "panic-site-not-listed", "names": sorted(panic_seen - set(manifest["panic_terminals"]))})

    # ── escaping rows, three rules ──
    intr_sites: dict[str, list[dict]] = defaultdict(list)
    for s in sites_out:
        if s["manifest_class"].startswith("intrinsic-terminal"):
            intr_sites[s["resolved"]].append(s)
    instances = sorted(intr_sites)

    # Rule /9: a SEQ premise site is not an escape (it is closed under P, never under the empty P).
    intr_ok = ("intrinsic-modelled", "atomic-seq-premise")

    def inst_escapes_strict(name: str) -> bool:
        return any(s["classification"] not in intr_ok for s in intr_sites[name])

    strict_intr = [n for n in instances if inst_escapes_strict(n)]
    any_intr_unmodelled = any(s["classification"] not in intr_ok
                              for ss in intr_sites.values() for s in ss)
    module_wide_intr = instances if any_intr_unmodelled else strict_intr
    reviewers_intr = [n for n in instances if any(s["verdict"] == "intrinsic-havoc" for s in intr_sites[n])]
    trustir_intr = [n for n in instances
                    if any(s["verdict"] not in ("intrinsic-unprojectable", "intrinsic-modelled",
                                                "intrinsic-modelled-seq")
                           for s in intr_sites[n])]
    n_rows = len(rows)
    # Rule /3: a manifest `Intrinsic` row is the producer's own per-instance verdict; the figures
    # take intrinsic instances from the SITES (`strict_intr` etc.), so those rows are cross-checked
    # below and never added on top of them.
    intr_row_subjects = {subj for rc, subj in row_info if rc == "intrinsic"}
    n_rows_nonintr = sum(1 for rc, _ in row_info if rc != "intrinsic")
    has_evidence = bool(manifest.get("_has_site_evidence"))
    producer_evidence_counts: Counter = Counter()
    if has_evidence:
        # The producer's per-site verdict must be the one this script derives from the module.
        for s in sites_out:
            if not s["manifest_class"].startswith("intrinsic-terminal"):
                continue
            producer_evidence_counts[s.get("producer_evidence")] += 1
            derived = derived_site_evidence(s)
            s["derived_evidence"] = derived
            if s.get("producer_evidence") != derived:
                unreconciled.append({"kind": "producer-site-evidence-disagrees", "member": s["member"],
                                     "name": s["member_name"], "bb": s["bb"], "resolved": s["resolved"],
                                     "producer": s.get("producer_evidence"), "derived": derived})
        # ...and so must its per-INSTANCE verdict: under the trust-ir rule an instance escapes iff
        # a site of it is not a native op, and that is exactly the set it must list.
        want = set(trustir_intr)
        if intr_row_subjects != want:
            unreconciled.append({"kind": "producer-intrinsic-rows-disagree",
                                 "listed": len(intr_row_subjects), "derived": len(want),
                                 "listed_not_derived": sorted(x[:160] for x in intr_row_subjects - want)[:12],
                                 "derived_not_listed": sorted(x[:160] for x in want - intr_row_subjects)[:12]})
    # Rows are counted from the SITES as well as from the manifest's list: an escaping
    # site that no manifest row accounts for (the producer dropped the row, or the
    # module contradicts a member/panic/foreign row) adds a row, per callee, or per
    # site for an indirect call. So an under-reporting manifest RAISES the figure.
    extra_rows = {("indirect@" + s["member_name"] + f"#{s['call_index']}")
                  if s["manifest_class"].startswith("escaping: indirect call") else s["resolved"]
                  for s in sites_out
                  if s["classification"] == "escaping" and s.get("row_index") is None
                  and not s["manifest_class"].startswith("intrinsic-terminal")}

    esc_sites = [s for s in sites_out if s["classification"] == "escaping"]
    silent = [s for s in sites_out if s.get("silent_havoc")]
    unkeyed = [s for s in sites_out if s["bb"] is None]
    premise_havoc = [s for s in sites_out if s.get("premise_lowered_as_havoc")]
    premise_call = [s for s in sites_out if s.get("premise_lowered_as_call")]
    seq_sites = [s for s in sites_out if s["classification"] == "atomic-seq-premise"]

    rows_without_site = [i for i in range(n_rows) if row_sites[i] == 0 and row_info[i][0] not in ("indirect", "intrinsic")
                         and not any(row_sites[k] for k in callee_rows.get(row_info[i][1], set()))]
    # An indirect row that no call_indirect claimed is unreconciled: each one stands for one site.
    for subj, pool in indirect_rows.items():
        for idx in pool:
            unreconciled.append({"kind": "indirect-row-without-site", "row_index": idx, "caller": subj})
    # A row's class must agree with what its sites show: a `virtual` row whose
    # callee is not a `<dyn ..>` instance is inconsistent.
    for s in esc_sites:
        if s.get("row_index") is not None and s["escaping_class"] == "virtual" and not s["resolved"].startswith("<dyn "):
            unreconciled.append({"kind": "virtual-row-on-non-dyn-callee", "resolved": s["resolved"]})

    closed_derived = (n_rows_nonintr + len(strict_intr) == 0 and not refused_roots and not premise_havoc
                      and not unreconciled and not silent and not unkeyed and not seq_sites)
    if manifest["closed"] and not closed_derived:
        unreconciled.append({"kind": "manifest-claims-closed", "detail": "manifest `closed` is true; the artifact does not support it"})
    if manifest["closed_modulo_foreign"] and (n_rows_nonintr + len(strict_intr) > 0 or refused_roots):
        unreconciled.append({"kind": "manifest-claims-closed-modulo-foreign",
                             "detail": "manifest `closed_modulo_foreign` is true; escaping rows remain"})

    metrics = {
        "escaping_rows_per_instance": n_rows_nonintr + len(extra_rows) + len(strict_intr),
        "escaping_rows_module_wide": n_rows_nonintr + len(extra_rows) + len(module_wide_intr),
        "escaping_call_sites": len(esc_sites),
        "silent_havoc_call_sites": len(silent),
        "unkeyed_call_sites": len(unkeyed),
        "refused_roots": len(refused_roots),
        "premise_sites_lowered_as_havoc": len(premise_havoc),
        "unreconciled": len(unreconciled),
        "drop_glue_assumption_sites": len(drops),
    }
    cls_counter = Counter(s["classification"] for s in sites_out)
    esc_class = Counter(s["escaping_class"] for s in esc_sites)
    row_class = Counter(rc for rc, _ in row_info)
    intr_verdicts = Counter()
    for n_ in instances:
        vs = {s["verdict"] for s in intr_sites[n_]}
        key = ("intrinsic-havoc" if "intrinsic-havoc" in vs else
               "unevidenced" if "unevidenced" in vs else
               "intrinsic-unprojectable" if "intrinsic-unprojectable" in vs else
               "intrinsic-modelled" if vs == {"intrinsic-modelled"} else
               "intrinsic-modelled-seq" if vs <= {"intrinsic-modelled", "intrinsic-modelled-seq"}
               else "|".join(sorted(vs)))
        intr_verdicts[key] += 1
    info = {
        "manifest_escaping_rows": n_rows,
        "manifest_escaping_rows_distinct": len(set(rows)),
        "manifest_rows_by_class": dict(sorted(row_class.items())),
        "manifest_rows_without_call_site": [rows[i][:200] for i in rows_without_site],
        "manifest_closed": manifest["closed"],
        "manifest_closed_modulo_foreign": manifest["closed_modulo_foreign"],
        "intrinsic_instances": len(instances),
        "intrinsic_instances_by_worst_site": dict(sorted(intr_verdicts.items())),
        "intrinsic_heads_escaping": sorted({intrinsic_head(n_) for n_ in strict_intr}),
        "per_instance_reviewers_rule_obligation_names_it": n_rows_nonintr + len(extra_rows) + len(reviewers_intr),
        "per_instance_trustir_native_counts_as_modelled": n_rows_nonintr + len(extra_rows) + len(trustir_intr),
        "manifest_intrinsic_rows": len(intr_row_subjects),
        "producer_declares_site_evidence": has_evidence,
        "producer_site_evidence": dict(sorted((str(k), v) for k, v in producer_evidence_counts.items())),
        "sites_keyed_by_producer_bb_only": sum(1 for s in sites_out if s.get("keyed_by") == "producer-bb"),
        "escaping_rows_derived_from_sites_without_a_manifest_row": sorted(x[:200] for x in extra_rows),
        "per_site_reviewers_rule_escaping": sum(1 for s in esc_sites
                                                if s["escaping_class"] not in ("intrinsic-unprojectable",
                                                                               "intrinsic-unevidenced")),
        "panic_terminal_sites_not_ending_unreachable": sum(
            1 for s in sites_out if s["classification"] in ("panic-terminal", "ub-terminal")
            and not s.get("panic_tail_unreachable")),
        "call_sites_total": len(sites_out),
        "call_sites_by_classification": dict(sorted(cls_counter.items())),
        "escaping_call_sites_by_class": dict(sorted(esc_class.items())),
        # Rule /6 (informational): indirect sites the producer lowered WITHOUT the marker.
        "indirect_sites_dispatched_by_value": len(by_value_sites),
        # Rule /10 (informational; crystal D1): of those, the ones through the shim adapter, and
        # the by-value sites by member.
        "indirect_sites_dispatched_through_shim_adapter": len(adapter_sites),
        # Rule /11 (informational; crystal D13): of those, the ones through supplied ABI thunks.
        "indirect_sites_dispatched_through_abi_thunk": len(thunk_sites),
        "abi_thunks": n_thunks,
        "indirect_sites_dispatched_by_value_members": sorted(
            f"{funcs[fid_]['name'][:160]} bb{bb_}" for fid_, bb_ in by_value_sites),
        # Rule /10 (informational; decision D11): the TLS INPUT premise's ops -- a
        # `trust_rust.thread_local_addr` in a member, its symbol certified by the manifest's
        # `tls_cells` rows -- and the ops no certificate covers. An entry of P (class INPUT,
        # type-complete certificate), never of the empty P, and not a call site.
        "tls_input_premise_ops": tls_ops["certified"],
        "tls_input_premise_ops_uncertified": tls_ops["uncertified"],
        "tls_certified_symbols": sorted(manifest.get("_tls_certified") or ()),
        "tls_premise": TLS_PREMISE,
        "roots_total": len(manifest["roots"]),
        "roots_resolved": len(manifest["roots"]) - len(refused_roots) - len(subsumed_roots),
        "roots_subsumed": len(subsumed_roots),
        "roots_subsumed_paths": [r.get("callee_def_path") for r in subsumed_roots],
        "refused_roots": [r.get("callee_def_path") for r in refused_roots],
        "refused_roots_with_member_instance_by_name": len(refused_with_member),
        "members": len(members),
        "closed_derived": closed_derived,
        "drop_glue_assumption_obligations": sum(len(v) for v in drops.values()),
        "drop_glue_assumption_distinct_types": len({t for v in drops.values() for t in v}),
        "drop_glue_sites_without_halting_assert": sum(
            1 for (fid_, bb_) in drops if funcs[fid_]["blocks"][bb_] is not None
            and not _has_false_assert(funcs[fid_]["blocks"][bb_])),
        # Rule /4. A GOOD count, so information only: foreign premise sites lowered as a call to a
        # bodiless declaration rather than as `assert false; undef` (the ratcheted bad count is
        # premise_sites_lowered_as_havoc), and the declarations the module carries.
        "premise_sites_lowered_as_call": len(premise_call),
        # Rule /5. Information only: the foreign-callback premises and the contracts they stand on.
        "foreign_callback_lane": bool(manifest.get("_foreign_callback_lane")),
        "foreign_callback_premises": fc_premises,
        "declared_premise_functions": len(decls),
        "declared_premise_names": sorted(d["name"][:200] for d in decls),
        # Rule /8 (information): the `intrinsic-arms` lane -- sites modelled by an exact arm, by
        # head; the preconditions those arms CHARGE; and the bodies the lane supplies.
        "intrinsic_arms_lane": bool(manifest.get("_intrinsic_arms")),
        "intrinsic_arm_sites_by_head": dict(sorted(Counter(
            s["arm_head"] for s in sites_out if s.get("arm_head")).items())),
        "intrinsic_arm_precondition_charges": sum(1 for s in sites_out if s.get("arm_charged")),
        "supplied_intrinsic_bodies": sorted(b["name"][:200] for b in supplied),
        # Rule /9 (information; D10): native atomic sites closed under the ENVIRONMENT premise SEQ,
        # by op, and the premise itself -- an entry of P, never of the empty P.
        "premise_sites_atomic_seq": len(seq_sites),
        "premise_sites_atomic_seq_by_op": dict(sorted(Counter(
            s.get("native_op", "?") for s in seq_sites).items())),
        "seq_premise": SEQ_PREMISE,
    }
    escaping_callees = sorted(
        {f"{rc}|{subj}" for rc, subj in row_info}
        | {f"unlisted|{x}" for x in extra_rows}
        | {f"intrinsic|{n_}" for n_ in strict_intr}
    )
    site_table_sha = site_table_sha256(sites_out)
    return {"metrics": metrics, "info": info, "sites": sites_out, "unreconciled": unreconciled,
            "escaping_callees": escaping_callees, "site_table_sha256": site_table_sha,
            "rows": [{"index": i, "class": row_info[i][0], "subject": row_info[i][1][:300],
                      "call_sites": row_sites[i]} for i in range(n_rows)],
            "intrinsics": [{"instance": n_, "head": intrinsic_head(n_), "sites": len(intr_sites[n_]),
                            "verdicts": dict(Counter(s["verdict"] for s in intr_sites[n_])),
                            "escapes_strict": n_ in strict_intr} for n_ in instances]}


def site_table_sha256(sites: list[dict], undo: dict | None = None) -> str:
    """The per-site table's digest. `undo` maps a classification a later rule introduced back to the
    (classification, escaping_class) that site had before it (`RULE_RECLASSIFICATIONS`), so a
    declared reclassification can be checked against a baseline cut under the earlier rule."""
    undo = undo or {}
    table = []
    for s in sites:
        if s["classification"] == "member-call":
            continue
        cls, esc = s["classification"], s.get("escaping_class", "")
        if cls in undo:
            cls, esc = undo[cls]
        table.append([s["member_name"], s["bb"], s["call_index"], s["resolved"], cls, esc])
    return hashlib.sha256(json.dumps(table, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def measure(manifest_path: Path, module_path: Path | None = None) -> dict:
    manifest = load_manifest(manifest_path)
    mod_path = module_path or (manifest_path.parent / manifest["artifacts"]["text"])
    module = parse_module(mod_path, manifest["artifacts"]["text_bytes"])
    result = reconcile(manifest, module)
    # What was measured. A smaller or different subject reports fewer escapes; it must never
    # read as progress (review 2026-09-23: a roots list that lost its six refused closures
    # passed as `refused_roots 6 -> 0` and --rebase locked it in).
    result["subject"] = {"crate": manifest["crate"], "filter": manifest["filter"],
                         "roots": sorted(f"{r['caller']} -> {r['callee_def_path']}" for r in manifest["roots"])}
    result["artifact"] = {
        "manifest_path": str(manifest_path),
        "manifest_sha256": sha256_file(manifest_path),
        "module_path": str(mod_path),
        "module_sha256": module["sha256"],
        "module_bytes": module["bytes"],
        "obligations": len(module["obligations"]),
    }
    return result


# ─────────────────────────────── baseline / ratchet ─────────────────────────────


def _seal(body: dict) -> str:
    b = {k: v for k, v in body.items() if k != "seal"}
    return hashlib.sha256(json.dumps(b, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def script_sha256() -> str:
    """The instrument's Python digest: this script's bytes, then the symbol reader it imports."""
    h = hashlib.sha256(Path(__file__).resolve().read_bytes())
    h.update(Path(tir_symbols.__file__).resolve().read_bytes())
    return h.hexdigest()


def load_baseline(path: Path) -> dict:
    if not path.exists():
        raise Refusal(f"no baseline at {path}; create one with --init --reason ...")
    try:
        b = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise Refusal(f"baseline {path} unreadable: {exc}") from exc
    _require(isinstance(b, dict) and b.get("schema") == BASELINE_SCHEMA, "baseline schema mismatch")
    for key in ("rule_version", "artifact", "subject", "metrics", "escaping_callees", "site_table_sha256", "seal"):
        _require(key in b, f"baseline has no `{key}`")
    _require(isinstance(b["subject"], dict) and isinstance(b["subject"].get("crate"), str)
             and isinstance(b["subject"].get("filter"), str) and isinstance(b["subject"].get("roots"), list),
             "baseline subject malformed")
    _require(isinstance(b["metrics"], dict) and all(k in b["metrics"] for k in RATCHETED),
             "baseline metrics incomplete")
    _require(all(isinstance(b["metrics"][k], int) and b["metrics"][k] >= 0 for k in RATCHETED),
             "baseline metrics must be non-negative integers")
    return b


def baseline_body(result: dict, reason: str, history: list, prev: dict | None,
                  migration: dict | None = None) -> dict:
    now = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    entry = {"date": now, "reason": reason, "script_sha256": script_sha256(),
             "artifact": {k: result["artifact"][k] for k in ("manifest_sha256", "module_sha256")},
             "metrics": result["metrics"]}
    if prev is not None:
        entry["from_metrics"] = prev["metrics"]
        entry["from_artifact"] = {k: prev["artifact"].get(k) for k in ("manifest_sha256", "module_sha256")}
    if migration is not None:
        entry["rule_migration"] = migration
    body = {
        "schema": BASELINE_SCHEMA,
        "rule_version": RULE_VERSION,
        "what": "Crystal link 3 per-call-site reconciliation baseline. Every metric is a BAD count, "
                "derived by scripts/crystal_link3_reconcile.py from the artifact below. Do not hand-edit: "
                "the seal and the same-artifact reproduction check refuse it. Lower it only with --rebase.",
        "artifact": result["artifact"],
        "subject": result["subject"],
        "metrics": result["metrics"],
        "info": {k: result["info"][k] for k in (
            "manifest_escaping_rows", "manifest_escaping_rows_distinct", "intrinsic_instances",
            "intrinsic_instances_by_worst_site", "per_instance_reviewers_rule_obligation_names_it",
            "per_instance_trustir_native_counts_as_modelled", "per_site_reviewers_rule_escaping",
            "escaping_call_sites_by_class", "call_sites_by_classification", "refused_roots",
            "drop_glue_assumption_obligations", "drop_glue_assumption_distinct_types",
            "roots_subsumed", "sites_keyed_by_producer_bb_only", "manifest_intrinsic_rows",
            "producer_declares_site_evidence", "premise_sites_lowered_as_call",
            "declared_premise_functions")},
        "escaping_callees": result["escaping_callees"],
        "site_table_sha256": result["site_table_sha256"],
        "history": history + [entry],
    }
    body["seal"] = _seal(body)
    return body


def write_json(path: Path, obj: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, indent=1, sort_keys=False) + "\n")
    os.replace(tmp, path)


def _rule_n(version: str) -> int:
    return int(version.rsplit("/", 1)[1])


def migration_check(baseline: dict) -> tuple[dict | None, str | None]:
    """A baseline cut under an older rule may be carried to this one only through a declared
    `RULE_MIGRATIONS` entry, and only if its OWN artifact, re-measured under this rule,
    reproduces its figures, pinned escaping-callee set and site-table digest exactly.
    Returns (migration record, None) or (None, why not)."""
    old = baseline["rule_version"]
    if old not in RULE_MIGRATIONS:
        return None, f"no declared migration from {old!r} to {RULE_VERSION!r}"
    art = baseline["artifact"]
    try:
        again = measure(Path(art["manifest_path"]), Path(art["module_path"]))
    except (Refusal, KeyError, OSError) as exc:
        return None, f"the baseline's own artifact cannot be re-measured under {RULE_VERSION}: {exc}"
    if (again["artifact"]["manifest_sha256"], again["artifact"]["module_sha256"]) != \
            (art.get("manifest_sha256"), art.get("module_sha256")):
        return None, "the baseline's artifact files have changed since it was measured"
    # A DECLARED RECLASSIFICATION between the two rules (`RULE_RECLASSIFICATIONS`): the old
    # artifact must reproduce the baseline's site table exactly once every declared move is
    # undone, and no ratcheted figure may rise and no escaping callee may appear.
    moves: dict = {}
    for rv, mv in RULE_RECLASSIFICATIONS.items():
        if _rule_n(old) < _rule_n(rv) <= _rule_n(RULE_VERSION):
            moves.update(mv)
    if moves and again["site_table_sha256"] != baseline["site_table_sha256"]:
        undone = site_table_sha256(again["sites"], undo=moves)
        worse = {k: (baseline["metrics"][k], again["metrics"][k]) for k in RATCHETED
                 if again["metrics"][k] > baseline["metrics"][k]}
        new_esc = sorted(set(again["escaping_callees"]) - set(baseline["escaping_callees"]))
        if undone != baseline["site_table_sha256"] or worse or new_esc:
            return None, (f"under {RULE_VERSION} the baseline's own artifact does not reproduce it modulo "
                          f"the declared reclassification {sorted(moves)} (site table "
                          f"{'differs' if undone != baseline['site_table_sha256'] else 'ok'}, figures "
                          f"worse {worse}, new escaping callees {new_esc[:4]})")
        moved = sum(1 for s_ in again["sites"] if s_["classification"] in moves)
        return {"from": old, "to": RULE_VERSION, "why": RULE_MIGRATIONS[old],
                "reclassification": {k: list(v) for k, v in sorted(moves.items())},
                "reclassified_sites": moved,
                "old_artifact_reproduced_modulo_reclassification": True}, None
    diff = {k: (baseline["metrics"][k], again["metrics"][k]) for k in RATCHETED
            if baseline["metrics"][k] != again["metrics"][k]}
    if diff or again["escaping_callees"] != baseline["escaping_callees"] \
            or again["site_table_sha256"] != baseline["site_table_sha256"]:
        return None, (f"under {RULE_VERSION} the baseline's own artifact does not reproduce it "
                      f"(figures {diff}; the rule change is not a pure refinement there)")
    return {"from": old, "to": RULE_VERSION, "why": RULE_MIGRATIONS[old],
            "old_artifact_reproduced_exactly": True}, None


def compare(baseline: dict, result: dict, migrating: bool = False,
            reclassified: bool = False) -> tuple[bool, list[str], list[str]]:
    """(ok, failures, notes). `migrating`: the rule-version difference was already cleared by
    `migration_check`, so it is not a failure here. `reclassified`: that migration was a DECLARED
    RECLASSIFICATION `migration_check` verified modulo its moves, so the same-artifact exact
    reproduction below is replaced by it (the ratchet's no-worse checks still run)."""
    fails: list[str] = []
    notes: list[str] = []
    if _seal(baseline) != baseline["seal"]:
        fails.append("BASELINE SEAL MISMATCH: the baseline was edited by hand (its content no longer "
                     "hashes to its seal). Regenerate it with --rebase/--init; never edit it.")
    if baseline["rule_version"] != RULE_VERSION and not migrating:
        fails.append(f"RULE VERSION: baseline {baseline['rule_version']!r} vs script {RULE_VERSION!r}. A "
                     f"changed rule changes what a figure means; re-create the baseline deliberately "
                     f"(git rm it, then --init) so the change is visible in review.")
    bs, ms = baseline["subject"], result["subject"]
    if (bs["crate"], bs["filter"]) != (ms["crate"], ms["filter"]):
        fails.append(f"SUBJECT CHANGED: baseline measured crate={bs['crate']!r} filter={bs['filter']!r}, this "
                     f"artifact is crate={ms['crate']!r} filter={ms['filter']!r}. Figures for another subject "
                     f"are not progress; re-create the baseline deliberately (git rm, then --init).")
    lost = Counter(bs["roots"]) - Counter(ms["roots"])
    if lost:
        fails.append(f"ROOTS LOST ({sum(lost.values())}): the artifact no longer lists roots the baseline "
                     f"measured, so a refused root could vanish as 'progress': "
                     + "; ".join(x[:140] for x in sorted(lost)[:6]))
    same_artifact = (baseline["artifact"].get("manifest_sha256") == result["artifact"]["manifest_sha256"]
                     and baseline["artifact"].get("module_sha256") == result["artifact"]["module_sha256"])
    bm, mm = baseline["metrics"], result["metrics"]
    if same_artifact and not reclassified:
        diff = {k: (bm[k], mm[k]) for k in RATCHETED if bm[k] != mm[k]}
        if diff:
            fails.append("BASELINE DOES NOT REPRODUCE from its own artifact (same sha256s): "
                         + ", ".join(f"{k} baseline={a} measured={b}" for k, (a, b) in diff.items())
                         + ". A baseline that claims a better (or a slacker) state than the artifact "
                           "supports is refused.")
        if baseline["escaping_callees"] != result["escaping_callees"]:
            fails.append("BASELINE DOES NOT REPRODUCE: pinned escaping-callee set differs on the same artifact.")
        if baseline["site_table_sha256"] != result["site_table_sha256"]:
            fails.append("BASELINE DOES NOT REPRODUCE: per-site table digest differs on the same artifact.")
    else:
        notes.append("artifact differs from the baseline's (manifest/module sha256): comparing as a ratchet")
    worse = [k for k in RATCHETED if mm[k] > bm[k]]
    for k in worse:
        fails.append(f"REGRESSION {k}: {bm[k]} -> {mm[k]}")
    # The anti-swap pin, keyed modulo identity hashes and compared as a multiset (see RATCHET SEMANTICS).
    canon_b = Counter(tir_symbols.canonical_identity(x) for x in baseline["escaping_callees"])
    canon_r = Counter(tir_symbols.canonical_identity(x) for x in result["escaping_callees"])
    new_canon = canon_r - canon_b
    new_esc = sorted(x for x in result["escaping_callees"] if tir_symbols.canonical_identity(x) in new_canon)
    if new_canon:
        fails.append(f"NEW ESCAPING CALLEES not in the baseline's pinned set, compared modulo identity hashes "
                     f"({sum(new_canon.values())}; a swap keeps counts flat): "
                     + "; ".join(x[:140] for x in new_esc[:8]))
    renamed = len(set(result["escaping_callees"]) - set(baseline["escaping_callees"])) if not new_canon else 0
    if renamed:
        notes.append(f"IDENTITY RENAMES: {renamed} pinned escaping callee(s) differ from the baseline's only in "
                     f"identity-hash tokens (__trust_args@, __trust_crate@, <crate>[..]); pinned modulo them")
    better = [k for k in RATCHETED if mm[k] < bm[k]]
    if better and not fails:
        notes.append("PROGRESS: " + ", ".join(f"{k} {bm[k]} -> {mm[k]}" for k in better)
                     + ". Run with --rebase --reason '...' to lock it in.")
    return (not fails), fails, notes


# ─────────────────────────────────── report ────────────────────────────────────


def _compact_sites(sites: list[dict]) -> dict:
    """Every site that is not a member call or a panic terminal, as table rows over
    interned member and callee names (the full names are long)."""
    members: dict[int, str] = {}
    callees: list[str] = []
    cidx: dict[str, int] = {}
    rows = []
    for s in sites:
        if s["classification"] in ("member-call", "panic-terminal", "ub-terminal"):
            continue
        members[s["member"]] = s["member_name"]
        if s["resolved"] not in cidx:
            cidx[s["resolved"]] = len(callees)
            callees.append(s["resolved"])
        ev = []
        for e in s["evidence"]:
            k, _, sub = e.partition(":")
            ev.append(k if k in ("obl_absent", "obl_panic", "obl_ub", "call") else e)
        rows.append([s["member"], s["bb"], s.get("bb_range"), s["call_index"], cidx[s["resolved"]],
                     s["classification"], s.get("escaping_class", ""), "+".join(ev),
                     bool(s.get("silent_havoc"))])
    return {
        "columns": ["member", "bb", "bb_range_if_unkeyed", "call_index", "callee", "classification",
                    "escaping_class", "evidence", "silent_havoc"],
        "members_note": "sidecar_func_id -> member name, truncated to 240 chars (the id is the key)",
        "members": {str(k): v[:240] for k, v in sorted(members.items())},
        "callees": [c[:300] for c in callees],
        "rows": rows,
    }


def build_report(result: dict, baseline_path: Path | None, verdict: str) -> dict:
    detail = _compact_sites(result["sites"])
    return {
        "schema": REPORT_SCHEMA,
        "rule_version": RULE_VERSION,
        "generated": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "script": "scripts/crystal_link3_reconcile.py",
        "script_sha256": script_sha256(),
        "baseline": str(baseline_path) if baseline_path else None,
        "verdict": verdict,
        "artifact": result["artifact"],
        "metrics": result["metrics"],
        "info": result["info"],
        "unreconciled": result["unreconciled"],
        "escaping_rows": result["rows"],
        "intrinsic_instances": result["intrinsics"],
        "escaping_callees_count": len(result["escaping_callees"]),
        "escaping_callees_note": "the pinned set itself lives in the baseline (anti-swap pin)",
        "site_table_sha256": result["site_table_sha256"],
        "sites_detail_note": "every Call terminator that is not a member call or a panic terminal, "
                             "keyed (member = sidecar_func_id, bb = MIR basic block). bb=null means no "
                             "positive evidence keys the site, and bb_range_if_unkeyed gives the admissible "
                             "blocks. Member calls and panic terminals are counted in "
                             "info.call_sites_by_classification and pinned by site_table_sha256 "
                             "(panic terminals) / the alignment (member calls).",
        "sites_detail": detail,
    }


def summary_lines(result: dict) -> list[str]:
    m, i = result["metrics"], result["info"]
    return [
        f"LINK3-RECONCILE members={i['members']} call_sites={i['call_sites_total']} "
        f"by_class={i['call_sites_by_classification']}",
        f"  escaping rows: per_instance={m['escaping_rows_per_instance']} module_wide={m['escaping_rows_module_wide']} "
        f"(manifest reports {i['manifest_escaping_rows']}; reviewers' rule {i['per_instance_reviewers_rule_obligation_names_it']}; "
        f"trust-ir-native-counts rule {i['per_instance_trustir_native_counts_as_modelled']})",
        f"  escaping call sites={m['escaping_call_sites']} by_class={i['escaping_call_sites_by_class']} "
        f"(reviewers' per-site rule {i['per_site_reviewers_rule_escaping']})",
        f"  intrinsic instances={i['intrinsic_instances']} worst-site={i['intrinsic_instances_by_worst_site']}",
        f"  producer per-site evidence: declared={i['producer_declares_site_evidence']} "
        f"{i['producer_site_evidence']} manifest intrinsic rows={i['manifest_intrinsic_rows']}",
        f"  silent havocs={m['silent_havoc_call_sites']} unkeyed={m['unkeyed_call_sites']} "
        f"(keyed by the producer's bb alone={i['sites_keyed_by_producer_bb_only']}) "
        f"refused roots={m['refused_roots']}/{i['roots_total']} (subsumed, verified={i['roots_subsumed']}) "
        f"premise sites lowered as havoc={m['premise_sites_lowered_as_havoc']} "
        f"(as a declared call={i['premise_sites_lowered_as_call']}, declarations={i['declared_premise_functions']}) "
        f"unreconciled={m['unreconciled']}",
        f"  drop-glue assumption sites={m['drop_glue_assumption_sites']} "
        f"({i['drop_glue_assumption_obligations']} obligations, {i['drop_glue_assumption_distinct_types']} glue types; "
        f"MIR Drop edges the walk never follows, outside the row figures)",
        f"  by value: indirect sites={i['indirect_sites_dispatched_by_value']} "
        f"(through the shim adapter={i['indirect_sites_dispatched_through_shim_adapter']}, "
        f"through an ABI thunk={i.get('indirect_sites_dispatched_through_abi_thunk', 0)}); "
        f"TLS input premise ops={i['tls_input_premise_ops']} (uncertified={i['tls_input_premise_ops_uncertified']})",
    ]


# ─────────────────────────────────── CLI ───────────────────────────────────────


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Crystal link-3 per-call-site reconciliation ratchet.")
    ap.add_argument("--manifest", type=Path, help="callees manifest JSON (default: the baseline's)")
    ap.add_argument("--module", type=Path, help="trust-ir text module (default: named by the manifest)")
    ap.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    ap.add_argument("--report", type=Path, help="write the full JSON report here")
    ap.add_argument("--rebase", action="store_true", help="lower the baseline to the measurement")
    ap.add_argument("--init", action="store_true", help="create the baseline (only if absent)")
    ap.add_argument("--reason", default="", help="mandatory with --rebase/--init")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--pinned-inputs", action="store_true",
                    help="print the first-party modules this script runs besides itself; run nothing")
    try:
        args = ap.parse_args(argv)
    except SystemExit as exc:
        return EXIT_USAGE if exc.code else EXIT_OK
    if args.pinned_inputs:
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return EXIT_OK
    if args.self_test:
        return self_test()
    if (args.rebase or args.init) and len(args.reason.strip()) < 10:
        print("USAGE: --rebase/--init require --reason with a real explanation (>= 10 chars)", file=sys.stderr)
        return EXIT_USAGE
    if args.rebase and args.init:
        print("USAGE: --rebase and --init are exclusive", file=sys.stderr)
        return EXIT_USAGE
    try:
        baseline = None
        if not args.init:
            baseline = load_baseline(args.baseline)
        manifest_path = args.manifest
        if manifest_path is None:
            if baseline is None:
                print("USAGE: --manifest is required with --init", file=sys.stderr)
                return EXIT_USAGE
            manifest_path = Path(baseline["artifact"]["manifest_path"])
        result = measure(manifest_path, args.module)
    except Refusal as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        return EXIT_REFUSE
    for line in summary_lines(result):
        print(line)
    for u in result["unreconciled"][:20]:
        print(f"  UNRECONCILED {json.dumps(u)[:300]}")

    if args.init:
        if args.baseline.exists():
            print(f"FAIL: --init refuses to overwrite {args.baseline}. Lower it with --rebase; a "
                  f"deliberate re-baseline is `git rm` then --init, visible in review.", file=sys.stderr)
            return EXIT_FAIL
        write_json(args.baseline, baseline_body(result, args.reason.strip(), [], None))
        verdict = "init"
        print(f"INIT: baseline written to {args.baseline}")
        if args.report:
            write_json(args.report, build_report(result, args.baseline, verdict))
        return EXIT_OK

    migration = None
    if args.rebase and baseline["rule_version"] != RULE_VERSION and _seal(baseline) == baseline["seal"]:
        migration, why_not = migration_check(baseline)
        if migration is None:
            print(f"FAIL: --rebase across a rule change refused: {why_not}. Re-create the baseline "
                  f"deliberately (git rm it, then --init) instead.", file=sys.stderr)
            return EXIT_FAIL
        if "reclassification" in migration:
            print(f"RULE MIGRATION {migration['from']} -> {migration['to']}: the baseline's own artifact "
                  f"reproduces its site table modulo the DECLARED RECLASSIFICATION "
                  f"{migration['reclassification']} ({migration['reclassified_sites']} site(s) moved), "
                  f"with no ratcheted figure worse")
        else:
            print(f"RULE MIGRATION {migration['from']} -> {migration['to']}: the baseline's own artifact "
                  f"reproduces every figure under the new rule")
    ok, fails, notes = compare(baseline, result, migrating=migration is not None,
                               reclassified=migration is not None and "reclassification" in migration)
    if args.rebase:
        if not ok:
            for f in fails:
                print(f"FAIL: {f}", file=sys.stderr)
            print("FAIL: --rebase refused; it may only LOWER the baseline, and only on a measurement that is "
                  "no worse on every figure and pins no new escaping callee.", file=sys.stderr)
            return EXIT_FAIL
        same = (baseline["artifact"]["manifest_sha256"] == result["artifact"]["manifest_sha256"]
                and baseline["artifact"]["module_sha256"] == result["artifact"]["module_sha256"])
        improved = any(result["metrics"][k] < baseline["metrics"][k] for k in RATCHETED) or \
            set(result["escaping_callees"]) < set(baseline["escaping_callees"])
        if same and not improved and migration is None:
            print("FAIL: --rebase refused: same artifact, nothing improved; there is nothing to lock in.",
                  file=sys.stderr)
            return EXIT_FAIL
        write_json(args.baseline, baseline_body(result, args.reason.strip(), baseline.get("history", []), baseline,
                                                migration))
        print(f"REBASE: baseline lowered/re-pinned in {args.baseline}")
        if args.report:
            write_json(args.report, build_report(result, args.baseline, "rebase"))
        return EXIT_OK
    for n in notes:
        print(n)
    if args.report:
        write_json(args.report, build_report(result, args.baseline, "pass" if ok else "fail"))
    if not ok:
        for f in fails:
            print(f"FAIL: {f}", file=sys.stderr)
        return EXIT_FAIL
    print("PASS: link-3 reconciliation is no worse than the baseline on every ratcheted figure")
    return EXIT_OK


# ───────────────────────────────── self-test ───────────────────────────────────

_F0 = "root::f0"
_F1 = "root::f1"
_CLONE = "<alloc::string::String as core::clone::Clone>::clone"
_CTPOP = "core::intrinsics::ctpop::<usize>::<__trust_args@aa>"
_XADD = "core::intrinsics::atomic_xadd::<usize, usize, core::intrinsics::AtomicOrdering::Relaxed>::<__trust_args@bb>"
_COLD = "core::intrinsics::cold_path"
_ALLOC = "alloc::alloc::{extern#0}::__rust_alloc"
_DYN = "<dyn T as T>::m::<__trust_args@cc>"
_PANIC = "core::panicking::panic"


def _q(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def _obl(oid: int, desc: str, fid: int, fname: str, bb: int, site: bool = False,
         src: str | None = None) -> str:
    src = src or f"mir-assert:{fname}:bb{bb}:terminator"
    payload = json.dumps({"source_id": src, "assertion_id": "trust-assertion:" + src,
                          "native_assertion_id": oid, "span": {"file": "x.rs", "line_start": 1}})
    line = (f"obligation {oid} panic_freedom pending {_q(desc)} function {fid} formula "
            f"{_q('trust.trust_ir.obligation-source.v1')} {_q(payload)} source {_q(src)} "
            f"assertion {_q('trust-assertion:' + src)} range 0 1 0 1 1")
    if site:
        line += f" site f{fid}/bb{bb}#1"
    return line


def _havoc(v: int, ty: str) -> list[str]:
    return [f"    %{v} = const bool false", f"    assert %{v}  ; #proof: no_panic",
            f"    %{v + 1} = undef {ty}  ; #proof: fresh_symbolic_havoc"]


def _synthetic(tmp: Path, tag: str, *, extra_escape: bool = False, swap: bool = False,
               drop_clone: bool = False, drop_ctpop_obligation: bool = False,
               ambiguous: bool = False, extra_drop: bool = False) -> Path:
    """A two-member bundle with one of every site class. Returns the manifest path."""
    mir_fn = "ext::other_fn" if swap else "ext::mir_unavail_fn"
    f0 = [f"fn @{_F0}(functy.0) {{", "    ; #producer: trust-ir",
          "bb0(%0: ptr):", "    %1 = call @func.1(%0)", "    br bb1",
          "bb1:", *_havoc(2, "u32"), "    br bb2",
          "bb2:", "    %4 = const u64 1", "    %5 = atomicrmw add u64, ptr %0, %4", "    br bb3",
          "bb3:", "    %6 = const bool true", "    condbr %6, bb4, bb5",
          "bb4:", "    %7 = const bool false", "    assert %7  ; #proof: no_panic", "    unreachable",
          "bb5:", "    ret",
          # a MIR Drop terminator whose glue is an unproven assumption: a halting `assert false`
          "bb6:", "    %8 = const bool false", "    assert %8  ; #proof: no_panic", "    br bb5",
          *(["bb7:", "    %9 = const bool false", "    assert %9  ; #proof: no_panic", "    br bb5"]
            if extra_drop else []),
          "}"]
    n0 = 8 if extra_drop else 7
    f1 = [f"fn @{_F1}(functy.1) {{", "    ; #producer: trust-ir",
          "bb0(%0: ptr):",
          *(["    %1 = copy ptr %0", "    %2 = undef u64"] if ambiguous else _havoc(1, "u64")),
          "    br bb1",
          "bb1:", "    %3 = copy ptr %0",
          ("    %4 = copy ptr %3" if drop_clone and not ambiguous else "    %4 = undef struct.1"),
          "    br bb2",
          "bb2:", *_havoc(5, "ptr"), "    %7 = call_indirect %6(functy.0)(%0)", "    br bb3",
          "bb3:", "    br bb4",
          "bb4:", *_havoc(8, "ptr"), "    br bb5",
          "bb5:", *_havoc(10, "u8"), "    br bb6"]
    if extra_escape:
        # one more absent MIR-unavailable call site in its own block, labels kept consecutive
        f1 += ["bb6:", *_havoc(12, "u8"), "    br bb7", "bb7:", "    ret", "}"]
        n1 = 8
    else:
        f1 += ["bb6:", "    ret", "}"]
        n1 = 7
    obls = []

    def add(desc, fid, fname, bb, site=False, src=None):
        obls.append(_obl(len(obls), desc, fid, fname, bb, site, src))

    # A function-level obligation that names no call site: losing it moves no figure.
    add(f"{_F0}: all assertions hold", 0, _F0, 0, src=f"mir-assertions:{_F0}:panic-freedom")
    if not drop_ctpop_obligation:
        add(f"[trust-absent-callee-assumption] call to absent callee `{_CTPOP}` (body not in the lowered bundle) may panic", 0, _F0, 1)
    add(f"panic call `{_PANIC}` must be unreachable", 0, _F0, 4, site=True)
    _drop = '[trust-drop-glue-assumption] drop glue for `Datatype { name: "root::T", variants: [] }` ' \
            'has unproven panic-freedom (user Drop impls may panic)'
    add(_drop, 0, _F0, 6)
    if extra_drop:
        add(_drop, 0, _F0, 7)
    if not ambiguous:
        add(f"[trust-absent-callee-assumption] call to absent callee `{mir_fn}` (body not in the lowered bundle) may panic", 1, _F1, 0)
    add("indirect call through fn-pointer `fn()` may panic (call target unresolved)", 1, _F1, 2)
    add(f"[trust-absent-callee-assumption] call to absent callee `{_ALLOC}` (body not in the lowered bundle) may panic", 1, _F1, 4)
    add(f"[trust-absent-callee-assumption] call to absent callee `{_DYN}` (dynamic dispatch) may panic", 1, _F1, 5)
    if extra_escape:
        add("[trust-absent-callee-assumption] call to absent callee `ext::another` (body not in the lowered bundle) may panic", 1, _F1, 6)
    text = "\n".join([MODULE_HEADER, 'module "synthetic::callees"', 'file 0 "x.rs"',
                      "struct @alloc::string::String id=1", *f0, *f1, *obls]) + "\n"
    mod = tmp / f"{tag}.trust-ir.txt"
    mod.write_text(text)
    calls1 = [
        {"site": mir_fn, "resolved": mir_fn, "class": "escaping: callee refused on its own walk"},
    ]
    if not drop_clone:
        calls1.append({"site": _CLONE + "::<__trust_args@dd>", "resolved": _CLONE,
                       "class": "escaping: callee refused on its own walk"})
    calls1 += [
        {"site": "<indirect>", "resolved": "", "class": "escaping: indirect call (fn()); enumerated targets []"},
        {"site": _COLD, "resolved": _COLD, "class": f"intrinsic-terminal: {_COLD}"},
        {"site": _ALLOC, "resolved": _ALLOC, "class": f"foreign-terminal: {_ALLOC}"},
        {"site": _DYN, "resolved": _DYN, "class": "escaping: callee refused on its own walk"},
    ]
    if extra_escape:
        calls1.append({"site": "ext::another", "resolved": "ext::another",
                       "class": "escaping: callee refused on its own walk"})
    escaping = [
        f"{_DYN}: bodyless instance kind Virtual; vtable enumeration 0 (downstream)",
        f"{mir_fn}: MIR unavailable",
        f"{_F1}: indirect call (non-const func operand of type fn()); enumerated targets 0",
        "ext::reified: MIR unavailable",
    ]
    if not drop_clone:
        escaping.insert(2, f"{_CLONE}: MIR unavailable")
    if extra_escape:
        escaping.append("ext::another: MIR unavailable")
    manifest = {
        "schema": MANIFEST_SCHEMA_V2, "crate": "synthetic", "filter": "local:f0", "producer": {},
        "closed": False, "closed_meaning": "", "closed_modulo_foreign": False,
        "closed_modulo_foreign_meaning": "", "lowering": "ok",
        "roots": [
            {"caller": "<local root>", "callee_def_path": "f0", "crate_decl_func_ids": [0],
             "resolved": _F0, "sidecar_func_id": 0, "outcome": "resolved"},
            {"caller": "<local root>", "callee_def_path": "f0::{closure#0}", "crate_decl_func_ids": [],
             "resolved": None, "sidecar_func_id": None, "outcome": "refused: local root is Closure, not a fn"},
        ],
        "members": [
            {"sidecar_func_id": 0, "name": _F0, "instance_kind": "Item", "def_path": "f0",
             "mir_blocks": n0, "extracted_blocks": n0, "calls": [
                 {"site": _F1, "resolved": _F1, "class": "member"},
                 {"site": _CTPOP, "resolved": _CTPOP, "class": f"intrinsic-terminal: {_CTPOP}"},
                 {"site": _XADD, "resolved": _XADD, "class": f"intrinsic-terminal: {_XADD}"},
                 {"site": _PANIC, "resolved": _PANIC, "class": "panic-terminal"},
             ]},
            {"sidecar_func_id": 1, "name": _F1, "instance_kind": "Item", "def_path": "f1",
             "mir_blocks": n1, "extracted_blocks": n1, "calls": calls1},
        ],
        "panic_terminals": [_PANIC],
        "foreign_terminals": [_ALLOC],
        "escaping": escaping,
        "artifacts": {"text": mod.name, "text_bytes": len(text.encode()), "binary": "x.bin", "binary_bytes": 0},
    }
    mpath = tmp / f"{tag}.manifest.json"
    mpath.write_text(json.dumps(manifest, indent=1))
    return mpath


def _run(argv: list[str]) -> tuple[int, str]:
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = main(argv)
    return code, out.getvalue() + err.getvalue()


def _respelled(mpath: Path, tag: str, *, only: int | None = None,
               subst: tuple[tuple[str, str], ...] = ()) -> Path:
    """A copy of the synthetic artifact at `mpath` whose `fn` headers are printed by the WS4.3
    printer (all of them, or only function `only`), with every `subst` pair applied to the module
    text and the manifest alike (identity-hash renames). Returns the new manifest path."""
    man = json.loads(mpath.read_text())
    text = (mpath.parent / man["artifacts"]["text"]).read_text()
    for a, b in subst:
        text = text.replace(a, b)
    k = [-1]

    def head(m: re.Match) -> str:
        k[0] += 1
        if (only is not None and k[0] != only) or m.group(1).startswith('"'):
            return m.group(0)
        return f"fn @{tir_symbols.spell_symbol(m.group(1))}(functy.{m.group(2)}) {{"

    text = re.sub(r"(?m)^fn @(.*)\(functy\.(\d+)\) \{$", head, text)
    mod = mpath.parent / f"{tag}.trust-ir.txt"
    mod.write_text(text)

    def walk(x):
        if isinstance(x, str):
            for a, b in subst:
                x = x.replace(a, b)
            return x
        if isinstance(x, list):
            return [walk(y) for y in x]
        if isinstance(x, dict):
            return {walk(k_): walk(v) for k_, v in x.items()}
        return x

    man = walk(man)
    man["artifacts"]["text"], man["artifacts"]["text_bytes"] = mod.name, len(text.encode())
    out = mpath.parent / f"{tag}.manifest.json"
    out.write_text(json.dumps(man, indent=1))
    return out


def self_test() -> int:
    results: list[tuple[str, bool, str]] = []

    def check(name: str, cond: bool, detail: str = "") -> None:
        results.append((name, bool(cond), detail))

    with tempfile.TemporaryDirectory(prefix="l3rec-") as td:
        tmp = Path(td)
        base = _synthetic(tmp, "base")
        bl = tmp / "baseline.json"

        # 1. The base artifact measures exactly as constructed by hand.
        r = measure(base)
        m = r["metrics"]
        # Rule /9 (D10): the base's xadd is a SEQ premise site, not an escape -- its instance leaves the
        # per-instance rows (5 + 2), the module-wide rule still counts every intrinsic instance while
        # one site anywhere is unmodelled (5 + 3), and one escaping site fewer (7 -> 6).
        expect = {"escaping_rows_per_instance": 5 + 2, "escaping_rows_module_wide": 5 + 3,
                  "escaping_call_sites": 6, "silent_havoc_call_sites": 1, "unkeyed_call_sites": 1,
                  "refused_roots": 1, "premise_sites_lowered_as_havoc": 1, "unreconciled": 0,
                  "drop_glue_assumption_sites": 1}
        check("01 base metrics are the hand-derived ones", m == expect, f"{m}")
        check("02 reviewers' rule counts only the obligation-named intrinsic (5+1)",
              r["info"]["per_instance_reviewers_rule_obligation_names_it"] == 6,
              str(r["info"]["per_instance_reviewers_rule_obligation_names_it"]))
        rmw_line0 = "    %5 = atomicrmw add u64, ptr %0, %4\n"
        src0 = (tmp / "base.trust-ir.txt").read_text()
        assert src0.count(rmw_line0) == 1, "self-test: the base module's xadd line moved"
        maxmod = tmp / "base-umax.trust-ir.txt"
        maxsrc = src0.replace(rmw_line0, rmw_line0.replace("atomicrmw add", "atomicrmw umax"), 1)
        maxmod.write_text(maxsrc)
        mjx = json.loads(base.read_text())
        mjx["artifacts"]["text"], mjx["artifacts"]["text_bytes"] = maxmod.name, len(maxsrc.encode())
        pmx = tmp / "base-umax.manifest.json"
        pmx.write_text(json.dumps(mjx))
        rmx = measure(pmx)
        check("03 rule /9 (D10): a native atomic the projector images under SEQ is a PREMISE site "
              "(`atomic-seq-premise`, not escaping); one it cannot image (an `umax` rmw) stays "
              "`intrinsic-unprojectable`",
              r["info"]["call_sites_by_classification"].get("atomic-seq-premise") == 1
              and r["info"]["escaping_call_sites_by_class"].get("intrinsic-unprojectable") is None
              and r["info"]["premise_sites_atomic_seq"] == 1 and r["info"]["closed_derived"] is False
              and rmx["info"]["escaping_call_sites_by_class"].get("intrinsic-unprojectable") == 1
              and rmx["info"]["premise_sites_atomic_seq"] == 0,
              f"{r['info']['call_sites_by_classification']} {rmx['info']['escaping_call_sites_by_class']}")
        check("04 the empty cold_path site is unevidenced and unkeyed, with a bb range",
              any(s["resolved"] == _COLD and s["bb"] is None and s["bb_range"] == [3, 3] for s in r["sites"]))
        check("05 the silent String::clone havoc is keyed to (f1, bb1)",
              any(s["resolved"] == _CLONE and s["bb"] == 1 and s.get("silent_havoc") for s in r["sites"]))
        check("06 every site is keyed by (member, bb) from the module",
              all((s["bb"] is not None) or s["verdict"] == "unevidenced" for s in r["sites"]))
        check("07 the address-taken row with no call site is reported, not dropped",
              r["info"]["manifest_rows_without_call_site"] == ["ext::reified: MIR unavailable"])

        # 2. PASS at the baseline.
        code, out = _run(["--init", "--reason", "self-test initial baseline", "--manifest", str(base),
                          "--baseline", str(bl)])
        check("08 --init writes a baseline", code == EXIT_OK and bl.exists(), out[-300:])
        code, out = _run(["--baseline", str(bl)])
        check("09 pass at baseline (exit 0)", code == EXIT_OK and "PASS" in out, out[-300:])
        code, out = _run(["--init", "--reason", "self-test initial baseline", "--manifest", str(base),
                          "--baseline", str(bl)])
        check("10 --init refuses to overwrite an existing baseline", code == EXIT_FAIL, out[-200:])

        # 3. FAIL on a regression.
        worse = _synthetic(tmp, "worse", extra_escape=True)
        code, out = _run(["--manifest", str(worse), "--baseline", str(bl)])
        check("11 regression (one more escaping site/row) fails (exit 1)",
              code == EXIT_FAIL and "REGRESSION escaping_rows_per_instance" in out, out[-400:])
        code, out = _run(["--rebase", "--reason", "trying to rebase a regression", "--manifest", str(worse),
                          "--baseline", str(bl)])
        check("12 --rebase refuses a regression", code == EXIT_FAIL and "refused" in out, out[-300:])

        # 4. FAIL on a one-for-one swap (counts flat, a different callee escapes).
        swap = _synthetic(tmp, "swap", swap=True)
        rs = measure(swap)
        code, out = _run(["--manifest", str(swap), "--baseline", str(bl)])
        check("13 swap with flat counts fails on the pinned escaping-callee set",
              rs["metrics"] == m and code == EXIT_FAIL and "NEW ESCAPING CALLEES" in out, out[-300:])

        # 5. A baseline that claims a BETTER state than the artifact supports is refused.
        good = json.loads(bl.read_text())
        tampered = json.loads(json.dumps(good))
        tampered["metrics"]["escaping_rows_per_instance"] -= 1
        tb = tmp / "tampered.json"
        tb.write_text(json.dumps(tampered))
        code, out = _run(["--baseline", str(tb)])
        check("14 hand-lowered baseline without re-seal is refused (seal)",
              code == EXIT_FAIL and "SEAL MISMATCH" in out, out[-300:])
        tampered["seal"] = _seal(tampered)
        tb.write_text(json.dumps(tampered))
        code, out = _run(["--baseline", str(tb)])
        check("15 hand-lowered AND re-sealed baseline is refused (same-artifact reproduction)",
              code == EXIT_FAIL and "DOES NOT REPRODUCE" in out, out[-300:])
        slack = json.loads(json.dumps(good))
        slack["metrics"]["silent_havoc_call_sites"] += 5
        slack["seal"] = _seal(slack)
        tb.write_text(json.dumps(slack))
        code, out = _run(["--baseline", str(tb)])
        check("16 hand-RAISED (slack) re-sealed baseline is refused too",
              code == EXIT_FAIL and "DOES NOT REPRODUCE" in out, out[-300:])
        rv = json.loads(json.dumps(good))
        rv["rule_version"] = "crystal-link3-reconcile/0"
        rv["seal"] = _seal(rv)
        tb.write_text(json.dumps(rv))
        code, out = _run(["--baseline", str(tb)])
        check("17 a baseline from another rule version is refused", code == EXIT_FAIL and "RULE VERSION" in out)

        # 6. A MISSING obligation never counts as evidence.
        noobl = _synthetic(tmp, "noobl", drop_ctpop_obligation=True)
        rn = measure(noobl)
        check("18 removing an intrinsic's obligation does not model it (still escaping, now unkeyed)",
              rn["metrics"]["escaping_rows_per_instance"] == m["escaping_rows_per_instance"]
              and rn["metrics"]["escaping_call_sites"] == m["escaping_call_sites"]
              and rn["metrics"]["unkeyed_call_sites"] == m["unkeyed_call_sites"] + 1,
              f"{rn['metrics']}")
        check("19 ...while the reviewers' name-intersection rule WOULD have promoted it",
              rn["info"]["per_instance_reviewers_rule_obligation_names_it"] == 5)
        code, out = _run(["--manifest", str(noobl), "--baseline", str(bl)])
        check("20 and the ratchet fails on it (unkeyed rose)", code == EXIT_FAIL and "unkeyed" in out, out[-300:])

        # 7. Fail closed on malformed or truncated artifacts: refusal (2), never "zero".
        mj = json.loads(base.read_text())
        del mj["escaping"]
        p = tmp / "noesc.manifest.json"
        p.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(p), "--baseline", str(bl)])
        check("21 manifest missing `escaping` is a REFUSAL, not zero escaping",
              code == EXIT_REFUSE and "no `escaping` key" in out, out[-300:])
        mj = json.loads(base.read_text())
        mj["escaping"] = {"n": 0}
        p.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(p), "--baseline", str(bl)])
        check("22 manifest `escaping` of the wrong type is refused", code == EXIT_REFUSE, out[-200:])
        p.write_text(base.read_text()[: len(base.read_text()) // 2])
        code, out = _run(["--manifest", str(p), "--baseline", str(bl)])
        check("23 truncated manifest JSON is refused", code == EXIT_REFUSE, out[-200:])

        mod_src = (tmp / "base.trust-ir.txt").read_text()

        def with_module(tag: str, text: str, fix_bytes: bool) -> Path:
            mp = tmp / f"{tag}.trust-ir.txt"
            mp.write_text(text)
            mj2 = json.loads(base.read_text())
            mj2["artifacts"]["text"] = mp.name
            if fix_bytes:
                mj2["artifacts"]["text_bytes"] = len(text.encode())
            mf = tmp / f"{tag}.manifest.json"
            mf.write_text(json.dumps(mj2))
            return mf

        cut = mod_src[:-40]
        code, out = _run(["--manifest", str(with_module("cut", cut, False)), "--baseline", str(bl)])
        check("24 module truncated mid-line: byte count refuses", code == EXIT_REFUSE and "truncated" in out, out[-200:])
        code, out = _run(["--manifest", str(with_module("cut2", cut, True)), "--baseline", str(bl)])
        check("25 module truncated mid-obligation with matching byte count: parser refuses",
              code == EXIT_REFUSE, out[-200:])
        lines = mod_src.rstrip("\n").split("\n")
        at_line = "\n".join(lines[:-1]) + "\n"
        code, out = _run(["--manifest", str(with_module("cut3", at_line, True)), "--baseline", str(bl)])
        check("26 module truncated at a line boundary (last obligation lost) does not pass",
              code != EXIT_OK, out[-300:])
        body_cut = mod_src[: mod_src.index("bb6:\n    ret\n}")] + "bb6:\n    ret"
        code, out = _run(["--manifest", str(with_module("cut4", body_cut, True)), "--baseline", str(bl)])
        check("27 module that ends inside a function is refused",
              code == EXIT_REFUSE and "ends inside function" in out, out[-200:])
        lost = mod_src.replace(lines[[i for i, l in enumerate(lines) if l.startswith("obligation 0 ")][0]] + "\n", "", 1)
        code, out = _run(["--manifest", str(with_module("lost", lost, True)), "--baseline", str(bl)])
        check("27b a lost obligation line is refused even when it moves no figure",
              code == EXIT_REFUSE and "obligation ids" in out, out[-200:])
        wrongfn = mod_src.replace(f"mir-assert:{_F1}:bb0:terminator", "mir-assert:root::fX:bb0:terminator")
        code, out = _run(["--manifest", str(with_module("wrongfn", wrongfn, True)), "--baseline", str(bl)])
        check("28 an obligation whose source names another function is refused",
              code == EXIT_REFUSE, out[-200:])
        mj = json.loads(base.read_text())
        mj["members"] = mj["members"][:1]
        p.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(p), "--baseline", str(bl)])
        check("29 members/functions count mismatch is refused", code == EXIT_REFUSE, out[-200:])
        mj = json.loads(base.read_text())
        mj["lowering"] = "error: partial"
        p.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(p), "--baseline", str(bl)])
        check("30 a partial bundle (lowering != ok) is refused", code == EXIT_REFUSE, out[-200:])
        code, out = _run(["--baseline", str(tmp / "absent.json")])
        check("31 a missing baseline is a refusal", code == EXIT_REFUSE, out[-200:])

        # 8. A text match is not evidence: a stray `call @core::intrinsics::` spelling cannot model anything.
        spoof = mod_src.replace("    br bb2\nbb2:", "    ; call @core::intrinsics::ctpop\n    br bb2\nbb2:", 1)
        rsp = measure(with_module("spoof", spoof, True))
        check("32 a comment spelling `call @core::intrinsics::` changes nothing",
              rsp["metrics"] == m, f"{rsp['metrics']}")

        # 9. A module call the manifest does not list is unreconciled.
        extra = mod_src.replace("bb3:\n    br bb4", "bb3:\n    %99 = call @func.0(%0)\n    br bb4", 1)
        rx = measure(with_module("extra", extra, True))
        check("33 an unexplained module call is counted as unreconciled",
              rx["metrics"]["unreconciled"] >= 1, f"{rx['unreconciled'][:2]}")
        gone = mod_src.replace("    %1 = call @func.1(%0)\n", "    %1 = copy ptr %0\n", 1)
        rg = measure(with_module("gone", gone, True))
        check("33b a manifest member call the module does not carry is unreconciled AND escaping",
              any(u["kind"] == "manifest-row-contradicted-by-module" for u in rg["unreconciled"])
              and rg["metrics"]["escaping_call_sites"] == m["escaping_call_sites"] + 1,
              f"{rg['metrics']} {rg['unreconciled'][:2]}")

        # 9a. A foreign terminal must be LISTED; an indirect site needs its obligation too.
        mj = json.loads(base.read_text())
        mj["foreign_terminals"] = []
        pf = tmp / "unlisted.manifest.json"
        pf.write_text(json.dumps(mj))
        ru = measure(pf)
        check("33d a foreign call whose callee is not in foreign_terminals is not a foreign terminal",
              ru["info"]["call_sites_by_classification"].get("foreign-terminal", 0) == 0
              and ru["metrics"]["unreconciled"] >= 1, f"{ru['metrics']}")
        noind = mod_src.replace('"indirect call through fn-pointer `fn()` may panic (call target unresolved)"',
                                f'"{_F1}: all assertions hold"', 1)
        noind = noind.replace(f'mir-assert:{_F1}:bb2:terminator', f'mir-assertions:{_F1}:panic-freedom')
        rni = measure(with_module("noind", noind, True))
        check("33e a call_indirect with no obligation is not reconciled as an indirect row",
              rni["metrics"]["unreconciled"] >= 1
              and not any(s.get("verdict") == "indirect" for s in rni["sites"]), f"{rni['metrics']}")

        mj = json.loads(base.read_text())
        mj["escaping"] = [r for r in mj["escaping"] if not r.startswith("ext::mir_unavail_fn:")]
        pd = tmp / "droprow.manifest.json"
        pd.write_text(json.dumps(mj))
        rd = measure(pd)
        check("33f a manifest that DROPS an escaping row does not lower the row count (derived from sites)",
              rd["metrics"]["escaping_rows_per_instance"] == m["escaping_rows_per_instance"]
              and rd["metrics"]["unreconciled"] >= 1, f"{rd['metrics']}")

        # 9b. Weak (silent) evidence keys a row only when it is the UNIQUE candidate.
        amb = _synthetic(tmp, "amb", drop_clone=True, ambiguous=True)
        ra = measure(amb)
        site = [s for s in ra["sites"] if s["resolved"] == "ext::mir_unavail_fn"]
        check("33c two silent-undef candidates for one row: the site stays UNKEYED, never guessed",
              len(site) == 1 and site[0]["bb"] is None and site[0].get("ambiguous_candidates") == [0, 1],
              f"{site}")

        # 10. Panic terminals need a HALTING false assert at the site; a dead `br` tail is counted.
        noassert = mod_src.replace("bb4:\n    %7 = const bool false", "bb4:\n    %7 = const bool true", 1)
        rna = measure(with_module("noassert", noassert, True))
        check("34 a panic obligation without a false assert is NOT a panic terminal (unreconciled)",
              rna["metrics"]["unreconciled"] >= 1
              and rna["info"]["call_sites_by_classification"].get("panic-terminal", 0) == 0,
              f"{rna['metrics']} {rna['info']['call_sites_by_classification']}")
        brtail = mod_src.replace("assert %7  ; #proof: no_panic\n    unreachable",
                                 "assert %7  ; #proof: no_panic\n    br bb5", 1)
        rbt = measure(with_module("brtail", brtail, True))
        check("35 a halting assert followed by a dead `br` is a panic terminal, and is counted",
              rbt["metrics"] == m and rbt["info"]["panic_terminal_sites_not_ending_unreachable"] == 1,
              f"{rbt['metrics']} {rbt['info']['panic_terminal_sites_not_ending_unreachable']}")

        # 11. Per-instance vs module-wide: only a Clean-PROJECTABLE lowering models an intrinsic.
        global CLEAN_PROJECTABLE_OPS
        saved = CLEAN_PROJECTABLE_OPS
        try:
            CLEAN_PROJECTABLE_OPS = saved | {"atomicrmw"}
            rp = measure(base)
        finally:
            CLEAN_PROJECTABLE_OPS = saved
        check("36 with a projectable lowering, the instance is modelled per instance (5+2)...",
              rp["metrics"]["escaping_rows_per_instance"] == 7, f"{rp['metrics']}")
        check("37 ...but the module-wide rule still refuses every intrinsic (5+3)",
              rp["metrics"]["escaping_rows_module_wide"] == 8, f"{rp['metrics']}")

        # 13. Review 2026-09-23: holes an adversarial review found. Each arm is RED on the
        #     unfixed script (demonstrated before the fix), and ADV-A/B/C reproduce them on the
        #     real artifact.
        mj = json.loads(base.read_text())
        mj["members"][1]["calls"] = [c for c in mj["members"][1]["calls"] if c["resolved"] != _CLONE]
        mj["escaping"] = [r_ for r_ in mj["escaping"] if not r_.startswith(_CLONE + ":")]
        pa = tmp / "forgot.manifest.json"
        pa.write_text(json.dumps(mj))
        rfa = measure(pa)
        code, out = _run(["--manifest", str(pa), "--baseline", str(bl)])
        check("44 a manifest that FORGETS a silent-havoc call row does not read as progress",
              any(u["kind"] == "module-silent-havoc-without-manifest-row" for u in rfa["unreconciled"])
              and code == EXIT_FAIL and "REGRESSION unreconciled" in out, out[-300:])
        mj = json.loads(base.read_text())
        mj["roots"] = [r_ for r_ in mj["roots"] if r_["outcome"] == "resolved"]
        pr = tmp / "rootslost.manifest.json"
        pr.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(pr), "--baseline", str(bl)])
        check("45 a roots list that lost its refused root fails ROOTS LOST (not refused_roots progress)",
              code == EXIT_FAIL and "ROOTS LOST" in out, out[-300:])
        bl45 = tmp / "bl45.json"
        bl45.write_text(bl.read_text())
        code, out = _run(["--rebase", "--reason", "self-test: try to lock in a lost root", "--manifest", str(pr),
                          "--baseline", str(bl45)])
        check("46 ...and --rebase refuses to lock it in",
              code == EXIT_FAIL and bl45.read_text() == bl.read_text(), out[-300:])
        mj = json.loads(base.read_text())
        mj["filter"] = "local:some::smaller::subject"
        psub = tmp / "subject.manifest.json"
        psub.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(psub), "--baseline", str(bl)])
        check("47 another subject (filter) is refused as SUBJECT CHANGED", code == EXIT_FAIL and "SUBJECT CHANGED" in out,
              out[-300:])
        mj = json.loads(base.read_text())
        for c in mj["members"][1]["calls"]:
            if c["resolved"] == "ext::mir_unavail_fn":
                c["class"] = "foreign-terminal: ext::mir_unavail_fn"
        mj["foreign_terminals"].append("ext::mir_unavail_fn")
        mj["escaping"] = [r_ for r_ in mj["escaping"] if not r_.startswith("ext::mir_unavail_fn:")]
        prl = tmp / "relabel.manifest.json"
        prl.write_text(json.dumps(mj))
        rrl = measure(prl)
        check("48 relabelling an escaping callee as a foreign terminal does not make it a premise",
              rrl["info"]["call_sites_by_classification"].get("foreign-terminal") == 1
              and rrl["metrics"]["escaping_call_sites"] == m["escaping_call_sites"]
              and rrl["metrics"]["escaping_rows_per_instance"] == m["escaping_rows_per_instance"]
              and any(u["kind"] == "foreign-terminal-not-a-foreign-item" for u in rrl["unreconciled"]),
              f"{rrl['metrics']} {rrl['info']['call_sites_by_classification']}")
        drop2 = _synthetic(tmp, "drop2", extra_drop=True)
        code, out = _run(["--manifest", str(drop2), "--baseline", str(bl)])
        check("49 one more unproven drop-glue site is a regression",
              measure(drop2)["metrics"]["drop_glue_assumption_sites"] == 2
              and code == EXIT_FAIL and "REGRESSION drop_glue_assumption_sites" in out, out[-300:])
        newtag = mod_src.replace("[trust-drop-glue-assumption] drop glue for", "[trust-new-thing-assumption] drop glue for", 1)
        code, out = _run(["--manifest", str(with_module("newtag", newtag, True)), "--baseline", str(bl)])
        check("50 an assumption tag the script does not model is a REFUSAL, never skipped",
              code == EXIT_REFUSE and "assumption tag" in out, out[-300:])
        reword = mod_src.replace("has unproven panic-freedom", "is assumed panic-free", 1)
        code, out = _run(["--manifest", str(with_module("reword", reword, True)), "--baseline", str(bl)])
        check("51 a drop-glue assumption in an unrecognised wording is a REFUSAL, never skipped",
              code == EXIT_REFUSE and "assumption tag" in out, out[-300:])

        # 14. Manifest schema v3 (trust callee_sidecar.rs, 2026-09-24): read, and a manifest
        #     that CLAIMS v3 with a v3 field missing or malformed is a refusal (2), never a
        #     v2 reading of it. The bbs are the synthetic module's own call blocks.
        v3_bbs = {0: [0, 1, 2, 4], 1: [0, 1, 2, 3, 4, 5]}

        def as_v3(tag: str, mutate=None) -> Path:
            mj3 = json.loads(base.read_text())
            mj3["schema"] = MANIFEST_SCHEMA_V3
            mj3["fuel"], mj3["fuel_exhausted"] = 64, False
            for mem in mj3["members"]:
                bbs = v3_bbs[mem["sidecar_func_id"]]
                assert len(bbs) == len(mem["calls"]), "self-test v3 bb table is stale"
                mem["mir_digest"] = "sha256:" + f"{mem['sidecar_func_id'] + 1:02x}" * 32
                for c, bb in zip(mem["calls"], bbs):
                    c["bb"] = bb
            if mutate:
                mutate(mj3)
            p3 = tmp / f"{tag}.manifest.json"
            p3.write_text(json.dumps(mj3))
            return p3

        v3 = as_v3("v3")
        r3 = measure(v3)
        code, out = _run(["--manifest", str(v3), "--baseline", str(bl)])
        check("52 a v3 manifest is KEYED by its bb (rule /3): it measures as its v2 twin except that the "
              "untraced cold_path site is now keyed, by the producer's bb alone",
              r3["metrics"] == {**m, "unkeyed_call_sites": 0} and code == EXIT_OK
              and r3["info"]["sites_keyed_by_producer_bb_only"] == 1
              and any(x["resolved"] == _COLD and x["bb"] == 3 and x["keyed_by"] == "producer-bb"
                      for x in r3["sites"]), f"{r3['metrics']} {out[-200:]}")

        def refused_v3(tag: str, mutate, needle: str) -> tuple[bool, str]:
            code_, out_ = _run(["--manifest", str(as_v3(tag, mutate)), "--baseline", str(bl)])
            return code_ == EXIT_REFUSE and needle in out_, out_[-300:]

        ok_, det = refused_v3("v3nobb", lambda j: j["members"][1]["calls"][2].pop("bb"), "has no `bb`")
        check("53 a v3 call row without `bb` is refused (exit 2), never read as unkeyed", ok_, det)
        ok_, det = refused_v3("v3nodig", lambda j: j["members"][0].pop("mir_digest"), "`mir_digest`")
        check("54 a v3 member without `mir_digest` is refused (exit 2)", ok_, det)
        ok_, det = refused_v3("v3zero", lambda j: j["members"][0].update(mir_digest=_ZERO_MIR_DIGEST),
                              "`mir_digest`")
        check("55 a v3 member carrying the all-zero placeholder digest is refused", ok_, det)
        ok_, det = refused_v3("v3order", lambda j: j["members"][0]["calls"][1].update(bb=0), "has no `bb`")
        check("56 v3 bbs that do not strictly increase (two rows on one block) are refused", ok_, det)
        ok_, det = refused_v3("v3range", lambda j: j["members"][0]["calls"][3].update(bb=7), "has no `bb`")
        check("57 a v3 bb past the member's mir_blocks is refused", ok_, det)
        ok_, det = refused_v3("v3fuel", lambda j: j.pop("fuel"), "`fuel`")
        check("58 a v3 manifest without `fuel` is refused", ok_, det)
        ok_, det = refused_v3("v3exh", lambda j: j.update(closed=True, fuel_exhausted=True), "fuel exhausted")
        check("59 a v3 manifest that is `closed` with its fuel exhausted is refused", ok_, det)
        mj = json.loads(base.read_text())
        mj["schema"] = "trust-ir-callee-sidecar-v4"
        p.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(p), "--baseline", str(bl)])
        check("60 an unknown manifest schema is refused", code == EXIT_REFUSE and "schema" in out, out[-300:])

        # 15. Rule /3: the producer's per-site evidence is RE-DERIVED and must agree; its Intrinsic
        #     rows are cross-checked against the site derivation and never added on top of it; a
        #     v3 row must be explained by the evidence at ITS bb.
        ev_ok = {_CTPOP: "absent-callee-havoc", _XADD: "native-op:atomicrmw", _COLD: "no-trace"}

        def as_v3e(tag: str, mutate=None, evidence=None, rows=(_CTPOP, _COLD)) -> Path:
            def m3(j):
                j["producer"] = {"call_evidence": "per-site verdicts"}
                for mem_ in j["members"]:
                    for c in mem_["calls"]:
                        if c["class"].startswith("intrinsic-terminal"):
                            c["evidence"] = (evidence or ev_ok)[c["resolved"]]
                j["escaping"] = j["escaping"] + [f"{n_}: bodyless instance kind Intrinsic" for n_ in rows]
                if mutate:
                    mutate(j)
            return as_v3(tag, m3)

        re_ = measure(as_v3e("v3e"))
        check("61 a v3 manifest with per-site evidence reconciles: every verdict re-derived, the two "
              "Intrinsic rows cross-checked and NOT counted twice",
              re_["metrics"] == {**m, "unkeyed_call_sites": 0} and re_["unreconciled"] == []
              and re_["info"]["producer_site_evidence"] == {"absent-callee-havoc": 1, "native-op:atomicrmw": 1,
                                                            "no-trace": 1}
              and re_["info"]["manifest_intrinsic_rows"] == 2
              and re_["info"]["per_instance_trustir_native_counts_as_modelled"] == 5 + 2,
              f"{re_['metrics']} {re_['unreconciled'][:2]} {re_['info']['producer_site_evidence']}")
        rw = measure(as_v3e("v3wrong", evidence={**ev_ok, _XADD: "absent-callee-havoc"}))
        code, out = _run(["--manifest", str(as_v3e("v3wrong2", evidence={**ev_ok, _XADD: "absent-callee-havoc"})),
                          "--baseline", str(bl)])
        check("62 a producer verdict the module does not support (xadd claimed havoc) is unreconciled, "
              "and the ratchet fails", any(u["kind"] == "producer-site-evidence-disagrees" and u["resolved"] == _XADD
                                           for u in rw["unreconciled"]) and code == EXIT_FAIL, out[-300:])
        rc_ = measure(as_v3e("v3cold", evidence={**ev_ok, _COLD: "native-op:atomicrmw"}))
        check("63 an untraced site the producer calls native is unreconciled (no self-certification)",
              any(u["kind"] == "producer-site-evidence-disagrees" and u["derived"] == "no-trace"
                  for u in rc_["unreconciled"]), f"{rc_['unreconciled'][:2]}")

        def refused_v3e(tag: str, mutate, needle: str) -> tuple[bool, str]:
            code_, out_ = _run(["--manifest", str(as_v3e(tag, mutate)), "--baseline", str(bl)])
            return code_ == EXIT_REFUSE and needle in out_, out_[-300:]

        ok_, det = refused_v3e("v3noev", lambda j: j["members"][0]["calls"][2].pop("evidence"), "`evidence`")
        check("64 an intrinsic site without `evidence` under a producer that declares it is refused", ok_, det)
        ok_, det = refused_v3e("v3memev", lambda j: j["members"][0]["calls"][0].update(evidence="no-trace"),
                               "`evidence`")
        check("65 `evidence` on a non-intrinsic row is refused", ok_, det)
        ok_, det = refused_v3e("v3undecl", lambda j: j.update(producer={}), "`evidence`")
        check("66 `evidence` under a producer that declares no `call_evidence` is refused", ok_, det)
        rx_ = measure(as_v3e("v3xrow", rows=(_CTPOP, _COLD, _XADD)))
        check("67 an Intrinsic row for an instance whose every site is native is unreconciled",
              any(u["kind"] == "producer-intrinsic-rows-disagree" for u in rx_["unreconciled"])
              and rx_["metrics"]["escaping_rows_per_instance"] == m["escaping_rows_per_instance"],
              f"{rx_['unreconciled'][:2]} {rx_['metrics']}")
        ro_ = measure(as_v3e("v3omit", rows=(_CTPOP,)))
        check("68 a producer that OMITS an escaping intrinsic (cold_path) is unreconciled",
              any(u["kind"] == "producer-intrinsic-rows-disagree" and u["derived_not_listed"]
                  for u in ro_["unreconciled"]), f"{ro_['unreconciled'][:2]}")
        rb_ = measure(as_v3(("v3badbb"), lambda j: j["members"][0]["calls"][3].update(bb=3)))
        check("69 a v3 row keyed at the wrong block (panic at bb3, not bb4) leaves bb4's evidence "
              "unclaimed: unreconciled", any(u["kind"] == "module-site-without-manifest-row" and u["bb"] == 4
                                             for u in rb_["unreconciled"]), f"{rb_['unreconciled'][:3]}")

        # 16. Rule /3: a `subsumed:` root is credited only after independent verification.
        sub_root = {"caller": "<local root>", "callee_def_path": "root::f1", "crate_decl_func_ids": [],
                    "resolved": _F1, "sidecar_func_id": 1, "outcome": f"subsumed: reached from {_F0}"}

        def with_sub(tag: str, **over) -> Path:
            return as_v3(tag, lambda j: j["roots"].__setitem__(1, {**sub_root, **over}))

        rs_ = measure(with_sub("sub"))
        check("70 a verified subsumed root is not refused",
              rs_["metrics"]["refused_roots"] == 0 and rs_["info"]["roots_subsumed"] == 1
              and rs_["unreconciled"] == [], f"{rs_['metrics']} {rs_['unreconciled'][:2]}")
        for tag, over, why in (
            ("subparent", {"outcome": f"subsumed: reached from {_F1}"}, "no `member` call row"),
            ("subpath", {"callee_def_path": "root::other"}, "instance path"),
            ("subid", {"sidecar_func_id": 0}, "not the one `resolved` names"),
        ):
            rn_ = measure(with_sub(tag, **over))
            check(f"71 an unverified subsumed root ({tag}) is refused AND unreconciled",
                  rn_["metrics"]["refused_roots"] == 1 and rn_["info"]["roots_subsumed"] == 0
                  and any(u["kind"] == "subsumed-root-not-verified" and why in u["why"]
                          for u in rn_["unreconciled"]), f"{rn_['unreconciled'][:2]}")

        def shim(j):
            j["roots"][1] = dict(sub_root)
            j["members"][1]["instance_kind"] = "Shim"
        rsh = measure(as_v3("subshim", shim))
        check("72 a subsumed root whose member is a shim is not credited",
              rsh["metrics"]["refused_roots"] == 1
              and any(u["kind"] == "subsumed-root-not-verified" for u in rsh["unreconciled"]))
        mj = json.loads(base.read_text())
        mj["roots"][1] = dict(sub_root)
        p.write_text(json.dumps(mj))
        code, out = _run(["--manifest", str(p), "--baseline", str(bl)])
        check("73 a `subsumed` root in a pre-v3 manifest is refused", code == EXIT_REFUSE and "subsumed" in out,
              out[-200:])

        # 17. The rule migration: a /2 baseline is carried to /3 by --rebase ONLY when its own
        #     artifact reproduces under /3, and only from a declared rule.
        blm = tmp / "blm.json"
        code, out = _run(["--init", "--reason", "self-test migration baseline", "--manifest", str(base),
                          "--baseline", str(blm)])
        old = json.loads(blm.read_text())
        old["rule_version"] = "crystal-link3-reconcile/2"
        old["seal"] = _seal(old)
        blm.write_text(json.dumps(old))
        code, out = _run(["--manifest", str(v3), "--baseline", str(blm)])
        check("74 a /2 baseline is refused by a plain run (RULE VERSION)", code == EXIT_FAIL and "RULE VERSION" in out,
              out[-200:])
        code, out = _run(["--rebase", "--reason", "self-test: migrate /2 -> /3 on a v3 artifact", "--manifest",
                          str(v3), "--baseline", str(blm)])
        nb_ = json.loads(blm.read_text())
        check("75 --rebase migrates a /2 baseline whose own artifact reproduces under /3",
              code == EXIT_OK and "RULE MIGRATION" in out and nb_["rule_version"] == RULE_VERSION
              and nb_["history"][-1]["rule_migration"]["old_artifact_reproduced_exactly"] is True
              and nb_["metrics"]["unkeyed_call_sites"] == 0, out[-300:])
        bad = dict(old)
        bad["metrics"] = {**old["metrics"], "escaping_rows_per_instance": old["metrics"]["escaping_rows_per_instance"] + 1}
        bad["seal"] = _seal(bad)
        blb = tmp / "blb.json"
        blb.write_text(json.dumps(bad))
        code, out = _run(["--rebase", "--reason", "self-test: migrate a non-reproducing baseline", "--manifest",
                          str(v3), "--baseline", str(blb)])
        check("76 the migration is refused when the old artifact does not reproduce the /2 baseline",
              code == EXIT_FAIL and "does not reproduce" in out and json.loads(blb.read_text()) == bad, out[-300:])
        und = dict(old)
        und["rule_version"] = "crystal-link3-reconcile/0"
        und["seal"] = _seal(und)
        blb.write_text(json.dumps(und))
        code, out = _run(["--rebase", "--reason", "self-test: migrate from an undeclared rule", "--manifest",
                          str(v3), "--baseline", str(blb)])
        check("77 a migration from an undeclared rule is refused", code == EXIT_FAIL and "no declared migration" in out,
              out[-300:])

        # 18. Rule /4: a FOREIGN premise lowered as a call to a bodiless DECLARATION (the trust
        #     bridge's `premise-decls` lane). The base module's __rust_alloc site is f1 bb4.
        havoc_bb4 = ("bb4:\n    %8 = const bool false\n    assert %8  ; #proof: no_panic\n"
                     "    %9 = undef ptr  ; #proof: fresh_symbolic_havoc\n    br bb5")
        call_bb4 = "bb4:\n    %9 = call @func.2(%0)\n    br bb5"
        first_obl = mod_src.index("\nobligation ") + 1

        def decl_mod(tag: str, *, body: str = call_bb4, decls: tuple[str, ...] = (_ALLOC,),
                     decl_text: str | None = None, text: str | None = None, lane: bool = True) -> Path:
            src = text if text is not None else mod_src
            assert src.count(havoc_bb4) == 1, "self-test: the base module's bb4 moved"
            src = src.replace(havoc_bb4, body, 1)
            at = src.index("\nobligation ") + 1
            block = decl_text if decl_text is not None else "".join(
                f"fn @{d}(functy.{2 + n}) {{\n}}\n" for n, d in enumerate(decls))
            mf = with_module(tag, src[:at] + block + src[at:], True)
            if lane:
                mj_ = json.loads(mf.read_text())
                mj_["producer"]["premise_decls"] = "ON (self-test)"
                mf.write_text(json.dumps(mj_))
            return mf

        assert mod_src[first_obl:].startswith("obligation 0 "), "self-test: obligation block moved"
        dm = decl_mod("decl")
        rdm = measure(dm)
        code, out = _run(["--manifest", str(dm), "--baseline", str(bl)])
        check("78 a foreign site lowered as `call @decl` is a premise LOWERED AS A CALL: premise havoc 1 -> 0, "
              "every other figure and the site table unchanged, and the ratchet reads PROGRESS",
              rdm["metrics"] == {**m, "premise_sites_lowered_as_havoc": 0} and rdm["unreconciled"] == []
              and rdm["info"]["premise_sites_lowered_as_call"] == 1
              and rdm["info"]["declared_premise_functions"] == 1
              and rdm["info"]["call_sites_by_classification"] == r["info"]["call_sites_by_classification"]
              and rdm["site_table_sha256"] == r["site_table_sha256"]
              and code == EXIT_OK and "premise_sites_lowered_as_havoc 1 -> 0" in out,
              f"{rdm['metrics']} {rdm['unreconciled'][:2]} {out[-300:]}")
        check("79 the base module (no declaration) reports zero declared calls",
              r["info"]["premise_sites_lowered_as_call"] == 0 and r["info"]["declared_premise_functions"] == 0)
        rka = measure(decl_mod("declassert", body="bb4:\n    %8 = const bool false\n    assert %8  ; #proof: no_panic\n"
                                                  "    %9 = call @func.2(%0)\n    br bb5"))
        check("80 a declared call BESIDE a halting `assert false` still halts: counted as havoc, not as a call",
              rka["metrics"]["premise_sites_lowered_as_havoc"] == 1
              and rka["info"]["premise_sites_lowered_as_call"] == 0 and rka["unreconciled"] == [],
              f"{rka['metrics']} {rka['unreconciled'][:2]}")
        noobl_src = mod_src.replace(
            f'"[trust-absent-callee-assumption] call to absent callee `{_ALLOC}` (body not in the lowered bundle) '
            f'may panic"', f'"{_F1}: all assertions hold"', 1)
        noobl_src = noobl_src.replace(f"mir-assert:{_F1}:bb4:terminator", f"mir-assertions:{_F1}:panic-freedom")
        rno = measure(decl_mod("declnoobl", text=noobl_src))
        code, out = _run(["--manifest", str(decl_mod("declnoobl2", text=noobl_src)), "--baseline", str(bl)])
        check("81 a declared call WITHOUT the absent-callee obligation is no premise: not a foreign terminal, "
              "unreconciled, and the ratchet fails",
              rno["info"]["call_sites_by_classification"].get("foreign-terminal", 0) == 0
              and rno["metrics"]["premise_sites_lowered_as_havoc"] == 0
              and rno["info"]["premise_sites_lowered_as_call"] == 0
              and rno["metrics"]["unreconciled"] >= 1 and code == EXIT_FAIL, f"{rno['metrics']} {out[-200:]}")
        rwd = measure(decl_mod("declwrong", decls=("alloc::alloc::{extern#0}::__rust_dealloc",)))
        check("82 a call to the declaration of ANOTHER foreign symbol does not lower this row's premise",
              rwd["metrics"]["premise_sites_lowered_as_havoc"] == 1
              and rwd["info"]["premise_sites_lowered_as_call"] == 0
              and any(u["kind"] == "extra-evidence-at-matched-site" for u in rwd["unreconciled"]),
              f"{rwd['metrics']} {rwd['unreconciled'][:2]}")
        rnc = measure(decl_mod("declunused", body=havoc_bb4))
        check("83 a declaration no member calls is unreconciled",
              any(u["kind"] == "declaration-never-called" for u in rnc["unreconciled"])
              and rnc["metrics"]["premise_sites_lowered_as_havoc"] == 1, f"{rnc['unreconciled'][:2]}")
        for tag, kw, needle in (
            ("declnotforeign", {"decls": ("ext::not_foreign",)}, "not an {extern#N} foreign item"),
            ("decltwice", {"decls": (_ALLOC, _ALLOC)}, "declared twice"),
            ("declbody", {"decl_text": f"fn @{_ALLOC}(functy.2) {{\nbb0:\n    ret\n}}\n"}, "has a body"),
            ("declmalformed", {"decl_text": f"fn @{_ALLOC}(functy.2) {{\n    %1 = const bool false\n}}\n"},
             "instruction before the first block label"),
            ("declunclosed", {"decl_text": f"fn @{_ALLOC}(functy.2) {{\n"}, "unexpected text inside a function"),
        ):
            code, out = _run(["--manifest", str(decl_mod(tag, **kw)), "--baseline", str(bl)])
            check(f"84 a malformed declaration table ({tag}) is a REFUSAL (exit 2)",
                  code == EXIT_REFUSE and needle in out, out[-300:])
        code, out = _run(["--manifest", str(decl_mod("declnolane", lane=False)), "--baseline", str(bl)])
        check("84b a module with declarations whose manifest does not declare the premise_decls lane is "
              "a REFUSAL", code == EXIT_REFUSE and "does not declare the `premise_decls` lane" in out, out[-300:])
        f1_start = mod_src.index(f"fn @{_F1}(")
        f1_end = mod_src.index("}\n", f1_start) + 2
        nobody = mod_src[:f1_start] + f"fn @{_F1}(functy.1) {{\n}}\n" + mod_src[f1_end:]
        code, out = _run(["--manifest", str(with_module("memberbodiless", nobody, True)), "--baseline", str(bl)])
        check("85 a bodiless MEMBER is a refusal, never read as a declaration",
              code == EXIT_REFUSE and "is a MEMBER and has no blocks" in out, out[-300:])
        # Rule /7 (crystal E3): the trust bridge's `abort-cleanup` lane lowers no cleanup block,
        # so a member's labels (the MIR block indices) may SKIP -- but only under that lane, and
        # no evidence may name a skipped block. f1's bb3 (`br bb4`) holds no call and no
        # obligation, so dropping it leaves every figure where it was.
        assert mod_src.count("bb3:\n    br bb4\n") == 1, "self-test: f1 bb3 moved"
        gap = mod_src.replace("bb3:\n    br bb4\n", "", 1)
        code, out = _run(["--manifest", str(with_module("gapnolane", gap, True)), "--baseline", str(bl)])
        check("120 a skipped block label without the abort_cleanup lane is a REFUSAL",
              code == EXIT_REFUSE and "does not declare the `abort_cleanup` lane" in out, out[-300:])

        def with_lane(mf: Path) -> Path:
            mj3 = json.loads(mf.read_text())
            mj3["producer"]["abort_cleanup"] = "ON (self-test)"
            mf.write_text(json.dumps(mj3))
            return mf

        rgap = measure(with_lane(with_module("gaplane", gap, True)))
        check("121 under the lane the module with a skipped label measures exactly as the dense one",
              rgap["metrics"] == m and rgap["unreconciled"] == [], f"{rgap['metrics']} {rgap['unreconciled'][:2]}")
        n_obl = sum(1 for ln_ in mod_src.split("\n") if ln_.startswith("obligation "))
        gap_obl = gap + _obl(n_obl, f"panic call `{_PANIC}` must be unreachable", 1, _F1, 3) + "\n"
        code, out = _run(["--manifest", str(with_lane(with_module("gapobl", gap_obl, True))),
                          "--baseline", str(bl)])
        check("122 even under the lane, an obligation naming a skipped block is a REFUSAL",
              code == EXIT_REFUSE and "which the module does not carry" in out, out[-300:])
        over = mod_src.replace("bb6:\n    ret\n}", "bb6:\n    ret\nbb7:\n    ret\n}", 1)
        code, out = _run(["--manifest", str(with_lane(with_module("gapover", over, True))),
                          "--baseline", str(bl)])
        check("123 a label past the member's MIR block count is a REFUSAL under the lane too",
              code == EXIT_REFUSE and "MIR blocks" in out, out[-300:])
        back = mod_src.replace("bb3:\n    br bb4\n", "bb2:\n    br bb4\n", 1)
        code, out = _run(["--manifest", str(with_lane(with_module("gapback", back, True))),
                          "--baseline", str(bl)])
        check("124 a repeated (non-increasing) label is a REFUSAL, lane or not",
              code == EXIT_REFUSE and "out of order" in out, out[-300:])
        dm_text = (tmp / "decl.trust-ir.txt").read_text()
        v3d = as_v3("v3decl", lambda j: (j["artifacts"].update(text="decl.trust-ir.txt",
                                                               text_bytes=len(dm_text.encode())),
                                          j["producer"].update(premise_decls="ON (self-test)")))
        r3d = measure(v3d)
        check("86 rule /4 on a v3 (bb-keyed) manifest: the declared call is explained at the row's own bb",
              r3d["metrics"] == {**r3["metrics"], "premise_sites_lowered_as_havoc": 0}
              and r3d["unreconciled"] == [] and r3d["info"]["premise_sites_lowered_as_call"] == 1,
              f"{r3d['metrics']} {r3d['unreconciled'][:2]}")
        # The /3 -> /4 migration: the /3 baseline's own artifact (no declarations) reproduces exactly,
        # and the artifact it is then compared with may carry declarations.
        bl3 = tmp / "bl3.json"
        code, out = _run(["--init", "--reason", "self-test /3 baseline", "--manifest", str(base),
                          "--baseline", str(bl3)])
        old3 = json.loads(bl3.read_text())
        old3["rule_version"] = "crystal-link3-reconcile/3"
        old3["seal"] = _seal(old3)
        bl3.write_text(json.dumps(old3))
        code, out = _run(["--manifest", str(dm), "--baseline", str(bl3)])
        check("87 a /3 baseline is refused by a plain /4 run (RULE VERSION)",
              code == EXIT_FAIL and "RULE VERSION" in out, out[-200:])
        code, out = _run(["--rebase", "--reason", "self-test: migrate /3 -> /4 on a declared-call artifact",
                          "--manifest", str(dm), "--baseline", str(bl3)])
        nb3 = json.loads(bl3.read_text())
        check("88 --rebase migrates /3 -> /4 (its own artifact reproduces) and locks in premise havoc 0",
              code == EXIT_OK and "RULE MIGRATION crystal-link3-reconcile/3" in out
              and nb3["rule_version"] == RULE_VERSION and nb3["metrics"]["premise_sites_lowered_as_havoc"] == 0
              and nb3["history"][-1]["rule_migration"]["old_artifact_reproduced_exactly"] is True, out[-300:])
        code, out = _run(["--manifest", str(base), "--baseline", str(bl3)])
        check("89 against the locked-in baseline, the havoc lowering is a REGRESSION",
              code == EXIT_FAIL and "REGRESSION premise_sites_lowered_as_havoc: 0 -> 1" in out, out[-300:])

        # 19. Rule /5: FOREIGN-CALLBACK premises (the trust sidecar's `foreign-callback` lane). The
        #     base module's __rust_alloc site (f1 bb4) is re-classed as a foreign callback whose
        #     callback is the member f0.
        def fc_manifest(tag: str, *, src: Path = base, contract: str | None = "invokes it once",
                        callbacks: tuple[str, ...] = (_F0,), site_bb: int = 4, lane: bool = True,
                        rows: bool = True, keep_foreign: bool = True) -> Path:
            mj_ = json.loads(src.read_text())
            for c in mj_["members"][1]["calls"]:
                if c["resolved"] == _ALLOC:
                    c["class"] = f"foreign-callback-terminal: {_ALLOC}"
            if lane:
                mj_["producer"]["foreign_callback"] = "ON (self-test)"
            if rows:
                mj_["foreign_callbacks"] = [{"callee": _ALLOC, "callback_param_types": ["fn(usize)"],
                                             "contract": contract,
                                             "sites": [{"member": _F1, "bb": site_bb,
                                                        "callbacks": list(callbacks)}]}]
            if not keep_foreign:
                mj_["foreign_terminals"] = []
                mj_["escaping"].append(f"{_ALLOC}: foreign item (no Rust body on this target); "
                                       f"foreign callback: no recorded foreign-callback contract")
            out_ = tmp / f"{tag}.manifest.json"
            out_.write_text(json.dumps(mj_))
            return out_

        rfc = measure(fc_manifest("fc"))
        by_cls = rfc["info"]["call_sites_by_classification"]
        check("90 a foreign-callback site under its contract is a PREMISE counted SEPARATELY: "
              "foreign-callback-terminal 1, foreign-terminal 0, every ratcheted figure as the plain foreign one",
              rfc["metrics"] == m and rfc["unreconciled"] == []
              and by_cls.get("foreign-callback-terminal") == 1 and by_cls.get("foreign-terminal", 0) == 0
              and rfc["info"]["foreign_callback_premises"] == [
                  {"callee": _ALLOC, "contract": "invokes it once", "sites": 1, "callbacks": [_F0]}],
              f"{rfc['metrics']} {rfc['unreconciled'][:2]} {by_cls}")
        rfd = measure(fc_manifest("fcdecl", src=dm))
        check("91 a foreign-callback premise lowered as `call @decl` is counted as lowered as a CALL",
              rfd["unreconciled"] == [] and rfd["metrics"]["premise_sites_lowered_as_havoc"] == 0
              and rfd["info"]["premise_sites_lowered_as_call"] == 1
              and rfd["info"]["call_sites_by_classification"].get("foreign-callback-terminal") == 1,
              f"{rfd['metrics']} {rfd['unreconciled'][:2]}")
        rfe = measure(fc_manifest("fcesc", contract=None, keep_foreign=False))
        check("92 a foreign callback with NO contract (kept escaping by the producer) is an escaping FOREIGN "
              "row, never a premise: one more escaping row and site, no premise",
              rfe["unreconciled"] == [] and rfe["info"]["call_sites_by_classification"].get(
                  "foreign-callback-terminal", 0) == 0
              and rfe["metrics"]["escaping_rows_per_instance"] == m["escaping_rows_per_instance"] + 1
              and rfe["metrics"]["escaping_call_sites"] == m["escaping_call_sites"] + 1
              and rfe["metrics"]["premise_sites_lowered_as_havoc"] == 0
              and any(s["resolved"] == _ALLOC and s.get("escaping_class") == "foreign" for s in rfe["sites"]),
              f"{rfe['metrics']} {rfe['unreconciled'][:2]}")
        rfn = measure(fc_manifest("fcnocontract", contract=None))
        check("92b a foreign callback LISTED as a terminal but carrying no contract is not a premise and is "
              "unreconciled", rfn["info"]["call_sites_by_classification"].get("foreign-callback-terminal", 0) == 0
              and rfn["metrics"]["unreconciled"] >= 1, f"{rfn['metrics']} {rfn['unreconciled'][:2]}")
        for tag, kw, needle in (
            ("fcnolane", {"lane": False, "rows": False}, "does not declare the `foreign_callback` lane"),
            ("fcnorows", {"rows": False}, "must come together"),
            ("fcrowsnolane", {"lane": False}, "must come together"),
        ):
            code, out = _run(["--manifest", str(fc_manifest(tag, **kw)), "--baseline", str(bl)])
            check(f"93 a foreign-callback artifact without its lane declaration ({tag}) is a REFUSAL",
                  code == EXIT_REFUSE and needle in out, out[-300:])
        rfm = measure(fc_manifest("fcnotmember", callbacks=("ext::not_a_member",)))
        check("94 a foreign callback whose callback is not a bundle member is unreconciled",
              any(u["kind"] == "foreign-callback-callback-not-a-member" for u in rfm["unreconciled"]),
              f"{rfm['unreconciled'][:3]}")
        rfb = measure(fc_manifest("fcwrongbb", site_bb=3))
        check("95 a foreign-callback row that names another site than the premise's is unreconciled both ways",
              {"foreign-callback-site-not-in-its-row", "foreign-callback-row-site-without-premise-site"}
              <= {u["kind"] for u in rfb["unreconciled"]}, f"{rfb['unreconciled'][:3]}")
        rfz = measure(fc_manifest("fcnocallback", callbacks=()))
        check("95b a foreign-callback site with no callback at all is unreconciled",
              any(u["kind"] == "foreign-callback-site-without-callback" for u in rfz["unreconciled"]),
              f"{rfz['unreconciled'][:3]}")

        # 19b. Rule /5: the dyn/erased-Fn* spelling of the absent-callee obligation (the base f1 bb5
        #      `<dyn T as T>::m` site) is read as naming its callee; another wording still refuses.
        dyn_old = (f'"[trust-absent-callee-assumption] call to absent callee `{_DYN}` (dynamic dispatch) '
                   f'may panic"')
        assert mod_src.count(dyn_old) == 1, "self-test: the base module's dyn obligation moved"
        dyn_new = (f'"[trust-absent-callee-assumption] indirect call `{_DYN}` through an untypeable callable '
                   f'receiver (dyn/erased Fn*; callee unknown) may panic"')
        rdy = measure(with_module("dynspell", mod_src.replace(dyn_old, dyn_new, 1), True))
        check("90c the untypeable-callable-receiver spelling names its callee: every figure and the site "
              "table as the base", rdy["metrics"] == m and rdy["unreconciled"] == []
              and rdy["site_table_sha256"] == r["site_table_sha256"], f"{rdy['metrics']} {rdy['unreconciled'][:2]}")
        code, out = _run(["--manifest", str(with_module("dynbad", mod_src.replace(
            dyn_old, dyn_new.replace("untypeable callable receiver", "untyped receiver"), 1), True)),
            "--baseline", str(bl)])
        check("90d any other `indirect call` wording under an assumption tag is still a REFUSAL",
              code == EXIT_REFUSE and "does not model" in out, out[-300:])

        # 20. Rule /5: a native cmpxchg is evidence for the intrinsic of its OWN strength only. The
        #     base f0 bb2 xadd site is rewritten as a compare-exchange of each strength.
        cx_weak = "core::intrinsics::atomic_cxchgweak::<u64, core::intrinsics::AtomicOrdering::SeqCst, " \
                  "core::intrinsics::AtomicOrdering::Relaxed>::<__trust_args@bb>"
        cx_strong = cx_weak.replace("atomic_cxchgweak", "atomic_cxchg")
        rmw_line = "    %5 = atomicrmw add u64, ptr %0, %4\n"
        assert mod_src.count(rmw_line) == 1, "self-test: the base module's xadd line moved"

        def cx_mod(tag: str, *, op_weak: bool, row: str) -> Path:
            src = mod_src.replace(rmw_line, "    %5, %12 = cmpxchg " + ("weak " if op_weak else "")
                                  + "u64 ptr %0, %4, %4 seq_cst relaxed\n", 1)
            mf = with_module(tag, src, True)
            mj_ = json.loads(mf.read_text())
            for c in mj_["members"][0]["calls"]:
                if c["resolved"] == _XADD:
                    c["site"] = c["resolved"] = row
                    c["class"] = f"intrinsic-terminal: {row}"
            mf.write_text(json.dumps(mj_))
            return mf

        rcw = measure(cx_mod("cxweak", op_weak=True, row=cx_weak))
        check("96 a `cmpxchg weak` evidences an atomic_cxchgweak site exactly as a native op evidences its "
              "intrinsic, and under rule /9 it stays unprojectable (a weak CAS has no SEQ image): one "
              "escaping site and one per-instance row more than the base, whose xadd is a SEQ premise",
              rcw["metrics"] == {**m, "escaping_call_sites": m["escaping_call_sites"] + 1,
                                 "escaping_rows_per_instance": m["escaping_rows_per_instance"] + 1}
              and rcw["unreconciled"] == []
              and any(s["resolved"] == cx_weak and s["verdict"] == "intrinsic-unprojectable"
                      and s["evidence"] == ["native_op_weak:cmpxchg"] for s in rcw["sites"]),
              f"{rcw['metrics']} {rcw['unreconciled'][:2]}")
        rcs = measure(cx_mod("cxstrong", op_weak=False, row=cx_strong))
        check("97 a strong `cmpxchg` evidences an atomic_cxchg site as before",
              rcs["metrics"] == m and rcs["unreconciled"] == [], f"{rcs['metrics']} {rcs['unreconciled'][:2]}")
        rcx = measure(cx_mod("cxmismatch", op_weak=False, row=cx_weak))
        check("98 a STRONG cmpxchg is NOT evidence for a weak intrinsic (it would delete spurious failures): "
              "unreconciled", rcx["metrics"]["unreconciled"] >= 1
              and not any(s["resolved"] == cx_weak and s["verdict"] == "intrinsic-unprojectable" for s in rcx["sites"]),
              f"{rcx['metrics']} {rcx['unreconciled'][:2]}")
        rcy = measure(cx_mod("cxmismatch2", op_weak=True, row=cx_strong))
        check("99 a WEAK cmpxchg is NOT evidence for a strong intrinsic: unreconciled",
              rcy["metrics"]["unreconciled"] >= 1, f"{rcy['metrics']} {rcy['unreconciled'][:2]}")
        # Rule /5: the undefined-behavior halt is its own class, and neither halt's wording is
        # evidence for the other.
        _ub = "core::hint::unreachable_unchecked"
        ub_ev = {"strong": [("obl_ub", _ub)], "weak": None, "ends_unreachable": True, "false_assert": True,
                 "ub_sited_halt": True}
        pn_ev = {"strong": [("obl_panic", _ub)], "weak": None, "ends_unreachable": True, "false_assert": True}
        check("99a a `ub-terminal` row stands on the bridge's UB wording and a halting assert",
              compat({"class": "ub-terminal", "resolved": _ub}, ub_ev, set()) == ("ub-terminal", {0}))
        check("99b the panic wording is NOT evidence for a `ub-terminal` row, nor the UB wording for a "
              "`panic-terminal` one",
              compat({"class": "ub-terminal", "resolved": _ub}, pn_ev, set()) is None
              and compat({"class": "panic-terminal", "resolved": _ub}, ub_ev, set()) is None)
        check("99c a `ub-terminal` row whose obligation does not SITE the halting assert is unevidenced "
              "(rule /11: a false assert elsewhere in the block no longer stands in for it)",
              compat({"class": "ub-terminal", "resolved": _ub}, dict(ub_ev, ub_sited_halt=False), set()) is None
              and compat({"class": "ub-terminal", "resolved": _ub},
                         dict(ub_ev, ub_sited_halt=False, false_assert=True), set()) is None)
        # Rule /11: block_evidence reads the site index -- the halting assert, the node the Clean
        # projector images as `unreachable` -- and nothing else.
        _blk = ["%0 = const bool false", "assert %0  ; #proof: no_panic", "unreachable"]
        _ev = lambda k: block_evidence(0, _blk, [], [("ub", _ub, 0, k)], 0)["ub_sited_halt"]
        check("99e rule /11: a UB obligation sited AT the halting assert is evidence; sited at the "
              "const, the terminator, out of range or nowhere, it is not",
              _ev(1) is True and _ev(0) is False and _ev(2) is False and _ev(9) is False
              and _ev(None) is False
              and block_evidence(0, ["%0 = const bool true", "assert %0", "unreachable"], [],
                                 [("ub", _ub, 0, 1)], 0)["ub_sited_halt"] is False)
        check("99d the UB obligation is collected at its call site under kind `ub`",
              _UB_RE.match(f"reaching `{_ub}` is undefined behavior; this program point must be proven "
                           "unreachable") is not None
              and _UB_RE.match(f"panic call `{_ub}` must be unreachable") is None)
        # The /4 -> /5 migration: a /4 baseline of the base artifact reproduces exactly.
        bl4 = tmp / "bl4.json"
        code, out = _run(["--init", "--reason", "self-test /4 baseline", "--manifest", str(base),
                          "--baseline", str(bl4)])
        old4 = json.loads(bl4.read_text())
        old4["rule_version"] = "crystal-link3-reconcile/4"
        old4["seal"] = _seal(old4)
        bl4.write_text(json.dumps(old4))
        code, out = _run(["--manifest", str(base), "--baseline", str(bl4)])
        check("100 a /4 baseline is refused by a plain /5 run (RULE VERSION)",
              code == EXIT_FAIL and "RULE VERSION" in out, out[-200:])
        code, out = _run(["--rebase", "--reason", "self-test: migrate /4 -> /5 on its own artifact",
                          "--manifest", str(dm), "--baseline", str(bl4)])
        nb4 = json.loads(bl4.read_text())
        check("101 --rebase migrates /4 -> /5 (its own artifact reproduces exactly)",
              code == EXIT_OK and "RULE MIGRATION crystal-link3-reconcile/4" in out
              and nb4["rule_version"] == RULE_VERSION
              and nb4["history"][-1]["rule_migration"]["old_artifact_reproduced_exactly"] is True, out[-300:])

        # Rule /6: a call_indirect WITHOUT its fail-closed marker (the trust sidecar's
        # `indirect-by-value` lane) needs the lane NAMED and an exact, all-member row.
        marker = "bb2:\n    %5 = const bool false\n    assert %5  ; #proof: no_panic\n"
        assert marker in mod_src
        # Rule /10: a real by-value site names its target (`[root::f0]`), and the module carries
        # the functy table the signature check reads (the call and f0 both at functy.0).
        byval_src = mod_src.replace(marker, "bb2:\n    %5 = const bool true\n", 1).replace(
            'file 0 "x.rs"\n', 'file 0 "x.rs"\nfuncty.0 = (ptr) -> ()\nfuncty.1 = (ptr) -> ()\n', 1)

        def byval(tag: str, lanes: str | None, row_tail: str, src: str | None = None,
                  extra: dict | None = None) -> Path:
            text_ = byval_src if src is None else src
            mp = tmp / f"{tag}.trust-ir.txt"
            mp.write_text(text_)
            mj2 = json.loads(base.read_text())
            mj2["artifacts"]["text"] = mp.name
            mj2["artifacts"]["text_bytes"] = len(text_.encode())
            if lanes is not None:
                mj2["producer"] = {"value_lanes": lanes}
            mj2["escaping"] = [r.replace("enumerated targets 0", f"enumerated targets 1 [{_F0}]") + row_tail
                               if ": indirect call (" in r else r for r in mj2["escaping"]]
            mj2.update(extra or {})
            mf = tmp / f"{tag}.manifest.json"
            mf.write_text(json.dumps(mj2))
            return mf

        exact = f" {_INDIRECT_EXACT_MEMBERS} {_INDIRECT_SCAN_COMPLETE}; the set is complete only under the address-taken hypothesis)"
        code, out = _run(["--manifest", str(byval("byval-nolane", None, exact)), "--baseline", str(bl)])
        check("102 a markerless call_indirect without the `indirect-by-value` lane is REFUSED",
              code == EXIT_REFUSE and "indirect-by-value" in out, out[-200:])
        lane = "ON: indirect-by-value: ..."
        code, out = _run(["--manifest", str(byval("byval-incomplete", lane,
                                                    f" {_INDIRECT_EXACT_MEMBERS} (crate-wide address-taken scan "
                                                    "INCOMPLETE for this type: 1 site(s) outside it)")),
                          "--baseline", str(bl)])
        check("103 a markerless call_indirect whose row is not scan-complete is REFUSED",
              code == EXIT_REFUSE and "all-member, scan-complete" in out, out[-200:])
        rbv = measure(byval("byval-ok", lane, exact))
        check("104 an admitted by-value site counts once and keeps its `indirect` classification",
              rbv["info"]["indirect_sites_dispatched_by_value"] == 1
              and rbv["info"]["escaping_call_sites_by_class"].get("indirect") == 1
              and rbv["info"]["indirect_sites_dispatched_through_shim_adapter"] == 0
              and measure(base)["info"]["indirect_sites_dispatched_by_value"] == 0,
              f"{rbv['info'].get('indirect_sites_dispatched_by_value')}")

        # Rule /10 (crystal D1): the signature is RE-DERIVED -- a target declared at another functy
        # is a positional misbinding and is refused; a target list that tiles no member is refused.
        mism = byval_src.replace(f"fn @{_F0}(functy.0) {{", f"fn @{_F0}(functy.1) {{", 1).replace(
            "functy.1 = (ptr) -> ()", "functy.1 = (ptr, u8) -> ()", 1)
        code, out = _run(["--manifest", str(byval("byval-mismatch", lane, exact, src=mism)),
                          "--baseline", str(bl)])
        check("105 a by-value target declared at another signature is REFUSED (positional mismatch)",
              code == EXIT_REFUSE and "positional mismatch" in out, out[-240:])
        mj_g = byval("byval-ghost", lane, exact)
        gj = json.loads(mj_g.read_text())
        gj["escaping"] = [r.replace(f"[{_F0}]", "[root::ghost]") for r in gj["escaping"]]
        mj_g.write_text(json.dumps(gj))
        code, out = _run(["--manifest", str(mj_g), "--baseline", str(bl)])
        check("106 a by-value row whose target list tiles no member is REFUSED",
              code == EXIT_REFUSE and "unambiguous tiling" in out, out[-240:])
        # The shim ADAPTER shape: `()` plus a full-write typed tuple, the call at the target's
        # rust-call signature. Admitted only from a producer naming `shim-adapter`.
        adapt = byval_src.replace(f"fn @{_F0}(functy.0) {{", f"fn @{_F0}(functy.2) {{", 1).replace(
            "functy.1 = (ptr) -> ()\n", "functy.1 = (ptr) -> ()\nfuncty.2 = ((), (ptr)) -> ()\n", 1).replace(
            "    %7 = call_indirect %6(functy.0)(%0)",
            "    %20 = const () phantomdata\n    %21 = const (ptr) { 0 }\n"
            "    %22 = insertfield (ptr) %21, 0, %0\n    %7 = call_indirect %6(functy.2)(%20, %22)", 1)
        assert adapt.count("functy.2") == 3, "self-test: the adapter module did not build"
        code, out = _run(["--manifest", str(byval("byval-adapter-nolane", lane, exact, src=adapt)),
                          "--baseline", str(bl)])
        check("107 an adapter-shaped by-value call without the `shim-adapter` lane is REFUSED",
              code == EXIT_REFUSE and "shim-adapter" in out, out[-240:])
        ra = measure(byval("byval-adapter", lane + "; shim-adapter: ...", exact, src=adapt))
        check("108 with the lane the adapter site is admitted, counted, and still `indirect`",
              ra["info"]["indirect_sites_dispatched_by_value"] == 1
              and ra["info"]["indirect_sites_dispatched_through_shim_adapter"] == 1
              and ra["info"]["escaping_call_sites_by_class"].get("indirect") == 1,
              f"{ra['info'].get('indirect_sites_dispatched_through_shim_adapter')}")
        partial = adapt.replace("    %22 = insertfield (ptr) %21, 0, %0\n", "    %22 = copy (ptr) %21\n", 1)
        rp = measure(byval("byval-adapter-partial", lane + "; shim-adapter: ...", exact, src=partial))
        check("109 a tuple the chain does not fully write is NOT the adapter shape",
              rp["info"]["indirect_sites_dispatched_through_shim_adapter"] == 0, str(rp["info"].get(
                  "indirect_sites_dispatched_through_shim_adapter")))
        # Rule /10 (decision D11): `tls_cells` rows need their lane; `certified` must be the
        # conjunction of its facts; a certified op is counted, an uncertified one separately.
        tls_row = {"symbol": "root::VAL", "static": "root::VAL", "def_path_hash": "h", "ty": "T",
                   "unique_symbol": True, "pointer_free": True, "definitely_not_sync": True,
                   "freeze": False, "needs_drop": False, "certified": True, "refused": []}
        tls_src = byval_src.replace(
            "bb3:\n    br bb4",
            'bb3:\n    %30 = dialect_op trust_rust.thread_local_addr() -> ptr '
            '[schema=str:"trust-rust.thread-local-addr/v1"] [symbol=str:"root::VAL"]\n'
            '    %31 = dialect_op trust_rust.thread_local_addr() -> ptr '
            '[schema=str:"trust-rust.thread-local-addr/v1"] [symbol=str:"root::OTHER"]\n    br bb4', 1)
        assert tls_src != byval_src, "self-test: the TLS ops did not insert"
        code, out = _run(["--manifest", str(byval("tls-nolane", lane, exact, src=tls_src,
                                                   extra={"tls_cells": [tls_row]})),
                          "--baseline", str(bl)])
        check("110 `tls_cells` rows without the `tls-cells` lane are REFUSED",
              code == EXIT_REFUSE and "tls-cells" in out, out[-240:])
        code, out = _run(["--manifest", str(byval("tls-forged", lane + "; tls-cells: ...", exact, src=tls_src,
                                                   extra={"tls_cells": [dict(tls_row, pointer_free=False)]})),
                          "--baseline", str(bl)])
        check("111 a `certified` that is not the conjunction of its facts is REFUSED",
              code == EXIT_REFUSE and "conjunction" in out, out[-240:])
        rt = measure(byval("tls-ok", lane + "; tls-cells: ...", exact, src=tls_src,
                           extra={"tls_cells": [tls_row]}))
        check("112 a certified TLS op is counted as the D11 premise, an uncertified one apart",
              rt["info"]["tls_input_premise_ops"] == 1 and rt["info"]["tls_input_premise_ops_uncertified"] == 1
              and rt["info"]["tls_certified_symbols"] == ["root::VAL"], str(rt["info"].get("tls_input_premise_ops")))
        # Rule /11 (crystal D13): the target is a SHIM (declared `((), (ptr)) -> ()`) behind a site
        # at `(ptr) -> ()`; its supplied ABI thunk, after the members, is the spread. Admitted only
        # from a producer naming `fnptr-thunks`, only for an exact thunk, and never when a constant
        # names the shim itself as a value.
        thunk_fn = (f'fn @{_F0}{THUNK_SUFFIX}(functy.0) {{\n    ; #producer: {THUNK_PRODUCER}\n'
                    f'bb0(%0: ptr):\n    %1 = const () phantomdata\n    %2 = const (ptr) {{ 0 }}\n'
                    f'    %3 = insertfield (ptr) %2, 0, %0\n    call @func.0(%1, %3)\n    ret\n}}\n')
        shim_src = byval_src.replace(f"fn @{_F0}(functy.0) {{", f"fn @{_F0}(functy.2) {{", 1).replace(
            "functy.1 = (ptr) -> ()\n", "functy.1 = (ptr) -> ()\nfuncty.2 = ((), (ptr)) -> ()\n", 1)
        first_obl = shim_src.index("\nobligation ") + 1
        thunked = shim_src[:first_obl] + thunk_fn + shim_src[first_obl:]
        assert thunked.count(THUNK_SUFFIX) == 1, "self-test: the thunk module did not build"
        code, out = _run(["--manifest", str(byval("thunk-nolane", lane, exact, src=thunked)),
                          "--baseline", str(bl)])
        check("113 rule /11: a module carrying an ABI thunk without the `fnptr-thunks` lane is REFUSED",
              code == EXIT_REFUSE and "fnptr-thunks" in out, out[-240:])
        rth = measure(byval("thunk-ok", lane + "; fnptr-thunks: ...", exact, src=thunked))
        check("114 rule /11: a shim site is admitted THROUGH its exact thunk, counted, still `indirect`",
              rth["info"]["indirect_sites_dispatched_by_value"] == 1
              and rth["info"]["indirect_sites_dispatched_through_abi_thunk"] == 1
              and rth["info"]["abi_thunks"] == 1
              and rth["info"]["escaping_call_sites_by_class"].get("indirect") == 1,
              str({k: rth["info"].get(k) for k in ("indirect_sites_dispatched_through_abi_thunk", "abi_thunks")}))
        code, out = _run(["--manifest", str(byval("thunk-bad", lane + "; fnptr-thunks: ...", exact,
                                                  src=thunked.replace("insertfield (ptr) %2, 0, %0",
                                                                      "insertfield (ptr) %2, 0, %1"))),
                          "--baseline", str(bl)])
        check("115 rule /11: a thunk that is not the exact spread of its shim is REFUSED",
              code == EXIT_REFUSE and "exact rust-call spread" in out, out[-240:])
        named = thunked.replace(f"fn @{_F0}(functy.2) {{",
                                f"global internal @gz (ptr) = {{ fndef<func.0> }}\nfn @{_F0}(functy.2) {{", 1)
        code, out = _run(["--manifest", str(byval("thunk-shim-named", lane + "; fnptr-thunks: ...", exact,
                                                  src=named)), "--baseline", str(bl)])
        check("116 rule /11: with a constant naming the SHIM as a value the thunk credit is withdrawn "
              "and the signature mismatch is REFUSED again",
              code == EXIT_REFUSE and "positional mismatch" in out, out[-240:])

        # 17. Rule /8 (crystal plan step 19): the `intrinsic-arms` lane. The base's ctpop havoc at
        #     f0/bb1 is replaced by an arm; everything else is the base.
        havoc_bb1 = "bb1:\n" + "\n".join(_havoc(2, "u32")) + "\n    br bb2"
        arm_src0 = (tmp / "base.trust-ir.txt").read_text()
        assert havoc_bb1 in arm_src0, "self-test: the base's ctpop site moved"
        ctpop_obl = next(ln for ln in arm_src0.split("\n")
                         if ln.startswith("obligation ") and f"absent callee `{_CTPOP}`" in ln)
        t_ctpop, t_add = INTRINSIC_ARM_TAG_BASE + 3, INTRINSIC_ARM_TAG_BASE + 0
        ctpop_arm = ["    %2 = const usize 7", f"    %3 = ctpop usize %2  ; #proof: custom({t_ctpop})",
                     f"    %20 = trunc usize %3 to u32  ; #proof: custom({t_ctpop})"]

        def arm_text(bb1: list[str], *, keep_ctpop_obl: bool = False, extra_obls: tuple = (),
                     supplied: list[str] | None = None) -> str:
            lines = arm_src0.replace(havoc_bb1, "bb1:\n" + "\n".join(bb1) + "\n    br bb2", 1).split("\n")
            if not keep_ctpop_obl:
                lines.remove(ctpop_obl)
            head = [ln for ln in lines if not ln.startswith("obligation ")]
            obls = [ln for ln in lines if ln.startswith("obligation ")]
            # Renumber 0..n-1 (the script refuses a gap), then append the extras.
            obls = [re.sub(r"^obligation \d+ ", f"obligation {i} ", ln) for i, ln in enumerate(obls)]
            obls += [_obl(len(obls) + i, d, fid, fname, bb) for i, (d, fid, fname, bb) in enumerate(extra_obls)]
            if supplied:
                at = max(i for i, ln in enumerate(head) if ln == "}") + 1
                head = head[:at] + supplied + head[at:]
            return "\n".join([ln for ln in head if ln != ""] + obls) + "\n"

        def arm_art(tag: str, text: str, *, lane: bool = True, callee: str = _CTPOP,
                    evidence: str | None = None, rows=(_COLD,)) -> Path:
            mp = tmp / f"{tag}.trust-ir.txt"
            mp.write_text(text)
            head_ = intrinsic_head(callee)

            def m8(j):
                j["artifacts"]["text"] = mp.name
                j["artifacts"]["text_bytes"] = len(text.encode())
                j["producer"] = {"call_evidence": "per-site verdicts"}
                if lane:
                    j["producer"]["intrinsic_arms"] = "ON (-Ztrust-ir-lanes=intrinsic-arms)"
                c1 = j["members"][0]["calls"][1]
                c1.update(site=callee, resolved=callee, **{"class": f"intrinsic-terminal: {callee}"})
                for mem_ in j["members"]:
                    for c in mem_["calls"]:
                        if c["class"].startswith("intrinsic-terminal"):
                            c["evidence"] = {_XADD: "native-op:atomicrmw", _COLD: "no-trace"}.get(
                                c["resolved"], evidence or f"exact-arm:{head_}")
                j["escaping"] = j["escaping"] + [f"{n_}: bodyless instance kind Intrinsic" for n_ in rows]
            return as_v3(tag, m8)

        ra = measure(arm_art("arm-ok", arm_text(ctpop_arm)))
        rh = measure(as_v3e("arm-ref"))
        check("105 rule /8: an exact ctpop arm is intrinsic-modelled (`exact-arm:ctpop`), one escaping "
              "site fewer than the havoc twin, nothing unreconciled",
              ra["unreconciled"] == [] and ra["info"]["intrinsic_arm_sites_by_head"] == {"ctpop": 1}
              and ra["metrics"]["escaping_call_sites"] == rh["metrics"]["escaping_call_sites"] - 1
              and ra["info"]["producer_site_evidence"].get("exact-arm:ctpop") == 1
              and any(x["resolved"] == _CTPOP and x["classification"] == "intrinsic-modelled"
                      for x in ra["sites"]), f"{ra['unreconciled'][:2]} {ra['metrics']}")
        code, out = _run(["--manifest", str(arm_art("arm-nolane", arm_text(ctpop_arm), lane=False)),
                          "--baseline", str(bl)])
        check("106 an `exact-arm:` verdict from a producer that does not name the lane is REFUSED",
              code == EXIT_REFUSE and "intrinsic_arms" in out, out[-200:])
        code, out = _run(["--manifest", str(arm_art("arm-nolane2", arm_text(ctpop_arm), lane=False,
                                                     evidence="no-trace", rows=(_CTPOP, _COLD))),
                          "--baseline", str(bl)])
        check("107 an arm TAG in a module whose producer does not name the lane is REFUSED",
              code == EXIT_REFUSE and "intrinsic-arm tag" in out, out[-200:])
        rt = measure(arm_art("arm-short", arm_text(ctpop_arm[:2]), rows=(_CTPOP, _COLD),
                             evidence="no-trace"))
        check("108 an arm whose opcodes are not its head's template (the trunc dropped) is not "
              "credited: the site escapes and its tagged evidence is unreconciled",
              any(u["kind"] == "row-bb-holds-evidence-the-row-does-not-explain" for u in rt["unreconciled"])
              and not rt["info"]["intrinsic_arm_sites_by_head"], f"{rt['unreconciled'][:2]}")
        wrong = [ln.replace(f"custom({t_ctpop})", f"custom({t_add})") for ln in ctpop_arm]
        rw8 = measure(arm_art("arm-otherhead", arm_text(wrong), rows=(_CTPOP, _COLD), evidence="no-trace"))
        check("109 another head's tag (saturating_add's) at a ctpop row is never ctpop evidence",
              any(u["kind"] == "row-bb-holds-evidence-the-row-does-not-explain" for u in rw8["unreconciled"])
              and not rw8["info"]["intrinsic_arm_sites_by_head"], f"{rw8['unreconciled'][:2]}")
        # A CHARGED head: ctlz_nonzero::<usize>, its charge + the 64-bit smear + ctpop + trunc.
        nz = "core::intrinsics::ctlz_nonzero::<usize>::<__trust_args@ee>"
        tz = INTRINSIC_ARM_TAG_BASE + 5
        nz_lines, v = [], 30

        def emit(code_: str) -> None:
            nz_lines.append(f"    {code_}  ; #proof: custom({tz})")

        emit(f"%{v} = const usize 0"); emit(f"%{v+1} = icmp ne usize %2, %{v}")
        emit(f"%{v+2} = const usize 1"); emit(f"%{v+3} = select usize %{v+1}, %{v+2}, %{v}")
        emit(f"%{v+4} = const usize 1"); emit(f"%{v+5} = udiv usize %{v+4}, %{v+3}")
        y, v = "%2", v + 6
        for sh in (1, 2, 4, 8, 16, 32):
            emit(f"%{v} = const usize {sh}"); emit(f"%{v+1} = lshr usize {y}, %{v}")
            emit(f"%{v+2} = or usize {y}, %{v+1}")
            y, v = f"%{v+2}", v + 3
        emit(f"%{v} = not usize {y}"); emit(f"%{v+1} = ctpop usize %{v}")
        emit(f"%{v+2} = trunc usize %{v+1} to u32")
        nz_bb1 = ["    %2 = const usize 9"] + nz_lines
        pre = (f"[trust-intrinsic-precondition] `{nz}` requires a nonzero argument; violating it is "
               f"undefined behaviour", 0, _F0, 1)
        rn = measure(arm_art("arm-nz-nopre", arm_text(nz_bb1), callee=nz, rows=(nz, _COLD),
                             evidence="no-trace"))
        rp = measure(arm_art("arm-nz-pre", arm_text(nz_bb1, extra_obls=(pre,)), callee=nz))
        check("110 a CHARGED head is credited only WITH its precondition obligation at the site",
              any(u["kind"] == "row-bb-holds-evidence-the-row-does-not-explain" for u in rn["unreconciled"])
              and rp["unreconciled"] == [] and rp["info"]["intrinsic_arm_sites_by_head"] == {"ctlz_nonzero": 1}
              and rp["info"]["intrinsic_arm_precondition_charges"] == 1,
              f"{rn['unreconciled'][:1]} {rp['unreconciled'][:2]} {rp['info']['intrinsic_arm_sites_by_head']}")
        rx8 = measure(arm_art("arm-pre-extra", arm_text(ctpop_arm, extra_obls=(
            (f"[trust-intrinsic-precondition] `{_CTPOP}` requires nothing", 0, _F0, 1),))))
        check("111 a precondition obligation at an UNCHARGED head's arm is evidence nobody claims",
              any(u["kind"] == "extra-evidence-at-matched-site" for u in rx8["unreconciled"]),
              f"{rx8['unreconciled'][:2]}")
        # compare_bytes: a SUPPLIED body right after the members.
        cb = "core::intrinsics::compare_bytes"
        body = ["fn @core::intrinsics::compare_bytes(functy.2) {", '    ; #producer: "trust-intrinsic-arm"',
                "bb0(%0: ptr, %1: ptr, %2: usize):", "    %3 = const usize 0", "    %4 = const i32 0",
                "    br bb1(%3, %4)", "bb1(%5: usize, %6: i32):", "    %7 = icmp ult usize %5, %2",
                "    condbr %7, bb2, bb3", "bb2:", "    %8 = gep u8, ptr %0, %5", "    %9 = load u8, ptr %8",
                "    %10 = gep u8, ptr %1, %5", "    %11 = load u8, ptr %10", "    %12 = zext u8 %9 to i32",
                "    %13 = zext u8 %11 to i32", "    %14 = sub i32 %12, %13", "    %15 = const i32 0",
                "    %16 = icmp eq i32 %6, %15", "    %17 = select i32 %16, %14, %6", "    %18 = const usize 1",
                "    %19 = add usize %5, %18", "    br bb1(%19, %17)", "bb3:", "    ret %6", "}"]
        cb_bb1 = ["    %2 = const usize 3",
                  f"    %3 = call @func.2(%0, %0, %2)  ; #proof: custom({INTRINSIC_ARM_TAG_BASE + 12})"]
        rc8 = measure(arm_art("arm-cb", arm_text(cb_bb1, supplied=body), callee=cb))
        check("112 compare_bytes calling its SUPPLIED body is credited; the body is neither a member nor a "
              "declaration", rc8["unreconciled"] == [] and rc8["info"]["supplied_intrinsic_bodies"] == [cb]
              and rc8["info"]["intrinsic_arm_sites_by_head"] == {"compare_bytes": 1}
              and rc8["info"]["declared_premise_functions"] == 0, f"{rc8['unreconciled'][:2]}")
        bad = body[:6] + ["    %99 = call @func.0(%0)"] + body[6:]
        code, out = _run(["--manifest", str(arm_art("arm-cb-call", arm_text(cb_bb1, supplied=bad), callee=cb)),
                          "--baseline", str(bl)])
        check("113 a supplied body that CALLS anything is refused", code == EXIT_REFUSE and "call nothing" in out,
              out[-200:])
        code, out = _run(["--manifest", str(arm_art("arm-cb-nolane", arm_text(cb_bb1, supplied=body),
                                                    callee=cb, lane=False, evidence="no-trace",
                                                    rows=(cb, _COLD))), "--baseline", str(bl)])
        check("114 a supplied body from a producer that does not name the lane is refused",
              code == EXIT_REFUSE and "supplied intrinsic" in out, out[-200:])
        ru8 = measure(arm_art("arm-cb-unused", arm_text(ctpop_arm, supplied=body)))
        check("115 a supplied body no member calls is unreconciled",
              any(u["kind"] == "supplied-body-never-called" for u in ru8["unreconciled"]),
              f"{ru8['unreconciled'][:2]}")
        code, out = _run(["--manifest", str(arm_art("arm-cb-user", arm_text(cb_bb1, supplied=[
            body[0].replace("core::intrinsics::compare_bytes", "mycrate::compare_bytes")] + body[1:]),
            callee=cb)), "--baseline", str(bl)])
        check("116 a supplied body not named as a core intrinsic the lane supplies is refused",
              code == EXIT_REFUSE and "not a core intrinsic" in out, out[-200:])

        # size_of_val: a slice tail is len * elem_size with the fits-isize bound CHARGED; a sized T is
        # a constant and owes nothing.
        sov = "core::intrinsics::size_of_val::<[u32]>::<__trust_args@ff>"
        ts = INTRINSIC_ARM_TAG_BASE + 14
        sov_bb1 = ["    %2 = const usize 0"] + [f"    {c}  ; #proof: custom({ts})" for c in (
            "%40 = ptr_metadata fatptr<slice ty.0> %0 to u64", "%41 = const u64 2305843009213693951",
            "%42 = icmp ule u64 %40, %41", "%43 = const u64 1", "%44 = const u64 0",
            "%45 = select u64 %42, %43, %44", "%46 = const u64 1", "%47 = udiv u64 %46, %45",
            "%48 = const u64 4", "%49 = mul u64 %40, %48")]
        sov_pre = (f"[trust-intrinsic-precondition] `{sov}` requires a slice tail whose total size fits "
                   f"isize; violating it is undefined behaviour", 0, _F0, 1)
        rs1 = measure(arm_art("arm-sov", arm_text(sov_bb1, extra_obls=(sov_pre,)), callee=sov))
        rs0 = measure(arm_art("arm-sov-nopre", arm_text(sov_bb1), callee=sov, rows=(sov, _COLD),
                              evidence="no-trace"))
        sized = "core::intrinsics::size_of_val::<root::S>::<__trust_args@fe>"
        rs2 = measure(arm_art("arm-sov-sized", arm_text(
            ["    %2 = const usize 0", f"    %3 = const usize 24  ; #proof: custom({ts})"]), callee=sized))
        check("121 size_of_val: the slice-tail arm is credited only WITH its fits-isize charge; the sized "
              "arm is one constant and owes no obligation",
              rs1["unreconciled"] == [] and rs1["info"]["intrinsic_arm_sites_by_head"] == {"size_of_val": 1}
              and rs1["info"]["intrinsic_arm_precondition_charges"] == 1
              and any(u["kind"] == "row-bb-holds-evidence-the-row-does-not-explain" for u in rs0["unreconciled"])
              and rs2["unreconciled"] == [] and rs2["info"]["intrinsic_arm_precondition_charges"] == 0
              and rs2["info"]["intrinsic_arm_sites_by_head"] == {"size_of_val": 1},
              f"{rs1['unreconciled'][:2]} {rs0['unreconciled'][:1]} {rs2['unreconciled'][:2]}")

        # 18. Rule /9 (D10): the /8 -> /9 migration is a DECLARED RECLASSIFICATION. A genuine /8
        #     baseline is cut with the SEQ image switched off (every atomic then measures as /8 did).
        global SEQ_IMAGED_ATOMIC_OPS
        saved_seq = SEQ_IMAGED_ATOMIC_OPS
        bl8 = tmp / "bl8.json"
        try:
            SEQ_IMAGED_ATOMIC_OPS = frozenset()
            r8 = measure(base)
            _run(["--init", "--reason", "self-test: a /8 baseline (no SEQ image)", "--manifest", str(base),
                  "--baseline", str(bl8)])
        finally:
            SEQ_IMAGED_ATOMIC_OPS = saved_seq
        b8 = json.loads(bl8.read_text())
        b8["rule_version"] = "crystal-link3-reconcile/8"
        b8["seal"] = _seal(b8)
        bl8.write_text(json.dumps(b8))
        code, out = _run(["--manifest", str(base), "--baseline", str(bl8)])
        check("117 a /8 baseline is refused by a plain /9 run (RULE VERSION)",
              code == EXIT_FAIL and "RULE VERSION" in out, out[-200:])
        code, out = _run(["--rebase", "--reason", "self-test: /8 -> /9, D10 reclassification", "--baseline", str(bl8)])
        nb9 = json.loads(bl8.read_text())
        mig = nb9["history"][-1].get("rule_migration", {})
        check("118 --rebase carries a /8 baseline to /9 as a DECLARED RECLASSIFICATION: exactly the one xadd "
              "site moved, from escaping/intrinsic-unprojectable to atomic-seq-premise, every figure no worse",
              code == EXIT_OK and nb9["rule_version"] == RULE_VERSION and mig.get("reclassified_sites") == 1
              and mig.get("old_artifact_reproduced_modulo_reclassification") is True
              and nb9["metrics"]["escaping_call_sites"] == r8["metrics"]["escaping_call_sites"] - 1,
              out[-300:])
        t8 = json.loads(bl8.read_text())
        t8 = {**b8, "site_table_sha256": "0" * 64}
        t8["seal"] = _seal(t8)
        bl8t = tmp / "bl8t.json"
        bl8t.write_text(json.dumps(t8))
        code, out = _run(["--rebase", "--reason", "self-test: a /8 baseline whose table does not match",
                          "--baseline", str(bl8t)])
        check("119 a /8 baseline whose site table does not reproduce modulo the declared move is REFUSED",
              code == EXIT_FAIL and "modulo the declared reclassification" in out, out[-300:])
        w8 = {**b8, "metrics": {**b8["metrics"], "silent_havoc_call_sites": 0}}
        w8["seal"] = _seal(w8)
        bl8w = tmp / "bl8w.json"
        bl8w.write_text(json.dumps(w8))
        code, out = _run(["--rebase", "--reason", "self-test: a /8 baseline claiming a better figure",
                          "--baseline", str(bl8w)])
        check("120 a reclassification cannot carry a figure the artifact makes WORSE", code == EXIT_FAIL, out[-300:])

        # 13. C-M0: trust-ir's QUOTED symbols (WS4.3) and the anti-swap pin modulo identity hashes.
        blq = tmp / "blq.json"
        _run(["--init", "--reason", "self-test C-M0 baseline", "--manifest", str(base), "--baseline", str(blq)])
        qd = _respelled(base, "ws43")
        qtext = (tmp / "ws43.trust-ir.txt").read_text()

        def measured_or_refusal(mpath: Path) -> dict:
            try:
                return measure(mpath)
            except Refusal as exc:
                return {"metrics": None, "refused": str(exc), "site_table_sha256": None,
                        "escaping_callees": None, "info": None, "sites": []}
        rq = measured_or_refusal(qd)
        check("125 the same bundle printed by a WS4.3 printer (every non-bare fn symbol QUOTED) measures "
              "identically: figures, site table, pinned callees, info",
              f'fn @"{_F0}"(functy.0) {{' in qtext and rq["metrics"] == m
              and rq["site_table_sha256"] == r["site_table_sha256"]
              and rq["escaping_callees"] == r["escaping_callees"] and rq["info"] == r["info"],
              rq.get("refused") or qtext[:300])
        code, out = _run(["--manifest", str(qd), "--baseline", str(blq)])
        check("126 the quoted bundle passes against the legacy bundle's baseline", code == EXIT_OK, out[-300:])
        odd = "root::f1<'a> ($x) {closure#0}"
        qo = _respelled(base, "ws43odd", subst=((_F1, odd),))
        oline = [ln for ln in (tmp / "ws43odd.trust-ir.txt").read_text().split("\n")
                 if ln.startswith("fn @") and "closure" in ln]
        ro = measured_or_refusal(qo)
        check("127 a quoted symbol holding a space, `(`, `{`, a lifetime and `$` decodes to the manifest's "
              "name (its obligations' sources name it too)",
              oline == ['fn @"root::f1<\'a> ($x) {closure#0}"(functy.1) {'] and ro["metrics"] == m
              and any(s_["member_name"] == odd for s_ in ro["sites"]), str(oline))
        rules = [('"a\\u{7}b"', "a\x07b"), ('"a::\\n\\t\\r\\0\\\\\\""', 'a::\n\t\r\0\\"'),
                 ('"a\\u{07}b"', None), ('"a\\u{7F}"', None), ('"a\\u{a}"', None), ('"a\\u{41}"', None),
                 ('"a\\qb"', None), ('"a::b', None), ('"a\x07b"', None), ('"abc"', None), ('""', None),
                 ('"a\\u{d800}"', None)]
        got = []
        for spelled, want in rules:
            try:
                nm = tir_symbols.read_def_symbol(spelled + "(functy.0) {", 0, re.compile(r"(\S+)"))[0]
            except tir_symbols.SymbolRefusal:
                nm = None
            got.append(nm == want)
        check("128 the quoted-symbol decoder takes exactly the printer's escapes: a control char as "
              "lowercase unpadded \\u{..}, the six short escapes; and REFUSES a padded, upper-case, "
              "short-escapable or non-control \\u, an unknown escape, an unterminated string, a raw control "
              "char, a bare-able or empty quoted name and a surrogate", all(got), str(got))
        mixed = _respelled(base, "ws43mixed", only=0)
        code, out = _run(["--manifest", str(mixed), "--baseline", str(blq)])
        check("129 a module mixing a QUOTED symbol with a RAW (unquoted, non-bare) one is REFUSED (exit 2): "
              "no trust-ir printer wrote it", code == EXIT_REFUSE and "mixes a QUOTED symbol" in out, out[-300:])
        rehash = (("__trust_args@aa>", "__trust_args@a9>"), ("__trust_args@cc>", "__trust_args@c9>"))
        rh = _respelled(base, "rehash", subst=rehash)
        rrh = measured_or_refusal(rh)
        code, out = _run(["--manifest", str(rh), "--baseline", str(blq)])
        check("130 a sysroot rebuild that renames only identity hashes (__trust_args@) PASSES, with the "
              "renames reported; the raw pin (C-M0's RED) read both as NEW ESCAPING CALLEES",
              rrh["metrics"] == m and len(set(rrh["escaping_callees"] or ()) - set(r["escaping_callees"])) == 2
              and code == EXIT_OK and "IDENTITY RENAMES: 2" in out, out[-400:])
        rsw = _respelled(_synthetic(tmp, "swap2", swap=True), "rehashswap", subst=rehash)
        code, out = _run(["--manifest", str(rsw), "--baseline", str(blq)])
        check("131 a REAL swap beside the identity renames still FAILS, naming only the swapped callee",
              code == EXIT_FAIL and "compared modulo identity hashes (1;" in out
              and "mir-unavailable|ext::other_fn" in out and "__trust_args@a9" not in out, out[-400:])
        gbl = tmp / "blg.json"
        gname = "ext::g::<__trust_args@e1>"
        gbase = _respelled(base, "gbase", subst=(("ext::mir_unavail_fn", gname),))
        _run(["--init", "--reason", "self-test C-M0 multiset baseline", "--manifest", str(gbase),
              "--baseline", str(gbl)])
        gdup = _respelled(gbase, "gdup", subst=(("ext::reified", "ext::g::<__trust_args@e2>"),))
        rg = measured_or_refusal(gdup)
        code, out = _run(["--manifest", str(gdup), "--baseline", str(gbl)])
        check("132 an escape swapped for a SECOND instance of a pinned callee (same name modulo hashes) "
              "FAILS: the pin is a multiset, so the canonical name's count rising is a new escape",
              rg["metrics"] == measured_or_refusal(gbase)["metrics"] is not None and code == EXIT_FAIL
              and "compared modulo identity hashes (1;" in out, out[-400:])
        canon = tir_symbols.canonical_identity
        check("133 canonical_identity blanks the hex of exactly __trust_args@<hex>>, __trust_crate@<hex>:: "
              "and <crate>[<hex>]:: and nothing else",
              canon("a::<__trust_args@ab12>") == "a::<__trust_args@#>"
              and canon("__trust_crate@0f1e::h::T") == "__trust_crate@#::h::T"
              and canon("DefId(2:9 ~ core[764f]::cmp::f)") == "DefId(2:9 ~ core[#]::cmp::f)"
              and canon("x::<[u8; 4]>::y") == "x::<[u8; 4]>::y" and canon("a::<__trust_args@zz>") == "a::<__trust_args@zz>"
              and canon("tag@deadbeef12") == "tag@deadbeef12" and canon("v[12]") == "v[12]")

        code, out = _run(["--pinned-inputs"])
        check("134 --pinned-inputs DERIVES the first-party modules this script runs besides itself "
              "(the shared symbol reader), for the gate registry's R7 pin",
              code == EXIT_OK and out.split() == ["scripts/crystal_trust_ir_symbols.py"], out[-200:])

        # 12. Improvement: PROGRESS passes; --rebase needs a reason, lowers, then passes.
        better = _synthetic(tmp, "better", drop_clone=True)
        rb = measure(better)
        code, out = _run(["--manifest", str(better), "--baseline", str(bl)])
        check("38 an improvement passes with PROGRESS", code == EXIT_OK and "PROGRESS" in out, out[-300:])
        code, out = _run(["--rebase", "--manifest", str(better), "--baseline", str(bl)])
        check("39 --rebase without --reason is a usage error", code == EXIT_USAGE)
        code, out = _run(["--rebase", "--reason", "self-test: clone site removed", "--manifest", str(better),
                          "--baseline", str(bl)])
        nb = json.loads(bl.read_text())
        check("40 --rebase lowers the baseline to the improved measurement",
              code == EXIT_OK and nb["metrics"] == rb["metrics"] and len(nb["history"]) == 2, out[-300:])
        code, out = _run(["--baseline", str(bl)])
        check("41 the rebased baseline passes on its own artifact", code == EXIT_OK, out[-200:])
        code, out = _run(["--manifest", str(base), "--baseline", str(bl)])
        check("42 the old (worse) artifact now fails against the lowered baseline", code == EXIT_FAIL, out[-200:])
        code, out = _run(["--rebase", "--reason", "self-test: nothing changed", "--baseline", str(bl)])
        check("43 --rebase on the same artifact with nothing improved is refused", code == EXIT_FAIL, out[-200:])

    width = max(len(n) for n, _, _ in results)
    failed = 0
    for name, ok, detail in results:
        print(f"  {'ok  ' if ok else 'FAIL'} {name.ljust(width)}" + ("" if ok else f"  -- {detail}"))
        failed += 0 if ok else 1
    print(f"SELF-TEST {'PASS' if not failed else 'FAIL'}: {len(results) - failed}/{len(results)} arms")
    return EXIT_OK if not failed else EXIT_FAIL


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
