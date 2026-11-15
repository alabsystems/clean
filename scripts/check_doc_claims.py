#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Fail closed when the navigation docs' prose stops matching the tree.

WHY THIS EXISTS
---------------
Every rule in `docs/GATE_REGISTRY.md` asks whether an *enforcement artifact* is
wired and whether it has been seen to fail. None of them asks whether the
**status prose** is true, and on 2026-08-26 four CLAUDE.md claims were proved
false by measurement in a single day -- two of which caused bricks to be opened
against things that were already fixed:

  1. "the everyday-language battery ... is 51/63"  -- the artifact the sentence
     itself cited, `reports/everyday-battery.json`, had read 63/63 since
     2026-08-24. The paragraph quoted 38/63 and then 51/63; both stood in it
     after the battery had gone green.
  2. "~75% of elaboration time is `ElabCtx::build_local_ctx`"  -- fixed
     2026-08-22, 10.5x.
  3. "the first kernel failure is `forall_true_iff`, a `Sort*` U2 universe
     mismatch"  -- fixed, and the diagnosis was wrong as well.
  4. "simp has NO conditional-lemma discharger"  -- it has had one since
     2026-08-02.

Lake's prose was wrong in the OTHER direction ("the native backend builds
nothing" -- it is native end-to-end), which is the same defect: a sentence
nobody re-derives.

WHAT THIS CATCHES, AND WHAT IT HONESTLY DOES NOT
------------------------------------------------
Of those four, exactly ONE is reachable by a cheap deterministic re-derivation:
claim 1, because the prose named the artifact that carries the number. That is
the whole mechanical purchase available here, and pretending otherwise would
make this gate the thing it exists to stop. Claims 2-4 are qualitative
assertions about program behaviour; no string-matching check can evaluate
"~75% of elaboration time" or "simp has no discharger" without running the
elaborator. What this gate does about them is structural rather than semantic:
D3 refuses a NEW quantitative claim that cites an artifact and does not bind
one, so the next claim of the shape that went stale cannot be written unbound.

The rules, all fail-closed (D5 LINK is documented beside its pattern below):

  D1 REF     A repo-rooted path cited in a governed doc must exist, unless the
             doc declares WHY it does not -- `absent` (deliberately gone, e.g.
             a `docs/GATE_REGISTRY.md` R8 retirement), `elsewhere` (a sibling
             repo, verified there when that repo is on disk), `pinned` (a
             sibling repo AT A NAMED COMMIT, verified present in that commit,
             and every paragraph citing the path must name the commit), or
             `base` (the doc writes paths relative to a subdirectory of THIS
             repo, so the path is resolved there as well and still has to
             exist).

             Every one of the four is a declaration that can go dead, and a
             dead declaration is worse than none -- it keeps a citation exempt
             on the day the thing it points at disappears. So each is checked
             from the other side too: a declaration for a path no citation in
             the doc reads is a refusal, an `elsewhere` or `pinned` whose path
             resolves locally is a refusal, and a `base` that rescues no
             citation at all is a refusal. `absent` is deliberately NOT refused
             for resolving locally, for a measured reason: CLAUDE.md correctly
             declares `reports/parser-mathlib-parse-rate.json` absent because
             the sweep mints it UNTRACKED, so it is present in the working tree
             of whoever last ran the sweep and absent everywhere else. A
             from-the-other-side rule there would refuse that author's push
             for being right.

             A declaration's REASON is checked where it can be: every commit
             id it names must be a commit of the repository the declaration is
             about (THIS one for `absent`, the sibling for `elsewhere` and
             `pinned`), and every `git show <rev>:<path>` it promises must
             show. For `pinned`, the citing paragraph must name the pinned
             commit as a whole commit-id TOKEN (another abbreviation of the
             same commit counts when the sibling resolves it); a longer hex run
             that merely contains the pin names a different commit. For
             `absent`, the same holds of the PROSE BLOCK that cites the path --
             its paragraph, or its list item, never just its physical line:
             `absent` exempts the path, not a "(commit <rev>)" or "read it at
             <rev>" beside it, so every commit id in that block must be a
             commit HERE, or -- attributed to a sibling by name
             (`trust <rev>`) -- a commit of THAT sibling when it is on this
             box (UNVERIFIED when it is not), and every `git show` in it must
             show.

             A citation is PROSE. Marker text is blanked before any path is
             read, so a declaration whose own reason backticks its path does
             not count as the citation that keeps it alive.
  D2 FIGURE  A `<!-- claim: figure ... -->` marker binds a prose figure to a
             key of a JSON artifact. The value is re-derived from the artifact
             and must appear in the BOUND SPAN -- the marker's own line and the
             three above it, clipped to its paragraph. There is no third copy
             of the number to drift: move the artifact and the prose is red
             until somebody reads it.

             The span is a backward window and not the whole paragraph, and
             that is load-bearing rather than fussy. The paragraph this gate
             was written for says the battery is 63/63 and then, three lines
             later, that it read 38/63 and 51/63 on two earlier dates -- which
             is exactly the right way to write it. Under a paragraph-wide
             span, a regression back to 51/63 would find "51/63" sitting in
             that history and report GREEN. So a marker is placed directly
             BELOW the sentence it binds, and only what is above it counts.
             A misplaced marker fails closed.
  D3 BIND    (Opted in by TEN more docs on 2026-09-14, each measured FREE
             first: AGENTS, README, VISION, VERIFICATION_AUDIT,
             JUSTIFIED_EXCEPTIONS, DESIGN, PUBLIC_DEMO, BENCHMARKS,
             RELEASE_READINESS, PHILOSOPHY. Vacuous on the day it is switched on
             is the POINT of a forcing function -- it binds the next figure
             somebody writes, not the ones already there. The five that are not
             free were measured too. The two CERTIFICATES were then priced and
             paid the same day -- one figure each, and BOTH were `pointer-only`
             rather than `figure`, which is the distinction that rule exists
             for: `39/538` is the dated 2026-07-17 finish-plan census, which the
             paragraph itself calls "a dated external measurement, not a current
             in-tree gate", and C5's `10/10` is re-derived by RUNNING
             `clean audit soundness`. Neither has a committed artifact, so
             binding either would have invented a source for a number. Three
             remain priced for whoever takes them: CRYSTAL_STATUS 14 unbound
             figure paragraphs, GATE_REGISTRY 3, SUITE_STATE 2 -- a judgement
             per figure, not a mechanical edit.)

             In a doc that opts in, a paragraph that BOTH cites a tracked
             `reports/`|`data/` JSON artifact AND quotes an `N/M` figure must
             carry a marker -- either a `figure` binding or an explicit
             `pointer-only` saying the figure is dated and not live. This is
             the forcing function: without it D2 is opt-in and nobody opts in.

  D4 ANCHOR  A `<!-- claim: anchor <path>:<line> <needle> -->` marker binds a
             LINE citation to the text that must be on it. D1 asks whether a
             cited path EXISTS; it has never asked whether the cited line says
             what the prose claims, and that gap cost four measured defects in
             governed docs, each of which resolved perfectly while pointing at
             something else -- a lineage parser, a `};`, a comment about float
             division, a doc comment ten lines above the function. One of the
             four was wrong the day it was written, under a parenthetical that
             said "read at last".

             Opt-in, like `figure`, and for the same reason: a heuristic over
             every `path:NNN` in these documents is noise, and a rule nobody
             can satisfy gets suppressed rather than obeyed. A near miss is
             reported with the real line and the signed offset, so the fix is a
             number rather than a hunt; a needle that occurs nowhere says so,
             because those are different repairs.

  D6 BUDGET  `CLAUDE.md` plus every `.claude/rules/*.md` must stay within
             INSTRUCTION_FILES_BUDGET characters, counted as UTF-16 code units
             because that is how Claude Code counts them. Claude Code loads
             those files whole into every session and warns once instruction
             files pass 150,000 characters IN TOTAL -- a total that also counts
             the operator's own `~/.claude/CLAUDE.md`, which this repository
             cannot see, so the budget stops well short of the limit. Measured
             2026-09-26: `CLAUDE.md` alone had reached 158,182 characters and
             the harness warned that the set was over its limit, because every
             lane appended a paragraph per measured class and nothing ever
             removed one. That
             file had been cut once before, on 2026-09-15, and grew straight
             back: a size nobody checks is a size nobody keeps. Narrative goes
             to docs/FRONTEND_CLASS_LEDGER.md, docs/SELF_VERIFICATION_NAVIGATION.md
             or docs/archive/CLAUDE_MD_HISTORY.md, and the instruction file
             keeps standing rules and pointers. Checked only when `CLAUDE.md` is
             governed, which it always is here.

SCOPE IS MEASURED, NOT ASSUMED
------------------------------
D1 is not switched on everywhere, because a first draft that was measured
2026-08-26 over every backticked path in seven docs produced 246 "missing" hits
of which the overwhelming majority were correct prose:

  * basename shorthand -- `local_gate.sh`, `x.py`, `coverage.json`, `mod.rs`.
    A path token only counts here if it contains `/` AND its first segment is a
    top-level directory of THIS repo -- one the index TRACKS, or a gitignored
    root in `IGNORED_ROOTS` (see the section below on why "is on disk" was the
    wrong test, in both directions).
  * cross-repo paths -- `docs/CRYSTAL_STATUS.md` cites paths that resolve in
    the sibling Trust repo (`scripts/trust_ir_rowdiff.py`, `tests/ledger`).
    Those need `elsewhere`, one per path.
  * deliberately-absent paths -- `docs/GATE_REGISTRY.md` NAMES retired files,
    and R8 requires that they be gone. A blanket "cited path must exist" rule
    contradicts a rule the repo already enforces. Hence `absent`, which makes
    the exemption a reviewable sentence instead of a hole.

On the four navigation docs D1 IS switched on, and there it found live rot on
the day it was written: `docs/AUDIT_LEAN4_REPLACEMENT_2026-07-23.md`, cited
five times across CLAUDE.md, AGENTS.md, README.md and VISION.md as "the
authoritative commit-pinned source interpretation", does not exist and never
did -- the file is `..._2026-07-22.md`, and the wrong date had propagated to
every doc that pointed at it.

THE CROSS-REPO SCOPE ESTIMATE WAS ITSELF A DOC CLAIM, AND IT WAS WRONG
----------------------------------------------------------------------
`docs/CRYSTAL_STATUS.md` was held out above -- and in the `check_doc_claims`
registry row, and in the fifth-pass section of `docs/GATE_REGISTRY.md` -- as
citing "76 paths that resolve in the sibling Trust repo". Switching D1 on for
it 2026-08-27 measured the three-way split, and the estimate was wrong in the
way that matters: it named the wrong REPO for most of them, so the debt looked
cross-repo and unresolvable when it is almost entirely local and checkable.

  270  rooted path tokens (the current whole-gate surface was 173)
   64  distinct paths that do not resolve at the repo root, in 73 places
   44  of those (49 places) resolve under `crates/clean-verify/` -- the doc is
        a status page ABOUT that crate and writes `tests/crystal_a2_mint_lz.rs`
        for `crates/clean-verify/tests/crystal_a2_mint_lz.rs`. Not cross-repo.
   20  (24 places) resolve in the sibling `trust` repo. The first pass said
        14, and called the other 6 dead; see the retraction below.

The 44 are what `base` is for. Rewriting 49 citations would have "fixed" the
gate's complaint and left the convention in place, so the next lane writing
about a clean-verify test would be refused for spelling it the way the whole
document already spells it. `base` legalises the convention without weakening
the rule: root is tried first, the base second, and a path in neither is still
a refusal -- delete `crates/clean-verify/tests/crystal_a2_mint_lz.rs` and the
citation goes red exactly as before.

SIX MORE "DEAD" CITATIONS, AND THE REASON THEY WERE NOT DEAD
------------------------------------------------------------
The first pass over those 64 said six of them resolved in NEITHER repo, five
being labelled "in the trust repo" by the prose citing them. The evidence
looked airtight: absent from `../trust`'s working tree, absent from
`git log --all --diff-filter=A`, and the sibling files that would surround
them absent too -- no `probes/mfr8*`, no `designs/2026-08-18-*`, no
`reports/enum-payload-*`, no crate matching `*bignum*`.

Every part of that was an artifact of the CHECKOUT. `../trust` on this box is
a shallow, `blob:none` partial clone whose working tree is `ef5a5910ea`
(2026-08-14) while its own `origin/main` is `605e61cb22` (2026-08-27). `--all`
over a shallow clone cannot find a commit that was truncated away, so the
corroborating query corroborated the same blind spot as the first one. One
batched `git ls-tree origin/main` finds ALL SIX, in 9 ms.

So the finding is RETRACTED, and it changed the gate rather than the prose:
`elsewhere` now resolves against the sibling's history (see `_sibling_tracked`)
and the six are ordinary `elsewhere` citations. Two things are worth keeping
from it. First, a gate that refuses is not thereby right -- the false-refusal
direction is the dangerous one here, because the fix a red build invites is an
`absent` marker, and six correct citations would have been permanently
exempted with six false sentences written into the repo's live status page.
Second, this repo drew the identical wrong conclusion about
`reports/metadata-v12-sysroot.md` twice from the same clone before today, and a
third lane retracted it in `9513f5136` within the hour this was being written.
Three lanes, one checkout, one wrong answer, arrived at independently -- which
is what makes it a mechanism defect and not three careless readings. That lane
fixed the sentences; this one fixes the instrument, so the next lane cannot
reach the same wrong answer by being careful.

WHICH FIRST SEGMENTS MAKE A CITATION ROOTED -- AND WHY NOT "WHAT IS ON DISK"
----------------------------------------------------------------------------
Until 2026-09-15 the leading-segment test read the directories that happened to
EXIST at the root. Measured that day at one commit: this leg was RED on the
maintainer box (`docs/SUITE_STATE.md:1931 cites target/verify-runner-pinned/
worktree, which is not in the tree`) and GREEN on a pristine worktree of the
SAME commit -- because the box had a gitignored `target/` directory and the
worktree did not, so `target/...` was a rooted citation on one machine and
"another repo's layout" on the other. A gate whose verdict depends on untracked
state is not a gate: it reports the shape of somebody's checkout.

The set is now derived, never observed:

  * the top-level directories the index TRACKS (`git ls-files`, first segment
    of every path with a `/`, dot-prefixed ones excluded as before), PLUS
  * `IGNORED_ROOTS` -- a reviewed table, today `target` and `metrics`. The
    criterion for a row, exactly: (1) the root `.gitignore` marks the name as
    a directory (a trailing-`/` line, no `!`, no glob, no inner `/`); (2) the
    index tracks NOTHING under it; (3) this repo's OWN tooling writes it at
    the root -- the row names the writer; (4) a governed doc cites a path
    under it, which is the only reason to root anything there. (1) and (2)
    are re-derived on every run and either failing is a D0 IGNORED refusal --
    the table cannot outlive the ignore rule it stands on, and a row the index
    tracks under has a false premise. (3) and (4) are facts about tooling and
    prose, which is why this is a table and not a derivation (below). What a
    row COSTS: every governed-doc citation under it must be declared
    `absent`, naming the writer, in the SAME commit as the row -- because a
    citation under a row is refused undeclared on every box (next paragraph),
    an unpaid row turns the leg red everywhere at once.

AND A CITATION UNDER AN IGNORED ROOT IS NEVER RESOLVED ON DISK. The first
version of this rule still asked the disk whether `target/x` existed, and
review caught the mirror image of the defect above: `metrics/lean4_parity.json`
(VISION.md:63, docs/VERIFICATION_AUDIT.md:171), a gitignored runtime artifact,
was on the maintainer box and not on a pristine worktree, so with `metrics` in
the table the leg was GREEN here and RED there -- the same split, moved one
directory over. What a box holds under a gitignored root is untracked state by
definition, so a citation there is checked by DECLARATION alone (`absent`, and
the reason says what writes it) and the verdict is the same on every box.
`absent` is not checked from the other side (see D1 above), so a build output
that IS on the author's box does not refuse the author.

WHY A TABLE AND NOT "EVERY DIRECTORY .gitignore NAMES". That derivation was
implemented first and measured: the root `.gitignore` is a synced template
naming SIXTEEN directory patterns (`__pycache__/`, `build/`, `/env/`,
`htmlcov/`, `/venv/`, `mutants/`, ...), and taking all of them as this repo's
layout produced six NEW refusals, every one of them correct prose that the
skip below exists for -- `env/trusted_ext.rs`, `env/decl_add`,
`env/axiom_audit.rs` are crate-relative shorthand (1,498 tracked paths sit
under an `env/` subdirectory of `crates/`), and `build/aarch64-apple-darwin/
stage1`, `build/release` are the trust repo's and Lean's build layouts. No
mechanical property separates `build/` from `target/` in that file (same
shape, neither a tracked basename); what separates them is that nothing in
this tree writes `build/` at the root, which is a fact about the tooling and
so a reviewed row, like the GOVERNED table above it.

WHAT A ROW COSTS, MEASURED ON `metrics`. The row was in the first version of
this table, was dropped by review because its price was unpaid -- two
undeclared citations of `metrics/lean4_parity.json`, VISION.md:63 and
docs/VERIFICATION_AUDIT.md:171 -- and was put back the same day WITH the two
declarations. The census that prices a row is derived, not typed: for every
`ref`-governed doc, every `PATH_TOKEN` whose first segment is the row, and
whether an `absent` marker names it. On 2026-09-15 that read `target`: 22
cited / 22 declared (already paid before the row landed); `metrics`: 3 cited /
1 declared before the declarations, 5 / 5 after -- the two new ledger sentences
cite the path themselves, and are declared by the marker under them, so the
row's census counts them too. The writer each declaration
names was measured too: `crates/clean-kernel/tests/lean4_parity.rs:155-162`
(`write_parity_summary`, run by `cargo test --locked -p clean-kernel --test
lean4_parity --features test-utils -- lean4_parity_check`) writes
`CARGO_MANIFEST_DIR/../../metrics/lean4_parity.json`, and
`scripts/bench_regression.sh:26` writes `metrics/benchmarks/`;
`git check-ignore -v metrics/lean4_parity.json` -> `.gitignore:42:metrics`
(line 41 is the `metrics/` form condition (1) reads), and
`git ls-files metrics | wc -l` -> 0. The first version's comment said `clean
replacement` writes it; `grep -rn 'metrics/' crates/clean-cli/src | grep -v
/tests/` returns nothing (the one hit is a test asserting an output string),
so that sentence was retyped rather than derived and is gone.

WHAT GIT IS ASKED, AND IN WHAT ENVIRONMENT. `git rev-parse --show-toplevel`
must answer the root itself (a subdirectory of some other repository is not
"asked"), then one `git ls-files -z`. Both run -- as does the sibling
`ls-tree` -- with git's repository-location variables scrubbed
(`GIT_LOCATION_VARS`: GIT_DIR, GIT_WORK_TREE, GIT_INDEX_FILE, ...). With
GIT_DIR set and GIT_WORK_TREE unset, git treats the cwd as the work tree, so
the toplevel check passes and `ls-files` answers from whatever index GIT_DIR
names. Measured 2026-09-15 on Apple Git-155: git exports an absolute GIT_DIR
into a pre-push hook run from a LINKED worktree, and under
`GIT_DIR=<this repo>/.git` the "a root that cannot be asked is a refusal" arm
went GREEN, answered from this repository's index, and the two sibling arms
went RED. Nothing in the set comes from `iterdir`, and nothing in it comes
from the environment.

Consequences, each pinned by an arm: a citation under `target/` is refused on
EVERY box until it is declared, whether or not the file is there, and stays
green once declared whether or not the file is there; deleting a whole tracked
directory turns its citations RED instead of making them vanish from D1 (the
old rule skipped them -- the directory was not on disk, so its paths were "not
this repo's layout"); a stray untracked directory does not make citations
under it rooted; a root that cannot be ASKED what it tracks (no `.git`, no
git, a leaked GIT_DIR) is a D0 refusal, never an empty set, because an empty
set would make D1 check nothing and print green; a root that CAN be asked and
tracks nothing under any directory (`git archive | tar -x; git init` with no
`git add`) is the SAME refusal -- until 2026-09-15 it collapsed the set to the
`IGNORED_ROOTS` rows silently, and the run was red only by the accident of two
`base` markers that then rescued nothing; and an `IGNORED_ROOTS` row that
`.gitignore` no longer names, or that the index tracks paths under, is a D0
refusal too.

The "another repo's layout" skip holds exactly as before for tracked paths: a
tracked directory is on disk in any checkout that is not itself broken, so
`Mathlib/...`, `std/src/...` and `elab_match/...` were never in the old set
and are not in the new one, while `docs/`, `crates/`, `tests/` were and are.
What moved is only the untracked edges above.

This reads Markdown and JSON, and asks git for the index. It never reads Rust
or Lean source, so it declares no `source_scan` (registry rule R9) -- and a
declaration left behind by a scanner that is not there is itself an R9
refusal. It needs a git checkout: a `git archive` snapshot is a D0 refusal by
design, not a green.

A CITATION PINNED AT A SIBLING COMMIT
------------------------------------
Trust's `6ba5324748` (2026-09-22) deleted three files `docs/CRYSTAL_STATUS.md`
cites from trust main. The repair on 2026-09-24 rewrote the prose to "read it
at trust `dc31063cd3`" -- the deletion's parent -- and declared the three paths
`absent`. That made the gate green and checked nothing the prose said: `absent`
exempts a path from every rule, so a wrong commit, a typo in it, or a path the
commit never held would all have passed, and the three citations had left the
cross-repo count entirely. `pinned` is the declaration that sentence needs:
the path must be in the sibling's tree AT that commit (`git ls-tree <rev>`,
never "anywhere in history", which is what `elsewhere` asks), and every
paragraph that cites the path must name the commit, so the rev a reader is told
to open is the rev that was checked. A rev the sibling cannot resolve refuses,
unless the sibling is a shallow clone, which cannot answer and is UNVERIFIED.

MARKER SYNTAX
-------------
    <!-- claim: figure <artifact.json> <expr> -->
    <!-- claim: pointer-only <reason...> -->
    <!-- claim: absent <path> <reason...> -->
    <!-- claim: elsewhere <path> <repo> <reason...> -->
    <!-- claim: pinned <path> <repo> <rev> <reason...> -->
    <!-- claim: base <dir> <reason...> -->
    <!-- claim: anchor <path>:<line> <text that must occur on that line> -->

`figure` and `pointer-only` are POSITIONAL -- they speak for the prose above
them. `absent`, `elsewhere`, `pinned` and `base` are document-scoped and may be gathered
into one ledger block; a status page that several lanes append to at once is
better served by one reviewable table than by fifteen hunks scattered through
it, and the checker reads them the same either way.

A DECLARATION IN A DOC THAT IS NOT UNDER D1 IS A REFUSAL
--------------------------------------------------------
`absent`, `elsewhere`, `pinned` and `base` only mean anything under D1. Writing one in a
`figure`-only doc reads as an exemption and grants nothing, so the checker
refuses it rather than ignoring it -- same reason an unknown marker kind is a
refusal and not a skip.

WHAT AN UNVERIFIABLE CROSS-REPO CITATION DOES, EXACTLY
-----------------------------------------------------
`elsewhere` is checked in the sibling when the sibling is on disk, and a
sibling missing from the box is not an error -- not every machine has every
sibling, and making it one would refuse pushes for the shape of somebody's
checkout. But it must never be SILENT, because "checked and fine" and "not
checked at all" printing the same line is precisely the vacuous-green class.
So the verdict line always carries the split, and an unverified citation is
named on stderr with the sibling that was missing:

    DOC_CLAIMS=ok ... cross-repo=16 (16 verified, 0 unverified)
                      pinned=3 (3 verified, 0 unverified)

Zero unverified is a fact about the box that ran it, re-derived every time,
not a property of the tree. `pinned` follows the same rule.

`<expr>` is deliberately tiny -- dotted/indexed lookup (`a.b`, `a[0].c`) and
one composite, `a/b`, rendering as "63/63". Anything larger becomes a language
nobody can review.

An ILLUSTRATIVE marker in a governed doc is a REAL marker, and there is no
escape hatch. Writing the D2 row of `docs/GATE_REGISTRY.md` with a literal
example turned this gate red on its own documentation, correctly: a comment
shaped like a binding either binds or it is a decoration that looks like a
guarantee, and this repo has enough of those. Document the syntax in backticks
without the comment delimiters, the way that row now does. An `example` kind
was considered and rejected -- it is a switch that turns a marker off, which is
the vacuous-green class wearing a different hat.

Usage:
    python3 scripts/check_doc_claims.py             # check, fail-closed
    python3 scripts/check_doc_claims.py --selftest  # mutation arms on a fixture
    python3 scripts/check_doc_claims.py --list      # what is governed, and how
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------- governed set
#
# Per-doc rule opt-in. A doc is in this table or it is not governed; there is no
# glob, because "every .md in docs/" would sweep in dated records and archived
# handoffs whose whole value is that they are NOT updated.
#
# rules: subset of {"ref", "bind"}. "figure" is unconditional -- a marker is
# honoured wherever it appears, because a marker is an explicit request to be
# checked and ignoring one would be the vacuous-green class in doc form.
GOVERNED = (
    # Added 2026-09-15: every remaining document CLAUDE.md's "Key references"
    # table names. That table tells a reader these are the authoritative
    # references, and nine of its twenty-two entries were checked by nothing --
    # which is how the never-existed AUDIT_LEAN4_REPLACEMENT_2026-07-23.md
    # survived in two of them after docs/GATE_REGISTRY.md recorded that citation
    # fixed. Priced before switching on: 4 D1 refusals across all nine.
    ("docs/JSON_RPC_API.md", ("ref",)),
    ("docs/MATHLIB_STUBS.md", ("ref",)),
    ("docs/COQ_IMPORT_PIPELINE.md", ("ref",)),
    ("docs/AUDIT_GOAL_2026-06-09.md", ("ref",)),
    ("docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md", ("ref",)),
    ("docs/plans/ROADMAP_THEORY_MINING.md", ("ref",)),
    ("designs/2026-06-09-trust-synergy-compilation.md", ("ref",)),
    ("docs/archive/HANDOFF_STATUS.md", ("ref",)),
    ("ACKNOWLEDGMENTS.md", ("ref",)),
    ("CLAUDE.md", ("ref", "bind")),
    ("AGENTS.md", ("ref", "bind")),
    ("README.md", ("ref", "bind")),
    ("VISION.md", ("ref", "bind")),
    # docs/GATE_REGISTRY.md and docs/SUITE_STATE.md were `figure` only until
    # 2026-09-14 -- the two docs most ABOUT gates and suite state were the only
    # governed docs whose citations nothing re-resolved, which is the wrong way
    # round for the same reason recorded below for the certificate. The debt was
    # sized at "~16 annotations, measured 2026-08-26" and belonged to whoever did
    # it; done, and the estimate was close: 18 unresolved citations, closed by
    # THIRTEEN declarations and ZERO prose changes, because every one of them was
    # already correct about what it pointed at. Nine `absent` (paths this page
    # cites precisely BECAUSE they were retired or never existed -- the citation
    # IS the evidence for the claim around it), three `elsewhere` in the sibling
    # trust checkout, two `base crates/clean-verify` for the crate-relative
    # spelling both pages quote. Each doc carries its ledger in a trailing
    # "Citation ledger (D1)" section.
    ("docs/GATE_REGISTRY.md", ("ref", "bind")),
    ("docs/SUITE_STATE.md", ("ref", "bind")),
    # Added 2026-09-14 with the doc itself. `figure` only: the backlog is a
    # DATED snapshot and deliberately cites design docs and trust-side files
    # that "ref" would have to be taught about. It is listed here rather than
    # left ungoverned because an unlisted doc is not READ AT ALL, so the
    # `claim: figure` marker in it would have looked checked while checking
    # nothing -- the vacuous-green class this whole script exists to refuse.
    ("docs/CRYSTAL_BACKLOG.md", ()),
    # Added 2026-08-27. This is the LIVE status page for the self-verification
    # programme and the repo's own rule is that it outranks the design docs and
    # CLAUDE.md -- design docs state intent, the status page and the committed
    # probes state fact. A doc that outranks the others is the last one that
    # should be exempt from having its citations re-derived. Switching "ref" on
    # cost one `base` (44 crate-relative citations), 14 `elsewhere` and 6
    # `absent`; the docstring records what the split measured and why the
    # previously-recorded "76 cross-repo" estimate was wrong.
    ("docs/CRYSTAL_STATUS.md", ("ref", "bind")),
    # Added 2026-08-27. The repo's central "what is proved" document was NOT
    # governed here, which is the wrong way round: it is the doc most likely to
    # be quoted as evidence and the one where a rotted citation does the most
    # damage. Switching "ref" on cost exactly three fixes -- one real path error
    # (`tests/kernel_core_red_env_fidelity.rs`, actually under
    # `crates/clean-verify/`) and two `elsewhere` annotations for the Trust
    # sibling -- so the debt this row was avoiding did not exist.
    ("docs/SELF_VERIFICATION_CERTIFICATE.md", ("ref", "bind")),
    # Added 2026-09-14. Three more claim-bearing docs from CLAUDE.md's own key-
    # references table, measured before switching on: SOUNDNESS_CERTIFICATE cost
    # ONE declaration, VERIFICATION_AUDIT two, JUSTIFIED_EXCEPTIONS zero, and
    # none needed a prose change -- every unresolved citation already said in
    # its own sentence that the path was deleted, never written, or a gitignored
    # runtime directory. The soundness certificate being outside D1 while the
    # SELF-VERIFICATION certificate was inside is the same wrong-way-round this
    # table already records for GATE_REGISTRY and SUITE_STATE: the document that
    # states C1-C5 and the TCB is the one a rotted citation costs most.
    ("docs/SOUNDNESS_CERTIFICATE.md", ("ref", "bind")),
    ("docs/VERIFICATION_AUDIT.md", ("ref", "bind")),
    ("docs/JUSTIFIED_EXCEPTIONS.md", ("ref", "bind")),
    # Added 2026-09-14, same pass, same discipline: measured first, and the cost
    # was declarations only. DESIGN six, PUBLIC_DEMO seven, BENCHMARKS one,
    # RELEASE_READINESS one, PHILOSOPHY zero -- no prose changed on any of them,
    # because each unresolved citation already said in its own sentence what it
    # was. The two shapes are a build output under the gitignored target/ tree,
    # and a document that was cited and NEVER WRITTEN: four of those sit in
    # DESIGN.md, and `git log --all --diff-filter=A` returns nothing for any.
    ("docs/DESIGN.md", ("ref", "bind")),
    ("docs/PUBLIC_DEMO.md", ("ref", "bind")),
    ("docs/BENCHMARKS.md", ("ref", "bind")),
    ("docs/RELEASE_READINESS.md", ("ref", "bind")),
    ("docs/PHILOSOPHY.md", ("ref", "bind")),
    # Added 2026-09-26 with the docs themselves: the frontend class ledger and
    # the self-verification navigation notes were cut VERBATIM out of CLAUDE.md
    # (see D6), carrying CLAUDE.md's own claim markers, rooted citations and
    # links with them. Left out of this table, every one of those would have
    # stopped being read at all -- the move would have turned checked prose
    # into unchecked prose with no failure to say so. Measured before
    # switching on: zero refusals, because the text was already governed
    # under the same rules one directory up.
    ("docs/FRONTEND_CLASS_LEDGER.md", ("ref", "bind")),
    ("docs/SELF_VERIFICATION_NAVIGATION.md", ("ref", "bind")),
)

# D6 BUDGET (see the docstring). The limit Claude Code enforces is 150,000
# characters across every instruction file it loads; this repository owns only
# CLAUDE.md and .claude/rules/, and leaves the rest of the total to the
# operator's own files.
INSTRUCTION_FILES_BUDGET = 100_000
INSTRUCTION_RULES_DIR = ".claude/rules"


def _utf16_units(text: str) -> int:
    """Characters as Claude Code counts them: UTF-16 code units, so a
    character outside the Basic Multilingual Plane counts twice."""
    return len(text.encode("utf-16-le")) // 2


def _instruction_units(root: Path) -> tuple[int, list[str]]:
    """(total UTF-16 units, the files counted) for CLAUDE.md plus every
    `.claude/rules/*.md` under `root`."""
    files = [root / "CLAUDE.md"] + sorted((root / INSTRUCTION_RULES_DIR).glob("*.md"))
    total, names = 0, []
    for f in files:
        if f.is_file():
            total += _utf16_units(f.read_text(encoding="utf-8"))
            names.append(f.relative_to(root).as_posix())
    return total, names

# Gitignored top-level directories that ARE this repo's layout. A row is a name
# that satisfies all four of: (1) the root .gitignore marks it as a directory
# (a trailing-`/` line, no `!`, no glob, no inner `/`); (2) the index tracks
# NOTHING under it; (3) this repo's OWN tooling writes it at the root -- the
# row's comment names the writer; (4) a governed doc cites a path under it.
# (1) and (2) are re-derived on every run and refused as D0 IGNORED when they
# stop holding; (3) and (4) are facts about tooling and prose, which is why
# this is a table and not "every directory .gitignore names" (the docstring
# section on rooted citations carries that measurement: 16 template names, 6
# false refusals). WHAT A ROW COSTS: a citation under a row is rooted on every
# box and is NEVER resolved on disk, so every governed-doc citation under it
# must be declared `absent` -- naming the writer -- in the same commit as the
# row, or the leg is red on every box at once. The census that prices a row is
# derived from the checker's own PATH_TOKEN/MARKER over the `ref` docs, and
# each row below quotes it with its date.
IGNORED_ROOTS = (
    # cargo's build tree; also `target/verify-runner*` (the suite runner's
    # cache and the pinned runner's detached worktree) and `target/public-demo`.
    # Census 2026-09-15: 22 citations across CLAUDE.md, SUITE_STATE, DESIGN,
    # PUBLIC_DEMO and BENCHMARKS, 22 declared.
    "target",
    # runtime measurements: `metrics/lean4_parity.json`, written by
    # `write_parity_summary` in crates/clean-kernel/tests/lean4_parity.rs
    # (`cargo test --locked -p clean-kernel --test lean4_parity --features
    # test-utils -- lean4_parity_check`), and `metrics/benchmarks/`, written by
    # scripts/bench_regression.sh. `.gitignore:41` is `metrics/`; `git ls-files
    # metrics | wc -l` -> 0 (2026-09-15). Census the same day, per occurrence
    # with this checker's own PATH_TOKEN / MARKER over the `ref` docs: 5 cited /
    # 5 declared (VISION.md 2, docs/VERIFICATION_AUDIT.md 3); it read 3 cited /
    # 1 declared before the two ledger declarations that pay this row's price.
    "metrics",
)

# git's repository-location variables. A pre-push hook run from a LINKED
# worktree inherits an absolute GIT_DIR, and with GIT_DIR set and GIT_WORK_TREE
# unset git treats the cwd as the work tree: `-C <root> rev-parse
# --show-toplevel` then answers <root> while `ls-files` answers from the OTHER
# repository's index. Measured 2026-09-15 (Apple Git-155). Every git call here
# scrubs them, so what a root tracks is a fact about the root.
GIT_LOCATION_VARS = (
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_COMMON_DIR",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_NAMESPACE",
    "GIT_CEILING_DIRECTORIES",
)

# Refs consulted in a sibling, in order, when a cited path is not in its
# working tree. See _sibling_tracked: the working tree of a sibling is a
# statement about somebody's checkout, not about the repo.
SIBLING_REFS = ("origin/HEAD", "origin/main", "origin/master", "main", "HEAD")

# Sibling repos a doc may point into with `elsewhere`. Absent from disk is not
# an error -- not every machine has every sibling -- but PRESENT and missing the
# path is, so a cross-repo citation cannot rot unnoticed on a box that could
# have checked it.
SIBLINGS = {
    "trust": ROOT.parent / "trust",
    "ay": ROOT.parent / "ay",
    "zani": ROOT.parent / "zani",
    "gamma-crown": ROOT.parent / "gamma-crown",
}
# Linked worktrees need not sit beside these repositories. An explicit setting
# names an exact Git worktree root; unlike an absent default, a bad setting is
# a configuration error, never an UNVERIFIED citation or a fallback.
SIBLING_ENV = {
    "trust": "CLEAN_GATE_TRUST_REPO",
    "ay": "CLEAN_GATE_AY_REPO",
    "zani": "CLEAN_GATE_ZANI_REPO",
    "gamma-crown": "CLEAN_GATE_GAMMA_CROWN_REPO",
}

MARKER = re.compile(r"<!--\s*claim:\s*(.*?)\s*-->")
# A `pinned` rev: an abbreviated or full commit id, nothing symbolic -- a
# branch name would move under the citation it pins.
PIN_REV = re.compile(r"[0-9a-f]{7,40}")
# A path token: backticked, contains a `/`, and no spaces. The leading-segment
# test against the TRACKED tree (plus the IGNORED_ROOTS rows) is what keeps
# `Mathlib/Logic/Basic.lean` and `elab_match/nested_ctor.rs` out -- neither
# names a directory of this repo.
PATH_TOKEN = re.compile(r"`([A-Za-z0-9_][A-Za-z0-9_.+-]*(?:/[A-Za-z0-9_.+-]+)+)`")
# A .gitignore line that cannot name ONE directory: any glob metacharacter.
GITIGNORE_GLOB = re.compile(r"[*?\[]")
ARTIFACT_TOKEN = re.compile(r"`((?:reports|data)/[A-Za-z0-9_./-]+\.json)`")
FIGURE = re.compile(r"\b\d+/\d+\b")
# D5 LINK. A markdown link target that is a repo path — `[text](../FOO.md)` or
# `[text](plans/BAR.md)`. D1's PATH_TOKEN only sees BACKTICKED rooted paths, so
# every relative link in every governed document was invisible to it. Measured
# 2026-09-15 across the governed set plus the nine ungoverned key-reference
# docs: 211 such links, of which THREE are dead — and two of those are further
# copies of `AUDIT_LEAN4_REPLACEMENT_2026-07-23.md`, the never-existed file
# docs/GATE_REGISTRY.md records as "cited five times across four docs" and
# fixed. That count was of ROOTED citations only. One of the three sits in
# docs/JUSTIFIED_EXCEPTIONS.md, which is already governed — so this blind spot
# bites INSIDE the governed set, not merely outside it.
def _blank_code_spans(text: str) -> str:
    """Markdown with fenced blocks and inline code spans blanked, offsets kept.

    D5's first draft skipped this and immediately accused
    docs/JUSTIFIED_EXCEPTIONS.md:108 of a dead link to `clean_compiler` — which
    is a RUSTDOC INTRA-DOC LINK QUOTED AS AN EXAMPLE inside a code span
    (``[FfiBridge](clean_compiler)``), not a link at all. That is this repo's
    own parse-not-grep rule (CLAUDE.md, *Proof soundness rules*) catching a
    scanner written to enforce a rule: a matcher over raw text counts MENTIONS,
    not code. Blank first, then scan.
    """
    out = list(text)
    for m in re.finditer(r"```[\s\S]*?```|``[^`]*``|`[^`\n]*`", text):
        for i in range(m.start(), m.end()):
            if out[i] != "\n":
                out[i] = " "
    return "".join(out)


LINK_TARGET = re.compile(r"\]\((?!https?:|mailto:|#)([^)\s]+?)(?:#[^)]*)?\)")

# Lines above a `figure` marker that count as its bound span. Three is enough
# for a wrapped sentence and short enough to exclude the next one.
SPAN_LINES = 3


class Problem(str):
    """A single fail-closed refusal, rendered verbatim to stderr."""


@lru_cache(maxsize=1)
def _git_local_environment_names():
    """Ask Git for its repository-local variables; never guess a partial list."""
    result = subprocess.run(
        ["git", "rev-parse", "--local-env-vars"], capture_output=True,
        text=True, timeout=10,
    )
    names = result.stdout.splitlines()
    if result.returncode != 0 or not names or any(
        re.fullmatch(r"GIT_[A-Z0-9_]+", name) is None for name in names
    ):
        raise ValueError("cannot enumerate Git repository-local environment")
    return frozenset(names) | frozenset(GIT_LOCATION_VARS)


def _git(where: Path, args, timeout: int, text: bool = False):
    """`git -C <where> <args>`, repository identity scrubbed; None if unavailable."""
    try:
        names = _git_local_environment_names()
        env = {k: v for k, v in os.environ.items() if k not in names}
        return subprocess.run(
            ["git", "-C", str(where)] + list(args),
            capture_output=True,
            text=text,
            timeout=timeout,
            env=env,
        )
    except (OSError, subprocess.SubprocessError, ValueError):
        return None


def _tracked_top_dirs(root: Path):
    """{top-level directory: tracked paths under it} as the INDEX has it, or None.

    `git ls-files -z`, first segment of every path that has one; dot-prefixed
    segments (`.cargo`, `.github`) are excluded exactly as the on-disk rule
    excluded them. Measured on this repo 2026-09-15: `git ls-files | wc -l`
    26,050, `time git ls-files -z` 0.012 s. None -- not a repository, or no
    git -- and an EMPTY dict -- a repository that tracks nothing under any
    directory -- are both the caller's refusal to make, because an empty set
    here would make D1 check nothing and print green.
    """
    top = _git(root, ["rev-parse", "--show-toplevel"], 60, text=True)
    if top is None or top.returncode != 0:
        return None
    if Path(top.stdout.strip()).resolve() != root.resolve():
        # A subdirectory of some OTHER repository, whose `ls-files` would
        # answer for a tree this is not the root of.
        return None
    out = _git(root, ["ls-files", "-z"], 60)
    if out is None or out.returncode != 0:
        return None
    tops = {}
    for entry in out.stdout.split(b"\0"):
        head, sep, _rest = entry.partition(b"/")
        if sep and head and not head.startswith(b"."):
            name = head.decode("utf-8", "surrogateescape")
            tops[name] = tops.get(name, 0) + 1
    return tops


def _gitignored_top_dirs(root: Path):
    """Top-level names the root `.gitignore` marks as DIRECTORIES.

    A line with a trailing `/` (gitignore's own "directory only" spelling), no
    `!`, no glob, and no inner `/` once a leading `/` is stripped: `target/`
    and `/vendor/` qualify, `target_*/` and `benchmarks/**/results/` do not.
    Only the root file is read -- a nested `.gitignore` cannot name a top-level
    directory, and `.git/info/exclude` is per-clone state, which is precisely
    what this set must not depend on.
    """
    gi = root / ".gitignore"
    if not gi.is_file():
        return set()
    names = set()
    for raw in gi.read_text(errors="replace").splitlines():
        line = raw.rstrip()
        if not line or line.startswith("#") or line.startswith("!") or not line.endswith("/"):
            continue
        name = line[:-1]
        if name.startswith("/"):
            name = name[1:]
        if not name or "/" in name or name.startswith(".") or GITIGNORE_GLOB.search(name):
            continue
        names.add(name)
    return names


def _top_dirs(root: Path, ignored_roots=IGNORED_ROOTS):
    """(rooted first segments, the IGNORED_ROOTS rows in force, problems).

    Tracked top-level directories UNION the `IGNORED_ROOTS` rows that the root
    `.gitignore` still marks as directories and the index tracks nothing
    under. Never what `iterdir` finds: that made the verdict a fact about the
    box (see the docstring section on which first segments make a citation
    rooted). Every refusal is D0 and none is a skip: a root that cannot be
    asked yields an EMPTY set beside its problem, so D1 checks nothing and the
    run is red rather than green.
    """
    tracked = _tracked_top_dirs(root)
    if tracked is None:
        return set(), frozenset(), [
            Problem(
                "D0 TREE: %s cannot be asked which top-level directories it "
                "TRACKS (`git ls-files` failed, or there is no git), so D1 "
                "cannot tell a rooted citation from another repo's layout. "
                "Run this from a git checkout of the repo." % root
            )
        ]
    if not tracked:
        # Askable, and the answer is "nothing under any directory". A snapshot
        # plus `git init` with no `git add` looks exactly like this, and until
        # 2026-09-15 it collapsed the set to the IGNORED_ROOTS rows: D1 then
        # checked nothing but citations under target/, and the run was red
        # only because two `base` markers happened to rescue nothing.
        return set(), frozenset(), [
            Problem(
                "D0 TREE: %s tracks NO path under any top-level directory "
                "(`git ls-files` answered and listed nothing containing `/`), "
                "so D1 would have only the IGNORED_ROOTS rows to root a "
                "citation in and would check nothing else. A `git archive` "
                "snapshot with a fresh `git init` looks like this: run from a "
                "real checkout, or `git add -A` the tree first." % root
            )
        ]
    named = _gitignored_top_dirs(root)
    problems, ignored = [], set()
    for r in ignored_roots:
        if r not in named:
            problems.append(
                Problem(
                    "D0 IGNORED: IGNORED_ROOTS names `%s`, which the root "
                    ".gitignore does not mark as a directory (a `%s/` line, no "
                    "`!`, no glob). The table has outlived the ignore rule it "
                    "stands on: drop the row, or restore the line." % (r, r)
                )
            )
        elif tracked.get(r):
            problems.append(
                Problem(
                    "D0 IGNORED: IGNORED_ROOTS names `%s`, and the index tracks "
                    "%d path(s) under it. The row's premise -- nothing there is "
                    "tracked, so a citation there is checked by declaration "
                    "alone -- is false: drop the row, or untrack the paths."
                    % (r, tracked[r])
                )
            )
        else:
            ignored.add(r)
    return set(tracked) | ignored, frozenset(ignored), problems


def _paragraphs(text: str):
    """(start_line, end_line, body) for each blank-line-delimited paragraph.

    Line numbers are 1-based and inclusive, so a diagnostic points at something
    a human can open.
    """
    out = []
    start = None
    buf = []
    for i, line in enumerate(text.splitlines(), 1):
        if line.strip():
            if start is None:
                start = i
            buf.append(line)
        elif start is not None:
            out.append((start, i - 1, "\n".join(buf)))
            start, buf = None, []
    if start is not None:
        out.append((start, start + len(buf) - 1, "\n".join(buf)))
    return out


# A markdown list item's first line: `* `, `- `, `+ `, `1. `, `1) `.
BULLET_ITEM = re.compile(r"^\s*[*+-]\s")
ORDERED_ITEM = re.compile(r"^\s*(\d{1,9})([.)])\s")


def _item_start(line: str, list_kind: str | None, at_start: bool) -> str | None:
    """The kind of list item `line` starts -- `bullet`, or `ordered.` /
    `ordered)` -- or None when it continues the block it is in.

    CommonMark's rule, not "any `N.` at the start of a line": a bullet item
    may interrupt a paragraph; an ORDERED item may interrupt one only when its
    number is 1, or when it continues an ordered list of the same delimiter
    already open in this block; at the start of a block any number starts one.
    Until verifier r7b (2026-09-24) every `\\d+[.)] ` line split the block, so
    a sentence wrapped before a year -- "was cut in\n2026. Its history is at
    (commit ...)" -- lost its second line to a "list item", and the commit
    there was never checked against the citation it belongs to.
    """
    if BULLET_ITEM.match(line):
        return "bullet"
    m = ORDERED_ITEM.match(line)
    if m is None:
        return None
    kind = "ordered" + m.group(2)
    if at_start or int(m.group(1)) == 1 or list_kind == kind:
        return kind
    return None


def _blocks(text: str):
    """(start_line, end_line, body) for each prose BLOCK: a blank-line
    paragraph, split again where a markdown list item starts (`_item_start`)
    -- each item is a block of its own, as markdown renders it."""
    out = []
    for start, _end, body in _paragraphs(text):
        cur, buf, kind = start, [], None
        for i, line in enumerate(body.split("\n")):
            item = _item_start(line, kind, at_start=not buf)
            if item is not None:
                if buf:
                    out.append((cur, start + i - 1, "\n".join(buf)))
                    cur, buf = start + i, []
                kind = item
            buf.append(line)
        out.append((cur, cur + len(buf) - 1, "\n".join(buf)))
    return out


# A path segment: a bracket-quoted key (which may contain `/` and `.`), a
# bracketed list index, or a bare dotted key.
SEGMENT_RE = re.compile(r"""\[\s*'([^']*)'\s*\]|\[\s*"([^"]*)"\s*\]|\[(\d+)\]|([^.\[\]]+)""")


def _segments(expr: str):
    """[(kind, value)] for an expression path, or raise on trailing garbage.

    Bracket-quoted segments exist because this repo's artifacts are routinely
    keyed by REPO PATH -- `data/source_elab_ratchet.json` is
    `files["Mathlib/Logic/Unique.lean"].success_baseline` -- and a dotted-only
    language cannot address any of them. Before 2026-09-15 that silently
    pushed every such figure to `pointer-only`, i.e. to unbound, which is the
    opposite of what D3 is for: the gap in the EXPRESSION language was making
    the honest answer unavailable.
    """
    out, pos = [], 0
    while pos < len(expr):
        m = SEGMENT_RE.match(expr, pos)
        if not m:
            if expr[pos] == ".":
                pos += 1
                continue
            raise ValueError(expr)
        if m.group(1) is not None:
            out.append(("key", m.group(1)))
        elif m.group(2) is not None:
            out.append(("key", m.group(2)))
        elif m.group(3) is not None:
            out.append(("idx", int(m.group(3))))
        else:
            out.append(("key", m.group(4)))
        pos = m.end()
    if not out:
        raise ValueError(expr)
    return out


def _resolve(obj, expr: str):
    """Dotted/indexed/bracket-quoted lookup. KeyError with a readable path."""
    cur = obj
    for kind, part in _segments(expr):
        if kind == "idx":
            if not isinstance(cur, list) or part >= len(cur):
                raise KeyError(expr)
            cur = cur[part]
        else:
            if not isinstance(cur, dict) or part not in cur:
                raise KeyError(expr)
            cur = cur[part]
    return cur


def _split_outside_quotes(expr: str, sep: str) -> list[str]:
    """Split on `sep` only where it is NOT inside a bracket-quoted segment.

    `files["a/b"].x/files["a/b"].y` is TWO halves, not four: a bare
    `expr.split("/")` cut the quoted repo paths apart and reported the
    expression as malformed, which is how a bindable figure looked unbindable.
    """
    out, buf, quote = [], [], None
    for ch in expr:
        if quote is None and ch in ("'", '"'):
            quote = ch
        elif quote is not None and ch == quote:
            quote = None
        if quote is None and ch == sep:
            out.append("".join(buf))
            buf = []
            continue
        buf.append(ch)
    if quote is not None:
        raise ValueError(expr)
    out.append("".join(buf))
    return out


def _render(obj, expr: str) -> str:
    parts = _split_outside_quotes(expr, "/")
    if len(parts) > 1:
        if len(parts) != 2:
            raise ValueError(expr)
        return "/".join(_render(obj, p) for p in parts)
    val = _resolve(obj, expr)
    if isinstance(val, bool) or not isinstance(val, (int, float, str)):
        raise ValueError(expr)
    return str(val)


def _parse_markers(text: str):
    """[(line, paragraph_index, kind, args)] for every marker in the document."""
    paras = _paragraphs(text)
    found = []
    for m in MARKER.finditer(text):
        line = text[: m.start()].count("\n") + 1
        body = m.group(1).split()
        pidx = next(
            (i for i, (s, e, _) in enumerate(paras) if s <= line <= e),
            None,
        )
        found.append((line, pidx, body[0] if body else "", body[1:]))
    return paras, found


def _bound_span(text: str, paras, pidx, line: str) -> str:
    """The prose a `figure` marker speaks for: its line and SPAN_LINES above.

    Clipped to the marker's paragraph, so a window can never reach across a
    blank line into a sentence about something else.
    """
    if pidx is None:
        return ""
    start = max(paras[pidx][0], line - SPAN_LINES)
    lines = text.splitlines()
    return "\n".join(lines[start - 1 : line])


def _resolve_cited(root: Path, bases, cited: str, ignored=frozenset()):
    """(resolved?, which base rescued it or None for the repo root).

    The root is always tried FIRST, so a declared base can only ever rescue a
    citation the root could not -- it cannot redirect one that already
    resolves, and it cannot make a path that exists nowhere resolve. A
    citation under an `ignored` root is never resolved at all: what sits
    under a gitignored root is untracked state, and the answer must be the
    same on every box.
    """
    if cited.split("/")[0] in ignored:
        return False, None
    if (root / cited).exists():
        return True, None
    for b in bases:
        if (root / b / cited).exists():
            return True, b
    return False, None


def _sibling_is_own_repo(sib: Path):
    """True iff `sib` is the TOP of its own git repository.

    `git -C <dir>` DISCOVERS a repository by walking up from <dir>, so a plain
    directory that happens to sit at the sibling path inside ANOTHER checkout
    is answered by that enclosing repository. Measured 2026-09-25: from a Clean
    worktree under `target.noindex/`, `../trust` was a stray non-repository
    directory, git answered from the enclosing Clean repository, and 36 correct
    Trust citations read as "NOT there either". An answer from the wrong
    repository is not an answer, so such a sibling cannot be ASKED and its
    citations are UNVERIFIED (arm 27d).
    """
    top = _git(sib, ["rev-parse", "--show-toplevel"], 20)
    if top is None or top.returncode != 0 or not top.stdout:
        return False
    try:
        # Git adds one LF. All other bytes belong to the filename, including
        # trailing whitespace and non-UTF-8 names; text mode would alter CRs.
        root = os.fsdecode(top.stdout.removesuffix(b"\n"))
        return bool(root) and Path(root).resolve() == sib.resolve()
    except OSError:
        return False


def selected_siblings(environ=None, defaults=None):
    """Select siblings, refusing invalid explicit roots even in diagnostic modes.

    Relative settings resolve from the invocation's working directory, as the
    provenance checker's explicit repository paths do. Git location variables
    are scrubbed by _sibling_is_own_repo's _git call.
    """
    environ = os.environ if environ is None else environ
    siblings = dict(SIBLINGS if defaults is None else defaults)
    for repo, name in SIBLING_ENV.items():
        if name not in environ:
            continue
        value = environ[name]
        if not value:
            raise ValueError("%s requires a nonempty Git worktree root" % name)
        try:
            path = Path(value).resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise ValueError("%s: cannot resolve %r: %s" % (name, value, exc)) from exc
        if not path.is_dir():
            raise ValueError("%s: not a directory: %s" % (name, path))
        if not _sibling_is_own_repo(path):
            raise ValueError("%s: not an exact Git worktree root: %s" % (name, path))
        siblings[repo] = path
    return siblings


def _sibling_tracked(sib: Path, wanted):
    """(subset of `wanted` tracked in the sibling's history, the ref consulted).

    Returns (None, None) when the sibling cannot be ASKED -- no git, not a
    repository, no usable ref -- which is UNVERIFIED, never a refusal.

    WHY THIS IS NOT `(sib / cited).exists()`, WHICH IS WHAT IT USED TO BE
    --------------------------------------------------------------------
    A sibling CHECKOUT is not the sibling REPO, and this gate learned that by
    getting it wrong. Measured 2026-08-27: `../trust` on this box is a shallow,
    `blob:none` partial clone whose working tree sits at `ef5a5910ea`
    (2026-08-14) while its own `origin/main` is at `605e61cb22` (2026-08-27) --
    thirteen days and one `git fetch` apart. Resolving cross-repo citations
    against that working tree reported SIX live, correct `docs/CRYSTAL_STATUS.md`
    citations as existing in neither repo, and `git log --all --diff-filter=A`
    "confirmed" it by finding no commit that added them -- because a shallow
    clone HAS no such commit. One batched `git ls-tree origin/main` found all
    six, in 9 ms.

    That is the false-refusal direction, and it is the dangerous one for a
    gate whose exemptions are written into prose: the fix a red build invites
    is an `absent` marker, so six correct citations would have been
    permanently exempted and six false sentences written into the repo's live
    status page. The same defect had already produced a wrong finding about
    `reports/metadata-v12-sysroot.md` twice in this repo.

    One `ls-tree` per sibling, non-recursive, all pathspecs batched, no network.
    """
    for ref in SIBLING_REFS:
        probe = _git(sib, ["rev-parse", "--verify", "-q", ref], 20)
        if probe is None:
            return None, None
        if probe.returncode != 0:
            continue
        out = _git(sib, ["ls-tree", "--name-only", ref, "--"] + sorted(wanted), 60, text=True)
        if out is None or out.returncode != 0:
            return None, None
        return {ln.rstrip("/") for ln in out.stdout.split("\n") if ln.strip()}, ref
    return None, None


def _classify_xrepo(elsewhere, siblings):
    """cited -> (verdict, detail) for every `elsewhere` declaration in a doc.

    verdict is one of "verified" | "missing" | "unverified" | "unknown-repo".
    Grouped by repo so each sibling costs at most one `git ls-tree`.
    """
    state = {}
    by_repo = {}
    for cited, (_where, repo) in elsewhere.items():
        by_repo.setdefault(repo, []).append(cited)

    for repo, cits in sorted(by_repo.items()):
        sib = siblings.get(repo)
        if sib is None:
            for c in cits:
                state[c] = ("unknown-repo", repo)
            continue
        if not sib.exists():
            for c in cits:
                state[c] = ("unverified", "sibling %r is not on this box (%s)" % (repo, sib))
            continue
        if not _sibling_is_own_repo(sib):
            for c in cits:
                state[c] = (
                    "unverified",
                    "sibling %r at %s is not the top of its own repository, so git "
                    "would answer from an enclosing one" % (repo, sib),
                )
            continue
        present = {c for c in cits if (sib / c).exists()}
        rest = [c for c in cits if c not in present]
        ref = "working tree"
        if rest:
            tracked, tref = _sibling_tracked(sib, rest)
            if tracked is None:
                for c in rest:
                    state[c] = (
                        "unverified",
                        "%r is on this box but its history could not be queried "
                        "(no git, or no usable ref); its working tree alone is "
                        "not an answer" % repo,
                    )
                rest = []
            else:
                present |= tracked
                ref = tref
        for c in cits:
            if c in present:
                state[c] = ("verified", ref)
            elif c not in state:
                state[c] = ("missing", ref)
    return state


def _classify_pinned(pinned, siblings):
    """cited -> (verdict, detail) for every `pinned` declaration in a doc.

    verdict is one of "verified" | "missing" | "unverified" | "unknown-repo".
    The path must be in the sibling's tree AT the pinned commit -- not in its
    working tree, not anywhere in its history.
    """
    state = {}
    for cited, (_where, repo, rev) in sorted(pinned.items()):
        sib = siblings.get(repo)
        if sib is None:
            state[cited] = ("unknown-repo", repo)
            continue
        if not sib.exists():
            state[cited] = ("unverified", "sibling %r is not on this box (%s)" % (repo, sib))
            continue
        if not _sibling_is_own_repo(sib):
            state[cited] = (
                "unverified",
                "sibling %r at %s is not the top of its own repository" % (repo, sib),
            )
            continue
        probe = _git(sib, ["rev-parse", "--verify", "-q", rev + "^{commit}"], 20, text=True)
        if probe is None:
            state[cited] = ("unverified", "%r is on this box but git cannot be asked" % repo)
            continue
        if probe.returncode != 0:
            shallow = _git(sib, ["rev-parse", "--is-shallow-repository"], 20, text=True)
            if shallow is not None and shallow.stdout.strip() == "true":
                state[cited] = (
                    "unverified",
                    "%r is a shallow clone and does not carry %s" % (repo, rev),
                )
            else:
                state[cited] = ("missing", "%s is not a commit in %r" % (rev, repo))
            continue
        full = probe.stdout.strip()
        out = _git(sib, ["ls-tree", "--name-only", full, "--", cited], 60, text=True)
        if out is None or out.returncode != 0:
            state[cited] = ("unverified", "%r could not list its tree at %s" % (repo, rev))
        elif cited in {ln.rstrip("/") for ln in out.stdout.split("\n") if ln.strip()}:
            state[cited] = ("verified", full)
        else:
            state[cited] = ("missing", "%s is not in %r's tree at %s" % (cited, repo, rev))
    return state


# `git show <rev>:<path>` in a declaration's reason: the recovery it promises.
RECOVER = re.compile(r"git show ([0-9a-f]{7,40}(?:\^|~[0-9]*)*):([A-Za-z0-9_./-]*[A-Za-z0-9_/-])")
# A commit-id TOKEN in prose: a hex run with no word character either side.
REV_TOKEN = re.compile(r"(?<![0-9A-Za-z])[0-9a-f]{7,40}(?![0-9A-Za-z])")


def _names_pin(para, rev, full=None):
    """Does `para` name the pinned commit? A token equal to `rev` does; so
    does a longer or shorter abbreviation of the SAME commit when the sibling
    resolved it (`full`). A substring does not: `dc31063cd3ff` contains
    `dc31063cd3` and names a different (here nonexistent) commit."""
    tokens = REV_TOKEN.findall(para)
    if rev in tokens:
        return True
    return full is not None and any(full.startswith(t) for t in tokens)


def _blank_markers(text: str) -> str:
    """The document with every claim marker blanked, offsets and newlines kept.

    A marker's REASON is data about a citation, not a citation: an `absent`
    whose own reason backticks its path used to count as the citation that
    keeps it alive, so the dead-declaration rule could not see it."""
    return MARKER.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)


# A commit id the prose ATTRIBUTES to a sibling by name: `trust dc31063cd3`,
# `trust `dc31063cd3``. Built per call from the sibling names in play.
def _attributed_revs(para: str, siblings):
    """[(start, end, sibling, rev)] for each commit id `para` attributes to a
    sibling repository by name."""
    if not siblings:
        return []
    names = "|".join(re.escape(n) for n in sorted(siblings, key=len, reverse=True))
    pat = re.compile(
        r"(?<![\w-])(%s)\s+`?([0-9a-f]{7,40})`?(?![0-9A-Za-z])" % names
    )
    return [(m.start(), m.end(), m.group(1), m.group(2)) for m in pat.finditer(para)]


def _sibling_rev(sib: Path, name: str, rev: str):
    """(verdict, what) for commit `rev` in sibling `name` at `sib`: "ok",
    "missing", or "unverified" when the sibling is not on this box, cannot be
    asked, or is a shallow clone that may simply not carry it."""
    if not sib.exists():
        return "unverified", "names %s `%s`, and %r is not on this box (%s)" % (name, rev, name, sib)
    if not _sibling_is_own_repo(sib):
        return "unverified", "names %s `%s`, and %r at %s is not the top of its own repository" % (
            name, rev, name, sib)
    probe = _git(sib, ["rev-parse", "--verify", "-q", rev + "^{commit}"], 20)
    if probe is None:
        return "unverified", "names %s `%s`, and %r cannot be asked" % (name, rev, name)
    if probe.returncode == 0:
        return "ok", ""
    sh = _git(sib, ["rev-parse", "--is-shallow-repository"], 20, text=True)
    if sh is not None and sh.stdout.strip() == "true":
        return "unverified", "names %s `%s`, which the shallow clone of %r may not carry" % (
            name, rev, name)
    return "missing", "names %s `%s`, which is not a commit in %r" % (name, rev, name)


def _para_revs(repo: Path, para: str, siblings):
    """[(verdict, what, repo)] for every commit id and `git show` the PROSE
    PARAGRAPH citing an `absent` path names that does not resolve where the
    paragraph says it lives (`repo`: the sibling's name, or "this
    repository").

    A commit id attributed to a sibling by name (`trust <rev>`) must be a
    commit of THAT sibling when it is on this box, and is UNVERIFIED when it is
    not; every other one must be a commit HERE. Until verifier r7 (2026-09-24)
    the scope was the physical LINE and an attributed id was stripped
    unchecked: `(read it at trust `fedcba98765`)` passed with the sibling
    present, and `(commit fedcba98765)` on the next line of the same sentence
    was never read."""
    out = []
    here = list(para)
    for start, end, name, rev in _attributed_revs(para, siblings):
        here[start:end] = " " * (end - start)
        verdict, what = _sibling_rev(siblings[name], name, rev)
        if verdict != "ok":
            out.append((verdict, what, name))
    out.extend((v, w, "this repository") for v, w in _reason_revs(repo, "".join(here)))
    return list(dict.fromkeys(out))


def _reason_revs(repo: Path, reason: str):
    """[(verdict, what)] for each commit id and `git show` a reason names that
    `repo` does not hold. verdict is "missing", or "unverified" when `repo`
    is a shallow clone that may simply not carry the commit."""
    out = []
    shallow = None
    for rev in dict.fromkeys(REV_TOKEN.findall(reason)):
        probe = _git(repo, ["rev-parse", "--verify", "-q", rev + "^{commit}"], 20)
        if probe is not None and probe.returncode == 0:
            continue
        if shallow is None:
            sh = _git(repo, ["rev-parse", "--is-shallow-repository"], 20, text=True)
            shallow = sh is not None and sh.stdout.strip() == "true"
        if probe is None or shallow:
            out.append(("unverified", "names %s, which a shallow or unaskable clone cannot resolve" % rev))
        else:
            out.append(("missing", "names %s, which is not a commit" % rev))
    for rev, shown in dict.fromkeys(RECOVER.findall(reason)):
        probe = _git(repo, ["cat-file", "-e", "%s:%s" % (rev, shown)], 20)
        if probe is None or probe.returncode != 0:
            out.append(("missing", "promises `git show %s:%s`, which cannot be shown" % (rev, shown)))
    return out


def check(root: Path, governed=GOVERNED, siblings=None):
    """Re-derive every governed claim. Returns a list of Problem strings."""
    siblings = SIBLINGS if siblings is None else siblings
    # Refused, not defaulted: with an empty set every citation reads as
    # "another repo's layout" and D1 checks nothing, so the problems that
    # come back with an empty set are what keeps that run from printing green.
    tops, ignored, problems = _top_dirs(root)
    stats = {
        "docs": 0,
        "paths": 0,
        "figures": 0,
        "anchors": 0,
        "links": 0,
        "bound": 0,
        "based": 0,
        "xrepo_verified": 0,
        "xrepo_unverified": 0,
        "pinned_verified": 0,
        "pinned_unverified": 0,
        "instruction_units": 0,
        # (doc, path, repo) for every cross-repo citation this box could not
        # check. Carried out of check() so the caller can NAME them: an
        # unverified claim that prints like a verified one is the whole defect.
        "unverified": [],
    }

    for rel, rules in governed:
        doc = root / rel
        if not doc.exists():
            problems.append(
                Problem(
                    "D0 GOVERNED: %s is in the governed set and is not in the "
                    "tree. Remove the row or restore the doc; a governed doc "
                    "that vanishes must not silently stop being checked." % rel
                )
            )
            continue
        stats["docs"] += 1
        text = doc.read_text()
        paras, markers = _parse_markers(text)
        # What the doc CITES is its prose, never its markers: a declaration
        # whose own reason backticks its path is not a citation of it, and
        # counting it as one kept a declaration nothing else reads alive.
        prose = _blank_markers(text)

        # -- marker shape. A malformed marker is a refusal, never a skip: a
        # -- marker that silently does nothing is the vacuous-green class.
        absent, elsewhere, figures, pointer_paras, bases = {}, {}, [], set(), []
        pinned = {}
        # (where, kind, path, sibling repo or None, reason) per declaration
        reasons = []
        # every path a D1/D5 rule actually reads in this doc, so a declaration
        # for a path nothing cites can be refused as dead
        cited_here = set()
        for line, pidx, kind, args in markers:
            where = "%s:%d" % (rel, line)
            if kind == "figure":
                if len(args) != 2:
                    problems.append(
                        Problem(
                            "D2 FIGURE: %s malformed -- expected `<!-- claim: "
                            "figure <artifact.json> <expr> -->`, got %r"
                            % (where, " ".join([kind] + args))
                        )
                    )
                    continue
                figures.append((where, pidx, line, args[0], args[1]))
            elif kind == "pointer-only":
                if not args:
                    problems.append(
                        Problem(
                            "D3 BIND: %s `pointer-only` needs a reason saying "
                            "why the figure beside it is not re-derivable "
                            "(dated measurement? different artifact?)." % where
                        )
                    )
                    continue
                pointer_paras.add(pidx)
            elif kind == "absent":
                if len(args) < 2:
                    problems.append(
                        Problem(
                            "D1 REF: %s `absent` needs `<path> <reason...>` -- "
                            "an unexplained exemption is a hole, not a record."
                            % where
                        )
                    )
                    continue
                absent[args[0]] = where
                reasons.append((where, "absent", args[0], None, " ".join(args[1:])))
            elif kind == "elsewhere":
                if len(args) < 3:
                    problems.append(
                        Problem(
                            "D1 REF: %s `elsewhere` needs `<path> <repo> "
                            "<reason...>`." % where
                        )
                    )
                    continue
                elsewhere[args[0]] = (where, args[1])
                reasons.append((where, "elsewhere", args[0], args[1], " ".join(args[2:])))
            elif kind == "pinned":
                if len(args) < 4 or not PIN_REV.fullmatch(args[2]):
                    problems.append(
                        Problem(
                            "D1 REF: %s `pinned` needs `<path> <repo> <rev> "
                            "<reason...>`, with <rev> a commit id (7-40 lowercase "
                            "hex) -- a branch name would move under the citation."
                            % where
                        )
                    )
                    continue
                pinned[args[0]] = (where, args[1], args[2])
                reasons.append((where, "pinned", args[0], args[1], " ".join(args[3:])))
            elif kind == "base":
                if len(args) < 2:
                    problems.append(
                        Problem(
                            "D1 REF: %s `base` needs `<dir> <reason...>` -- a "
                            "second resolution root that nobody justified is a "
                            "blanket, not a convention." % where
                        )
                    )
                    continue
                bases.append((args[0].rstrip("/"), where))
            elif kind == "anchor":
                # D4 ANCHOR -- the line-level half of D1.
                #
                # D1 asks whether a cited PATH exists. It never asks whether the
                # cited LINE says what the prose claims, and that gap has cost
                # four measured defects in governed docs, all of which resolved
                # perfectly while pointing somewhere else:
                #   * CLAUDE.md cited `bodyful_reachable_closure` at
                #     crystal_a0_census.py:139, a line inside the lineage parser
                #   * CLAUDE.md's help-claims twin cited env/mod.rs:3365, which
                #     is `};` -- and was wrong the day it was written
                #   * CRYSTAL_STATUS cited the link-2c gate at
                #     crystal_a1_lineage.rs:293, a comment about float division
                #   * the certificate cited structure eta at structural.rs:181,
                #     a doc comment ten lines above the function
                #
                # Opt-in, like `figure`, and for the same reason: a heuristic
                # over every `path:NNN` in these documents would be noise, and a
                # rule nobody can satisfy gets suppressed rather than obeyed.
                # What it buys is that a citation somebody DID bind cannot drift
                # silently -- the needle must occur on that line, and a near
                # miss is reported with its real offset so the fix is a number,
                # not a hunt.
                if len(args) < 2:
                    problems.append(
                        Problem(
                            "D4 ANCHOR: %s malformed -- expected `<!-- claim: "
                            "anchor <path>:<line> <text that must occur on that "
                            "line> -->`" % where
                        )
                    )
                    continue
                target, _, lineno = args[0].rpartition(":")
                needle = " ".join(args[1:])
                if not target or not lineno.isdigit():
                    problems.append(
                        Problem(
                            "D4 ANCHOR: %s first argument %r is not `<path>:<line>`"
                            % (where, args[0])
                        )
                    )
                    continue
                tp = root / target
                if not tp.is_file():
                    problems.append(
                        Problem(
                            "D4 ANCHOR: %s cites %s, which is not in the tree"
                            % (where, target)
                        )
                    )
                    continue
                lines = tp.read_text(errors="replace").splitlines()
                n = int(lineno)
                if not 1 <= n <= len(lines):
                    problems.append(
                        Problem(
                            "D4 ANCHOR: %s cites %s:%d, but that file has %d lines"
                            % (where, target, n, len(lines))
                        )
                    )
                    continue
                if needle in lines[n - 1]:
                    stats["anchors"] += 1
                    continue
                near = [i + 1 for i, ln in enumerate(lines) if needle in ln]
                if near:
                    delta = min(near, key=lambda x: abs(x - n))
                    problems.append(
                        Problem(
                            "D4 ANCHOR: %s cites %s:%d for %r, but that line reads "
                            "%r -- the text is at :%d, %+d lines away. Re-cite it; "
                            "do not widen the window."
                            % (where, target, n, needle, lines[n - 1].strip()[:80],
                               delta, delta - n)
                        )
                    )
                else:
                    problems.append(
                        Problem(
                            "D4 ANCHOR: %s cites %s:%d for %r, and that text occurs "
                            "NOWHERE in the file. That line reads %r. The construct "
                            "moved out or was renamed; find it before re-citing."
                            % (where, target, n, needle, lines[n - 1].strip()[:80])
                        )
                    )
            else:
                problems.append(
                    Problem(
                        "D0 MARKER: %s unknown claim kind %r. Known: figure, "
                        "pointer-only, absent, elsewhere, pinned, base, anchor."
                        % (where, kind)
                    )
                )

        # -- a declaration only means something under D1. In a `figure`-only
        # -- doc it reads as an exemption and grants nothing, which is the
        # -- marker-that-silently-does-nothing class wearing a rule's clothes.
        if "ref" not in rules:
            for cited, where in sorted(absent.items()):
                problems.append(
                    Problem(
                        "D0 MARKER: %s declares %s `absent`, but %s is not "
                        "under D1 REF, so the declaration exempts nothing. "
                        "Switch the doc's rules on or drop the marker."
                        % (where, cited, rel)
                    )
                )
            for cited, (where, repo) in sorted(elsewhere.items()):
                problems.append(
                    Problem(
                        "D0 MARKER: %s declares %s `elsewhere` in %s, but %s "
                        "is not under D1 REF, so the declaration exempts "
                        "nothing." % (where, cited, repo, rel)
                    )
                )
            for cited, (where, repo, rev) in sorted(pinned.items()):
                problems.append(
                    Problem(
                        "D0 MARKER: %s declares %s `pinned` in %s at %s, but %s "
                        "is not under D1 REF, so the declaration checks nothing."
                        % (where, cited, repo, rev, rel)
                    )
                )
            for b, where in bases:
                problems.append(
                    Problem(
                        "D0 MARKER: %s declares base `%s`, but %s is not under "
                        "D1 REF, so nothing resolves through it."
                        % (where, b, rel)
                    )
                )

        # -- D5 LINK: a markdown link to a repo path must resolve, relative
        # -- to the DOCUMENT it is written in. Part of the D1 family and gated
        # -- on the same `ref` opt-in: a link is a citation, and a citation
        # -- that resolves nowhere is the defect D1 exists to refuse.
        if "ref" in rules:
            for lm in LINK_TARGET.finditer(_blank_code_spans(prose)):
                target = lm.group(1)
                if target.startswith("/"):
                    continue
                stats["links"] += 1
                cited_here.add(target)
                if target in absent or target in elsewhere or target in pinned:
                    continue
                if (doc.parent / target).exists():
                    continue
                line = text[: lm.start()].count("\n") + 1
                problems.append(
                    Problem(
                        "D5 LINK: %s:%d links to `%s`, which does not exist "
                        "relative to %s. A dead link in a document this repo "
                        "names as a reference sends a reader nowhere; fix the "
                        "target, or declare it `absent`/`elsewhere` with a "
                        "reason." % (rel, line, target, doc.parent)
                    )
                )

        # -- D2 FIGURE (always on, wherever a marker appears)
        for where, pidx, mline, art, expr in figures:
            stats["bound"] += 1
            apath = root / art
            if not apath.exists():
                problems.append(
                    Problem(
                        "D2 FIGURE: %s binds a figure to %s, which is not in "
                        "the tree." % (where, art)
                    )
                )
                continue
            try:
                data = json.loads(apath.read_text())
            except (OSError, ValueError) as exc:
                problems.append(
                    Problem("D2 FIGURE: %s cannot read %s: %s" % (where, art, exc))
                )
                continue
            try:
                value = _render(data, expr)
            except (KeyError, ValueError, TypeError):
                problems.append(
                    Problem(
                        "D2 FIGURE: %s binds `%s`, which %s does not carry as a "
                        "scalar. The artifact moved or the expression is wrong."
                        % (where, expr, art)
                    )
                )
                continue
            span = _bound_span(text, paras, pidx, mline)
            if value not in span:
                problems.append(
                    Problem(
                        "D2 FIGURE: %s re-derives `%s` = %s from %s, and that "
                        "value does NOT appear in the %d lines above the "
                        "marker. Either the artifact moved and the prose did "
                        "not -- read the artifact and rewrite the sentence -- "
                        "or the marker sits above the sentence it binds "
                        "instead of below it."
                        % (where, expr, value, art, SPAN_LINES)
                    )
                )

        # -- D1 REF
        if "ref" in rules:
            base_dirs, base_used = [], {}
            for b, where in bases:
                if not (root / b).is_dir():
                    problems.append(
                        Problem(
                            "D1 REF: %s declares base `%s`, which is not a "
                            "directory of this repo. A base that does not "
                            "exist rescues nothing and hides nothing -- it is "
                            "a typo wearing a rule's clothes." % (where, b)
                        )
                    )
                    continue
                base_dirs.append(b)
                base_used.setdefault(b, 0)

            xrepo = _classify_xrepo(elsewhere, siblings)
            pins = _classify_pinned(pinned, siblings)
            seen_xrepo = set()
            seen_para_claims = set()
            prose_blocks = _blocks(prose)
            for m in PATH_TOKEN.finditer(prose):
                cited = m.group(1).rstrip("/")
                if cited.split("/")[0] not in tops:
                    continue  # basename shorthand or another repo's layout
                stats["paths"] += 1
                cited_here.add(cited)
                ok, via = _resolve_cited(root, base_dirs, cited, ignored)
                if ok:
                    if via is not None:
                        base_used[via] += 1
                        stats["based"] += 1
                    continue
                line = text[: m.start()].count("\n") + 1
                if cited in absent:
                    # `absent` exempts the PATH, not the prose around it: a
                    # paragraph that sends a reader to "commit <rev>" for a
                    # path this repo no longer has makes a claim about THIS
                    # repository -- or, attributed by name, about a sibling --
                    # and DESIGN.md's `(commit fe4217c28)` named an object no
                    # clone of it has ever held. The scope is the citation's
                    # BLOCK -- its paragraph, or its list item -- not its
                    # physical line: a sentence wraps.
                    pstart, _, pbody = next(
                        ((s0, e0, b0) for s0, e0, b0 in prose_blocks if s0 <= line <= e0),
                        (line, line, prose.split("\n")[line - 1]),
                    )
                    for verdict, what, where in _para_revs(root, pbody, siblings):
                        if (pstart, what) in seen_para_claims:
                            continue
                        seen_para_claims.add((pstart, what))
                        if verdict == "unverified":
                            stats["unverified"].append(
                                (rel, cited, "absent (its citing paragraph)", where, what)
                            )
                            continue
                        problems.append(
                            Problem(
                                "D1 REF: %s:%d cites `%s`, declared `absent`, and its "
                                "paragraph (the block from line %d) %s. A commit the prose sends a "
                                "reader to must be one here -- or one of the sibling "
                                "repo it names (`trust <rev>`)."
                                % (rel, line, cited, pstart, what)
                            )
                        )
                    continue
                head = cited.split("/")[0]
                if cited in pinned:
                    where, repo, rev = pinned[cited]
                    verdict, detail = pins[cited]
                    # The PROSE of the citing paragraph: the marker itself
                    # names the rev, and must not be what satisfies this.
                    para = MARKER.sub(
                        "", next((body for s, e, body in paras if s <= line <= e), "")
                    )
                    if not _names_pin(para, rev, detail if verdict == "verified" else None):
                        problems.append(
                            Problem(
                                "D1 REF: %s:%d cites `%s`, pinned in %s at %s (%s), "
                                "and its paragraph does not name %s. The rev that "
                                "was checked must be the rev the prose sends a "
                                "reader to." % (rel, line, cited, repo, rev, where, rev)
                            )
                        )
                    # The verdict is per declaration, reported once; the
                    # paragraph rule above is per citation.
                    if (cited, "pinned") in seen_xrepo:
                        continue
                    seen_xrepo.add((cited, "pinned"))
                    if verdict == "unknown-repo":
                        problems.append(
                            Problem(
                                "D1 REF: %s declares %s `pinned` in unknown repo %r."
                                % (where, cited, repo)
                            )
                        )
                    elif verdict == "missing":
                        problems.append(
                            Problem(
                                "D1 REF: %s declares %s `pinned` in %s at %s, and %s. "
                                "(If %s's checkout is behind its own remote, fetch it.)"
                                % (where, cited, repo, rev, detail, repo)
                            )
                        )
                    elif verdict == "unverified":
                        stats["pinned_unverified"] += 1
                        stats["unverified"].append(
                            (rel, cited, "pinned at %s" % rev, repo, detail)
                        )
                    else:
                        stats["pinned_verified"] += 1
                    continue
                if head in ignored and cited not in elsewhere:
                    problems.append(
                        Problem(
                            "D1 REF: %s:%d cites `%s`, under the gitignored `%s/` "
                            "tree. What is there is untracked state and is never "
                            "read: a build or runtime output is checked by "
                            "DECLARATION, the same on every box. Declare it: "
                            "`<!-- claim: absent %s <what writes it> -->`."
                            % (rel, line, cited, head, cited)
                        )
                    )
                    continue
                if cited in elsewhere:
                    where, repo = elsewhere[cited]
                    verdict, detail = xrepo[cited]
                    if verdict == "unknown-repo":
                        problems.append(
                            Problem(
                                "D1 REF: %s declares %s `elsewhere` in unknown "
                                "repo %r." % (where, cited, repo)
                            )
                        )
                    elif verdict == "missing":
                        problems.append(
                            Problem(
                                "D1 REF: %s declares %s `elsewhere` in %s, and "
                                "it is NOT there either -- checked in its "
                                "working tree and at `%s`. A cross-repo "
                                "citation rots exactly like a local one. (If "
                                "%s's checkout is behind its own remote, fetch "
                                "it: a stale ref reads exactly like a deleted "
                                "file.)" % (where, cited, repo, detail, repo)
                            )
                        )
                    elif cited in seen_xrepo:
                        pass
                    elif verdict == "unverified":
                        # Not an error -- not every machine has every sibling.
                        # But it is NOT a pass either, so it is counted and
                        # named rather than being folded into the green line.
                        seen_xrepo.add(cited)
                        stats["xrepo_unverified"] += 1
                        stats["unverified"].append((rel, cited, "elsewhere", repo, detail))
                    else:
                        seen_xrepo.add(cited)
                        stats["xrepo_verified"] += 1
                    continue
                problems.append(
                    Problem(
                        "D1 REF: %s:%d cites `%s`, which is not in the tree. "
                        "Fix the path, or declare it: `<!-- claim: absent %s "
                        "<why> -->` if it is deliberately gone, `<!-- claim: "
                        "elsewhere %s <repo> <why> -->` if it lives in a "
                        "sibling repo, `<!-- claim: base <dir> <why> -->` if "
                        "the doc writes its paths relative to a subdirectory "
                        "of this repo." % (rel, line, cited, cited, cited)
                    )
                )

            # -- declarations checked from the OTHER side. A dead exemption is
            # -- worse than none: it stays in force after the thing it was
            # -- written for is gone, and exempts whatever moves into its name.
            for b, where in bases:
                if base_used.get(b) == 0:
                    problems.append(
                        Problem(
                            "D1 REF: %s declares base `%s` and NOT ONE cited "
                            "path needed it. Either the citations it was "
                            "written for have been fixed -- delete it with "
                            "them -- or it never matched anything and has been "
                            "granting an exemption nobody uses." % (where, b)
                        )
                    )
            for cited, (where, repo, rev) in sorted(pinned.items()):
                if _resolve_cited(root, base_dirs, cited, ignored)[0]:
                    problems.append(
                        Problem(
                            "D1 REF: %s declares %s `pinned` in %s at %s, and it "
                            "resolves in THIS repo. The declaration is dead: point "
                            "the citation at the local file." % (where, cited, repo, rev)
                        )
                    )
            for cited, (where, repo) in sorted(elsewhere.items()):
                if _resolve_cited(root, base_dirs, cited, ignored)[0]:
                    problems.append(
                        Problem(
                            "D1 REF: %s declares %s `elsewhere` in %s, and it "
                            "resolves in THIS repo. The declaration is dead: "
                            "point the citation at the local file, or the "
                            "exemption will still be standing on the day the "
                            "local file goes." % (where, cited, repo)
                        )
                    )

            # A declaration no citation reads grants an exemption nobody
            # uses -- and keeps granting it to whatever is cited under that
            # name next. `base` has had this rule since it was written; the
            # three path declarations had not, so a `pinned` for a path the
            # doc never cites was never checked at all.
            for kind, table in (("absent", absent), ("elsewhere", elsewhere), ("pinned", pinned)):
                for cited, val in sorted(table.items()):
                    if cited in cited_here:
                        continue
                    where = val if kind == "absent" else val[0]
                    problems.append(
                        Problem(
                            "D1 REF: %s declares %s `%s`, and no citation in %s "
                            "reads it (not as a rooted path, not as a link). The "
                            "declaration checks nothing: delete it with the "
                            "citation it was written for, or fix its path."
                            % (where, cited, kind, rel)
                        )
                    )
            # The commits a declaration's REASON names are the one part of an
            # exemption that can still be checked: `absent` exempts its path
            # from every rule, so "added at <rev>" or "recoverable with `git
            # show <rev>:<path>`" is the whole of what a reader is told, and
            # nothing re-derived it. Each commit id must be a commit of the
            # repository the declaration is about -- THIS one for `absent`,
            # the sibling for `pinned`/`elsewhere` -- and each promised
            # `git show` must show.
            for where, kind, cited, repo, reason in reasons:
                if not (REV_TOKEN.search(reason) or RECOVER.search(reason)):
                    continue
                if repo is None:
                    at, label = root, "this repository"
                else:
                    at, label = siblings.get(repo), repo
                    if at is None:
                        continue  # the unknown-repo refusal above covers it
                    if not at.exists():
                        stats["unverified"].append(
                            (rel, cited, "%s reason" % kind, repo,
                             "sibling %r is not on this box (%s)" % (repo, at))
                        )
                        continue
                    if not _sibling_is_own_repo(at):
                        stats["unverified"].append(
                            (rel, cited, "%s reason" % kind, repo,
                             "sibling %r at %s is not the top of its own repository"
                             % (repo, at))
                        )
                        continue
                for verdict, what in _reason_revs(at, reason):
                    if verdict == "unverified":
                        stats["unverified"].append(
                            (rel, cited, "%s reason" % kind, label, what)
                        )
                        continue
                    problems.append(
                        Problem(
                            "D1 REF: %s declares %s `%s`, and its reason %s in %s. "
                            "A reason is what a reader is sent to; it must resolve."
                            % (where, cited, kind, what, label)
                        )
                    )

        # -- D3 BIND
        if "bind" in rules:
            for i, (s, e, body) in enumerate(paras):
                arts = ARTIFACT_TOKEN.findall(body)
                if not arts or not FIGURE.search(body):
                    continue
                stats["figures"] += 1
                if i in pointer_paras:
                    continue
                if any(pidx == i for _, pidx, _, _, _ in figures):
                    continue
                problems.append(
                    Problem(
                        "D3 BIND: %s:%d-%d quotes an N/M figure in a paragraph "
                        "that cites %s, and binds neither. This is the shape "
                        "that went stale: add `<!-- claim: figure %s <expr> "
                        "-->` so the number is re-derived, or `<!-- claim: "
                        "pointer-only <why> -->` if the figure is a dated "
                        "measurement the artifact does not carry."
                        % (rel, s, e, ", ".join(sorted(set(arts))), arts[0])
                    )
                )

    # -- D6 BUDGET
    if any(rel == "CLAUDE.md" for rel, _ in governed):
        units, counted = _instruction_units(root)
        stats["instruction_units"] = units
        if units > INSTRUCTION_FILES_BUDGET:
            problems.append(
                Problem(
                    "D6 BUDGET: %s total %d characters (UTF-16 units), over the "
                    "%d-character INSTRUCTION_FILES_BUDGET. Claude Code loads these "
                    "whole into every session and warns once instruction files pass "
                    "150,000 characters in total. Move narrative, closed classes "
                    "and measured deltas out -- to docs/FRONTEND_CLASS_LEDGER.md, "
                    "docs/SELF_VERIFICATION_NAVIGATION.md or "
                    "docs/archive/CLAUDE_MD_HISTORY.md -- and leave a pointer; do "
                    "not raise the budget to fit."
                    % (" + ".join(counted), units, INSTRUCTION_FILES_BUDGET)
                )
            )

    return problems, stats


# --------------------------------------------------------------------- selftest
#
# Arms run against a synthetic tree, never the real one. `check_add_decl_ratchet`
# plants into a tracked file and restores it in a `finally`; that arm is
# genuinely falsifying and it is also a measured hazard -- a concurrent
# `local_gate.sh` compiled the planted file and died on it (see the
# check_add_decl_ratchet note in data/gate_registry.json). Nothing here needs
# the real tree, so nothing here touches it.

_ART = '{"passed": 63, "total": 63, "rows": [{"n": 7}]}'


def _git_env(tmp: Path):
    """An environment in which git reads NO config of the box it runs on.

    HOME is the fixture, so a global excludesFile, hooksPath or templateDir on
    the maintainer's machine cannot shape what a synthetic repo tracks.
    """
    return {
        "GIT_AUTHOR_NAME": "t",
        "GIT_AUTHOR_EMAIL": "t@t",
        "GIT_COMMITTER_NAME": "t",
        "GIT_COMMITTER_EMAIL": "t@t",
        "GIT_CONFIG_NOSYSTEM": "1",
        "PATH": "/usr/bin:/bin:/usr/local/bin",
        "HOME": str(tmp),
    }


def _fixture(tmp: Path):
    (tmp / "docs").mkdir(parents=True)
    (tmp / "reports").mkdir()
    (tmp / "scripts").mkdir()
    # `tests/` must be a TRACKED top-level dir or `tests/probe.rs` is not a
    # rooted citation at all and the base arms would measure nothing. It holds
    # only a placeholder (git tracks files, not directories), so the probe
    # below resolves only through the declared base -- which is the exact
    # shape docs/CRYSTAL_STATUS.md has against crates/clean-verify.
    (tmp / "tests").mkdir()
    (tmp / "tests/.keep").write_text("")
    # The fixture is a REPOSITORY since 2026-09-15, because what makes a first
    # segment rooted is the index plus IGNORED_ROOTS -- never what is on disk.
    # Its .gitignore names both rows the way the real one does, plus `build/`,
    # a gitignored directory that is NOT a row (the real .gitignore names it
    # too, and `build/release` is Lean's layout, not this repo's); none of the
    # three exists here, which is the shape a pristine worktree has.
    (tmp / ".gitignore").write_text(
        "# build output\ntarget/\n# runtime output\nmetrics/\n"
        "# named by .gitignore, deliberately not an IGNORED_ROOTS row\nbuild/\n"
    )
    (tmp / "crates/pkg/tests").mkdir(parents=True)
    (tmp / "crates/pkg/tests/probe.rs").write_text("fn probe() {}\n")
    # For the D4 ANCHOR arms: a file whose construct sits at a KNOWN line, with
    # a decoy comment above it so a drifted citation lands on something that
    # reads plausibly -- which is exactly how all four real instances survived.
    (tmp / "scripts/anchored.py").write_text(
        "# line 1\n"
        "# line 2: a comment that reads like the thing below it\n"
        "def the_construct(x):\n"
        "    return x\n"
    )
    (tmp / "reports/battery.json").write_text(_ART)
    # 2026-09-15: an artifact keyed by REPO PATH. `data/source_elab_ratchet.json`
    # is shaped exactly like this, and until the expression language grew
    # bracket-quoted segments no figure over it could be BOUND at all -- the
    # dotted-only lookup cut `Mathlib/Logic/Unique.lean` into pieces, so the
    # honest answer (bind it) was unavailable and every such figure fell to
    # `pointer-only`. A gap in the language reads as a gap in the evidence.
    (tmp / "reports/by_path.json").write_text(
        '{"files": {"Mathlib/Logic/Unique.lean": {"ok": 15, "total": 41}}}\n'
    )
    (tmp / "docs/real.md").write_text("real\n")
    # Shaped like the real CLAUDE.md paragraph this gate was written for: the
    # live figure, the marker under it, and the superseded figures BELOW -- so
    # the arms exercise the span rule instead of a toy with no history in it.
    (tmp / "CLAUDE.md").write_text(
        "# Fixture\n"
        "\n"
        "The battery is 63/63 -- artifact `reports/battery.json`.\n"
        "<!-- claim: figure reports/battery.json passed/total -->\n"
        "It read 38/63 in July and 51/63 in August.\n"
        "\n"
        "See `docs/real.md` and `scripts/`.\n"
        "\n"
        "The probe is `tests/probe.rs`; the driver is `scripts/gone.sh`.\n"
        "<!-- claim: base crates/pkg this doc writes probe paths crate-relative -->\n"
        "<!-- claim: elsewhere scripts/gone.sh trust it lives in the sibling -->\n"
        "\n"
        "The retired driver `scripts/retired.sh` reads at the sibling's `0123abc`.\n"
        "<!-- claim: pinned scripts/retired.sh ay 0123abc gone from the sibling's "
        "main; read at the pin -->\n"
        "\n"
        "The construct is at `scripts/anchored.py:3`.\n"
        "<!-- claim: anchor scripts/anchored.py:3 def the_construct(x): -->\n"
        "\n"
        "See [the real one](docs/real.md) for detail.\n"
        "A rustdoc intra-doc link quoted as an EXAMPLE, not a link: "
        "`[FfiBridge](clean_compiler)`.\n"
        "\n"
        "Unique.lean measures 15/41 -- artifact `reports/by_path.json`.\n"
        '<!-- claim: figure reports/by_path.json files["Mathlib/Logic/Unique.lean"].ok'
        '/files["Mathlib/Logic/Unique.lean"].total -->\n'
    )
    # Index only, no commit: `git ls-files` reads the index, and an arm that
    # mutates the working tree afterwards (deleting `docs/`, adding a stray
    # `target/`) is measuring exactly the gap between index and disk.
    env = _git_env(tmp)
    subprocess.run(["git", "-C", str(tmp), "init", "-q", "-b", "main"], env=env, check=True)
    subprocess.run(["git", "-C", str(tmp), "add", "-A"], env=env, check=True)
    return tmp


def _git_sibling(tmp: Path, files, delete_from_worktree=(), at="no-such-sibling"):
    """A real git repository at tmp/<at> (default: the fixture's `elsewhere`
    sibling), committed, then optionally with files removed from the WORKING
    TREE while they stay in history.

    That last shape is not a curiosity -- it is what a shallow or stale sibling
    checkout looks like, and resolving against the working tree alone reported
    six live citations as dead on 2026-08-27. `at` exists for the arm that
    needs a FOREIGN repository the check must ignore: it cannot live at the
    sibling path, where a repo lacking `scripts/gone.sh` is arm 12's refusal.
    """
    sib = tmp / at
    sib.mkdir(parents=True, exist_ok=True)
    env = _git_env(tmp)
    subprocess.run(["git", "-C", str(sib), "init", "-q", "-b", "main"], env=env, check=True)
    for rel in files:
        p = sib / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("x\n")
    subprocess.run(["git", "-C", str(sib), "add", "-A"], env=env, check=True)
    subprocess.run(["git", "-C", str(sib), "commit", "-qm", "seed"], env=env, check=True)
    for rel in delete_from_worktree:
        (sib / rel).unlink()
    return sib


def _foreign_shallow_environment(_template: Path, tmp: Path):
    """An inherited shallow marker must not replace a full sibling's history."""
    head = subprocess.run(
        ["git", "-C", str(tmp / "no-such-ay"), "rev-parse", "HEAD"],
        env=_git_env(tmp), check=True, capture_output=True, text=True,
    ).stdout
    marker = tmp / "foreign-shallow"
    marker.write_text(head)
    return {"GIT_SHALLOW_FILE": str(marker)}


def _pinned_sibling(tmp: Path, at_pin, after=None, shallow=False):
    """The `pinned` fixture's sibling (`ay`, at tmp/no-such-ay): its FIRST
    commit holds `at_pin`, a second applies `after` (path -> text, or None to
    delete), and the doc's pin is rewritten to the FIRST commit -- so an arm
    measures the tree AT the pin, not the sibling's tip. `shallow` makes the
    sibling a depth-1 clone that does not carry the pinned commit."""
    env = _git_env(tmp)
    src = tmp / ("ay-full" if shallow else "no-such-ay")
    src.mkdir()
    git = lambda *a: subprocess.run(  # noqa: E731
        ["git", "-C", str(src), *a], env=env, check=True, capture_output=True, text=True
    )
    git("init", "-q", "-b", "main")
    for rel in at_pin:
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        (src / rel).write_text("x\n")
    git("add", "-A")
    git("commit", "-qm", "pin")
    pin = git("rev-parse", "HEAD").stdout.strip()
    for rel, text in (after or {}).items():
        if text is None:
            (src / rel).unlink()
        else:
            (src / rel).parent.mkdir(parents=True, exist_ok=True)
            (src / rel).write_text(text)
    if after:
        git("add", "-A")
        git("commit", "-qm", "after")
    if shallow:
        subprocess.run(
            ["git", "clone", "-q", "--depth", "1", "file://%s" % src, str(tmp / "no-such-ay")],
            env=env,
            check=True,
            capture_output=True,
        )
    doc = tmp / "CLAUDE.md"
    doc.write_text(doc.read_text().replace("0123abc", pin[:10]))


def _pinned_prose(tmp: Path, rewrite):
    """Build the deleted-after-pin fixture and rewrite only its PROSE token.
    The marker keeps the first commit; `rewrite(pin, full)` gives the token."""
    _pinned_sibling(tmp, ["scripts/retired.sh"], after={"scripts/retired.sh": None})
    doc = tmp / "CLAUDE.md"
    text = doc.read_text()
    m = re.search(r"reads at the sibling's `([0-9a-f]+)`", text)
    pin = m.group(1)
    full = subprocess.run(
        ["git", "-C", str(tmp / "no-such-ay"), "rev-parse", pin + "^{commit}"],
        env=_git_env(tmp), check=True, capture_output=True, text=True,
    ).stdout.strip()
    doc.write_text(text.replace(m.group(0), "reads at the sibling's `%s`" % rewrite(pin, full)))


def _absent_recovery(tmp: Path, shown: str):
    """Commit the fixture, then declare `docs/gone.md` absent with a reason
    that says it is recoverable with `git show <that commit>:<shown>`."""
    env = _git_env(tmp)
    subprocess.run(["git", "-C", str(tmp), "commit", "-qm", "seed"], env=env, check=True)
    head = subprocess.run(
        ["git", "-C", str(tmp), "rev-parse", "--short=10", "HEAD"],
        env=env, check=True, capture_output=True, text=True,
    ).stdout.strip()
    doc = tmp / "CLAUDE.md"
    doc.write_text(
        doc.read_text()
        + "\nThe old note was `docs/gone.md`.\n"
        + "<!-- claim: absent docs/gone.md deleted; recoverable with "
        + "`git show %s:%s`. -->\n" % (head, shown)
    )


def _commit_fixture(tmp: Path):
    """Commit the fixture as it stands, so its repository has refs to answer from."""
    env = _git_env(tmp)
    subprocess.run(["git", "-C", str(tmp), "commit", "-qm", "seed"], env=env, check=True)


def _absent_line(tmp: Path, tail):
    """Commit the fixture, then cite `docs/gone.md` -- declared `absent` with
    no commit in its reason -- on a PROSE line ending in `tail(<that commit>)`."""
    env = _git_env(tmp)
    subprocess.run(["git", "-C", str(tmp), "commit", "-qm", "seed"], env=env, check=True)
    head = subprocess.run(
        ["git", "-C", str(tmp), "rev-parse", "--short=10", "HEAD"],
        env=env, check=True, capture_output=True, text=True,
    ).stdout.strip()
    doc = tmp / "CLAUDE.md"
    doc.write_text(
        doc.read_text()
        + "\nThe old note was `docs/gone.md` %s.\n" % tail(head)
        + "<!-- claim: absent docs/gone.md deleted -->\n"
    )


def _absent_sibling_line(tmp: Path, real: bool):
    """`_absent_line`'s shape with the `trust` sibling PRESENT (a real git
    repository holding the fixture's `elsewhere` path): the citing line says
    "read it at trust `<rev>`", where <rev> is the sibling's own commit when
    `real`, else one it does not have."""
    sib = _git_sibling(tmp, ["scripts/gone.sh"])
    env = _git_env(tmp)
    head = subprocess.run(
        ["git", "-C", str(sib), "rev-parse", "--short=11", "HEAD"],
        env=env, check=True, capture_output=True, text=True,
    ).stdout.strip()
    rev = head if real else "fedcba98765"
    _absent_line(tmp, lambda _here: "(read it at trust `%s`)" % rev)


def _pad_instructions(tmp: Path, total: int, into_rules: bool = False,
                      astral: bool = False):
    """Grow the fixture's instruction files to exactly `total` UTF-16 units
    by plain prose (no path, figure or marker, so no other rule moves). With
    `into_rules` the padding lands in `.claude/rules/pad.md` instead; with
    `astral` one padding character is replaced by U+1D49E, which is ONE code
    point and TWO units -- so the file reads `total` code points and
    `total + 1` units."""
    have, _ = _instruction_units(tmp)
    need = total - have
    if into_rules:
        rules = tmp / INSTRUCTION_RULES_DIR
        rules.mkdir(parents=True, exist_ok=True)
        pad = "x" * (need - 1) + "\n"
        (rules / "pad.md").write_text(pad, encoding="utf-8")
        return
    pad = "\n" + "x" * (need - 1)
    if astral:
        pad = pad[:-1] + "\U0001D49E"
    doc = tmp / "CLAUDE.md"
    doc.write_text(doc.read_text(encoding="utf-8") + pad, encoding="utf-8")


def _run(tmp: Path, governed=None, sibling_config=None):
    if governed is None:
        governed = (("CLAUDE.md", ("ref", "bind")),)
    siblings = {"trust": tmp / "no-such-sibling", "ay": tmp / "no-such-ay"}
    if sibling_config is not None:
        siblings = selected_siblings(sibling_config, defaults=siblings)
    return check(tmp, governed=governed, siblings=siblings)


def selftest() -> int:
    arms = [
        # (name, expected-prefix or "" for green, mutation)
        ("01 baseline is GREEN", "", lambda t: None),
        # ── D4 ANCHOR (audit r17, 2026-09-14) ────────────────────────────
        #
        # D1 asks whether a cited PATH exists and never whether the cited LINE
        # says what the prose claims. Four measured defects in governed docs
        # resolved perfectly while pointing elsewhere, one of them wrong the
        # day it was written. These arms are two-way on purpose: 01 keeps the
        # bound citation GREEN, so a rule that reds on everything cannot pass
        # for a rule that works.
        (
            "01b D4 the construct MOVES and the citation does not follow",
            "D4 ANCHOR",
            lambda t: _sub(
                t, "scripts/anchored.py",
                "# line 1\n", "# line 1\n# an inserted line\n"),
        ),
        (
            "01c D4 the construct is RENAMED out of the file",
            "D4 ANCHOR",
            lambda t: _sub(
                t, "scripts/anchored.py",
                "def the_construct(x):", "def renamed_away(x):"),
        ),
        (
            "01d D4 a citation past the end of the file is refused",
            "D4 ANCHOR",
            lambda t: _sub(
                t, "CLAUDE.md",
                "anchor scripts/anchored.py:3 ", "anchor scripts/anchored.py:900 "),
        ),
        (
            "01e D4 a malformed anchor is refused, not ignored",
            "D4 ANCHOR",
            lambda t: _sub(
                t, "CLAUDE.md",
                "anchor scripts/anchored.py:3 def", "anchor scripts/anchored.py def"),
        ),
        # ── D5 LINK (2026-09-15) ────────────────────────────────────────
        #
        # D1's PATH_TOKEN sees only BACKTICKED rooted paths, so every markdown
        # link in every governed doc was invisible to it. Measured across the
        # governed set plus the nine key-reference docs: 253 links, 2 dead --
        # both further copies of AUDIT_LEAN4_REPLACEMENT_2026-07-23.md, the
        # never-existed file GATE_REGISTRY.md records as "cited five times
        # across four docs" AND FIXED. That count was of rooted citations only.
        #
        # Arm 01i is the one this rule owes its existence to twice over: the
        # FIRST draft of D5 had no code-span blanking and immediately accused
        # docs/JUSTIFIED_EXCEPTIONS.md of a dead link to `clean_compiler` --
        # which is a rustdoc intra-doc link QUOTED AS AN EXAMPLE inside
        # backticks. A matcher over raw text counts mentions, not links.
        (
            "01h D5 a markdown link to a path that is not there is refused",
            "D5 LINK",
            lambda t: _sub(t, "CLAUDE.md", "](docs/real.md)", "](docs/vanished.md)"),
        ),
        (
            "01i D5 a link-shaped string inside a CODE SPAN is not a link "
            "(the false positive this rule shipped with)",
            "",
            lambda t: None,
        ),
        (
            "01j D5 a dead link DECLARED absent is exempt, like any citation",
            "",
            lambda t: (
                _sub(t, "CLAUDE.md", "](docs/real.md)", "](docs/vanished.md)"),
                _sub(t, "CLAUDE.md", "See [the real one]",
                     "<!-- claim: absent docs/vanished.md deliberately gone -->\nSee [the real one]"),
            ),
        ),
        # ── bracket-quoted path segments (2026-09-15) ───────────────────
        #
        # WHERE THE TWO DIRECTIONS ACTUALLY LIVE, stated because my first
        # reading of the control was wrong. 01f alone cannot tell "the artifact
        # moved" from "the expression language is broken": both raise, and both
        # surface as a `D2 FIGURE` problem, so 01f passes either way. What
        # catches a broken language is ARM 01, the baseline-is-GREEN arm — with
        # bracket-quoted keys removed, the fixture's bound figure stops
        # rendering and 11 arms red at once, 01 among them. Measured both
        # mutants: dropping the quoted-key branch, and restoring the old
        # `expr.split("/")` that cut quoted repo paths apart.
        #
        # So do not "simplify" arm 01 into a smoke test: it is the other half
        # of this pair.
        (
            "01f a key containing `/` and `.` is addressable, and the figure binds",
            "D2 FIGURE",
            lambda t: (t / "reports/by_path.json").write_text(
                '{"files": {"Mathlib/Logic/Unique.lean": {"ok": 8, "total": 41}}}\n'
            ),
        ),
        (
            "01g an unterminated quote in an expression is REFUSED, not guessed",
            "D2 FIGURE",
            lambda t: _sub(
                t, "CLAUDE.md",
                'files["Mathlib/Logic/Unique.lean"].ok',
                'files["Mathlib/Logic/Unique.lean].ok'),
        ),
        (
            "02 D2 artifact moves, prose stale -- THE 51/63 arm, and the arm "
            "that a paragraph-wide span would have passed: 51/63 IS in this "
            "paragraph, as superseded history one line below the marker",
            "D2 FIGURE",
            lambda t: (t / "reports/battery.json").write_text(
                '{"passed": 51, "total": 63}'
            ),
        ),
        (
            "03 D2 anti-correlation: prose follows the artifact -> GREEN",
            "",
            lambda t: (
                (t / "reports/battery.json").write_text('{"passed": 51, "total": 63}'),
                _sub(t, "CLAUDE.md", "is 63/63", "is 51/63"),
            ),
        ),
        (
            "04 D2 artifact deleted",
            "D2 FIGURE",
            lambda t: (t / "reports/battery.json").unlink(),
        ),
        (
            "05 D2 bound key gone from the artifact",
            "D2 FIGURE",
            lambda t: (t / "reports/battery.json").write_text('{"total": 63}'),
        ),
        (
            "06 D2 value sits in the paragraph but BELOW the marker",
            "D2 FIGURE",
            lambda t: (
                _sub(
                    t,
                    "CLAUDE.md",
                    "The battery is 63/63 -- artifact",
                    "The battery is 9/9 -- artifact",
                ),
                _sub(t, "CLAUDE.md", "It read 38/63", "It read 63/63 and 38/63"),
            ),
        ),
        (
            "06b D2 marker placed ABOVE the sentence it binds",
            "D2 FIGURE",
            lambda t: _sub(
                t,
                "CLAUDE.md",
                "The battery is 63/63 -- artifact `reports/battery.json`.\n"
                "<!-- claim: figure reports/battery.json passed/total -->\n",
                "<!-- claim: figure reports/battery.json passed/total -->\n"
                "The battery is 63/63 -- artifact `reports/battery.json`.\n",
            ),
        ),
        (
            "07 D2 malformed marker is a refusal, not a skip",
            "D2 FIGURE",
            lambda t: _sub(
                t, "CLAUDE.md", "figure reports/battery.json passed/total", "figure"
            ),
        ),
        (
            "08 D0 unknown marker kind",
            "D0 MARKER",
            # Anchored on the FULL marker since 2026-09-15: the fixture now
            # carries a second `claim: figure` (the bracket-quoted-key arms),
            # and _sub requires its anchor to be unique — which is the point
            # of _sub, not an obstacle to it.
            lambda t: _sub(
                t, "CLAUDE.md",
                "claim: figure reports/battery.json",
                "claim: figvre reports/battery.json"),
        ),
        (
            "09 D1 rooted path that is not in the tree",
            "D1 REF",
            lambda t: (t / "docs/real.md").unlink(),
        ),
        (
            "10 D1 the same path, declared `absent` -> GREEN",
            "",
            lambda t: (
                (t / "docs/real.md").unlink(),
                _sub(
                    t,
                    "CLAUDE.md",
                    "See `docs/real.md`",
                    "<!-- claim: absent docs/real.md retired 2026-08-26 -->\n"
                    "See `docs/real.md`",
                ),
            ),
        ),
        (
            "11 D1 `absent` with no reason is still a refusal",
            "D1 REF",
            lambda t: (
                (t / "docs/real.md").unlink(),
                _sub(
                    t,
                    "CLAUDE.md",
                    "See `docs/real.md`",
                    "<!-- claim: absent docs/real.md -->\nSee `docs/real.md`",
                ),
            ),
        ),
        (
            "12 D1 `elsewhere` into a sibling that IS a repo and lacks it, in "
            "its working tree AND in its history",
            "D1 REF",
            lambda t: _git_sibling(t, ["something/else.txt"]),
        ),
        (
            "13 D1 basename shorthand is NOT a citation -> GREEN",
            "",
            lambda t: _sub(t, "CLAUDE.md", "See `docs/real.md`", "See `nothing.rs`"),
        ),
        (
            "14 D1 a first segment that is not a dir of this repo -> GREEN",
            "",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`", "See `Mathlib/Logic/Basic.lean`"
            ),
        ),
        (
            "15 D3 artifact + figure paragraph with no marker at all",
            "D3 BIND",
            lambda t: _sub(
                t, "CLAUDE.md", "<!-- claim: figure reports/battery.json passed/total -->\n", ""
            ),
        ),
        (
            "16 D3 the same paragraph with `pointer-only` -> GREEN",
            "",
            lambda t: _sub(
                t,
                "CLAUDE.md",
                "<!-- claim: figure reports/battery.json passed/total -->",
                "<!-- claim: pointer-only dated 2026-07-12 run, not a live key -->",
            ),
        ),
        (
            "17 D3 `pointer-only` with no reason is a refusal",
            "D3 BIND",
            lambda t: _sub(
                t,
                "CLAUDE.md",
                "<!-- claim: figure reports/battery.json passed/total -->",
                "<!-- claim: pointer-only -->",
            ),
        ),
        (
            "18 D0 a governed doc that disappears is a refusal, not a skip",
            "D0 GOVERNED",
            lambda t: (t / "CLAUDE.md").unlink(),
        ),
        # ---- base: a doc that writes its paths relative to a subdirectory
        (
            "19 D1 `base` rescues a crate-relative citation, and SAYS it did",
            "",
            lambda t: None,
            {"stats": {"based": 1}},
        ),
        (
            "20 D1 the same citation with the `base` declaration removed",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md", "<!-- claim: base crates/pkg this doc writes probe paths crate-relative -->\n", ""
            ),
        ),
        (
            "21 D1 `base` naming a directory that is not in the tree",
            "D1 REF",
            lambda t: _sub(t, "CLAUDE.md", "base crates/pkg ", "base crates/nope "),
        ),
        (
            "22 D1 `base` that rescues NOTHING is a dead declaration -- the "
            "citation now resolves at the root, so the base grants an "
            "exemption nobody uses",
            "D1 REF",
            lambda t: (t / "tests/probe.rs").write_text("fn probe() {}\n"),
        ),
        (
            "23 D1 `base` with no reason is still a refusal",
            "D1 REF",
            lambda t: _sub(
                t,
                "CLAUDE.md",
                "base crates/pkg this doc writes probe paths crate-relative",
                "base crates/pkg",
            ),
        ),
        (
            "24 D1 a base CANNOT rescue a path that is in neither place",
            "D1 REF",
            lambda t: (t / "crates/pkg/tests/probe.rs").unlink(),
        ),
        # ---- elsewhere, from both sides
        (
            "25 D1 a DEAD `elsewhere`: the path resolves in THIS repo, so the "
            "exemption outlives its reason and covers whatever moves in",
            "D1 REF",
            lambda t: (t / "scripts/gone.sh").write_text("#!/bin/sh\n"),
        ),
        (
            "26 D1 an `elsewhere` this box cannot check is GREEN but is "
            "COUNTED and named -- never folded into the pass",
            "",
            lambda t: None,
            {"stats": {"xrepo_unverified": 1, "xrepo_verified": 0}},
        ),
        (
            "27 D1 the same `elsewhere` with the sibling PRESENT and carrying "
            "the file -> verified, and counted as verified",
            "",
            lambda t: _git_sibling(t, ["scripts/gone.sh"]),
            {"stats": {"xrepo_verified": 1, "xrepo_unverified": 0}},
        ),
        (
            "27b D1 THE REFUTED-MEASUREMENT ARM: the sibling's WORKING TREE "
            "does not carry the file and its HISTORY does -- a shallow or "
            "stale checkout, which is what ../trust is on this box. Resolving "
            "against the checkout alone called six live citations dead",
            "",
            lambda t: _git_sibling(
                t, ["scripts/gone.sh"], delete_from_worktree=["scripts/gone.sh"]
            ),
            {"stats": {"xrepo_verified": 1, "xrepo_unverified": 0}},
        ),
        (
            "27c D1 a sibling that is present but is NOT a repository cannot "
            "be asked, so it is UNVERIFIED -- its working tree alone is not an "
            "answer, and answering from it is how 27b happens",
            "",
            lambda t: (t / "no-such-sibling").mkdir(),
            {"stats": {"xrepo_verified": 0, "xrepo_unverified": 1}},
        ),
        (
            "27d D1 the same plain directory inside a COMMITTED checkout: git "
            "discovers the ENCLOSING repository from it, and answering from that "
            "one called 36 live Trust citations dead (2026-09-25) -- UNVERIFIED",
            "",
            lambda t: (_commit_fixture(t), (t / "no-such-sibling").mkdir()),
            {"stats": {"xrepo_verified": 0, "xrepo_unverified": 1}},
        ),
        # ---- a declaration in a doc that D1 does not govern
        (
            "28 D0 `absent`/`elsewhere`/`base` in a doc that is NOT under D1 "
            "reads as an exemption and grants nothing",
            "D0 MARKER",
            lambda t: None,
            {"governed": (("CLAUDE.md", ()),)},
        ),
        # ---- which first segments are ROOTED (2026-09-15). The fixture has
        # ---- `target/` in .gitignore and NO target/ directory, like a pristine
        # ---- worktree. Under the on-disk rule arm 29 was GREEN here and RED on
        # ---- the maintainer box, at one commit -- the defect these arms pin.
        (
            "29 D1 a citation under a GITIGNORED top-level dir is rooted with no "
            "such directory on disk -- refused without a declaration",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md",
                "See `docs/real.md`",
                "See `docs/real.md` and `target/pinned/worktree`"),
        ),
        (
            "30 D1 the same citation declared `absent` -> GREEN, on every box",
            "",
            lambda t: _sub(
                t, "CLAUDE.md",
                "See `docs/real.md`",
                "<!-- claim: absent target/pinned/worktree made by the pinned "
                "runner under the gitignored target/ tree -->\n"
                "See `docs/real.md` and `target/pinned/worktree`"),
        ),
        (
            "29b D1 the SECOND IGNORED_ROOTS row (`metrics/`) roots a citation "
            "too -- a table handled as one name would pass 29 and miss this",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md",
                "See `docs/real.md`",
                "See `docs/real.md` and `metrics/lean4_parity.json`"),
        ),
        (
            "31 D1 a directory that is ON DISK but neither tracked nor an "
            "IGNORED_ROOTS row is not the repo's layout: a stray untracked dir "
            "must not change the verdict -> GREEN (the old rule read it as rooted)",
            "",
            lambda t: (
                (t / "stray").mkdir(),
                _sub(
                    t, "CLAUDE.md",
                    "See `docs/real.md`",
                    "See `docs/real.md` and `stray/pinned/worktree`"),
            ),
        ),
        (
            "31b D1 a directory .gitignore NAMES that is not an IGNORED_ROOTS "
            "row (`build/`, Lean's layout in the real docs) does not root "
            "citations either -> GREEN: the table is not \"every name in "
            ".gitignore\", and this arm is what keeps that decision from "
            "silently reverting",
            "",
            lambda t: _sub(
                t, "CLAUDE.md",
                "See `docs/real.md`",
                "See `docs/real.md` and `build/release`"),
        ),
        (
            "32 D1 a TRACKED directory deleted from the working tree keeps its "
            "citations rooted, so they go RED rather than vanishing from D1 "
            "(the old rule skipped them: not on disk, so not this repo)",
            "D1 REF",
            lambda t: shutil.rmtree(t / "docs"),
        ),
        (
            "33 D0 a root that cannot be ASKED what it tracks is a refusal, "
            "never an empty set that checks nothing and prints green",
            "D0 TREE",
            lambda t: shutil.rmtree(t / ".git"),
        ),
        (
            "33b D0 a root that CAN be asked and tracks NOTHING is the same "
            "refusal -- not a silent collapse of the set to the IGNORED_ROOTS "
            "rows (a `git archive` snapshot plus `git init` with no `git add`)",
            "D0 TREE",
            lambda t: subprocess.run(
                ["git", "-C", str(t), "rm", "-r", "-q", "--cached", "."],
                env=_git_env(t),
                check=True,
            ),
        ),
        (
            "34 D0 an IGNORED_ROOTS row that .gitignore stops naming is refused "
            "-- the table cannot outlive the ignore rule it stands on",
            "D0 IGNORED",
            lambda t: _sub(t, ".gitignore", "target/\n", ""),
        ),
        # ---- the disk under an ignored root is never read (2026-09-15, from
        # ---- review of the first version: `metrics/lean4_parity.json` was on
        # ---- the maintainer box and not on a pristine worktree, so resolving
        # ---- IGNORED_ROOTS citations on disk was the same defect mirrored).
        (
            "35 D1 an IGNORED_ROOTS citation whose file IS on this box's disk "
            "and is undeclared is still refused -- a gitignored build output "
            "is checked by declaration, never by the disk",
            "D1 REF",
            lambda t: (
                (t / "target/pinned/worktree").mkdir(parents=True),
                _sub(
                    t, "CLAUDE.md",
                    "See `docs/real.md`",
                    "See `docs/real.md` and `target/pinned/worktree`"),
            ),
        ),
        (
            "36 D1 the same on-disk citation declared `absent` -> GREEN: "
            "`absent` is not checked from the other side, so a build output "
            "present on the author's box does not refuse the author",
            "",
            lambda t: (
                (t / "target/pinned/worktree").mkdir(parents=True),
                _sub(
                    t, "CLAUDE.md",
                    "See `docs/real.md`",
                    "<!-- claim: absent target/pinned/worktree made by the pinned "
                    "runner under the gitignored target/ tree -->\n"
                    "See `docs/real.md` and `target/pinned/worktree`"),
            ),
        ),
        # ---- a leaked GIT_DIR (a pre-push hook run from a LINKED worktree
        # ---- exports one) must not answer for a root or a sibling that has no
        # ---- repository of its own. The foreign repository is the fixture
        # ---- TEMPLATE, whose index knows `docs/`: unscrubbed, 37 reads it as
        # ---- the root's and prints green, and 37b cannot see the sibling.
        (
            "37 D0 under a leaked GIT_DIR a root with no repository is still "
            "a refusal -- the environment does not get to say what a root tracks",
            "D0 TREE",
            lambda t: shutil.rmtree(t / ".git"),
            {"env": lambda template, tmp: {"GIT_DIR": str(template / ".git")}},
        ),
        (
            "37b D1 under the same leak a sibling is still asked its OWN "
            "history (27b's shape): verified, not answered from the leak",
            "",
            lambda t: _git_sibling(
                t, ["scripts/gone.sh"], delete_from_worktree=["scripts/gone.sh"]
            ),
            {
                "env": lambda template, tmp: {"GIT_DIR": str(template / ".git")},
                "stats": {"xrepo_verified": 1, "xrepo_unverified": 0},
            },
        ),
        (
            "37c D1 under a leaked GIT_DIR naming a FOREIGN repository whose "
            "index tracks `stray/`, a citation under `stray/` is still NOT "
            "rooted: the root's own index decides, never the environment's "
            "-> GREEN (with the scrub removed the foreign index roots it and "
            "the arm reds)",
            "",
            lambda t: (
                _git_sibling(t, ["stray/x.txt"], at="foreign"),
                _sub(
                    t, "CLAUDE.md",
                    "See `docs/real.md`",
                    "See `docs/real.md` and `stray/pinned/worktree`"),
            ),
            {"env": lambda template, tmp: {"GIT_DIR": str(tmp / "foreign" / ".git")}},
        ),
        # ---- `pinned` (2026-09-24): a sibling citation checked AT a commit.
        (
            "39 D1 `pinned`: the path is in the sibling's tree AT the pin and "
            "deleted after it -- the shape trust's 6ba5324748 left -- VERIFIED",
            "",
            lambda t: _pinned_sibling(
                t, ["scripts/retired.sh"], after={"scripts/retired.sh": None}
            ),
            {"stats": {"pinned_verified": 1, "pinned_unverified": 0}},
        ),
        (
            "39b D1 `pinned` at a commit whose tree LACKS the path, though a "
            "later commit adds it: checked AT the pin, not anywhere in history",
            "D1 REF",
            lambda t: _pinned_sibling(
                t, ["scripts/other.sh"], after={"scripts/retired.sh": "x\n"}
            ),
        ),
        (
            "39c D1 `pinned` at a rev the (full) sibling does not have -- a typo "
            "in the commit the prose names -- is refused, not unverified",
            "D1 REF",
            lambda t: _git_sibling(t, ["scripts/retired.sh"], at="no-such-ay"),
        ),
        (
            "39c2 a foreign shallow marker cannot hide a nonexistent pin in a full sibling",
            "D1 REF",
            lambda t: _git_sibling(t, ["scripts/retired.sh"], at="no-such-ay"),
            {"env": _foreign_shallow_environment, "stats": {"pinned_unverified": 0}},
        ),
        (
            "39c3 a real historical pin still verifies under a foreign shallow marker",
            "",
            lambda t: _pinned_sibling(
                t, ["scripts/retired.sh"], after={"scripts/retired.sh": None}
            ),
            {"env": _foreign_shallow_environment,
             "stats": {"pinned_verified": 1, "pinned_unverified": 0}},
        ),
        (
            "39d D1 the paragraph citing a pinned path does not name the pin, so "
            "the prose sends a reader somewhere other than what was checked",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md", "reads at the sibling's `0123abc`",
                "reads on the sibling's main"),
        ),
        (
            "39i D1 the citing paragraph names a LONGER hex token that merely "
            "contains the pin -- a different commit, which a substring test "
            "passed -- is refused",
            "D1 REF",
            lambda t: _pinned_prose(t, lambda pin, full:
                                   pin + ("00" if not full.startswith(pin + "00") else "ff")),
        ),
        (
            "39j D1 FULL commit id and abbreviated marker name the SAME commit: VERIFIED",
            "",
            lambda t: _pinned_prose(t, lambda pin, full: full),
            {"stats": {"pinned_verified": 1, "pinned_unverified": 0}},
        ),
        (
            "39k D1 LONGER abbreviation of the SAME pinned commit: VERIFIED",
            "",
            lambda t: _pinned_prose(t, lambda pin, full: full[:12]),
            {"stats": {"pinned_verified": 1, "pinned_unverified": 0}},
        ),
        (
            "40 D1 an `absent` reason says the path is recoverable with `git "
            "show <rev>:<path>` and the commit holds that path -- GREEN",
            "",
            lambda t: _absent_recovery(t, "CLAUDE.md"),
        ),
        (
            "40b D1 an `absent` reason promises `git show <rev>:<path>` for a "
            "path that commit never held -- the exemption's only checkable "
            "part, and docs/archive/HANDOFF_STATUS.md named a commit this "
            "repository does not have",
            "D1 REF",
            lambda t: _absent_recovery(t, "docs/never-written.md"),
        ),
        (
            "40c D1 an `absent` reason names a commit this repository does not "
            "have -- 'added at <rev>' sends a reader nowhere",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`",
                "<!-- claim: absent docs/real.md retired; added at fedcba98765 -->\n"
                "See `docs/real.md`",
            ),
        ),
        (
            "40d D1 a `pinned` reason names a commit the (full) sibling does not "
            "have, beside a pin that resolves",
            "D1 REF",
            lambda t: (
                _sub(t, "CLAUDE.md", "main; read at the pin", "main after fedcba98765; read at the pin"),
                _pinned_sibling(t, ["scripts/retired.sh"], after={"scripts/retired.sh": None}),
            ),
        ),
        (
            "40e D1 a `pinned` reason that names the pin itself -- a commit the "
            "sibling has -- is VERIFIED (the control for 40d)",
            "",
            lambda t: (
                _sub(t, "CLAUDE.md", "main; read at the pin", "main; read at 0123abc"),
                _pinned_sibling(t, ["scripts/retired.sh"], after={"scripts/retired.sh": None}),
            ),
            {"stats": {"pinned_verified": 1, "pinned_unverified": 0}},
        ),
        (
            "41 D1 an `absent` for a path no citation in the doc reads is a dead "
            "declaration",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`",
                "<!-- claim: absent docs/never-cited.md retired 2026-08-26 -->\n"
                "See `docs/real.md`",
            ),
        ),
        (
            "41b D1 an `elsewhere` for a path no citation reads is a dead "
            "declaration, whatever the sibling holds",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`",
                "<!-- claim: elsewhere reports/never-cited.md trust the sibling -->\n"
                "See `docs/real.md`",
            ),
        ),
        (
            "41c D1 a `pinned` for a path no citation reads is a dead declaration "
            "-- it was never checked at all (verifier, 2026-09-24)",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`",
                "<!-- claim: pinned reports/never-cited.md ay 0123abc never cited -->\n"
                "See `docs/real.md`",
            ),
        ),
        (
            "41d D1 an `absent` whose ONLY citation is its own reason "
            "backticking the path is a dead declaration: a marker is not prose "
            "(verifier, 2026-09-24 -- PATH_TOKEN read marker text)",
            "D1 REF",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`",
                "<!-- claim: absent docs/never-cited.md retired; `docs/never-cited.md` "
                "was the old note -->\nSee `docs/real.md`",
            ),
        ),
        (
            "41e D1 the same reason backticking its path, beside a PROSE citation "
            "of it, is a live declaration -- GREEN (the control for 41d)",
            "",
            lambda t: _sub(
                t, "CLAUDE.md", "See `docs/real.md`",
                "The old note was `docs/gone.md`.\n"
                "<!-- claim: absent docs/gone.md retired; `docs/gone.md` was the old "
                "note -->\n\nSee `docs/real.md`",
            ),
        ),
        (
            "42 D1 the LINE citing an `absent` path names a commit this "
            "repository does not have -- DESIGN.md's `(commit fe4217c28)` shape",
            "D1 REF",
            lambda t: _absent_line(t, lambda head: "(commit fedcba98765)"),
        ),
        (
            "42b D1 the line citing an `absent` path names a commit this "
            "repository HAS -- GREEN (the control for 42)",
            "",
            lambda t: _absent_line(t, lambda head: "(commit %s)" % head),
        ),
        (
            "42c D1 the line attributes the commit to a SIBLING by name -- "
            "`read it at trust `<rev>`` is not a claim about this repository "
            "-- GREEN",
            "",
            lambda t: _absent_line(t, lambda head: "(read it at trust `fedcba98765`)"),
        ),
        (
            "42e D1 a commit the citing line ATTRIBUTES to a sibling that is on this "
            "box, and that the sibling does not have, is refused -- an attributed "
            "rev was stripped unchecked until verifier r7 (2026-09-24)",
            "D1 REF",
            lambda t: _absent_sibling_line(t, real=False),
        ),
        (
            "42f D1 the same attribution naming a commit the sibling HAS -- GREEN "
            "(the control for 42e)",
            "",
            lambda t: _absent_sibling_line(t, real=True),
        ),
        (
            "42g D1 the commit is on the NEXT LINE of the sentence citing the "
            "`absent` path -- the scope is the paragraph, not the physical line "
            "(verifier r7, 2026-09-24)",
            "D1 REF",
            lambda t: _absent_line(
                t, lambda head: "and its history\nis at (commit fedcba98765)"
            ),
        ),
        (
            "42h D1 a SEPARATE list item of the same paragraph names a commit this "
            "repository lacks -- it is its own block, and says nothing about the "
            "`absent` citation -- GREEN (the control for 42g; docs/GATE_REGISTRY.md's "
            "`blob 11cce7075` bullet)",
            "",
            lambda t: _absent_line(
                t, lambda head: "\n* another note, at trust `origin/main` `fedcba98765`"
            ),
        ),
        (
            "42i D1 the commit is on a wrapped line that STARTS WITH A YEAR "
            "(`2026. Its history ...`) -- not a list item, so still the citing "
            "paragraph (verifier r7b, 2026-09-24)",
            "D1 REF",
            lambda t: _absent_line(
                t, lambda head: "and was cut in\n2026. Its history is at (commit fedcba98765)"
            ),
        ),
        (
            "42j D1 a SEPARATE ordered item of a list the paragraph opens names a "
            "commit this repository lacks -- its own block -- GREEN (the control "
            "for 42i)",
            "",
            lambda t: _absent_line(
                t, lambda head: "\n1. a first step\n2. then trust `origin/main` `fedcba98765`"
            ),
        ),
        (
            "42d D1 the line citing an `absent` path promises `git show "
            "<rev>:<path>` for a path that commit never held",
            "D1 REF",
            lambda t: _absent_line(
                t, lambda head: "(recoverable with `git show %s:docs/never.md`)" % head
            ),
        ),
        (
            "39e D1 a DEAD `pinned`: the path resolves in THIS repo",
            "D1 REF",
            lambda t: (t / "scripts/retired.sh").write_text("#!/bin/sh\n"),
        ),
        (
            "39f D1 a `pinned` whose rev is a branch name is refused -- it would "
            "move under the citation",
            "D1 REF",
            lambda t: _sub(t, "CLAUDE.md", "ay 0123abc gone", "ay main gone"),
        ),
        (
            "39g D1 a SHALLOW sibling that does not carry the pin cannot answer: "
            "GREEN, but counted and named UNVERIFIED",
            "",
            lambda t: _pinned_sibling(
                t, ["scripts/retired.sh"], after={"scripts/retired.sh": None},
                shallow=True,
            ),
            {"stats": {"pinned_verified": 0, "pinned_unverified": 1}},
        ),
        (
            "39h D1 a `pinned` sibling absent from the box: GREEN, counted "
            "UNVERIFIED -- never folded into the pass",
            "",
            lambda t: None,
            {"stats": {"pinned_verified": 0, "pinned_unverified": 1}},
        ),
        (
            "38 D0 an IGNORED_ROOTS row the index tracks a path under is "
            "refused -- the row's premise is that nothing there is tracked",
            "D0 IGNORED",
            lambda t: (
                (t / "target").mkdir(),
                (t / "target/tracked.txt").write_text("x\n"),
                subprocess.run(
                    ["git", "-C", str(t), "add", "-f", "target/tracked.txt"],
                    env=_git_env(t),
                    check=True,
                ),
            ),
        ),
        # ── D6 BUDGET (2026-09-26) ──────────────────────────────────────
        # Two-way: one unit over refuses, exactly at the budget is GREEN, and
        # a rules file counts toward the same total -- the harness counts the
        # SET, so a check over CLAUDE.md alone would pass a tree it warns on.
        (
            "60 D6 CLAUDE.md one character past the instruction budget is refused",
            "D6 BUDGET",
            lambda t: _pad_instructions(t, INSTRUCTION_FILES_BUDGET + 1),
        ),
        (
            "60b D6 exactly AT the budget is GREEN, and the total is reported",
            "",
            lambda t: _pad_instructions(t, INSTRUCTION_FILES_BUDGET),
            {"stats": {"instruction_units": INSTRUCTION_FILES_BUDGET}},
        ),
        (
            "60c D6 a .claude/rules file counts toward the same total",
            "D6 BUDGET",
            lambda t: _pad_instructions(t, INSTRUCTION_FILES_BUDGET + 1, into_rules=True),
        ),
        (
            "60d D6 a character outside the BMP counts twice, as the harness "
            "counts it",
            "D6 BUDGET",
            lambda t: _pad_instructions(t, INSTRUCTION_FILES_BUDGET, astral=True),
        ),
        (
            "61 explicit Trust root selects a real repository outside the default layout",
            "",
            lambda t: _git_sibling(t, ["scripts/gone.sh"], at="configured-trust"),
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "configured-trust")},
             "stats": {"xrepo_verified": 1, "xrepo_unverified": 0}},
        ),
        (
            "61b a configured real repository missing the citation still refuses it",
            "D1 REF",
            lambda t: _git_sibling(t, ["scripts/other.sh"], at="configured-trust"),
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "configured-trust")}},
        ),
        (
            "61c an empty explicit root refuses instead of falling back",
            "D0 SIBLING",
            lambda t: _git_sibling(t, ["scripts/gone.sh"]),
            {"sibling_config": {"CLEAN_GATE_TRUST_REPO": ""}},
        ),
        (
            "61d a nonexistent explicit root refuses instead of becoming UNVERIFIED",
            "D0 SIBLING",
            lambda t: None,
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "missing")}},
        ),
        (
            "61e a file is not an explicit repository root",
            "D0 SIBLING",
            lambda t: None,
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "CLAUDE.md")}},
        ),
        (
            "61f a directory inside another repository is not an explicit root",
            "D0 SIBLING",
            lambda t: None,
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "docs")}},
        ),
        (
            "61g a symlink to an exact repository root selects its canonical path",
            "",
            lambda t: (_git_sibling(t, ["scripts/gone.sh"], at="configured-trust"),
                       (t / "trust-link").symlink_to(t / "configured-trust", target_is_directory=True)),
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "trust-link")},
             "stats": {"xrepo_verified": 1, "xrepo_unverified": 0}},
        ),
        (
            "61h leaked Git identity cannot counterfeit an explicit non-root",
            "D0 SIBLING",
            lambda t: None,
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "docs")},
             "env": lambda template, tmp: {"GIT_DIR": str(template / ".git")}},
        ),
        (
            "61i leaked Git identity cannot replace a configured sibling's history",
            "",
            lambda t: _git_sibling(t, ["scripts/gone.sh"],
                                   delete_from_worktree=["scripts/gone.sh"], at="configured-trust"),
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "configured-trust")},
             "env": lambda template, tmp: {"GIT_DIR": str(template / ".git")},
             "stats": {"xrepo_verified": 1, "xrepo_unverified": 0}},
        ),
        (
            "61j an explicit repository root preserves trailing whitespace bytes",
            "",
            lambda t: _git_sibling(t, ["scripts/gone.sh"], at="configured-trust \t\r\n"),
            {"sibling_config": lambda t: {"CLEAN_GATE_TRUST_REPO": str(t / "configured-trust \t\r\n")},
             "stats": {"xrepo_verified": 1, "xrepo_unverified": 0}},
        ),
        (
            "61k a whitespace-suffixed directory within a repository is not its root",
            "D0 SIBLING",
            lambda t: (_git_sibling(t, ["scripts/gone.sh"], at="configured-trust"),
                       (t / "configured-trust" / "child \t\r\n").mkdir()),
            {"sibling_config": lambda t: {
                "CLEAN_GATE_TRUST_REPO": str(t / "configured-trust" / "child \t\r\n")}},
        ),
    ]
    # Every supported key must select its own root and reject an empty value;
    # testing only Trust would leave a misspelled less-used variable unchecked.
    for repo, variable in (
        ("trust", "CLEAN_GATE_TRUST_REPO"),
        ("ay", "CLEAN_GATE_AY_REPO"),
        ("zani", "CLEAN_GATE_ZANI_REPO"),
        ("gamma-crown", "CLEAN_GATE_GAMMA_CROWN_REPO"),
    ):
        arms.append((
            "62 %s selects the %s sibling" % (variable, repo), "",
            lambda t, repo=repo: _git_sibling(t, ["scripts/gone.sh"], at="configured-" + repo),
            {"sibling_config": lambda t, variable=variable, repo=repo: {
                variable: str(t / ("configured-" + repo))},
             "selected_repo": repo, "governed": (("docs/real.md", ()),)},
        ))
        arms.append((
            "62b %s refuses an empty explicit value" % variable, "D0 SIBLING",
            lambda t: None, {"sibling_config": {variable: ""}},
        ))

    failed = 0
    # The fixture is built ONCE and copied per arm. It is a git repository now,
    # and `git init` + `git add` cost ~20 ms each through the Apple git shim
    # (measured: `git --version` alone is 20 ms); paying that per arm took the
    # selftest from 0.37 s to 6.3 s wall. A copy of a dozen-file `.git` is
    # sub-millisecond and the index it carries is relative, so it moves.
    template = Path(tempfile.mkdtemp(prefix="doc-claims-template-"))
    try:
        _fixture(template)
        for arm in arms:
            failed += _run_arm(template, arm)
    finally:
        shutil.rmtree(template, ignore_errors=True)
    print("DOC_CLAIMS_SELFTEST arms=%d failed=%d" % (len(arms), failed))
    return 1 if failed else 0


def _run_arm(template: Path, arm) -> int:
    """One arm on a fresh copy of the fixture; 1 if it failed, else 0."""
    name, expect, mutate = arm[0], arm[1], arm[2]
    opts = arm[3] if len(arm) > 3 else {}
    failed = 0
    tmp = Path(tempfile.mkdtemp(prefix="doc-claims-"))
    # An arm may LEAK environment into the check -- the way git's own hooks
    # do -- and the leak is undone whatever the arm did. The fixture's own git
    # calls pass an explicit env, so the leak reaches only the code under test.
    # A callable patch sees (template, tmp) AFTER the mutation, so it can name
    # a repository the mutation built.
    patch = opts.get("env")
    saved = {}
    try:
        shutil.copytree(template, tmp, symlinks=True, dirs_exist_ok=True)
        mutate(tmp)
        patch = patch(template, tmp) if callable(patch) else (patch or {})
        saved = {k: os.environ.get(k) for k in patch}
        os.environ.update(patch)
        config = opts.get("sibling_config")
        config = config(tmp) if callable(config) else config
        if "selected_repo" in opts:
            repo = opts["selected_repo"]
            selected = selected_siblings(config, defaults={})
            if selected.get(repo) != (tmp / ("configured-" + repo)).resolve():
                failed += 1
                print("  ARM SELECTION %s: wrong repository selected" % name)
        try:
            problems, stats = _run(tmp, governed=opts.get("governed"), sibling_config=config)
        except ValueError as exc:
            problems, stats = [Problem("D0 SIBLING: " + str(exc))], {}
        got = [p for p in problems]
        for key, want in opts.get("stats", {}).items():
            if stats.get(key) != want:
                failed += 1
                print(
                    "  ARM STAT %s: %s = %r, expected %r"
                    % (name, key, stats.get(key), want)
                )
        if expect == "":
            if got:
                failed += 1
                print("  ARM RED (expected green) %s: %s" % (name, got[0]))
        elif not any(p.startswith(expect) for p in got):
            failed += 1
            print(
                "  ARM GREEN (expected %s) %s: %s"
                % (expect, name, got[0] if got else "<no problem reported>")
            )
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        shutil.rmtree(tmp, ignore_errors=True)
    return failed


def _sub(tmp: Path, rel: str, old: str, new: str):
    p = tmp / rel
    text = p.read_text()
    if text.count(old) != 1:
        raise AssertionError(
            "selftest anchor %r occurs %d times in %s, not once"
            % (old, text.count(old), rel)
        )
    p.write_text(text.replace(old, new))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--selftest", action="store_true", help="mutation arms on a fixture")
    ap.add_argument("--list", action="store_true", help="print the governed set")
    ap.epilog = "Sibling roots may be set with " + ", ".join(SIBLING_ENV.values()) + "."
    args = ap.parse_args()
    try:
        siblings = selected_siblings()
    except ValueError as exc:
        ap.error(str(exc))

    if args.selftest:
        return selftest()

    if args.list:
        print("%-28s %s" % ("DOC", "RULES (figure is always on)"))
        for rel, rules in GOVERNED:
            print("%-28s %s" % (rel, ", ".join(rules) if rules else "figure only"))
        return 0

    # The self-test runs first on every invocation, for the reason the
    # gate-registry and add-decl legs do: a demonstrator whose falsifiability is
    # only checked when somebody remembers is the artifact this repo keeps
    # finding shipped.
    if selftest() != 0:
        print("DOC_CLAIMS=fail its own arms no longer fire", file=sys.stderr)
        return 1

    print("DOC_CLAIMS_REPOSITORIES " + " ".join(
        "%s=%s" % (repo, path) for repo, path in siblings.items()))
    problems, stats = check(ROOT, siblings=siblings)

    # Named BEFORE the verdict and on stderr in both branches: a cross-repo
    # citation this box could not check is neither a pass nor a failure, and
    # the one thing it must never do is print like a pass.
    for rel, cited, how, repo, detail in stats["unverified"]:
        print(
            "  DOC_CLAIMS UNVERIFIED: %s cites `%s` %s in %r and it "
            "was NOT checked -- %s." % (rel, cited, how, repo, detail),
            file=sys.stderr,
        )

    if problems:
        print(
            "DOC_CLAIMS=fail docs=%d problems=%d" % (stats["docs"], len(problems)),
            file=sys.stderr,
        )
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    print(
        "DOC_CLAIMS=ok docs=%d rooted-paths=%d based=%d cross-repo=%d "
        "(%d verified, %d unverified) pinned=%d (%d verified, %d unverified) "
        "bound-figures=%d figure-paragraphs=%d line-anchors=%d "
        "instruction-chars=%d/%d"
        % (
            stats["docs"],
            stats["paths"],
            stats["based"],
            stats["xrepo_verified"] + stats["xrepo_unverified"],
            stats["xrepo_verified"],
            stats["xrepo_unverified"],
            stats["pinned_verified"] + stats["pinned_unverified"],
            stats["pinned_verified"],
            stats["pinned_unverified"],
            stats["bound"],
            stats["figures"],
            stats["anchors"],
            stats["instruction_units"],
            INSTRUCTION_FILES_BUDGET,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
