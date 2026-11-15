#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The gate that gates the gates: every enforcement artifact is wired, and can fail.

WHY THIS EXISTS
---------------
Six times in one week an invariant was asserted in this repo where nothing
re-derived it, and each was found and fixed as an INSTANCE:

  1. `add_decl_structural` / `add_decl_unchecked` -- a first-class CLAUDE.md
     soundness rule that two gates "enforced" by reading a JSON file against
     itself. A planted bypass left every cheap gate byte-identical.
  2. `scripts/crystal_fixture_freshness.py` -- existed, wired into NOTHING; the
     fixtures had been stale for days.
  3. `gate::srcelab` -- recorded `skipped:no-binary` as GREEN. A gate that
     measured nothing reported a pass.
  4. Four crystal perturbation batteries -- silently vacuous, because `|| exit 9`
     was bound to a function DEFINITION, so a failed substitution never aborted.
  5. `scripts/seal_driver.sh guard` -- tested only for the literal string `FAIL`,
     so an ABSENT verdict passed.
  6. `premise_witness_gate` -- chains registering a reflected type and an
     `Encodes*` premise with nobody inhabiting it, caught hours later at a
     separate suite row, for the third time.

Every one of those was repaired. Nothing stopped number seven, because the
class was never named: **an enforcement artifact has two independent ways to be
worthless, and this repo checked neither.**

  * It can be UNWIRED -- it exists, it is maintained-looking, and no runner
    invokes it. Instance 2. Measured again while building this file:
    `scripts/check_constructive_ratchet.py` is invoked by no runner in the tree.
  * It can be UNFALSIFIABLE -- it runs, it prints a verdict, and no mutation has
    ever made it say no. Instances 1, 3, 4, 5. A gate nobody has seen fail is
    indistinguishable from `exit 0`.

So the registry is data (`data/gate_registry.json`), the demonstrations are
EXECUTABLE data (`data/gate_demonstrations.json`), and this checker refuses when:

  R1 SHAPE       a row is malformed, or names a path that does not exist.
  R2 INVENTORY   a gate-shaped file in the tree has no registry row, or a row
                 points at a file that is gone.  <-- this is the clause that
                 stops number seven: a new `check_*` is a BUILD ERROR until
                 somebody classifies it.
  R3 WIRED       a row of kind `gate` has no runner, or its re-derived runner
                 set disagrees with the declared one (a deleted runner is RED),
                 or a row declared unwired is in fact invoked by a runner.
  R4 DEMO        a row that claims `soundness`, or is a `battery`, has no
                 demonstrated failure and no unexpired waiver.
  R5 EVIDENCE    a demonstration names a `--selftest` the script does not have,
                 a self-test file that does not exist or that the self-test
                 suite does not run, or a record that never mentions the gate.
  R6 IDS         the `leg` rows are exactly local_gate.sh's `# GATE-LEG:` ids and
                 the `suite-row` rows are exactly verify_runner.py's `gate::*`
                 plan ids.
  R7 FRESH       a demonstration is pinned to the sha256 of the file it
                 demonstrated -- the row's `path`, or for a `leg`/`suite-row`
                 the `implemented_by` where the gate actually lives. Gut the
                 implementation, keep the badge -> RED. This is the half a
                 dated note in a header can never do. A row may DELEGATE its
                 pin with `inherited_from`, and only to a row that pins the
                 very same file. A pin must be the one its last `--repin`
                 replay recorded (`replayed`); a row pinning derived inputs
                 must carry that record.
  R8 RETIRED     a `retired` entry still has its file in the tree, or names a
                 successor that does not exist / is itself unwired.
  R10 PUSHED     R7, re-derived over the COMMIT BEING PUSHED rather than over
                 the working tree. Only active when the pre-push hook exports
                 CLEAN_PUSH_RANGES; see the block above `check_pushed_tips`.

THREAT MODEL
------------
These rules defend against ACCIDENTAL regressions -- a forgotten row, an
unpinned input, a pin moved by hand or by a half-taken merge -- not against a
script written to forge the registry. docs/GATE_REGISTRY.md#threat-model
records what is out of model.

NOTES STATE NO ARM COUNTS
-------------------------
A row's arm count is a fact of data/gate_demonstrations.json, and `--list`
prints it from there (the ARMS column). Until verifier r7b (2026-09-24) notes
typed it and a rule (R13 ARM COUNT) compared the typed number with the record;
every revision of that rule missed a spelling ('two replayed arms', "Inherits
X's N arms"), so the counts were taken out of the notes and the rule deleted.

RETIREMENT IS A RECORD, NOT A DELETION
--------------------------------------
Deleting a gate deletes the ANSWER with it: six months later nobody can tell
whether the property stopped mattering or the file just went missing. So the
registry carries a `retired` list, and R8 makes the claim it records
falsifiable rather than decorative:

  * the retired `path` must be GONE. A file that is "retired" but still sitting
    in `scripts/` is one somebody will run and believe -- both prover audits
    exited 1 at HEAD for two months in exactly that state.
  * `superseded_by` must name LIVE, WIRED registry rows. This is the clause
    that stops the trap this repo actually walked into:
    `prover_phase_0_audit.sh` duplicated `check_constructive_ratchet.py`, which
    was ITSELF an orphan, so "the property is enforced elsewhere" was true of a
    gate nothing ran. You cannot retire a gate onto another orphan.
  * a retirement that supersedes NOTHING must say `enforces_nothing: true` out
    loud, which is a reviewable sentence rather than a silent `git rm`.

WIRING, RE-DERIVED AND NOT TRUSTED
----------------------------------
`wired_by` in the registry is an EXPECTATION. The checker computes the actual
runner set by parsing the runner roots (`scripts/local_gate.sh`,
`scripts/githooks/pre-push`, `scripts/verify_runner.py`, `Justfile`) plus every
file any row declares, and requires equality. Reading the declaration and
printing it back is the exact failure mode this file exists to end.

The scan is bounded to those files on purpose: it is a registry read plus ~30
small files, which is milliseconds, so this runs in the pre-push hook. The
expensive direction (does some file somewhere mention this script?) is not
needed -- an un-runner-ed gate must be classified `battery`/`tool` in the
registry, and R3 re-checks that classification against the roots.

DEMONSTRATIONS ARE REPLAYED, NOT CITED -- IN A SANDBOX
------------------------------------------------------
`--demonstrate` applies each recorded mutation, runs the real gate, and requires
a non-zero exit and the recorded diagnostic. A demonstration in this repo is
therefore a thing that RUNS, not a sentence in a header that was true once.

It no longer runs in THIS checkout. Until 2026-08-30 the mutation was planted
here -- a real defect in a tracked file, for 0.2 s on a python ratchet and for
2383 s on the everyday-battery arm -- and several lanes commit to this tree at
once, so for that window the plant was indistinguishable from a real defect to
anybody who ran a gate, staged a file or read `git status`. It had already
produced a false RED in a co-tenant-visible hook run. The mutation now lands in
a per-invocation sandbox assembled from the WORKING TREE (clonefile copies,
symlinked member crates, cloned .git, and -- since 2026-09-15 -- a cargo target
dir of its OWN under this tree's `target/`, never the shared one), the arm's
bytes and the gate's own script are re-hashed against this tree before the arm
runs, and the shared tree's status and digests are re-measured after it. See
the block above `_clone_tree` for why that is still the REAL gate, what it does
not cover, and why a compiling arm now pays one cold build the first time.

WIRING IS RE-DERIVED LOOSELY, AND THAT IS MEASURED
--------------------------------------------------
R3's scan asks "does this file RUN that script?" and answers it from a path in
a non-prose line. In a shell file that is exactly right. In a .py file it is
not: an ordinary DATA string carrying a path reads as an invocation, and three
of R3's live edges are exactly that (a `"wired_by"` value inside an artifact a
script EMITS, a `mint_command=` recorded for a human, prose inside an emitted
artifact). Tightening it also challenges the registry's own `wired_by`, which
today means "mentions", not "runs".

So the discriminator is landed REPORTING-ONLY, under `--wiring-audit`: it is
unreachable from `check()`, the gate's verdict and output are unchanged byte
for byte, and the true/false edge sets are measured across every row first.
See `docs/issues/2026-08-27-gate-registry-wiring-scan-counts-data-strings.md`
for the three-step order, and the block above `EXEC_CTX` for the rule.

Usage:
    scripts/check_gate_registry.py                 # check (fail-closed, ~ms)
    scripts/check_gate_registry.py --selftest      # mutation arms on itself; the
                                                   # count is the live arms=N line
    scripts/check_gate_registry.py --list          # the registry, as a table
    scripts/check_gate_registry.py --demonstrate   # replay every recorded arm
    scripts/check_gate_registry.py --demonstrate <id>
    scripts/check_gate_registry.py --demonstrate <id> --keep-sandbox
    scripts/check_gate_registry.py --repin <id>    # runs/replays the demonstration,
                                                   # moves the pin only if it is green
    scripts/check_gate_registry.py --repin-undemonstrated <id>  # an owned, expiring
                                                   # account for a row nothing can replay
    scripts/check_gate_registry.py --wiring-audit  # REPORTING ONLY, always 0
    scripts/check_gate_registry.py --wiring-audit --wiring-audit-out <path>
"""

from __future__ import annotations

import argparse
import ast
import contextlib
import fnmatch
import hashlib
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import types
from datetime import date, timedelta
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "data/gate_registry.json"
DEMOS = ROOT / "data/gate_demonstrations.json"

# Execute the declared helper source; ignored bytecode is not an input.
_transport = types.ModuleType("gate_registry_resource_transport")
_transport.__file__ = str(ROOT / "scripts/resource_transport.py")
exec(compile(Path(_transport.__file__).read_bytes(), _transport.__file__, "exec",
             dont_inherit=True), _transport.__dict__)

LOCAL_GATE = "scripts/local_gate.sh"
HOOK = "scripts/githooks/pre-push"
VERIFY_RUNNER = "scripts/verify_runner.py"
JUSTFILE = "Justfile"
RUNNER_ROOTS = (LOCAL_GATE, HOOK, VERIFY_RUNNER, JUSTFILE)

KINDS = ("gate", "leg", "suite-row", "battery", "tool")
CLAIMS = ("soundness", "quality", "hygiene", "evidence", "none")
DEMO_KINDS = ("selftest-inline", "selftest-file", "mutation-record")
STRONG = ("selftest-inline", "selftest-file")

# A file under scripts/ whose name matches any of these is gate-shaped: it must
# have a registry row. The patterns are deliberately broad -- a false positive
# costs one `tool` row with a reason, a false negative costs instance number
# seven. `test_*` is excluded: those are the self-tests, and the suite that runs
# them (scripts/check_script_selftests.sh) is itself a registry row.
GATE_SHAPED = (
    re.compile(r"^scripts/(?:.+/)?check_[A-Za-z0-9_.-]+\.(?:py|sh)$"),
    re.compile(r"^scripts/(?:.+/)?[A-Za-z0-9_.-]*_gate\.(?:py|sh)$"),
    re.compile(r"^scripts/(?:.+/)?[A-Za-z0-9_.-]*ratchet[A-Za-z0-9_.-]*\.(?:py|sh)$"),
    re.compile(r"^scripts/(?:.+/)?[A-Za-z0-9_.-]*census[A-Za-z0-9_.-]*\.(?:py|sh)$"),
    re.compile(r"^scripts/(?:.+/)?crystal_perturb_[A-Za-z0-9_.-]+\.sh$"),
    # ADDED 2026-08-24, after the widened scan found live artifacts the five
    # patterns above could not see. `scripts/axiom_audit_release_check.sh` is a
    # fail-closed release gate on the AXIOM CENSUS, reached through the `clean`
    # CLI exactly the way `kernel_soundness_gate.sh` is -- and it had no row,
    # because its name carries neither `check_` as a PREFIX nor `_gate.` as a
    # suffix. `scripts/audits/prover_phase_0_audit.sh` and
    # `prover_building_clean_audit.sh` were ratchets that `exit $status` on a
    # regression, invoked by nothing, and both exited 1 at HEAD -- RETIRED
    # 2026-08-25 (see the `retired` list and R8; the pattern stays, because it
    # is what found them). The `check_` pattern is anchored at the start of the
    # basename, so every `*_check.(py|sh)` in the tree was invisible to it for
    # the same reason.
    re.compile(r"^scripts/(?:.+/)?[A-Za-z0-9_.-]*audit[A-Za-z0-9_.-]*\.(?:py|sh)$"),
    re.compile(r"^scripts/(?:.+/)?[A-Za-z0-9_.-]*_check\.(?:py|sh)$"),
)
GATE_SHAPED_EXCLUDE = re.compile(r"^scripts/(?:.+/)?test_[A-Za-z0-9_.-]+\.(?:py|sh)$")

# ── THE SHAPE THE NAME PATTERNS CANNOT SEE: an artifact GENERATOR ────────────
#
# Every pattern above matches a BASENAME, and the defect this rule was written
# for has no name in common: a script that MINTS a committed artifact and
# carries a `--check` that re-derives it. Such a script IS an enforcement
# artifact -- it is the only thing that can say the committed file is stale --
# and four of them were found unregistered and unwired in one pass on
# 2026-09-14, of which two were RED at HEAD and one had been stale for twenty
# days and one for forty-six. None matched a pattern above; none was run by the
# enforcement path, so the "anything the gate actually runs" union could not see
# them either. A generator nobody re-runs is exactly how a derived artifact
# rots, and the rot is invisible by construction.
#
# The rule is stated over what makes such a script an ARTIFACT rather than a
# helper: it accepts `--check` AND it names a tracked artifact under data/,
# docs/, tests/ or reports/. Package MEMBERS are excluded -- a directory with an
# `__init__.py` is a library whose entry point is covered by the wrapper that
# imports it (scripts/axiom_audit/ is the standing example, already documented
# under GATE_SHAPED_PACKAGE). A false positive costs one `tool` row with a
# reason, which is the registry's whole point; a false negative costs another
# forty-six days.
GENERATOR_CHECK_FLAG = re.compile(r"--check\b")
GENERATOR_ARTIFACT = re.compile(
    r"""["'](?:data|docs|tests|reports)/[A-Za-z0-9_./-]+\.(?:json|md|txt)"""
)


def _mints_and_checks_a_tracked_artifact(root: Path, rel: str) -> bool:
    if not rel.endswith((".py", ".sh")):
        return False
    path = root / rel
    if (path.parent / "__init__.py").is_file():
        return False
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return False
    return bool(GENERATOR_CHECK_FLAG.search(text)) and bool(GENERATOR_ARTIFACT.search(text))

# A gate does not have to be a FILE. `scripts/masquerade_gate/` was a five-file
# Python PACKAGE -- `__main__.py`, `constants.py`, `detect.py`, `parser.py`,
# `staging.py` -- carrying a soundness detector, and every one of the seven
# patterns above missed it, because they all match a BASENAME and not one of
# those basenames is gate-shaped. It sat unregistered and unrun from the day it
# was ported until 2026-08-25 (retired that day; see the `retired` list).
#
# The rule is stated over what makes a package an ARTIFACT rather than a
# library: a `__main__.py`, i.e. `python3 -m scripts.<name>` runs it. That is
# the distinction that keeps `scripts/axiom_audit/` out -- it has an
# `__init__.py` and no `__main__.py`, is not independently runnable, and is
# already covered as the implementation of two registered shell wrappers.
GATE_SHAPED_PACKAGE = re.compile(
    r"^(?:check_[A-Za-z0-9_.-]+"
    r"|[A-Za-z0-9_.-]*_gate"
    r"|[A-Za-z0-9_.-]*ratchet[A-Za-z0-9_.-]*"
    r"|[A-Za-z0-9_.-]*census[A-Za-z0-9_.-]*"
    r"|[A-Za-z0-9_.-]*audit[A-Za-z0-9_.-]*"
    r"|[A-Za-z0-9_.-]*_check)$"
)

# ── R9 SCANNER: "a line count is not a measurement" ──────────────────────────
#
# Two months apart, two repo-wide scanners in this tree decided a soundness
# question by matching RAW SOURCE TEXT and counting the hits. Both were wrong in
# the SAME direction, and the direction is what makes this a rule rather than a
# bug report:
#
#   * `prover_phase_0_audit.sh` (retired 2026-08-25, see the `retired` list)
#     read `grep -rhE 'add_decl_(structural|unchecked)' crates/ | wc -l` as a
#     bypass census. Of the 722 lines it counted, 353 were COMMENTS. The commit
#     that ADDED the add_decl accounting and its `// SOUNDNESS:` comment moved
#     the count 716 -> 722: the ratchet read a soundness FIX as a soundness
#     REGRESSION.
#   * `check_extend_constants_ratchet.py`, `check_trust_verdict_emitters.py` and
#     `crates/clean-elab/src/tactic/tests/bypass_ratchet.rs` had the same defect
#     latent (measured 2026-08-25, lane ANTICORR): each turned RED on a
#     `// SOUNDNESS:` comment that merely NAMED the call it promised not to
#     make. The gate's own remediation text asked for that comment.
#
# The common shape is not "grep" and not "count" -- it is deciding a question
# about CODE from text that includes PROSE. So the rule is stated over the thing
# a scanner can actually re-derive: a row whose implementation READS Rust or
# Lean source must say, in `source_scan.kind`, how it reads it.
#
#   "lexed"      comments and string/char-literal bodies are blanked before
#                matching. Re-derived: the implementation must contain a
#                recognised stripper, or the declaration is a lie.
#   "raw-lines"  it matches the raw text, prose included. Permitted -- and
#                REFUSED for a `soundness` row. A soundness verdict may not
#                come from a line count.
#   "digest"     it reads source but its verdict is not a text match at all
#                (a tree hash, a brace-matched extraction, a parse). The escape
#                hatch, and it is written down with a note saying which.
#
# The point is visibility: the next one is legible when it LANDS, not two
# months later when somebody finally decomposes the number.
SOURCE_SCAN_KINDS = ("lexed", "raw-lines", "digest")

# An implementation that reads Rust/Lean SOURCE files.
#
# The last three alternatives are 2026-08-25 (lane LOOSE). R9 could not see a
# RUST battery that walks the tree with its OWN recursor: crates/clean-auto/
# tests/expr_let_constructor_hygiene.rs reads every `.rs` under src/ and tests/
# via a hand-rolled `collect_rust_files` + `path.extension() == Some("rs")`, and
# R9 reported it as "no longer reads source" -- i.e. a source-reading gate that
# could have declared nothing. The blind spot was shaped exactly like the one
# R9 exists to close: the detector recognised the SHARED helper and the shell
# form, and missed the open-coded one.
#
# Every open-coded `.rs` walker in the tree spells the extension test
# differently -- `path.extension() == Some("rs")`,
# `path.extension().is_some_and(|e| e == "rs")`, `file_name.ends_with(".rs")` --
# so all three forms are listed. A FALSE POSITIVE here costs one row a
# `source_scan` declaration it did not need; a false negative costs instance
# number eight. It is the cheap direction, deliberately.
READS_SOURCE = re.compile(
    r"""rglob\(\s*["'][^"']*\.(?:rs|lean)["']\)"""
    r"""|glob\(\s*["'][^"']*\.(?:rs|lean)["']\)"""
    r"""|collect_rust_source_files"""
    r"""|--include=['"]?\*\.(?:rs|lean)"""
    r"""|git grep[^\n]*'\*\.(?:rs|lean)'"""
    r"""|grep\s+-[A-Za-z]*r[A-Za-z]*\s[^\n|]*(?:crates/|\.rs\b)"""
    r"""|collect_rust_files"""
    r"""|extension\(\)[^\n]*Some\(&?["'](?:rs|lean)["']\)"""
    r"""|read_to_string\([^\n]*\.(?:rs|lean)["']"""
    r"""|ends_with\(\s*["']\.(?:rs|lean)["']\s*\)"""
    r"""|==\s*["'](?:rs|lean)["']"""
    # Instance eight after all (audit r2 M-1, wf_0a50b8bb): a DATA-DRIVEN
    # source reader -- crystal_a0_census's clause_b_theorem_registered opens
    # repo files whose .rs paths live in the discharge TABLE, so no literal
    # extension appears anywhere near the open() and every pattern above
    # missed it. `open(os.path.join(repo_root, ...))` is the shape: joining a
    # caller-supplied relative path onto the repo root and reading it is a
    # source read whichever table named the path. Cheap direction, as the
    # header says: a false positive only obliges a declaration.
    r"""|os\.path\.join\(\s*(?:repo_)?root\s*,"""
    # Item 17 review (2026-10-27): a MANIFEST-driven Lean reader. The tactic
    # family minter opens the fixture files a MANIFEST names and blanks their
    # comments with lean_suite_conformance's Lean lexer; no extension literal
    # appears near the read. Calling the Lean blanker is the evidence.
    r"""|blank_noncode_lean\("""
)

# Rust COMMENT spans, for `script_code_only` below: block comments (with their
# string-literal bodies) and line comments, blanked so line geometry survives.
#
# COMMENTS ONLY, and that is deliberate (lane LOOSE, 2026-08-25). The first cut
# blanked string literals too and made things WORSE, not better: every
# open-coded `.rs` walker identifies itself by a string literal --
# `path.extension() == Some("rs")`, `file_name.ends_with(".rs")` -- so blanking
# strings deleted the only evidence that the file reads source, and R9 reported
# two freshly-fixed Rust scanners as "no longer reads source". This mirrors the
# .py/.sh treatment exactly, where docstrings (prose) are blanked and inline
# string literals are kept. The rule being enforced is "do not read PROSE as
# code"; a string literal in an expression is code.
RUST_COMMENT_RE = re.compile(r"/\*.*?\*/|//[^\n]*", re.DOTALL)

# A recognised comment/literal stripper. Adding a new one here is a deliberate
# act: it is the list that decides whether `kind: "lexed"` is true.
# `code_before_line_comment` was REMOVED from this list on 2026-08-25 (lane
# LOOSE) and then deleted from the tree. It was a `line.split("//").next()`
# one-liner: it does not see block comments, it does not see string literals,
# and it TRUNCATES the line at the first `//` anywhere -- including inside a
# string -- so it also hid real calls. Accepting its name as evidence of
# `kind: "lexed"` would have let R9 certify exactly the defect R9 exists to
# find. Adding a name here is a deliberate act; it is the list that decides
# whether `kind: "lexed"` is TRUE.
STRIPS_NONCODE = re.compile(
    r"strip_noncode|strip_code\(|strip_comments|blank_noncode|production_code_lines"
    r"|NONCODE_RE|strip_cfg_test_blocks|cfg_test_mod_line_ranges"
    # audit r2 M-1: crystal_a0_census's comment-only lexer. Deliberately a
    # COMMENT-only blank (string literals kept -- the clause-(b) registration
    # convention carries the spec source inside them), which is still a lex,
    # not a raw-text match.
    r"|_blank_comments|_COMMENT_RE"
)


# A recognised stripper USED in code -- called, or read as an attribute (`strip_noncode(text)`,
# `NONCODE_RE.sub(..)`) -- never only its `def`, `class` or a bare mention.
_STRIPPER_USE = re.compile(
    r"(?<!\w)(?<!def )(?<!class )(?:" + STRIPS_NONCODE.pattern.replace(r"strip_code\(", "strip_code")
    + r")\w*(?=\s*[(.])")


def _lexes_through(root: Path, rel: str) -> str:
    """The input `rel` lexes through, or "" (R9; see its use): one it derives
    (`--pinned-inputs`, the set R7 pins) that its own CODE names by file name
    and whose CODE uses a recognised stripper (`_STRIPPER_USE`).

    Both halves since 2026-11-01's review. The first cut took the first
    derived input whose code held a stripper's NAME, and the reference lexer
    (scripts/check_add_decl_ratchet.py, which defines `strip_noncode`) sorts
    first among check_test_target_coverage's inputs: any gate that merely
    pinned the lexer passed, whatever its walker did with the text. Arms 25d
    and 25e pin both halves."""
    if not rel or not _answers_pinned_inputs(root, rel):
        return ""
    derived, _why = _derived_inputs(root, rel)
    own = script_code_only(rel, _read(root, rel))
    for inp in sorted(derived or ()):
        if inp != rel and inp.endswith((".py", ".sh", ".rs")) and Path(inp).name in own \
                and _STRIPPER_USE.search(script_code_only(inp, _read(root, inp))):
            return inp
    return ""


def script_code_only(rel: str, text: str) -> str:
    """The EXECUTABLE half of a .py/.sh file: `#` comments and Python
    docstrings blanked, line geometry preserved.

    R9's own detector needs this, and finding that out was the joke of the
    lane: the first cut of READS_SOURCE matched the PROSE in the paragraph
    above -- which quotes `grep -rhE ... crates/` while explaining why counting
    prose is wrong -- and duly reported that this file scans Rust source. A
    rule against reading prose as code cannot itself read prose as code.
    """
    if rel.endswith((".rs", ".lean")):
        # 2026-08-25 (lane LOOSE). Rust rows used to reach the detectors as RAW
        # TEXT -- so a doc comment naming `collect_rust_source_files`, or a
        # `// SOUNDNESS:`-style note naming a stripper, decided an R9 verdict.
        # A rule against reading prose as code may not read prose as code, and
        # that applies to the Rust rows too, not only to the .py/.sh ones.
        # Comments only: see RUST_COMMENT_RE for why string literals stay.
        return RUST_COMMENT_RE.sub(
            lambda m: "".join("\n" if ch == "\n" else " " for ch in m.group(0)),
            text,
        )
    out: list[str] = []
    in_block = ""
    is_py = rel.endswith(".py")
    for line in text.splitlines():
        rest = line
        if is_py:
            if in_block:
                idx = rest.find(in_block)
                if idx < 0:
                    out.append("")
                    continue
                rest = rest[idx + 3:]
                in_block = ""
            scan, offset = rest, 0
            while True:
                hits = [(scan.find(q), q) for q in (chr(34) * 3, chr(39) * 3) if scan.find(q) >= 0]
                if not hits:
                    break
                pos, q = min(hits)
                after = scan[pos + 3:]
                close = after.find(q)
                if close >= 0:
                    scan = after[close + 3:]
                    offset += pos + 3 + close + 3
                    continue
                in_block = q
                rest = rest[: offset + pos]
                break
        stripped = rest.lstrip()
        if stripped.startswith("#"):
            out.append("")
            continue
        hash_at = rest.find(" #")
        if hash_at >= 0:
            rest = rest[:hash_at]
        out.append(rest)
    return "\n".join(out)

# An invocation of a repo script, as it appears in a runner. Deliberately loose
# on the launcher (bash/python3/$PY/$GATE_PYTHON/timeout/bare) and on the path
# prefix ($REPO_ROOT/, ./, bare), because every one of those forms is in use.
INVOCATION = re.compile(
    r"""(?:^|[\s;&|(`"'=])
        (?:bash|sh|python3(?:\.\d+)?|python|exec|timeout\s+\S+|
           \$GATE_PYTHON|\$\{GATE_PYTHON\}|\$PY|\$\{PY\}|\$PYTHON|\$\{PYTHON\})?
        \s*["']?(?:\./)?(?:\$\{?(?:REPO_ROOT|ROOT|REPO)\}?/)?
        (scripts/[A-Za-z0-9_./-]+\.(?:sh|py))""",
    re.VERBOSE,
)
GATE_LEG = re.compile(r"^\s*#\s*GATE-LEG:\s*(\S+)\s*$")
SUITE_ROW = re.compile(r'^\s*"id":\s*"(gate::[A-Za-z0-9_.:-]+)"')
ISO = re.compile(r"^\d{4}-\d{2}-\d{2}$")


class Red(Exception):
    """A refusal. Carries the actionable diagnostic and nothing else."""


def _resource_fds(env: dict[str, str]) -> tuple[int, ...]:
    """Transport live descriptors; native owners still authenticate authority."""
    try:
        return _transport.resource_fds(env)
    except RuntimeError as exc:
        raise Red(f"resource transport refused: {exc}") from exc


# ── reading ──────────────────────────────────────────────────────────────────


def _read(root: Path, rel: str) -> str:
    p = root / rel
    try:
        return p.read_text(errors="replace")
    except OSError:
        return ""


def _sha256(root: Path, rel: str) -> str:
    p = root / rel
    try:
        return hashlib.sha256(p.read_bytes()).hexdigest()
    except OSError:
        return ""


# -- R7 over a DERIVED input set (verifier r8b, 2026-09-25) --------------------
#
# R7 pinned ONE file per row: its `path` or `implemented_by`. That is the whole
# decision procedure for most gates. It was not for `check_lint_coverage`: that
# check RUNS the crystal-A2 projector's tests and lint, so the projector's
# source is as much the gate as the script -- and once the retired
# `crystal-a2-project` row stopped pinning it, deleting a projector mechanism
# TOGETHER WITH its test left GATE_REGISTRY=ok, because the arms naming that
# test re-run only when the row's pin moves. Listing the extra files here would
# be the same hole one file later. So a subject that DERIVES the files its
# verdict depends on declares it -- a line `ANSWERS_PINNED_INPUTS = True` at
# the top level of the script -- and answers `--pinned-inputs` with them, one
# repo-relative path per line. Its row must then pin that set too
# (`demonstrated.inputs`, path -> sha256, written only by `--repin`, which
# replays the row's arms first and records that replay beside the pin), and R7
# re-derives the set on every run: an edited, added or removed input is RED
# until the arms are replayed over it.
# A row that pins inputs whose subject no longer declares them is RED too, so
# dropping the declaration takes a hand edit of the registry, in the diff.
PINNED_INPUTS_FLAG = "--pinned-inputs"
PINNED_INPUTS_MARKER = re.compile(r"(?m)^ANSWERS_PINNED_INPUTS\s*=\s*True\s*$")


def _answers_pinned_inputs(root: Path, subject: str) -> bool:
    return bool(subject) and bool(PINNED_INPUTS_MARKER.search(_read(root, subject)))


def _derived_inputs(root: Path, subject: str) -> tuple[dict[str, str] | None, str]:
    """({path: sha256} of the set `subject --pinned-inputs` derives, "") or
    (None, why). Every listed path must be a regular file reached through no
    symlink (see below)."""
    interp = [sys.executable] if subject.endswith(".py") else ["bash"]
    env = dict(os.environ)
    try:
        proc = subprocess.run([*interp, subject, PINNED_INPUTS_FLAG], cwd=str(root),
                              capture_output=True, text=True, check=False, timeout=120,
                              env=env, pass_fds=_resource_fds(env))
    except (OSError, subprocess.TimeoutExpired, Red) as exc:
        return None, f"`{subject} {PINNED_INPUTS_FLAG}` could not run: {exc}"
    if proc.returncode != 0:
        tail = (proc.stderr or proc.stdout).strip().splitlines()[-1:] or ["(no output)"]
        return None, f"`{subject} {PINNED_INPUTS_FLAG}` exited {proc.returncode}: {tail[0]}"
    rels = [line.strip() for line in proc.stdout.splitlines() if line.strip()]
    if not rels:
        return None, f"`{subject} {PINNED_INPUTS_FLAG}` derived an EMPTY set"
    # A pin is the sha256 of a REGULAR FILE's bytes. A tracked directory
    # symlink hashed as "" (reading a directory fails), so an edit to anything
    # it reached left the derived set byte-identical and R7 never went red
    # again (verifier r9 recheck, 2026-09-25: a projector module behind
    # `src/extra -> ../../a2_extra_mod`). Any path whose resolution goes
    # through a symlink, or that is not a file (missing included: "" pinned
    # against "" is a pin against nothing), is refused rather than hashed.
    real_root = os.path.realpath(root)
    irregular = [rel for rel in rels if not (
        (root / rel).is_file()
        and os.path.realpath(root / rel) == os.path.join(real_root, os.path.normpath(rel)))]
    if irregular:
        return None, (f"`{subject} {PINNED_INPUTS_FLAG}` lists {', '.join(irregular)}, "
                      f"reached through a symlink or not a regular file -- its bytes "
                      f"cannot be pinned")
    return {rel: _sha256(root, rel) for rel in rels}, ""


def _inputs_drift(pinned: dict, live: dict) -> str:
    """How a pinned input set differs from the derived one ("" if it does not)."""
    changed = sorted(r for r in pinned.keys() & live.keys() if pinned[r] != live[r])
    added = sorted(live.keys() - pinned.keys())
    removed = sorted(pinned.keys() - live.keys())
    parts = ([f"changed: {', '.join(changed)}"] if changed else []) + \
        ([f"new: {', '.join(added)}"] if added else []) + \
        ([f"gone: {', '.join(removed)}"] if removed else [])
    return "; ".join(parts)


def _inputs_digest(inputs) -> str | None:
    """One sha256 over a pinned input set (None when the row pins none)."""
    if not isinstance(inputs, dict):
        return None
    return hashlib.sha256(json.dumps(sorted(inputs.items())).encode()).hexdigest()


# -- A PIN IS TIED TO THE REPLAY THAT MOVED IT (lane r10, 2026-09-26) -----------
#
# `--repin` moves a pin only after the row's demonstration ran or replayed green
# IN THE SAME PROCESS, and writes `replayed` -- the script sha and the input-set
# digest that replay produced -- beside it. R7 and R10 then require the pin to be
# the one its replay produced: a `script_sha256` or `inputs` moved by any other
# path (a hand edit "because only a comment changed", a merge that took one
# side's sha and the other side's inputs) is RED. A row pinning a derived input
# set must carry the record. A script written to forge the record is outside the
# threat model (docs/GATE_REGISTRY.md); this closes the accidental shapes.
def _pin_state(root: Path, subject: str) -> tuple:
    """What a pin of `subject` names in the tree at `root`: (its sha256, the
    {path: sha256} input set it derives, or None when it derives none). An
    input set that cannot be derived there is the reason, which equals no pin.

    `--repin` reads this IN the demonstration's sandbox before every arm and
    moves the pin only if each read equals the one in the shared tree after
    the run (verifier r10: the pin was hashed after a multi-minute replay whose
    sandbox had been cloned before the first arm, so a scanner edited in the
    tree meanwhile was pinned, replay record and all, though no arm ran over
    it). The pin is then exactly the bytes every arm ran over."""
    sha = _sha256(root, subject)
    if not _answers_pinned_inputs(root, subject):
        return sha, None
    derived, why = _derived_inputs(root, subject)
    return sha, derived if derived is not None else f"underivable: {why}"


def _replay_record(d: dict, how: str) -> dict:
    return {"script_sha256": d.get("script_sha256"),
            "inputs_sha256": _inputs_digest(d.get("inputs")), "by": how}


def _replay_disagreement(rid: str, d: dict) -> str | None:
    rec = d.get("replayed")
    if rec is None and "replayed" in d:
        # Review of R7c (2026-11-14): a null record read as NO record here and
        # as a record in R7c, so a hand-moved pin with `"replayed": null` was
        # green under both. Only --repin writes the field, and it writes an object.
        return (f"{rid} carries a null `replayed` record -- only --repin writes it, and it "
                f"writes an object")
    if rec is None:
        if isinstance(d.get("inputs"), dict):
            return (f"{rid} pins a derived input set that no recorded replay produced -- "
                    f"only --repin writes `inputs`, after the row's arms replay green, and it "
                    f"records that replay beside them")
        return None
    if not isinstance(rec, dict):
        return f"{rid} carries a `replayed` record that is not an object"
    moved = [k for k, live in (("script_sha256", d.get("script_sha256")),
                               ("inputs_sha256", _inputs_digest(d.get("inputs"))))
             if rec.get(k) != live]
    if moved:
        return (f"{rid}'s pin is not the one its last recorded replay produced ({', '.join(moved)} "
                f"moved since) -- a pin that moved without --repin: a hand edit, or a merge "
                f"that took one side's sha")
    return None


# Refusal sites a gate script owns that its arms need not reach, each with the
# reason. Same discipline as check_census_arms.UNLISTED_OK: "hard to test" is
# not a reason; "cannot move a verdict" is.
ARM_COVERAGE_ACCOUNTED: dict[tuple[str, str], str] = {
    # (row id, a NEEDLE that must appear in a measured site's text): reason.
    # AUDIT r12 M12-8: the single entry that lived here accounted for a "usage"
    # guard that does not exist in kernel_soundness_gate.sh -- and because the
    # lookup keyed on the row id alone, the needle and the reason were matched
    # against nothing, so it silently decremented 7 real sites. Removed; the
    # lookup is site-anchored now, so a future entry that names a site which is
    # not there accounts for nothing instead of quietly discounting others.
}


def refusal_sites_of_script(path: Path) -> list[tuple[int, str]]:
    """Every PROCESS refusal a gate script can take.

    AUDIT r12 M12-8: this was `re.match` against the START of a stripped line,
    i.e. a prefix grep — the shape CLAUDE.md forbids ("a gate's verdict comes
    from a parse, never a line count"), applied to the rule that judges other
    gates. Re-derived over all 143 rows it undercounted badly:
    check_silent_tactic_ratchet 1 vs 11 real refusals,
    check_prelude_collision_ratchet 1 vs 10, check_trust_verdict_emitters 1 vs 5
    (`sys.exit(f"FAIL: ...")` invisible), kv_invariance_gate 1 vs 4 (a `fail()`
    helper, a `|| exit 1`, a heredoc `sys.exit(1)` all invisible) — and the rule
    was escapable by RE-SPELLING one `return 1` as `sys.exit(...)`.

    Python is parsed with `ast`; shell is matched anywhere on a line (plus calls
    to helpers that themselves exit), because shell has no cheap parser here and
    a positional grep was exactly the defect.
    """
    import ast as _ast
    import re as _re
    out: list[tuple[int, str]] = []
    try:
        src = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return out
    lines = src.split("\n")
    if path.suffix == ".py":
        try:
            tree = _ast.parse(src)
        except SyntaxError:
            return out
        # AUDIT r14 M14-6, half one: a gate could leave R12's site count by
        # RE-SPELLING its refusals as named constants -- `EXIT_FAIL = 1` at
        # module level, then `return EXIT_FAIL`, which is an ast.Name and was
        # invisible. Resolve the module's own int bindings so the spelling is
        # not what decides.
        _int_names: dict[str, int] = {}
        for _n in tree.body:
            if isinstance(_n, _ast.Assign) and isinstance(_n.value, _ast.Constant) \
                    and isinstance(_n.value.value, int) and _n.value.value is not True:
                for _t in _n.targets:
                    if isinstance(_t, _ast.Name):
                        _int_names[_t.id] = _n.value.value
            elif isinstance(_n, _ast.AnnAssign) and isinstance(_n.value, _ast.Constant) \
                    and isinstance(_n.value.value, int) and isinstance(_n.target, _ast.Name):
                _int_names[_n.target.id] = _n.value.value
        # half two: only `SystemExit` and the literal name `Drift` counted as a
        # raised refusal, so a gate refusing through its OWN exception type --
        # which is this very script's idiom (`raise Red(...)`) -- counted zero.
        # Every exception class the module defines is a refusal when raised.
        _own_excs = {
            _n.name for _n in _ast.walk(tree)
            if isinstance(_n, _ast.ClassDef)
            and any(getattr(_b, "id", "") in ("Exception", "BaseException", "RuntimeError",
                                              "ValueError")
                    or getattr(_b, "attr", "") in ("Exception", "BaseException")
                    for _b in _n.bases)
        }

        def _nonzero(value) -> bool:
            return isinstance(value, int) and value is not True and value not in (0, None)

        for node in _ast.walk(tree):
            ln = getattr(node, "lineno", None)
            if ln is None:
                continue
            text = lines[ln - 1].strip()[:60] if ln - 1 < len(lines) else ""
            if isinstance(node, _ast.Raise):
                exc = node.exc
                # `raise SystemExit(main())` forwards a status; it is the
                # entrypoint idiom, not a refusal of its own
                if (isinstance(exc, _ast.Call) and getattr(exc.func, "id", "") == "SystemExit"
                        and len(exc.args) == 1 and isinstance(exc.args[0], _ast.Call)
                        and getattr(exc.args[0].func, "id", "") == "main"):
                    continue
                _exc_name = ""
                if isinstance(exc, _ast.Call):
                    _exc_name = getattr(exc.func, "id", "") or getattr(exc.func, "attr", "")
                elif isinstance(exc, _ast.Name):
                    _exc_name = exc.id
                if _exc_name in ({"SystemExit", "Drift"} | _own_excs):
                    out.append((ln, text))
            elif isinstance(node, _ast.Call):
                # AUDIT r13 M13-8: `sys.exit` was the only recognised call, so
                # `os._exit`, a bare `exit(...)` and a qualified `parser.error`
                # were invisible. Any exit-shaped call counts, however qualified.
                fn = node.func
                name = getattr(fn, "id", None) or getattr(fn, "attr", None)
                # AUDIT r14 M14-6: `sys.exit(main())` FORWARDS a status; it is
                # the entrypoint idiom, exactly as `raise SystemExit(main())` is,
                # and the Raise branch has excluded it since r12 while this one
                # counted it. Two spellings of one thing were being counted
                # differently by the same rule.
                _forwards = (len(node.args) == 1 and isinstance(node.args[0], _ast.Call)
                             and getattr(node.args[0].func, "id", "") == "main")
                if name in ("exit", "_exit", "error") and not _forwards:
                    out.append((ln, text))
            elif isinstance(node, _ast.Return):
                # AUDIT r13 M13-8: this recognised ONLY a literal `return 1`, so
                # `return 0 if ok else 1` -- the DOMINANT main-verdict spelling
                # in this repo (check_add_decl_ratchet, check_env_bypass_census,
                # check_extend_constants_ratchet all use it) -- counted zero, and
                # `return True` predicates counted as refusals because True == 1.
                # Count by EFFECT: a return that can yield a non-zero status, and
                # never a bare boolean predicate.
                v = node.value
                if isinstance(v, _ast.Constant):
                    if _nonzero(v.value):
                        out.append((ln, text))
                elif isinstance(v, _ast.Name):
                    if _nonzero(_int_names.get(v.id)):
                        out.append((ln, text))
                elif isinstance(v, _ast.IfExp):
                    for branch in (v.body, v.orelse):
                        if isinstance(branch, _ast.Constant) and _nonzero(branch.value):
                            out.append((ln, text))
                            break
                        if isinstance(branch, _ast.Name) and _nonzero(_int_names.get(branch.id)):
                            out.append((ln, text))
                            break
        return sorted(set(out))
    # shell: `exit N` ANYWHERE on the line, and helper definitions that exit
    helpers = set(_re.findall(r"^\s*([a-z_][a-z0-9_]*)\s*\(\)\s*\{[^}]*\bexit\b",
                              src, _re.M | _re.S))
    for i, ln in enumerate(lines, 1):
        t = ln.strip()
        if t.startswith("#"):
            continue
        # AUDIT r13 M13-8: `exit\s+[1-9]` missed `exit "$RC"` and there was no
        # `return` rule at all, so a shell gate's own verdict helpers counted
        # zero. Any exit with an operand, and any function-level `return` with a
        # non-zero or variable operand, is a refusal.
        if (_re.search(r"\bexit\s+\S", t) or _re.search(r"\bsys\.exit\s*\(", t)
                or _re.search(r"\breturn\s+(?:[1-9][0-9]*|\$\S+)", t)):
            out.append((i, t[:60]))
        elif helpers and _re.search(r"\b(" + "|".join(sorted(helpers)) + r")\b", t) \
                and not _re.match(r"[a-z_]+\s*\(\)\s*\{", t):
            out.append((i, t[:60]))
    return sorted(set(out))


def check_arm_coverage(root: Path, doc: dict, demos: dict) -> list[str]:
    """R12 ARM COVERAGE: a soundness gate's arms must reach more than one refusal.

    AUDIT r11 M11-1(a): `kernel_soundness_gate` owns three refusal points -- a
    pure-Python Lane 0 preflight that `exit 1`s BEFORE either cargo lane starts,
    then Lane 1 (parity) and Lane 2 (elab). Its sole recorded arm perturbs the
    differential corpus, i.e. Lane 0. Measured consequence: replacing both cargo
    lanes with `if true` made the gate print PASS having run nothing, and
    `--repin` then re-pinned it with the replay GREEN in ~4 seconds -- no cargo
    ran, which is itself the proof the arm never reached a soundness lane.

    A precise per-arm reachability measurement would need instrumenting the
    gate. What is cheap and still binding: a soundness gate carrying SEVERAL
    refusal sites may not be demonstrated by a single arm. That refuses the
    measured shape without pretending to more precision than is measured.
    """
    out = []
    for row in doc["rows"]:
        if row.get("claims") != "soundness":
            continue
        subject = row.get("path") or row.get("implemented_by") or ""
        if not subject.startswith("scripts/") or not subject.endswith((".sh", ".py")):
            continue
        d = row.get("demonstrated") or {}
        if d.get("inherited_from") or d.get("kind") != "mutation-record":
            continue
        sites = refusal_sites_of_script(root / subject)
        # AUDIT r12 M12-8: the accounting was keyed on the row id ALONE, so the
        # second tuple element and the reason matched nothing -- the no-op
        # accounting r10 condemned in check_census_arms next door. It is
        # site-anchored now: an entry counts only if its needle appears in a
        # measured site's text, so an entry for a site that does not exist (the
        # one live entry named a "usage" guard that is nowhere in the script)
        # accounts for nothing.
        accounted = sum(
            1 for (rid_k, needle) in ARM_COVERAGE_ACCOUNTED
            if rid_k == row["id"] and any(needle in text for _, text in sites))
        effective = len(sites) - accounted
        arms = len(demos.get("arms", {}).get(row["id"], []))
        debt = (demos.get("arm_coverage_debt", {}).get("rows", {}) or {}).get(row["id"])
        if effective >= 2 and arms < 2 and debt:
            # An OPEN, DATED account: the debt is named, owned and expires, so
            # it cannot rot into silence. It is not a discharge -- the row is
            # still under-demonstrated and says so.
            # AUDIT r14 M14-4: the row RECORDS `sites` and `arms`, and until now
            # nothing read them -- only `expires` was checked, so the two numbers
            # that say how big the debt is were decoration. A row could read
            # `sites: 2, arms: 2` (i.e. "no debt at all") beside a script with
            # eight refusals and one arm, and the account would still pass. They
            # are RE-DERIVED here: the row is an account of a MEASURED quantity,
            # so a gate that grows a refusal site stales its own waiver and
            # forces a re-review instead of silently widening it.
            _rec_sites, _rec_arms = debt.get("sites"), debt.get("arms")
            if _rec_sites != effective or _rec_arms != arms:
                out.append(
                    f"R12 ARM COVERAGE: {row['id']} arm-coverage debt records "
                    f"sites={_rec_sites!r}/arms={_rec_arms!r}, measured "
                    f"{effective}/{arms} in {subject}. The debt must state what is "
                    f"owed TODAY -- re-derive both numbers, or write the arms.")
                continue
            _exp = str(debt.get("expires") or "")
            if not ISO.match(_exp):
                out.append(f"R12 ARM COVERAGE: {row['id']} arm-coverage debt has "
                           f"expires={_exp!r}, not YYYY-MM-DD")
            elif _exp < date.today().isoformat():
                out.append(f"R12 ARM COVERAGE: {row['id']} arm-coverage debt EXPIRED "
                           f"{_exp} (owner {debt.get('owner')}) -- write the arms it owes: "
                           f"{debt.get('owed')}")
            elif _exp > (date.today() + timedelta(days=180)).isoformat():
                out.append(f"R12 ARM COVERAGE: {row['id']} arm-coverage debt expires "
                           f"{_exp}, beyond the 180-day horizon")
            continue
        if effective >= 2 and arms < 2:
            out.append(
                f"R12 ARM COVERAGE: {row['id']} claims soundness and owns {effective} "
                f"refusal sites in {subject}, but carries {arms} recorded arm(s). One "
                f"arm cannot demonstrate several independent refusals -- the measured "
                f"failure is a gate whose later lanes were replaced by `if true`, "
                f"printing PASS while its single arm still replayed green. Record an "
                f"arm per refusal, or account the extra sites in "
                f"ARM_COVERAGE_ACCOUNTED with why deleting them cannot move a verdict.")
    return out


def check_soundness_claims_ratchet(root: Path, doc: dict) -> list[str]:
    """R11 CLAIMS: a row may not quietly stop claiming soundness.

    AUDIT r11 M11-8: `claims` is self-declared and switches off R4 and R9, and
    nothing anchored it -- relabelling a gate soundness -> quality with
    `demonstrated: null` left the registry green, visible only as summary
    counters that appear in no artifact. The committed set in
    data/soundness_claims_ratchet.json may GROW freely; removing a row from it
    requires editing that file, which is a reviewable act.
    """
    path = root / "data/soundness_claims_ratchet.json"
    if not path.exists():
        return ["R11 CLAIMS: data/soundness_claims_ratchet.json is missing -- the "
                "soundness-claim set is unanchored and a row can demote itself silently"]
    try:
        anchored = set(json.loads(path.read_text())["soundness_rows"])
    except (OSError, ValueError, KeyError) as exc:
        return [f"R11 CLAIMS: soundness_claims_ratchet.json is unreadable: {exc}"]
    live = {r["id"] for r in doc["rows"] if r.get("claims") == "soundness"}
    # AUDIT r12 M12-6: this compared `anchored - live` ONLY, so the anchor could
    # be emptied by a contentless commit and every soundness row freed in the
    # next one -- measured: `soundness_rows: []` alone left the registry
    # byte-identical to baseline, after which demoting two rows to `quality`
    # with `demonstrated: null` and `source_scan: raw-lines` also passed. The
    # r11 premise (the removal edit travels WITH the demotion and is therefore
    # reviewed) is false: they need not be the same commit or the same week.
    # Both directions are checked now, and the artifact's own `count` -- read by
    # nothing before -- must agree with its list.
    problems = []
    try:
        anchored_count = json.loads(path.read_text()).get("count")
    except (OSError, ValueError):
        anchored_count = None
    if anchored_count is not None and anchored_count != len(anchored):
        problems.append(
            f"R11 CLAIMS: soundness_claims_ratchet.json says count={anchored_count} but "
            f"lists {len(anchored)} rows -- the artifact disagrees with itself")
    unanchored = sorted(live - anchored)
    if unanchored:
        problems.append(
            "R11 CLAIMS: " + ", ".join(unanchored) + " claim soundness but are not in "
            "data/soundness_claims_ratchet.json -- a row unanchored from birth can be "
            "demoted later with nothing noticing. Add them (the set may grow freely).")
    lost = sorted(anchored - live)
    if lost:
        return problems + [f"R11 CLAIMS: {rid} no longer claims soundness -- R4 (demonstration "
                f"required) and R9 (no raw-line scanning) stop binding it. If the "
                f"demotion is intended, remove it from "
                f"data/soundness_claims_ratchet.json in the same change, with the "
                f"reason." for rid in lost]
    return problems


def load_registry(root: Path) -> dict:
    path = root / "data/gate_registry.json"
    try:
        doc = json.loads(path.read_text())
    except OSError as exc:
        raise Red(f"data/gate_registry.json is unreadable: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise Red(f"data/gate_registry.json is not valid JSON: {exc}") from exc
    if not isinstance(doc, dict) or not isinstance(doc.get("rows"), list):
        raise Red("data/gate_registry.json must be an object with a 'rows' list")
    return doc


def load_demos(root: Path) -> dict:
    path = root / "data/gate_demonstrations.json"
    if not path.exists():
        return {}
    try:
        doc = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise Red(f"data/gate_demonstrations.json is not valid JSON: {exc}") from exc
    arms = doc.get("arms")
    if not isinstance(arms, dict):
        raise Red("data/gate_demonstrations.json must carry an 'arms' object")
    return arms


# ── mechanical re-derivation ─────────────────────────────────────────────────


def _code_lines(rel: str, text: str):
    """`(lineno, code)` for every line of `rel` that is CODE rather than prose.

    Factored out of `invocations_in` unchanged, because the wiring
    discriminator below has to see EXACTLY the same lines the loose scan sees:
    a discriminator measured over a different denominator is not a measurement
    of this scan. Two exclusions live here (the third, backticks, is per-match
    and stays at the call site):

      1. comment lines (# and //);
      2. lines inside a Python triple-quoted block, which is where docstrings,
         usage text and long rationale live in every script here.
    """
    is_py = rel.endswith(".py")
    quotes = (chr(34) * 3, chr(39) * 3)
    in_block = ""
    for lineno, line in enumerate(text.splitlines(), 1):
        if is_py:
            rest = line
            if in_block:
                idx = rest.find(in_block)
                if idx < 0:
                    continue
                rest = rest[idx + 3:]
                in_block = ""
            scan = rest
            offset = 0
            while True:
                hits = [(scan.find(q), q) for q in quotes if scan.find(q) >= 0]
                if not hits:
                    break
                pos, q = min(hits)
                after = scan[pos + 3:]
                close = after.find(q)
                if close >= 0:
                    scan = after[close + 3:]
                    offset += pos + 3 + close + 3
                    continue
                in_block = q
                rest = rest[: offset + pos]
                break
            line = rest
        stripped = line.lstrip()
        if stripped.startswith("#") or stripped.startswith("//"):
            continue
        yield lineno, line


def invocations_in(root: Path, rel: str) -> set[str]:
    """Scripts that `rel` invokes. PROSE is not an invocation.

    Three exclusions, and the third was learned the hard way. This file's own
    module docstring names scripts/check_constructive_ratchet.py while
    explaining that nothing runs it -- and the first version of this scan read
    that sentence as a runner edge, which made the one genuinely unwired gate in
    the tree look WIRED. A scan that cannot tell a mention from a call would
    have quietly buried the finding it exists to surface.

      1. comment lines (# and //);
      2. lines inside a Python triple-quoted block, which is where docstrings,
         usage text and long rationale live in every script here;
      3. a path wrapped in backticks, which is this repo's universal convention
         for naming a file in prose -- in markdown, in shell comments, and in
         docstrings alike.

    A real invocation is never backticked and never sits inside a docstring, so
    nothing legitimate is lost.

    It is still LOOSE in one direction, and that is measured rather than
    guessed: see the wiring discriminator below and `--wiring-audit`. In a .py
    file an ordinary DATA string carrying a path -- `"wired_by":
    ["scripts/local_gate.sh"]` inside an artifact this repo emits -- reads here
    as an invocation. Nothing in this function changes until that measurement
    has been read row by row.
    """
    found: set[str] = set()
    for _, line in _code_lines(rel, _read(root, rel)):
        for m in INVOCATION.finditer(line):
            if m.start(1) > 0 and line[m.start(1) - 1] == "`":
                continue  # a backticked path in prose is a name, not a call
            found.add(m.group(1))
    return found


def runner_edges(root: Path, extra_runners: set[str]) -> dict[str, set[str]]:
    """script -> set of runners that invoke it.

    The scanned set is the TRANSITIVE closure from the four runner roots, plus
    every runner any registry row declares. Closure matters: `deny_sorry_gate.sh`
    calls `check_add_decl_ratchet.py` and is itself called from a root, so a
    root-only scan would miss the edge and R3 would report a false `extra`.
    It is still bounded to a few dozen small files -- milliseconds, hook-safe.
    """
    edges: dict[str, set[str]] = {}
    seen: set[str] = set()
    frontier = set(RUNNER_ROOTS) | extra_runners
    while frontier:
        runner = frontier.pop()
        if runner in seen:
            continue
        seen.add(runner)
        for target in invocations_in(root, runner):
            if target == runner:
                continue
            edges.setdefault(target, set()).add(runner)
            if target.endswith((".sh", ".py")) and (root / target).exists():
                frontier.add(target)
    return edges


# ── THE WIRING DISCRIMINATOR (reporting-only; `--wiring-audit`) ──────────────
#
# `invocations_in` decides "does this file RUN that script?" from a path
# appearing in a non-prose line. In a shell file that is exactly right: there a
# bare path IS the command word. In a .py file it is not, and the gap is
# measured, not theorised -- three edges R3 reported on 2026-08-27 were paths
# sitting in ordinary DATA strings (see
# docs/issues/2026-08-27-gate-registry-wiring-scan-counts-data-strings.md):
#
#     "wired_by": ["scripts/local_gate.sh"],              a value in an EMITTED artifact
#     mint_command="scripts/source_elab_gate.sh --update" a command RECORDED for a human
#     "... and scripts/verdict_gate.sh reads them"        prose inside an emitted artifact
#
# and the same issue found the OTHER direction: declared `wired_by` entries
# that are not invocations either (a file that PARSES local_gate.sh, a Rust
# const, an input-dependency list). The `wired_by` column currently means
# "mentions", not "runs".
#
# This block re-derives which is which. It is REPORTING-ONLY: nothing here is
# reachable from `check()`, so the gate's verdict and its output are unchanged
# byte for byte until step 3 of that issue flips it on. Step 2 -- auditing
# `wired_by` row by row -- reads the table this produces.
#
# THE RULE, by file class:
#
#   shell (.sh, Justfile, scripts/githooks/pre-push, anything with no
#         extension): every loose match is a real invocation. Today's
#         behaviour, deliberately unchanged -- a bare path there is the
#         command word.
#
#   python (.py) and other (.rs, ...): a match is a real invocation only with
#         E1 EXEC CONTEXT -- `subprocess.`, `Popen`, `os.system`, a bare
#            `run(`, `shell=True`, `Command::new` ... on the match's own line,
#            or on the line that opened a bracket group still open at the
#            match. The second half is what carries a multi-line
#            `subprocess.run(\n    [...],\n)`.
#         E2 COMMAND-VECTOR HEAD -- the path is the head element of a list or
#            tuple literal that is BOUND TO A COMMAND-SHAPED NAME (`argv`,
#            `cmd`, `command`, `args`, `*_cmd`, ...). The head may be preceded
#            only by launcher tokens and flags, so `["python3", "scripts/x.py"]`
#            counts and `["data/x.json", "scripts/y.sh"]` does not.
#
# The binding name is load-bearing and it is what the prototype in the issue
# was missing. `"argv": ["scripts/x.sh"]` and `"_extra_paths":
# ["scripts/x.sh"]` are the SAME SHAPE in verify_runner.py -- one is a command,
# one is an input-dependency list -- and only the key tells them apart.
#
# MULTI-LINE VECTORS ARE HANDLED, and they are the reason this is a bracket
# machine rather than a regex over one line. `"argv": [` with its elements on
# following lines is the ordinary formatting of a long command in this repo,
# and reading it as data would be a FALSE NEGATIVE -- an invocation reported as
# a mention, which is the direction that hides a real runner. Arms `W4`/`W8`
# in the self-test pin both halves: multi-line under `argv` is an edge,
# multi-line under `_extra_paths` is not.
#
# WHAT IT CANNOT SEE, stated rather than hidden: execution through a NAME.
# `const SCRIPT: &str = "scripts/x.sh"` followed twenty lines later by
# `Command::new("bash").arg(&script)` is a real invocation that no
# single-statement rule can reach. Those are not silently downgraded -- the
# audit marks them `indirect?` and the step-2 auditor reads them by hand.

EXEC_CTX = re.compile(
    r"""subprocess\.|\bPopen\b|os\.system|os\.exec|os\.spawn|os\.popen"""
    r"""|\bcheck_call\b|\bcheck_output\b|\bgetoutput\b|\bgetstatusoutput\b"""
    r"""|(?<!def )\brun\s*\(|shell\s*=\s*True"""
    r"""|Command::new|process::Command|\.spawn\("""
)

# The text immediately before a `[`/`(` that makes the literal a COMMAND
# VECTOR rather than a list of data. Matched against the line prefix, so it
# works for `cmd = [`, `argv=[`, `"argv": [` and `mint_command=[` alike.
COMMAND_BINDING = re.compile(
    r"""(?i)["']?\b(?:[A-Za-z0-9_]*_)?(?:argv|cmd|cmdline|command|args)s?["']?\s*[:=]\s*$"""
)

# A binding whose right-hand side is (or starts with) a single literal, for the
# `indirect?` flag: `GATE = ROOT / "scripts/local_gate.sh"`,
# `const SCRIPT_REL_PATH: &str = "scripts/x.sh";`.
BINDING_NAME = re.compile(
    r"""^\s*(?:pub(?:\([a-z]+\))?\s+)?(?:const\s+|static\s+|let\s+|var\s+)?"""
    r"""([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]*?)?=\s*"""
)

_LAUNCHER_ELEMS = frozenset((
    "sh", "bash", "zsh", "env", "exec", "timeout", "nohup", "xargs",
    "python", "py", "sys.executable", "PY", "PYTHON", "GATE_PYTHON",
    "$PY", "$GATE_PYTHON", "PYTHON_BIN", "interpreter", "self.python",
))
_PYTHON_EXE = re.compile(r"^python3(?:\.\d+)?$")
_SHELLISH = (".sh", ".bash", ".zsh")

# A triple-quoted string that OPENS AND CLOSES on one line. `_code_lines` does
# not drop these -- its docstring rule only skips lines inside an UNCLOSED
# block -- so a one-line docstring reaches the loose scan as code. That is a
# live instance of the same prose class, not a hypothetical: R3 records
# `check_script_selftests <- scripts/check_gate_registry.py` today, and the
# whole edge is the one-line docstring of `selftest_suite_files`.
ONE_LINE_DOC = re.compile(r'""".*?"""' + r"|'''.*?'''")

# A keyword argument: `mint_command="scripts/x.sh --update"` is a command
# RECORDED for a human, and naming the keyword is what makes that legible in
# the audit.
KWARG_SLOT = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*$")
CALL_PREFIX = re.compile(r"[A-Za-z0-9_\])]\s*$")


def _describe_slot(frame, prev: list, cur: str) -> str:
    """Where a non-invocation literal actually sits, in the auditor's terms."""
    owner = frame.prefix.strip()[-48:]
    kw = KWARG_SLOT.search(cur)
    if kw:
        return "keyword argument %s= in %s" % (kw.group(1), owner or "a call")
    if frame.opener == "{":
        return "a dict entry under %s" % (owner or "a literal")
    if frame.opener == "(" and CALL_PREFIX.search(frame.prefix):
        return "argument %d of the call %s(...)" % (len(prev), owner)
    if prev:
        return "element %d of %s, not the command word" % (len(prev), owner or "a literal")
    if owner.endswith(":"):
        return "the value of %s, which is not a command binding" % owner
    return "the head of %s, which is not a command binding" % (owner or "a literal")


def _file_class(rel: str) -> str:
    """"shell", "python" or "other" -- which discriminator applies."""
    base = rel.rsplit("/", 1)[-1]
    if rel.endswith(".py"):
        return "python"
    if rel.endswith(_SHELLISH) or "." not in base:
        return "shell"
    return "other"


def _is_launcher_elem(tok: str) -> bool:
    """A vector element that may precede the command word: a launcher, a flag,
    a number, or an empty slot. Anything else means the path is an ARGUMENT or
    a list entry, not the command."""
    t = tok.strip().strip("\"'").strip()
    if not t or t.startswith("-"):
        return True
    if t.isdigit():
        return True
    base = t.rsplit("/", 1)[-1]
    return (
        base in _LAUNCHER_ELEMS
        or t in _LAUNCHER_ELEMS
        or bool(_PYTHON_EXE.match(base))
    )


class _Frame:
    """One open bracket group, and what the machine knows about it."""

    __slots__ = ("opener", "prefix", "exec_open", "elems", "cur")

    def __init__(self, opener: str, prefix: str, exec_open: bool) -> None:
        self.opener = opener
        self.prefix = prefix
        self.exec_open = exec_open
        self.elems: list[str] = []
        self.cur: list[str] = []


def _rec(rel, target, lineno, line, real, why, indirect=False) -> dict:
    return {
        "runner": rel, "target": target, "line": lineno,
        "text": line.strip()[:200], "real": real, "why": why,
        "indirect": indirect, "binding": "",
    }


def wiring_records(rel: str, text: str) -> list:
    """Every loose match in `rel`, each classified real / reference-only.

    The returned targets are EXACTLY `invocations_in`'s set (deduped), by
    construction: same lines, same regex, same backtick exclusion. Only the
    `real` verdict is new.
    """
    cls = _file_class(rel)
    recs: list = []
    if cls == "shell":
        for lineno, line in _code_lines(rel, text):
            for m in INVOCATION.finditer(line):
                if m.start(1) > 0 and line[m.start(1) - 1] == "`":
                    continue
                recs.append(_rec(rel, m.group(1), lineno, line, True,
                                 "shell-command-word"))
        return recs

    stack: list = []
    file_has_exec = False
    bound_names: dict = {}          # lineno -> name bound on that line
    lines = list(_code_lines(rel, text))
    for lineno, line in lines:
        exec_here = bool(EXEC_CTX.search(line))
        file_has_exec = file_has_exec or exec_here
        bm = BINDING_NAME.match(line)
        if bm:
            bound_names[lineno] = bm.group(1)
        spans: list = []            # (start, end, (exec_ctx, frame, prev_elems))
        in_str, esc, s_start, s_ctx = "", False, -1, None
        for i, ch in enumerate(line):
            if in_str:
                if stack:
                    stack[-1].cur.append(ch)
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == in_str:
                    spans.append((s_start, i, s_ctx))
                    in_str = ""
                continue
            if ch in "\"'":
                top = stack[-1] if stack else None
                s_ctx = (exec_here or any(f.exec_open for f in stack),
                         top, list(top.elems) if top else [],
                         "".join(top.cur) if top else "")
                in_str, s_start = ch, i
                if stack:
                    stack[-1].cur.append(ch)
                continue
            if ch in "([{":
                inherited = exec_here or any(f.exec_open for f in stack)
                if stack:
                    stack[-1].cur.append(ch)
                stack.append(_Frame(ch, line[:i].rstrip(), inherited))
                continue
            if ch in ")]}":
                if stack:
                    stack.pop()
                if stack:
                    stack[-1].cur.append(ch)
                continue
            if ch == "," and stack:
                stack[-1].elems.append("".join(stack[-1].cur).strip())
                stack[-1].cur = []
                continue
            if stack:
                stack[-1].cur.append(ch)
        if in_str:                  # a literal does not survive the newline here
            spans.append((s_start, len(line), s_ctx))
        doc_spans = [(m.start(), m.end()) for m in ONE_LINE_DOC.finditer(line)]
        for m in INVOCATION.finditer(line):
            if m.start(1) > 0 and line[m.start(1) - 1] == "`":
                continue
            col = m.start(1)
            ctx = None
            for a, b, c in spans:
                if a <= col <= b:
                    ctx = c
                    break
            if any(a <= col < b for a, b in doc_spans):
                real = False
                why = ("inside a ONE-LINE docstring -- prose, which the loose "
                       "scan's docstring rule only skips when the block spans lines")
            elif ctx is None:
                real = exec_here
                why = "exec-context" if real else "bare text, no execution context"
            else:
                in_exec, frame, prev, cur = ctx
                head = (frame is not None and frame.opener in "(["
                        and all(_is_launcher_elem(t) for t in prev))
                if in_exec:
                    real, why = True, "exec-context"
                elif head and COMMAND_BINDING.search(frame.prefix):
                    real, why = True, "command-vector-head"
                elif frame is not None:
                    real, why = False, _describe_slot(frame, prev, cur)
                else:
                    real, why = False, "a data string, bound to no command"
            rec = _rec(rel, m.group(1), lineno, line, real, why)
            rec["binding"] = bound_names.get(lineno, "")
            recs.append(rec)

    # `indirect?`: a reference-only match that BINDS the path to a name, in a
    # file that spawns processes at all. That is the one shape this machine
    # provably cannot decide (`Command::new("bash").arg(&script)` twenty lines
    # away), so it is flagged for a human instead of being called either way.
    if file_has_exec:
        body = "\n".join(l for _, l in lines)
        for rec in recs:
            name = rec["binding"]
            if rec["real"] or not name:
                continue
            if len(re.findall(r"\b%s\b" % re.escape(name), body)) > 1:
                rec["indirect"] = True
    return recs


def wiring_measure(root: Path, rows: list) -> tuple:
    """(loose, real, records, scanned) over the same closure `runner_edges`
    walks, so the two are directly comparable."""
    loose: dict = {}
    real: dict = {}
    records: dict = {}
    seen: set = set()
    frontier = set(RUNNER_ROOTS) | {r for row in rows for r in row["wired_by"]}
    while frontier:
        runner = frontier.pop()
        if runner in seen:
            continue
        seen.add(runner)
        for rec in wiring_records(runner, _read(root, runner)):
            target = rec["target"]
            if target == runner:
                continue
            loose.setdefault(target, set()).add(runner)
            records.setdefault((runner, target), []).append(rec)
            if rec["real"]:
                real.setdefault(target, set()).add(runner)
            if target.endswith((".sh", ".py")) and (root / target).exists():
                frontier.add(target)
    return loose, real, records, sorted(seen)


def enforcement_path_scripts(root: Path) -> set[str]:
    """Scripts the enforcement path invokes DIRECTLY.

    Name patterns catch `check_*` and `*_gate.sh`; they do not catch
    `spine_scoreboard.py` or `trust_ir_axes.py selftest`, both of which the
    pre-push hook runs as fail-closed legs. Anything local_gate.sh or the hook
    calls in its own body is a gate whatever it is called, so it needs a row.
    """
    out: set[str] = set()
    for runner in (LOCAL_GATE, HOOK):
        out |= invocations_in(root, runner)
    return {p for p in out if (root / p).exists() and p not in (LOCAL_GATE, HOOK)}


def gate_shaped_files(root: Path) -> set[str]:
    """Gate-shaped files, from the index UNION the working tree.

    `git ls-files` alone would miss a gate that has been written but not yet
    staged, so an author running the gate before `git add` would be told
    everything is fine and only find out at push. The working-tree half closes
    that; `git check-ignore` keeps scratch and generated files out, so a stray
    file under scripts/ that git already ignores does not become a build error.
    """
    files: list[str] = []
    try:
        out = subprocess.run(
            ["git", "ls-files", "-z", "scripts"],
            cwd=root, capture_output=True, text=True, check=True,
        ).stdout
        files = [f for f in out.split("\0") if f]
    except (OSError, subprocess.CalledProcessError):
        pass
    on_disk = {
        str(p.relative_to(root))
        for p in (root / "scripts").rglob("*")
        if p.is_file()
    }
    extra = sorted(on_disk - set(files))
    if extra:
        try:
            ignored = subprocess.run(
                ["git", "check-ignore", "--stdin"], cwd=root,
                input="\n".join(extra), capture_output=True, text=True,
            ).stdout.split()
        except OSError:
            ignored = []
        files.extend(f for f in extra if f not in set(ignored))
    if not files:
        files = sorted(on_disk)
    hits = set()
    for f in files:
        if GATE_SHAPED_EXCLUDE.match(f):
            continue
        if any(pat.match(f) for pat in GATE_SHAPED):
            hits.add(f)
            continue
        if _mints_and_checks_a_tracked_artifact(root, f):
            hits.add(f)
    # ... and the PACKAGE form, which is what hid scripts/masquerade_gate/ for
    # the whole life of this registry. The artifact is the DIRECTORY: one row
    # classifies the package, not five rows for five modules.
    scripts_dir = root / "scripts"
    if scripts_dir.is_dir():
        pkgs = [
            d for d in sorted(scripts_dir.rglob("*"))
            if d.is_dir()
            and (d / "__main__.py").is_file()
            and GATE_SHAPED_PACKAGE.match(d.name)
        ]
        rels = [str(d.relative_to(root)) for d in pkgs]
        if rels:
            try:
                ignored = set(subprocess.run(
                    ["git", "check-ignore", "--stdin"], cwd=root,
                    input="\n".join(rels), capture_output=True, text=True,
                ).stdout.split())
            except OSError:
                ignored = set()
            hits.update(r for r in rels if r not in ignored)
    return hits


def gate_leg_ids(root: Path) -> list[str]:
    return [m.group(1) for m in (GATE_LEG.match(l) for l in _read(root, LOCAL_GATE).splitlines()) if m]


def suite_row_ids(root: Path) -> list[str]:
    return [m.group(1) for m in (SUITE_ROW.match(l) for l in _read(root, VERIFY_RUNNER).splitlines()) if m]


def selftest_suite_files(root: Path) -> set[str]:
    """What scripts/check_script_selftests.sh actually runs (the DIRECTORY glob)."""
    body = _read(root, "scripts/check_script_selftests.sh")
    if not body:
        return set()
    # The runner walks the whole tree (`find scripts -type f`), not the top level.
    out = set()
    for pattern in ("test_*.py", "test_*.sh"):
        for p in (root / "scripts").rglob(pattern):
            if p.is_file() and not p.is_symlink():
                out.add(str(p.relative_to(root)))
    return out


# ── the rules ────────────────────────────────────────────────────────────────

REQUIRED = ("id", "path", "kind", "claims", "wired_by", "demonstrated", "waiver")
RETIRED_REQUIRED = ("id", "path", "retired", "by", "reason", "superseded_by")


def _has_replay_route(root: Path, d: dict) -> bool:
    """Whether `--repin` has a way to demonstrate this row in a tree: a `ref`
    naming a script it can run, or recorded arms it can replay. The same test
    `repin` applies before it moves a pin."""
    words = str(d.get("ref") or "").split()
    if words and words[0] in ("python3", "bash", "sh"):
        words = words[1:]
    runnable = bool(words) and words[0].startswith("scripts/") and (root / words[0]).exists()
    return runnable or bool(d.get("replayable"))


def _soundness_under_account(rows: list, row: dict) -> list[str]:
    """The rows claiming soundness whose pin is `row`'s: `row` itself and every
    row that inherits its pin (`inherited_from`). An undemonstrated-pin account
    on `row` would stand under each of these claims."""
    rid = row.get("id")
    return [r.get("id", "?") for r in rows
            if isinstance(r, dict) and r.get("claims") == "soundness"
            and (r is row or (isinstance(r.get("demonstrated"), dict)
                              and r["demonstrated"].get("inherited_from") == rid))]


def check(root: Path) -> list[str]:
    doc = load_registry(root)
    rows = doc["rows"]
    demos = load_demos(root)
    problems: list[str] = []
    today = date.today().isoformat()
    # 180-day waiver horizon (audit r10 M10-4), shared with the
    # source-elab exception's rule so 'dated' means the same thing everywhere.
    _HORIZON = (date.today() + timedelta(days=180)).isoformat()

    # R1 SHAPE
    seen_ids: set[str] = set()
    for i, row in enumerate(rows):
        if not isinstance(row, dict):
            problems.append(f"R1 SHAPE: row {i} is not an object")
            continue
        rid = row.get("id", f"<row {i}>")
        missing = [k for k in REQUIRED if k not in row]
        if missing:
            problems.append(f"R1 SHAPE: {rid} is missing key(s): {', '.join(missing)}")
            continue
        if rid in seen_ids:
            problems.append(f"R1 SHAPE: duplicate row id {rid}")
        seen_ids.add(rid)
        if row["kind"] not in KINDS:
            problems.append(f"R1 SHAPE: {rid} kind={row['kind']!r} is not one of {KINDS}")
        if row["claims"] not in CLAIMS:
            problems.append(f"R1 SHAPE: {rid} claims={row['claims']!r} is not one of {CLAIMS}")
        if not isinstance(row["wired_by"], list):
            problems.append(f"R1 SHAPE: {rid} wired_by must be a list")
        if row["kind"] in ("gate", "battery", "tool"):
            if not row["path"]:
                problems.append(f"R1 SHAPE: {rid} kind={row['kind']} needs a path")
            elif not (root / row["path"]).exists():
                problems.append(
                    f"R2 INVENTORY: {rid} points at {row['path']}, which does not exist "
                    f"-- delete the row or restore the file"
                )
        impl = row.get("implemented_by")
        if impl and not (root / impl).exists():
            problems.append(f"R1 SHAPE: {rid} implemented_by={impl} does not exist")
        if row["kind"] == "tool" and not row.get("tool_reason"):
            problems.append(
                f"R1 SHAPE: {rid} is classified `tool` (exempt from the wiring "
                f"requirement) with no tool_reason -- say why it asserts no invariant"
            )
        w = row.get("waiver")
        if w is not None:
            for k in ("owner", "expires", "reason"):
                if not w.get(k):
                    problems.append(f"R1 SHAPE: {rid} waiver is missing {k}")
            exp = w.get("expires", "")
            if exp and not ISO.match(exp):
                problems.append(f"R1 SHAPE: {rid} waiver expires={exp!r} is not YYYY-MM-DD")
            elif exp and exp > _HORIZON:
                # AUDIT r10 M10-4: shape + `< today` alone made a far-future
                # date a PERMANENT retirement of a soundness row's
                # demonstration requirement -- measured: setting a
                # claims=soundness row's demonstration to null and adding
                # expires 2999-12-31 took the registry back to green
                # (soundness 49/56 -> 48/56) with no other change. A waiver is
                # a dated account, so it gets the same 180-day horizon the
                # source-elab exception uses; renewing it is a visible, dated
                # act.
                problems.append(
                    f"R4 DEMO: {rid} waiver expires={exp} is beyond the 180-day "
                    f"horizon ({_HORIZON}) -- a waiver that outlives review is a "
                    f"permanent bypass wearing a date; shorten it and renew "
                    f"deliberately")
            elif exp and exp < today:
                problems.append(
                    f"R4 DEMO: {rid} waiver EXPIRED {exp} (owner {w.get('owner')}) "
                    f"-- demonstrate the gate or re-justify the waiver"
                )
        d = row.get("demonstrated")
        if d is not None:
            if d.get("kind") not in DEMO_KINDS:
                problems.append(f"R1 SHAPE: {rid} demonstrated.kind={d.get('kind')!r} not in {DEMO_KINDS}")
            if not ISO.match(str(d.get("date", ""))):
                problems.append(f"R1 SHAPE: {rid} demonstrated.date is not YYYY-MM-DD")
            elif str(d["date"]) > today:
                problems.append(f"R1 SHAPE: {rid} demonstrated.date {d['date']} is in the future")
            if w is not None:
                problems.append(
                    f"R4 DEMO: {rid} carries a waiver AND a demonstration -- a stale "
                    f"waiver silently re-opens the hole it was covering; delete it"
                )

    if problems:
        return problems  # shape must hold before anything else means anything

    by_path = {r["path"]: r for r in rows if r["path"]}

    # R2 INVENTORY -- the anti-#7 clause. Three independent sources, unioned: a
    # gate-shaped NAME, an artifact GENERATOR (mints a tracked artifact and
    # carries --check; the shape no basename can express), and anything the
    # enforcement path actually runs.
    shaped = gate_shaped_files(root)
    on_path = enforcement_path_scripts(root)
    for f in sorted(shaped | on_path):
        if f not in by_path:
            generator = f in shaped and _mints_and_checks_a_tracked_artifact(root, f) \
                and not any(pat.match(f) for pat in GATE_SHAPED)
            if generator:
                why = ("an artifact GENERATOR (it mints a tracked artifact and carries "
                       "--check, so it is the only thing that can call the committed "
                       "file stale)")
            else:
                why = "gate-shaped by name" if f in shaped else "run by the enforcement path"
            if f in shaped and f in on_path and not generator:
                why = "gate-shaped by name AND run by the enforcement path"
            problems.append(
                f"R2 INVENTORY: {f} is {why}, and has NO row in "
                f"data/gate_registry.json. Every enforcement artifact is classified "
                f"deliberately or not at all -- add a row (kind/claims/wired_by/"
                f"demonstrated) before landing it."
            )

    # R3 WIRED -- re-derived, never read back.
    declared_runners = {r for row in rows for r in row["wired_by"]}
    edges = runner_edges(root, declared_runners)
    for row in rows:
        if row["kind"] in ("leg", "suite-row"):
            continue
        actual = edges.get(row["path"], set())
        declared = set(row["wired_by"])
        if row["kind"] == "gate":
            if not declared and row.get("waiver") is None:
                # Waivable, and only through the waiver: an unwired gate needs an
                # owner and an EXPIRY, so "nothing runs it" cannot quietly become
                # a permanent category. R1 already refuses a waiver without both.
                problems.append(
                    f"R3 WIRED: {row['id']} is kind=gate with an EMPTY wired_by -- a gate "
                    f"nothing runs is not a gate. Wire it, reclassify it as "
                    f"kind=battery/tool with a reason, or waive it with an owner and an "
                    f"expiry that says so out loud."
                )
            if not actual and declared:
                problems.append(
                    f"R3 WIRED: {row['id']} declares runners {sorted(declared)} but NONE of "
                    f"them invokes {row['path']} any more -- the gate has been unwired."
                )
        missing = declared - actual
        extra = actual - declared
        if missing:
            problems.append(
                f"R3 WIRED: {row['id']} declares runner(s) {sorted(missing)} that no longer "
                f"invoke {row['path']} -- restore the call or update the registry row."
            )
        if extra:
            problems.append(
                f"R3 WIRED: {row['id']} is invoked by {sorted(extra)}, which the registry "
                f"does not declare -- record the runner (an undeclared runner is an "
                f"unreviewed one)."
            )

    # R4 DEMO + R5 EVIDENCE + R7 FRESH
    suite_files = selftest_suite_files(root)
    by_id = {r["id"]: r for r in rows}
    for row in rows:
        rid, d, w = row["id"], row.get("demonstrated"), row.get("waiver")
        needs = row["claims"] == "soundness" or row["kind"] == "battery"
        if d is None:
            if needs and w is None:
                problems.append(
                    f"R4 DEMO: {rid} claims={row['claims']} kind={row['kind']} has NO "
                    f"demonstrated failure and no waiver. A soundness gate that has never "
                    f"been seen to fail is the worst artifact in the repo -- add an arm to "
                    f"data/gate_demonstrations.json, or waive it with an owner and an expiry."
                )
            continue
        kind, ref = d["kind"], d.get("ref", "")
        # A leg/suite-row is a thin wrapper: its evidence lives in the script it
        # calls, named by `implemented_by`, so the citation resolves there.
        subject = row["path"] or row.get("implemented_by", "")
        if row["kind"] in ("leg", "suite-row") and not subject:
            problems.append(
                f"R5 EVIDENCE: {rid} is a {row['kind']} carrying a demonstration but names "
                f"no implemented_by -- say which script the evidence lives in"
            )
        # R5 EVIDENCE: the citation must resolve, mechanically.
        if kind == "selftest-inline":
            flag = d.get("flag", "--selftest")
            body = _read(root, subject) if subject else ""
            if not body:
                problems.append(f"R5 EVIDENCE: {rid} claims an inline self-test but {subject or '(no subject)'} is unreadable")
            elif flag not in body:
                problems.append(
                    f"R5 EVIDENCE: {rid} claims an inline self-test {flag!r} that "
                    f"{subject} does not contain -- the self-test was removed while "
                    f"the badge stayed."
                )
        elif kind == "selftest-file":
            if not (root / ref).exists():
                problems.append(f"R5 EVIDENCE: {rid} names self-test {ref}, which does not exist")
            elif ref not in suite_files:
                problems.append(
                    f"R5 EVIDENCE: {rid} names self-test {ref}, which "
                    f"scripts/check_script_selftests.sh does not run -- a self-test "
                    f"nobody runs demonstrates nothing."
                )
        elif kind == "mutation-record":
            if not (root / ref).exists():
                problems.append(f"R5 EVIDENCE: {rid} names mutation record {ref}, which does not exist")
            else:
                text = _read(root, ref)
                needle = Path(subject).name if subject else rid
                if needle not in text and rid not in text:
                    problems.append(
                        f"R5 EVIDENCE: {rid} names mutation record {ref}, which never "
                        f"mentions {needle} -- a record pointed at unrelated evidence."
                    )
            if row["claims"] == "soundness" and w is None and not d.get("replayable"):
                problems.append(
                    f"R4 DEMO: {rid} claims soundness and its only demonstration is a "
                    f"dated record ({ref}), which nothing replays. Add a replayable arm "
                    f"to data/gate_demonstrations.json, or waive with an expiry."
                )
        if d.get("replayable"):
            arm_key = d.get("inherited_from", rid)
            if arm_key not in demos:
                problems.append(
                    f"R5 EVIDENCE: {rid} is marked replayable but has no arms in "
                    f"data/gate_demonstrations.json under {arm_key!r}"
                )
            elif not demos[arm_key]:
                problems.append(f"R5 EVIDENCE: {rid} has an EMPTY arm list -- zero arms is not a demonstration")
        # R7 FRESH -- over `subject`, which is `path` OR `implemented_by`.
        #
        # A `gate`/`battery` row IS its script, so `path` was the whole story for
        # those. A `leg` or `suite-row` is a thin wrapper: the code that runs
        # lives in `implemented_by`, and until 2026-08-30 NOTHING pinned it. That
        # left seven rows carrying a demonstration frozen against nothing --
        # exactly the blind spot R7 exists to close, one level up, because the
        # badge was on a different file from the gate. Two of the seven had
        # already moved under it, measured by hashing each implementation at the
        # commit that recorded its demonstration against HEAD:
        #   soundness-cert   crates/clean-kernel/src/env/soundness_certificate.rs
        #                    9db72a1560cc -> b1c503b93769  (7c4d32693, 2026-08-27)
        #   everyday-battery crates/clean-elab/src/lean4_corpus_tests.rs
        #                    443414e74c7c -> 8e0155dafc90  (bd60299ac, 2026-08-27)
        #
        # Cost: one extra sha256 per self-demonstrated leg (five files, ~0.9 MB
        # all told). A DELEGATED row hashes nothing -- the parent's own R7 does
        # that work, which is why the delegation has to be checked rather than
        # believed.
        # R4b UNDEMONSTRATED PIN (audit r11 M11-1b, made non-optional r13 M13-9).
        #
        # THE ACCOUNT USED TO BE THE ONLY RECORD, so deleting it re-greened the
        # row: `if _rwd:` meant absent = no check, `--repin` then re-minted
        # renewals to 0, first_issued to today and pinned_sha256 from the current
        # subject, and the deletion diff is byte-identical to a legitimate
        # discharge. R4b's own red message named the account as the problem,
        # making deletion the cheapest green. It is asymmetric with the waiver it
        # was modelled on: a removed waiver reds because what it excuses is
        # independently checked.
        #
        # So the excused condition is checked independently now. A row that
        # cites a mutation record whose sha does not match its pin is RED by
        # R7b whether or not an account exists; the account only SUPPRESSES that
        # red, and only while it is valid. Deleting it therefore goes red rather
        # than green -- but ONLY for a row R7b reaches (one citing a reports/*.json
        # record with a script_sha256). A row whose demonstration is a
        # Every other row (all but two today) cites no such record. For a pin
        # under a soundness claim, R7c (check_replay_record_debt) catches the
        # hand edit instead: such a pin carries its replay record or an account,
        # or is named as debt in data/replay_record_debt.json. Elsewhere -- a debt
        # row, or a row no soundness claim stands on -- deleting an account or
        # moving a pin by hand still goes green unseen (review of d5619e490,
        # 2026-11-13; R7c widened by its own review, 2026-11-14).
        #
        # An account never stands under a soundness claim that has a replay
        # route (2026-11-13, same review). R4 makes a soundness row's dated
        # mutation record replayable so its pin moves over a replay; an account
        # is a pin no replay backs. So R4b reds an account on a row with a
        # replay route (a runnable ref or replayable arms, as `repin` judges)
        # when that row, or any row inheriting its pin, claims soundness --
        # d5619e490 re-greened the soundness leg trust-ir-codegen-ratchet that
        # way, through its evidence-claiming parent trust_ir_build. A soundness
        # row with no route at all (a cargo-test ref nothing here runs) keeps
        # the account as its only verb, as R4 accepts such rows unreplayed.
        _rwd = d.get("repinned_without_demonstration")
        if _rwd:
            if not isinstance(_rwd, dict):
                problems.append(
                    f"R4b UNDEMONSTRATED: {rid} carries a free-text "
                    f"repinned_without_demonstration; it must be an object with "
                    f"reason, owner and expires so it can be read and can lapse")
            else:
                _exp = str(_rwd.get("expires") or "")
                if not ISO.match(_exp):
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} undemonstrated-pin account has "
                        f"expires={_exp!r}, not YYYY-MM-DD")
                elif _exp < today:
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} was re-pinned without a "
                        f"demonstration and that account EXPIRED {_exp} (owner "
                        f"{_rwd.get('owner')}) -- demonstrate it now or restore the pin")
                elif _exp > _HORIZON:
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} undemonstrated-pin account expires "
                        f"{_exp}, beyond the 180-day horizon ({_HORIZON})")
                if _rwd.get("pinned_sha256") and d.get("script_sha256") \
                        and _rwd["pinned_sha256"] != d["script_sha256"]:
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} carries an undemonstrated-pin "
                        f"account written for sha256:{str(_rwd['pinned_sha256'])[:12]} "
                        f"but the row now pins sha256:{str(d['script_sha256'])[:12]} -- "
                        f"the excuse does not travel to a later edit")
                if not str(_rwd.get("reason") or "").strip():
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} undemonstrated-pin account has no reason")
                _own = str(_rwd.get("owner") or "").strip()
                if not _own or _own == "(unnamed)":
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} undemonstrated-pin account has no named "
                        f"owner (audit r12 M12-7: R4b checked reason and never owner, while "
                        f"the mint defaulted owner to the literal '(unnamed)')")
                if _rwd.get("renewals", 0) >= 1:
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} undemonstrated-pin account has been "
                        f"RENEWED (first issued {_rwd.get('first_issued')}) -- renewal is not "
                        f"a discharge; demonstrate it")
            if _has_replay_route(root, d):
                for _sound in _soundness_under_account(rows, row):
                    problems.append(
                        f"R4b UNDEMONSTRATED: {rid} carries an undemonstrated-pin "
                        f"account under {_sound}'s soundness claim, and {rid} has a "
                        f"replay route -- re-pin it over a replay (--repin {rid}) "
                        f"where its demonstration runs, or restore the pin")

        pinned = d.get("script_sha256")
        parent_id = d.get("inherited_from")
        # R7b RECORD AGREEMENT (audit r9 M-3). A row whose demonstration cites a
        # committed mutation-proof record must pin the SAME sha that record
        # says it demonstrated. Without this, `--repin` on a row whose ref is
        # not runnable is a blind re-hash: the r8 commit advanced
        # `source_elab_gate`'s pin past the record that backs it, so a refusal
        # and its own sanctioned bypass shipped demonstrated by nothing while
        # every rule stayed green. R7 asks "does the pin match the file?"; this
        # asks the question R7 cannot: "does the pin match the EVIDENCE?"
        if pinned:
            import re as _re7b
            _blob = json.dumps(d)
            _seen, _match = [], False
            for _rec in sorted(set(_re7b.findall(r"reports/[\w./-]+\.json", _blob))):
                _rp = root / _rec
                if not _rp.exists():
                    continue
                try:
                    _rj = json.loads(_rp.read_text())
                except (OSError, ValueError):
                    continue
                _rsha = _rj.get("script_sha256")
                if not _rsha:
                    continue
                _seen.append((_rec, _rsha))
                if _rsha == pinned:
                    _match = True
            # A row may cite SEVERAL records -- the current demonstration plus
            # the historical ones it does not retire. History is not drift, so
            # the rule is "at least one cited record demonstrates THIS pin",
            # not "all of them do".
            # audit r13 M13-9: a VALID account suppresses this red; an absent
            # one cannot, which is what makes deletion go red instead of green.
            _acct = d.get("repinned_without_demonstration") or {}
            _acct_ok = (isinstance(_acct, dict)
                        and ISO.match(str(_acct.get("expires") or ""))
                        and str(_acct.get("expires")) >= today
                        and str(_acct.get("owner") or "").strip() not in ("", "(unnamed)")
                        and _acct.get("renewals", 0) < 1)
            if _seen and not _match and not _acct_ok:
                _lst = ", ".join(f"{r} -> sha256:{h[:12]}" for r, h in _seen)
                problems.append(
                    f"R7b RECORD: {rid} pins sha256:{str(pinned)[:12]} and NO cited record "
                    f"demonstrates that sha ({_lst}) -- the pin moved past its evidence, so "
                    f"the row is backed only by records about other versions of the file. "
                    f"Re-demonstrate at the new sha and mint a record, or restore the pin.")
        if pinned and parent_id and (parent_id == rid or parent_id not in by_id):
            # Review of R7c (2026-11-14): a row with its own pin is judged on it
            # here, so the delegation checks below never ran for it, and
            # `inherited_from` naming the row itself or no row passed unread --
            # while R7c, R7b and R12 read the field as "this pin is someone else's".
            problems.append(
                f"R7 FRESH: {rid} pins its own subject and names inherited_from "
                f"{parent_id!r}, which is {'the row itself' if parent_id == rid else 'no registry row'} "
                f"-- a delegation pointer names another row, or is removed.")
        if pinned:
            live = _sha256(root, subject)
            if not live:
                problems.append(
                    f"R7 FRESH: {rid} pins {subject or '(no subject)'} at "
                    f"sha256:{str(pinned)[:12]}, and that file cannot be read -- "
                    f"a pin against nothing is not a pin."
                )
            elif live != pinned:
                what = "script" if row["path"] else "implementation"
                problems.append(
                    f"R7 FRESH: {rid} was demonstrated against {subject} at "
                    f"sha256:{str(pinned)[:12]}, the tree has sha256:{live[:12]}. "
                    f"The {what} changed since it was last seen to fail -- "
                    f"re-demonstrate "
                    f"(scripts/check_gate_registry.py --demonstrate {rid}) then "
                    f"--repin {rid}."
                )
            # The DERIVED inputs (see PINNED_INPUTS_FLAG).
            declares = _answers_pinned_inputs(root, subject)
            pinned_inputs = d.get("inputs")
            if pinned_inputs is not None and not declares:
                problems.append(
                    f"R7 FRESH: {rid} pins a derived input set, and {subject} no longer "
                    f"declares one (ANSWERS_PINNED_INPUTS) -- the files it runs besides "
                    f"itself would go unwatched. Restore the declaration, or remove "
                    f"`inputs` from the row by hand, in the diff.")
            elif declares and (not isinstance(pinned_inputs, dict) or not pinned_inputs):
                problems.append(
                    f"R7 FRESH: {rid} is implemented by {subject}, which derives the files "
                    f"its verdict depends on ({PINNED_INPUTS_FLAG}), and the row pins only "
                    f"{subject} -- an edit to any of the others would leave the recorded "
                    f"arms un-replayed. Re-demonstrate "
                    f"(scripts/check_gate_registry.py --demonstrate {rid}) then "
                    f"--repin {rid}.")
            elif declares:
                derived, why = _derived_inputs(root, subject)
                if derived is None:
                    problems.append(f"R7 FRESH: {rid} cannot re-derive its pinned inputs: "
                                    f"{why} -- a pin that cannot be re-derived is not a pin")
                else:
                    drift = _inputs_drift(pinned_inputs, derived)
                    if drift:
                        problems.append(
                            f"R7 FRESH: {rid} was demonstrated against a derived input set "
                            f"that has moved since ({drift}) -- the gate RUNS those files, "
                            f"so its arms were last seen to fail over other code. "
                            f"Re-demonstrate (scripts/check_gate_registry.py --demonstrate "
                            f"{rid}) then --repin {rid}.")
            unreplayed = _replay_disagreement(rid, d)
            if unreplayed:
                problems.append(f"R7 FRESH: {unreplayed}. Re-pin it with "
                                f"scripts/check_gate_registry.py --repin {rid}.")
        elif parent_id:
            # DELEGATED freshness: this row inherits another row's arms, so that
            # row's pin is what watches the code. True only if the parent pins
            # THIS row's implementation; a delegation onto some other file is the
            # same hole wearing a pointer.
            parent = by_id.get(parent_id)
            if parent is None:
                problems.append(
                    f"R7 FRESH: {rid} inherits its demonstration from "
                    f"{parent_id!r}, which has no registry row -- its freshness "
                    f"is delegated to nothing."
                )
            elif not (parent.get("demonstrated") or {}).get("script_sha256"):
                problems.append(
                    f"R7 FRESH: {rid} inherits from {parent_id}, which carries no "
                    f"script_sha256 -- an unpinned parent cannot hold this row's "
                    f"pin for it."
                )
            elif _subject(parent) != subject:
                problems.append(
                    f"R7 FRESH: {rid} is implemented by {subject} and inherits its "
                    f"demonstration from {parent_id}, which pins "
                    f"{_subject(parent) or '(nothing)'}. The delegation watches a "
                    f"DIFFERENT file from the one that runs -- pin {subject} on "
                    f"this row instead."
                )
        elif subject:
            problems.append(
                f"R7 FRESH: {rid} carries a demonstration with NO freshness pin, "
                f"so its implementation ({subject}) can be rewritten under the "
                f"badge and nothing says so. Re-demonstrate "
                f"(scripts/check_gate_registry.py --demonstrate {rid}) then "
                f"--repin {rid}; or set inherited_from to a row that already pins "
                f"that exact file."
            )

    # R8 RETIRED -- the retirement record, re-derived like everything else.
    retired = doc.get("retired", [])
    if not isinstance(retired, list):
        problems.append("R1 SHAPE: data/gate_registry.json 'retired' must be a list")
        retired = []
    live_ids = {r["id"] for r in rows}
    wired_ids = {
        r["id"] for r in rows
        if r["wired_by"] or r["kind"] in ("leg", "suite-row")
    }
    seen_retired: set[str] = set()
    for i, ent in enumerate(retired):
        if not isinstance(ent, dict):
            problems.append(f"R1 SHAPE: retired[{i}] is not an object")
            continue
        rid = ent.get("id", f"<retired {i}>")
        missing = [k for k in RETIRED_REQUIRED if k not in ent]
        if missing:
            problems.append(
                f"R1 SHAPE: retired {rid} is missing key(s): {', '.join(missing)}"
            )
            continue
        if rid in seen_retired:
            problems.append(f"R1 SHAPE: duplicate retired id {rid}")
        seen_retired.add(rid)
        if rid in live_ids:
            problems.append(
                f"R8 RETIRED: {rid} is listed as retired AND as a live row -- "
                f"one artifact, one state"
            )
        if not ISO.match(str(ent["retired"])):
            problems.append(f"R1 SHAPE: retired {rid} retired={ent['retired']!r} is not YYYY-MM-DD")
        elif str(ent["retired"]) > today:
            problems.append(f"R1 SHAPE: retired {rid} retired={ent['retired']} is in the future")
        if ent["path"] and (root / ent["path"]).exists():
            problems.append(
                f"R8 RETIRED: {rid} is recorded retired but {ent['path']} is STILL IN "
                f"THE TREE. A retired gate somebody can still run is a gate -- delete "
                f"the file or take the row out of `retired`."
            )
        succ = ent["superseded_by"]
        if not isinstance(succ, list):
            problems.append(f"R1 SHAPE: retired {rid} superseded_by must be a list")
            continue
        if not succ and not ent.get("enforces_nothing"):
            problems.append(
                f"R8 RETIRED: {rid} supersedes NOTHING and does not say so. Name the "
                f"row(s) that carry the property now, or set enforces_nothing:true "
                f"and say in `reason` why the property stopped needing a gate."
            )
        for s in succ:
            if s not in live_ids:
                problems.append(
                    f"R8 RETIRED: {rid} claims {s!r} carries its property, and {s!r} "
                    f"has no registry row -- the successor must be a live gate."
                )
            elif s not in wired_ids:
                problems.append(
                    f"R8 RETIRED: {rid} is superseded by {s!r}, which is itself UNWIRED. "
                    f"Retiring a gate onto an orphan moves the hole, it does not close "
                    f"it -- this is exactly how prover_phase_0_audit came to 'duplicate' "
                    f"an orphan."
                )

    # R9 SCANNER -- how a row's implementation reads source, re-derived.
    #
    # AUDIT r17 (2026-09-14): the subject is `path OR implemented_by`, not
    # `path`. R9 read `path` alone while R5/R7 (:1506), R7b's delegation, R10,
    # R4's arm coverage and this file's own `_subject()` helper all resolve
    # both -- so for a `leg` or `suite-row`, whose `path` is "", R9 computed
    # reads=False and SKIPPED the row: no `source_scan` demanded, and the
    # raw-lines-for-a-soundness-row refusal never reached. 57 rows carry only
    # `implemented_by` and 22 of them satisfy R9's own READS_SOURCE detector.
    # Twenty-one were covered only INCIDENTALLY, by a sibling `path` row for the
    # same file whose declaration happened to be compatible; one was not covered
    # at all (`nat-operand-shape`, which globs `*.lean`). This is the same defect
    # that was found and fixed for R7 on 2026-08-30 and never carried across.
    for row in rows:
        rel = _subject(row)
        decl = row.get("source_scan")
        # A leg's declaration may be its GATE sibling's, but only DERIVED: the
        # sibling must be the row whose `path` IS this row's implementation, and
        # the raw-lines refusal below is then applied at THIS row's claims, not
        # the sibling's. Before r17 that coverage was incidental -- 21 of the 22
        # reads-source leg rows happened to have such a sibling and nothing said
        # so, so the day a soundness leg pointed at a file that is no other
        # row's path, R9 would have gone quiet instead of red.
        declared_via = None
        if decl is None and not row.get("path") and rel:
            sibling = by_path.get(rel)
            if sibling is not None and sibling.get("source_scan") is not None:
                decl = sibling["source_scan"]
                declared_via = sibling["id"]
        raw = _read(root, rel) if rel and (root / rel).exists() else ""
        body = script_code_only(rel, raw) if rel and rel.endswith(
            (".py", ".sh", ".rs", ".lean")
        ) else raw
        # This file DEFINES READS_SOURCE, so its own pattern literals name every
        # token the detector looks for. It reads no .rs file; the exemption is
        # named here rather than hidden in a regex so it stays visible.
        reads = rel != "scripts/check_gate_registry.py" and bool(body) and bool(
            READS_SOURCE.search(body)
        )
        rid = row["id"]
        if not reads:
            # Only a row's OWN key can be stale; an inherited one is the
            # sibling's problem and is reported against the sibling.
            if row.get("source_scan") is not None:
                problems.append(
                    f"R9 SCANNER: {rid} declares source_scan, but {rel} no longer reads "
                    f"Rust/Lean source -- a stale declaration describes a scanner that "
                    f"is gone; delete the key"
                )
            continue
        if decl is None:
            problems.append(
                f"R9 SCANNER: {rid} ({rel}) READS RUST/LEAN SOURCE and declares no "
                f"`source_scan`. Say how it reads it: \"lexed\" (comments and string "
                f"literals blanked before matching), \"raw-lines\" (matches prose too "
                f"-- refused for a soundness row), or \"digest\" (hash/parse, not a "
                f"text match). A scanner that counts MENTIONS instead of CODE moves "
                f"the wrong way on a fix; this is the declaration that makes the next "
                f"one visible when it lands."
            )
            continue
        if not isinstance(decl, dict):
            problems.append(f"R1 SHAPE: {rid} source_scan must be an object")
            continue
        kind = decl.get("kind")
        if kind not in SOURCE_SCAN_KINDS:
            problems.append(
                f"R1 SHAPE: {rid} source_scan.kind={kind!r} is not one of {SOURCE_SCAN_KINDS}"
            )
            continue
        if not decl.get("note"):
            problems.append(
                f"R1 SHAPE: {rid} source_scan needs a `note` saying what it matches "
                f"and over what scope"
            )
        strips = bool(STRIPS_NONCODE.search(body))
        # A gate may lex THROUGH a file it runs (2026-11-01: check_test_target_
        # coverage reads Rust only through scripts/rust_modules.py, the module
        # walk it shares with check_cargo_test_selectors and verify_runner, and
        # holds no stripper of its own). That counts only for a file the gate
        # DERIVES as an input (`--pinned-inputs`), which R7 pins, so an edit to
        # the walker re-demonstrates the gate; only for one the gate's own code
        # names, so pinning the reference lexer beside a walker that never
        # calls it is no evidence; and only for a stripper that file's CODE
        # USES (`_lexes_through`), never a name in a comment or a bare `def`.
        if kind == "lexed" and not strips and not _lexes_through(root, rel):
            problems.append(
                f"R9 SCANNER: {rid} declares source_scan.kind=\"lexed\", and {rel} "
                f"contains no recognised comment/literal stripper, nor does an input it "
                f"derives (--pinned-inputs) and names in its code use one. Either it does not "
                f"lex (say \"raw-lines\" -- and a soundness row may not) or the "
                f"stripper is spelled in a way STRIPS_NONCODE does not know; add it "
                f"there deliberately."
            )
        if kind == "raw-lines" and row["claims"] == "soundness":
            problems.append(
                f"R9 SCANNER: {rid} claims SOUNDNESS and decides by matching RAW "
                f"SOURCE TEXT. That is the prover_phase_0_audit defect: the count "
                f"includes comments and string literals, so it moves the WRONG WAY "
                f"on the `// SOUNDNESS:` comment CLAUDE.md requires. Lex it (see "
                f"`scripts/check_add_decl_ratchet.py`), or drop the soundness claim."
            )

    # R6 IDS
    for kind, actual_ids, source in (
        ("leg", gate_leg_ids(root), LOCAL_GATE),
        ("suite-row", suite_row_ids(root), VERIFY_RUNNER),
    ):
        declared = {r["id"] for r in rows if r["kind"] == kind}
        live = set(actual_ids)
        for extra in sorted(live - declared):
            problems.append(
                f"R6 IDS: {source} declares {kind} {extra!r}, which has no registry row"
            )
        for gone in sorted(declared - live):
            problems.append(
                f"R6 IDS: registry has {kind} {gone!r}, which {source} no longer declares"
            )
    # R5 EVIDENCE, the SHAPE half: an arm whose mutation carries no payload for
    # its op is a demonstration that CANNOT RUN, and until 2026-08-30 nothing
    # said so until somebody replayed it -- which for these three arms nobody
    # ever had. Static, in the 0.27 s check the hook runs, because the replay is
    # exactly the thing that does not run often enough to be a gate.
    #
    # This block sits AFTER the row loop, and that is load-bearing: written
    # inside it at 4-space indent it silently CLOSED the row loop, so R7 and
    # everything below became this loop's body and six R7 arms went green.
    # Caught by the selftest in the same minute; recorded because the file
    # parses either way.
    for arm_id, arm_list in sorted(demos.items()):
        for arm in (arm_list if isinstance(arm_list, list) else []):
            mut = arm.get("mutate") or {}
            want = MUT_KEYS.get(mut.get("op"))
            if want is None:
                problems.append(
                    f"R5 EVIDENCE: {arm_id} arm {arm.get('arm')!r} has mutation op "
                    f"{mut.get('op')!r}, which `_apply` does not implement")
            elif want not in mut:
                problems.append(
                    f"R5 EVIDENCE: {arm_id} arm {arm.get('arm')!r} is an "
                    f"{mut.get('op')!r} mutation with no {want!r} (keys: {sorted(mut)}) "
                    f"-- it would fail the moment anyone replayed it")
    problems.extend(check_pushed_tips(root))
    problems.extend(check_soundness_claims_ratchet(root, doc))
    problems.extend(check_r7b_coverage(root, doc))
    problems.extend(check_replay_record_debt(root, doc))
    try:
        _demos = json.loads((root / "data/gate_demonstrations.json").read_text())
    except (OSError, ValueError):
        _demos = {"arms": {}}
    problems.extend(check_arm_coverage(root, doc, _demos))
    return problems


# -- R10 PUSHED: R7 over the commit being pushed ------------------------------
#
# WHY THIS EXISTS, MEASURED.
#
# R7 hashes `row["path"]` out of the WORKING TREE. That is the right question
# when the working tree is what is being landed. It is not what happens here.
# The standing lane protocol in this repo composes a commit with `git
# commit-tree` over a temporary `GIT_INDEX_FILE` and pushes THAT sha, so the
# pusher's working tree can sit at an entirely different commit than the one
# going to the remote -- and `git`'s pre-push hook runs in the working tree, not
# in the pushed one.
#
# The hole is not hypothetical. Measured 2026-08-25, in two detached worktrees:
#
#   $ git worktree add --detach wt-r7 7c0801a9e && cd wt-r7
#   $ python3 scripts/check_gate_registry.py; echo $?
#   GATE_REGISTRY=fail problems=1
#     R7 FRESH: clean-elab::tactic::bypass_ratchet was demonstrated against
#     crates/clean-elab/src/tactic/tests/bypass_ratchet.rs at
#     sha256:b6d05778ea12, the tree has sha256:e08259428cc5. ...
#   1
#
#   $ cd $HOME/clean   # working tree parked at 3086bbc21
#   $ python3 scripts/check_gate_registry.py; echo $?
#   GATE_REGISTRY=ok rows=103 ...
#   0
#
# Same push, two answers. The leg asked the second question, got a 0, and
# 7c0801a9e landed on origin/main carrying an R7 RED that stayed there for four
# commits until an unrelated lane tripped over it while rebasing. R7 caught the
# gutted-script case it was built for and could not catch this one, because it
# was never looking at the object being shipped.
#
# So the pushed TIP is re-checked in its own terms: both the registry and the
# pinned script are read out of that commit's tree with `git show`, no checkout
# and no working-tree state involved. The TIP specifically, not every commit in
# the range -- what the measured harm was is `origin/main`'s tip carrying a red,
# and a mid-stack commit that repins in the next commit is a normal stack, not a
# defect. If a bisectable-every-commit rule is ever wanted it is a strictly
# larger rule and it gets its own id.
#
# This is additive: R7 still runs on the working tree exactly as before, and
# with no CLEAN_PUSH_RANGES in the environment (every interactive run, every
# `local_gate.sh` run, every existing self-test arm) `check_pushed_tips` returns
# an empty list and nothing changes.
#
# WHOSE COPY OF THIS RULE RUNS (verifier r9 recheck, 2026-09-25). Since r9 the
# hook's legs run inside a clean checkout of the pushed commit, and for one
# revision the hook handed that checkout to the commit's OWN pre-push file: a
# commit adding `exit 0` to its hook and an unpinned edit to a gate script
# pushed with no leg run, this rule included. So the hook's outer role (the
# pusher's copy) now runs `--pushed-in <checkout>` with the pusher's copy of
# THIS script before anything of the commit's runs: a pushed commit that edits
# a pinned gate -- this file, or the hook's legs' scripts -- without re-pinning
# it is refused by code the commit did not write.


GIT_ZERO = "0" * 40


def _git_show(root: Path, tip: str, rel: str) -> bytes | None:
    """The bytes of `rel` in commit `tip`, or None if that commit has no such path."""
    proc = subprocess.run(
        ["git", "show", f"{tip}:{rel}"],
        cwd=str(root), capture_output=True, check=False,
    )
    return proc.stdout if proc.returncode == 0 else None


def pushed_tips() -> list[str]:
    """The local shas this push puts on the remote, from the hook's export.

    Same env contract as scripts/check_fmt_changed.py: one "<remote> <local>"
    line per updated ref. A deletion carries an all-zero local sha and has no
    tree to check.
    """
    raw = os.environ.get("CLEAN_PUSH_RANGES", "").strip()
    tips: list[str] = []
    for line in raw.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        local_sha = parts[1]
        if local_sha == GIT_ZERO or local_sha in tips:
            continue
        tips.append(local_sha)
    return tips


def _is_clean_checkout_of(root: Path, tip: str) -> bool:
    """True when `root` is a checkout whose HEAD is `tip` with no tracked
    change -- then the working-tree rules (R7) judged exactly the pushed tree."""
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(root),
                          capture_output=True, text=True, check=False)
    if head.returncode != 0 or head.stdout.strip() != tip:
        return False
    dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"],
                           cwd=str(root), capture_output=True, text=True, check=False)
    return dirty.returncode == 0 and not dirty.stdout.strip()


def check_pushed_tips(root: Path) -> list[str]:
    problems: list[str] = []
    for tip in pushed_tips():
        # Say WHICH of the two failures this is. A sha that is not a commit
        # HERE and a commit that is missing the registry are different
        # accidents with different fixes, and reporting the second for the
        # first sent one reader hunting for a deleted file that was never
        # deleted (measured on this rule's own first hook run, 2026-08-25 --
        # the four green-control self-test arms inherited the hook's
        # CLEAN_PUSH_RANGES into a synthetic non-git directory and were told
        # the registry was missing).
        if subprocess.run(["git", "cat-file", "-e", f"{tip}^{{commit}}"],
                          cwd=str(root), capture_output=True,
                          check=False).returncode != 0:
            problems.append(
                f"R10 PUSHED: {tip[:9]} is not a commit in the repository at "
                f"{root} -- this rule reads the pushed object out of the repo "
                f"the hook is running in, and cannot judge a sha that is not "
                f"there."
            )
            continue
        blob = _git_show(root, tip, "data/gate_registry.json")
        if blob is None:
            problems.append(
                f"R10 PUSHED: commit {tip[:9]} has no data/gate_registry.json. "
                f"Every commit that reaches the remote carries the registry; a "
                f"push whose tip does not is not a state this gate can judge, "
                f"and it is not therefore a pass."
            )
            continue
        try:
            doc = json.loads(blob.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            problems.append(
                f"R10 PUSHED: data/gate_registry.json in commit {tip[:9]} is not "
                f"valid JSON ({exc}) -- the registry is unreadable in the object "
                f"being shipped"
            )
            continue
        rows = doc.get("rows")
        if not isinstance(rows, list):
            problems.append(
                f"R10 PUSHED: data/gate_registry.json in commit {tip[:9]} carries "
                f"no 'rows' list"
            )
            continue
        judged_here = _is_clean_checkout_of(root, tip)
        for row in rows:
            if not isinstance(row, dict):
                continue
            d = row.get("demonstrated")
            if not isinstance(d, dict):
                continue
            if isinstance(d.get("inputs"), dict) and not judged_here:
                # A derived input set is re-derived by RUNNING the subject over
                # a tree, so the pushed commit's set exists only in a checkout
                # of it. Where this runs IS one (the pre-push hook runs every leg
                # in a checkout of the commit it pushes), R7 above already
                # judged it; anywhere else this cannot, and says so.
                problems.append(
                    f"R10 PUSHED: {row.get('id')} pins a derived input set, which is "
                    f"re-derived by running {_subject(row) or 'its subject'}, so only a "
                    f"clean checkout of {tip[:9]} can judge it and {root} is not one -- "
                    f"the pre-push hook runs every leg in such a checkout."
                )
            unreplayed = _replay_disagreement(str(row.get("id")), d)
            if unreplayed:
                problems.append(f"R10 PUSHED: in commit {tip[:9]}, {unreplayed}.")
            pinned = d.get("script_sha256")
            # Same subject as R7: a leg's pin is on its `implemented_by`, and
            # R10 is R7 over the commit being pushed, so it has to read the same
            # file or the two rules would disagree about what is pinned.
            rel = _subject(row)
            if not pinned or not rel:
                continue
            content = _git_show(root, tip, rel)
            if content is None:
                problems.append(
                    f"R10 PUSHED: {row.get('id')} pins {rel} at "
                    f"sha256:{str(pinned)[:12]}, and commit {tip[:9]} does not "
                    f"contain that path at all -- the pushed tree cannot honour "
                    f"its own demonstration."
                )
                continue
            live = hashlib.sha256(content).hexdigest()
            if live != pinned:
                problems.append(
                    f"R10 PUSHED: {row.get('id')} is pinned at "
                    f"sha256:{str(pinned)[:12]} and {rel} in the commit you are "
                    f"pushing ({tip[:9]}) is sha256:{live[:12]}. The working tree "
                    f"may well be consistent -- this rule reads the OBJECT BEING "
                    f"SHIPPED, which is the one that becomes origin/main. "
                    f"Re-demonstrate and repin IN THE COMMIT: "
                    f"scripts/check_gate_registry.py --demonstrate {row.get('id')} "
                    f"&& scripts/check_gate_registry.py --repin {row.get('id')}, "
                    f"then rebuild the commit so data/gate_registry.json travels "
                    f"with the edit."
                )
    return problems


# ── reporting ────────────────────────────────────────────────────────────────


R7B_COVERAGE_REL = "data/r7b_record_coverage.json"


def r7b_backed_rows(root: Path, rows: list[dict]) -> tuple[set[str], int]:
    """(ids R7b can actually judge, count of ids it is eligible to judge).

    AUDIT r14 M14-5. R7b compares a row's pin against the sha a committed
    evidence record says it demonstrated -- but only for a row whose
    `demonstrated` block CITES such a record. Measured 2026-09-02: one row of
    64. A rule that reaches 1.6% of its subject is not wrong, but a rule whose
    reach can silently fall to zero is unanchored, and nothing here read that
    number back until this function existed.
    """
    backed: set[str] = set()
    eligible = 0
    for row in rows:
        d = row.get("demonstrated") or {}
        if not d.get("script_sha256") or d.get("inherited_from"):
            continue
        eligible += 1
        blob = json.dumps(d)
        for rec in sorted(set(re.findall(r"reports/[\w./-]+\.json", blob))):
            path = root / rec
            if not path.exists():
                continue
            try:
                doc = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                continue
            if isinstance(doc, dict) and doc.get("script_sha256"):
                backed.add(row["id"])
                break
    return backed, eligible


def check_r7b_coverage(root: Path, doc: dict) -> list[str]:
    """R7b REACH: a row may not silently leave R7b's reach.

    The set only shrinks by editing the artifact, which is reviewable; it may
    grow freely. This does NOT assert a coverage target -- see the artifact's
    own `_not_a_target`.
    """
    path = root / R7B_COVERAGE_REL
    try:
        anchor = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        return [f"R7b REACH: {R7B_COVERAGE_REL} is missing. R7b's reach was measured "
                f"at 1 of 64 rows; without the anchor a fall to zero is silent."]
    except ValueError as exc:
        return [f"R7b REACH: {R7B_COVERAGE_REL} is not valid JSON: {exc}"]
    committed = anchor.get("rows")
    if not isinstance(committed, list) or not all(isinstance(x, str) for x in committed):
        return [f"R7b REACH: {R7B_COVERAGE_REL} must carry a list of row ids under 'rows'"]
    if anchor.get("count") != len(committed):
        return [f"R7b REACH: {R7B_COVERAGE_REL} says count={anchor.get('count')!r} beside "
                f"{len(committed)} row(s) -- the two halves of one claim disagree."]
    backed, eligible = r7b_backed_rows(root, doc["rows"])
    out = []
    for rid in sorted(set(committed) - backed):
        out.append(
            f"R7b REACH: {rid} is anchored as record-backed and is not any more -- its "
            f"demonstration no longer cites a committed reports/*.json carrying a "
            f"script_sha256, so R7b can no longer ask whether its pin matches its "
            f"evidence. Restore the citation, or remove the id from "
            f"{R7B_COVERAGE_REL} deliberately.")
    if not out and eligible and len(backed) < len(committed):
        out.append(f"R7b REACH: {len(backed)} backed rows against {len(committed)} anchored")
    return out


REPLAY_DEBT_REL = "data/replay_record_debt.json"

# The debt as it was MINTED (docs/DECISIONS.md, 2026-11-14): the only ids the
# anchor may name. --repin removes a row from the anchor and never adds one, so
# the anchor shrinks inside this set; naming any other id is refused, and
# widening the set is an edit to this R7-pinned file, which moves only over its
# own self-test (--repin check_gate_registry). Review of R7c: an anchor the
# check compared with nothing reopened the hand-edit hole with one appended id.
REPLAY_DEBT_MINTED = frozenset({
    "axiom_audit_release_check",
    "clean-auto::ay_coupling_boundary_ratchet",
    "clean-auto::expr_let_constructor_hygiene",
    "clean-cli::cmd_replacement::row_prose_inertness",
    "clean-cli::cmd_replacement::self_reported_gate_refusal",
    "clean-cli::replacement::evidence_substitution",
    "clean-elab::cert::external::tests_source_hygiene",
    "clean-elab::tactic::bypass_ratchet",
    "clean-elab::tactic::replace_target_ratchet",
    "clean-elab::trust_soundness_ouroboros_gate",
    "crystal_fixture_freshness",
    "gate::masquerade",
    "lean-profile-reducer-differential",
    "native-exec-battery",
    "trust-verify-soundness",
})
# The self-test's mini-repo names its own debt; `selftest()` sets this for the
# duration of its run and nothing else does.
_REPLAY_DEBT_FIXTURE: frozenset = frozenset()


def replay_record_debt(rows: list[dict]) -> set[str]:
    """The rows with a pin of their own (`script_sha256`) that a soundness claim
    stands on (their own, or that of a row inheriting their pin) and that carry
    neither a replay record (an object under `replayed`) nor an undemonstrated-pin
    account (`repinned_without_demonstration`, which R4b polices).

    Review of d5619e490 (2026-11-13): R7 compares a pin with the live file and
    `_replay_disagreement` compares it with its replay record, but a pin moved
    by hand together with deleting that record satisfies both. Such a row reads
    exactly like one that never had a record. So the rows with no record are
    named, once, in an anchor: anything else must carry one.

    Review of R7c (2026-11-14) narrowed the exemptions to the two records:
    a row is judged on its OWN pin whether or not it also names `inherited_from`
    (R7 judges such a row self-pinned, so the field took it out of this rule
    while R7 never checked the delegation), and the rule no longer asks whether
    the row has a replay route, which is read from free text (`ref`,
    `replayable`) that a one-word edit removes. A row nothing can replay stays
    named until it gains a route and a --repin, or carries an account.
    """
    owed: set[str] = set()
    for row in rows:
        d = row.get("demonstrated")
        if not isinstance(d, dict) or not d.get("script_sha256"):
            continue
        if isinstance(d.get("replayed"), dict) or d.get("repinned_without_demonstration"):
            continue
        if _soundness_under_account(rows, row):
            owed.add(row["id"])
    return owed


def check_replay_record_debt(root: Path, doc: dict) -> list[str]:
    """R7c REPLAY RECORD: a pin under a soundness claim carries the record of
    the replay it moved over (or an undemonstrated-pin account), or is named
    as debt; the anchor names only rows that still owe one, and only ids in the
    debt as minted (`REPLAY_DEBT_MINTED`). `--repin` removes a row when it
    writes its record."""
    path = root / REPLAY_DEBT_REL
    try:
        anchor = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        return [f"R7c REPLAY RECORD: {REPLAY_DEBT_REL} is missing -- without it a pin moved "
                f"by hand with its replay record deleted reads as an old, unrecorded pin."]
    except ValueError as exc:
        return [f"R7c REPLAY RECORD: {REPLAY_DEBT_REL} is not valid JSON: {exc}"]
    if not isinstance(anchor, dict):
        return [f"R7c REPLAY RECORD: {REPLAY_DEBT_REL} must be a JSON object carrying "
                f"'count' and 'rows'"]
    listed = anchor.get("rows")
    if not isinstance(listed, list) or not all(isinstance(x, str) for x in listed):
        return [f"R7c REPLAY RECORD: {REPLAY_DEBT_REL} must carry a list of row ids under 'rows'"]
    out = []
    if anchor.get("count") != len(listed):
        out.append(f"R7c REPLAY RECORD: {REPLAY_DEBT_REL} says count={anchor.get('count')!r} "
                   f"beside {len(listed)} row(s) -- the two halves of one claim disagree.")
    minted = REPLAY_DEBT_MINTED | _REPLAY_DEBT_FIXTURE
    for rid in sorted(set(listed) - minted):
        out.append(
            f"R7c REPLAY RECORD: {rid} is listed in {REPLAY_DEBT_REL} but was not in the debt "
            f"minted with this rule -- the debt only shrinks; re-pin the row over a replay "
            f"(--repin {rid}) instead of naming it as debt.")
    owed = replay_record_debt(doc["rows"])
    for rid in sorted(owed - set(listed)):
        out.append(
            f"R7c REPLAY RECORD: {rid} has a soundness claim on a pin and no replay record "
            f"(`replayed`) -- re-pin it over a replay (--repin {rid}), or, where nothing can "
            f"replay it, record an account (--repin-undemonstrated {rid}). A pin moved by "
            f"hand with its record deleted looks exactly like this.")
    for rid in sorted(set(listed) - owed):
        out.append(
            f"R7c REPLAY RECORD: {rid} is listed in {REPLAY_DEBT_REL} but owes no replay "
            f"record (it has one or an account, or no longer has a pin, a soundness claim or "
            f"a row) -- remove it; the anchor names only rows that still owe one.")
    return out


def _discharge_replay_debt(root: Path, rid: str) -> None:
    """Remove `rid` from the replay-record debt once a replay record (or an
    undemonstrated-pin account) backs it. A missing or malformed anchor is left
    alone: R7c names it on the next check."""
    path = root / REPLAY_DEBT_REL
    try:
        anchor = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return
    if not isinstance(anchor, dict):
        return
    listed = anchor.get("rows")
    if isinstance(listed, list) and rid in listed:
        anchor["rows"] = [x for x in listed if x != rid]
        anchor["count"] = len(anchor["rows"])
        path.write_text(json.dumps(anchor, indent=2) + "\n")
        print(f"{rid}: removed from {REPLAY_DEBT_REL} ({anchor['count']} left)")


def summarise(root: Path) -> dict:
    doc = load_registry(root)
    rows = doc["rows"]
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["kind"]] = counts.get(r["kind"], 0) + 1
    demoed = sum(1 for r in rows if r.get("demonstrated"))
    strong = sum(1 for r in rows if (r.get("demonstrated") or {}).get("kind") in STRONG)
    replay = sum(1 for r in rows if (r.get("demonstrated") or {}).get("replayable"))
    waived = sum(1 for r in rows if r.get("waiver"))
    sound = sum(1 for r in rows if r["claims"] == "soundness")
    sound_demo = sum(1 for r in rows if r["claims"] == "soundness" and r.get("demonstrated"))
    scanners: dict[str, int] = {}
    for r in rows:
        k = (r.get("source_scan") or {}).get("kind")
        if k:
            scanners[k] = scanners.get(k, 0) + 1
    return {
        "rows": len(rows), "kinds": counts, "demonstrated": demoed,
        "strong": strong, "replayable": replay, "waived": waived,
        "soundness_rows": sound, "soundness_demonstrated": sound_demo,
        "source_scanners": scanners,
        "r7b_backed": len(r7b_backed_rows(root, rows)[0]),
        "r7b_eligible": r7b_backed_rows(root, rows)[1],
    }


def _subject(row: dict) -> str:
    """What a row's wiring is ABOUT: its path, or for a leg/suite-row the
    script that implements it (which is where its runner edge really lands)."""
    return row.get("path") or row.get("implemented_by") or ""


def _md(text: str) -> str:
    """A cell that cannot break the table (or the code span it sits in)."""
    return text.replace("|", "\\|").replace("\n", " ").replace("`", "'")


def wiring_audit_report(root: Path) -> tuple:
    """(markdown, headline-counts). REPORTING ONLY -- never reached by check()."""
    doc = load_registry(root)
    rows = doc["rows"]
    loose, real, records, scanned = wiring_measure(root, rows)
    control = runner_edges(root, {r for row in rows for r in row["wired_by"]})

    def best(runner: str, target: str):
        recs = records.get((runner, target), [])
        for r in recs:
            if r["real"]:
                return r
        for r in recs:
            if r.get("indirect"):
                return r
        return recs[0] if recs else None

    per_row = []
    for row in rows:
        subj = _subject(row)
        declared = list(row["wired_by"])
        r_real = real.get(subj, set()) if subj else set()
        r_loose = loose.get(subj, set()) if subj else set()
        ent = {"row": row, "subject": subj, "real": [], "ref": [], "absent": [],
               "undeclared": sorted(r_real - set(declared)) if subj else []}
        for w in sorted(declared):
            if not subj:
                ent["absent"].append(w)
            elif w in r_real:
                ent["real"].append(w)
            elif w in r_loose:
                ent["ref"].append(w)
            else:
                ent["absent"].append(w)
        per_row.append(ent)

    # R3 judges `gate`/`battery`/`tool` rows and SKIPS `leg`/`suite-row`. The
    # split is not cosmetic: a leg's `wired_by` names local_gate.sh, but a leg
    # has no path of its own, so it is measured through `implemented_by` --
    # which for half of them is a RUST TEST FILE that local_gate.sh reaches
    # through cargo, not through a path. Pooling the two would report ~46
    # "undeclared runners" that are an artifact of the denominator, and bury
    # the number that matters.
    judged = [e for e in per_row if e["row"]["kind"] in ("gate", "battery", "tool")]
    skipped = [e for e in per_row if e["row"]["kind"] in ("leg", "suite-row")]

    def tally(group):
        t = {
            "rows": len(group),
            "slots": sum(len(e["real"]) + len(e["ref"]) + len(e["absent"]) for e in group),
            "real": sum(len(e["real"]) for e in group),
            "ref": sum(len(e["ref"]) for e in group),
            "absent": sum(len(e["absent"]) for e in group),
            "undeclared": sum(len(e["undeclared"]) for e in group),
            "indirect": 0,
        }
        for e in group:
            for w in e["ref"]:
                b = best(w, e["subject"])
                if b and b["indirect"]:
                    t["indirect"] += 1
        return t

    t_judged, t_skipped = tally(judged), tally(skipped)
    orphaned = [e for e in per_row
                if e["subject"] and e["row"]["wired_by"] and not e["real"]
                and not e["undeclared"]]
    orphan_gates = [e for e in orphaned if e["row"]["kind"] == "gate"]
    orphan_judged = [e for e in orphaned
                     if e["row"]["kind"] in ("gate", "battery", "tool")]
    orphan_skipped = [e for e in orphaned
                      if e["row"]["kind"] in ("leg", "suite-row")]
    head = {
        "rows": len(rows),
        "declared_slots": t_judged["slots"] + t_skipped["slots"],
        "judged_rows": t_judged["rows"], "judged_slots": t_judged["slots"],
        "judged_real": t_judged["real"],
        "judged_references_only": t_judged["ref"],
        "judged_absent": t_judged["absent"],
        "judged_undeclared_real": t_judged["undeclared"],
        "indirect_flagged": t_judged["indirect"] + t_skipped["indirect"],
        "skipped_rows_undeclared_real": t_skipped["undeclared"],
        "judged_rows_with_no_real_runner": len(orphan_judged),
        "gate_rows_with_no_real_runner": len(orphan_gates),
        "scanned_files": len(scanned),
        "loose_edges": sum(len(v) for v in loose.values()),
        "real_edges": sum(len(v) for v in real.values()),
    }

    out: list = []
    w = out.append
    w("# Gate-registry wiring audit — %s" % date.today().isoformat())
    w("")
    w("**REPORTING ONLY. Nothing here changes a gate verdict.** This is step 1 of")
    w("`docs/issues/2026-08-27-gate-registry-wiring-scan-counts-data-strings.md`:")
    w("the discriminator is landed and *measured* across every row so that step 2")
    w("(auditing `wired_by` row by row) can be done by READING evidence rather than")
    w("by re-deriving it, and step 3 (flipping the discriminator on inside R3) can be")
    w("done against a known edge set instead of a guess.")
    w("")
    dest = "docs/analysis/%s-gate-registry-wiring-audit.md" % date.today().isoformat()
    w("Regenerate: `python3 scripts/check_gate_registry.py --wiring-audit "
      "--wiring-audit-out %s`" % dest)
    w("")
    w("| provenance | value |")
    w("|---|---|")
    w("| registry | `data/gate_registry.json`, %d rows |" % len(rows))
    w("| checker | `scripts/check_gate_registry.py` sha256:%s |"
      % _sha256(root, "scripts/check_gate_registry.py")[:12])
    w("| files scanned | %d (the transitive closure from the four runner roots, "
      "plus every declared runner) |" % len(scanned))
    w("| loose edges (today's R3) | %d |" % head["loose_edges"])
    w("| real edges (discriminator) | %d |" % head["real_edges"])
    w("| loose set identical to `runner_edges()` | %s |"
      % ("YES" if loose == control else "NO -- THE MEASUREMENT IS NOT COMPARABLE, STOP"))
    w("")
    w("Where the difference lives, by runner file class — the shell half is")
    w("unchanged by construction, so every edge the discriminator drops comes from")
    w("a `.py` or `.rs` runner:")
    w("")
    by_class: dict = {}
    for (runner, target), recs in records.items():
        cell = by_class.setdefault(_file_class(runner), [0, 0])
        cell[0] += 1
        if any(r["real"] for r in recs):
            cell[1] += 1
    w("| runner class | loose edges | real edges | dropped |")
    w("|---|---:|---:|---:|")
    for cls in sorted(by_class):
        lo, re_ = by_class[cls]
        w("| %s | %d | %d | %d |" % (cls, lo, re_, lo - re_))
    w("")
    w("## The rule being measured")
    w("")
    w("* **shell** (`.sh`, `Justfile`, `scripts/githooks/pre-push`, anything with no")
    w("  extension) — every loose match is a real invocation. Today's behaviour,")
    w("  deliberately unchanged: a bare path there *is* the command word.")
    w("* **python / other** — a match counts only with **E1** an execution context")
    w("  (`subprocess.`, `Popen`, `os.system`, a bare `run(`, `shell=True`,")
    w("  `Command::new` …) on its own line *or* on the line that opened a bracket")
    w("  group still open at the match; or **E2** a command-vector head — the path is")
    w("  the head element (launchers and flags may precede it) of a list/tuple bound")
    w("  to a command-shaped name (`argv`, `cmd`, `command`, `args`, `*_cmd`).")
    w("  Multi-line vectors count: `\"argv\": [` with elements on the following lines")
    w("  is ordinary formatting here, and reading it as data would be the")
    w("  false-NEGATIVE — an invocation reported as a mention.")
    w("* `indirect?` marks a reference-only edge whose path is **bound to a name**")
    w("  used elsewhere in a file that spawns processes. That is the shape no")
    w("  single-statement rule can decide (`const S = \"scripts/x.sh\"` … twenty lines")
    w("  later `Command::new(\"bash\").arg(&script)`). It is flagged, never guessed.")
    w("")
    w("## Headline — the rows R3 judges (`gate` / `battery` / `tool`)")
    w("")
    w("| measure | count |")
    w("|---|---:|")
    w("| rows | %d |" % t_judged["rows"])
    w("| declared `wired_by` slots | %d |" % t_judged["slots"])
    w("| … REAL invocations | %d |" % t_judged["real"])
    w("| … **references only** | **%d** |" % t_judged["ref"])
    w("| … of those, `indirect?` (needs reading) | %d |" % t_judged["indirect"])
    w("| … not mentioned at all | %d |" % t_judged["absent"])
    w("| **real invocations the registry does not declare** | **%d** |" % t_judged["undeclared"])
    w("| rows whose real-runner set is EMPTY | %d |" % len(orphan_judged))
    w("| … of those, `kind: gate` | %d |" % len(orphan_gates))
    w("")
    w("### Informational — `leg` / `suite-row`, which R3 skips")
    w("")
    w("A leg has no path of its own, so it is measured through `implemented_by`:")
    w("`local_gate.sh` runs the leg's *script* by path, but reaches a leg implemented")
    w("as a RUST TEST through cargo, where no path appears at all. Every number in")
    w("this block is that denominator, not a finding — pooling it with the table")
    w("above would report %d phantom \"undeclared runners\"." % t_skipped["undeclared"])
    w("")
    w("| measure | count |")
    w("|---|---:|")
    w("| rows | %d |" % t_skipped["rows"])
    w("| declared slots | %d |" % t_skipped["slots"])
    w("| … resolve to a real invocation of `implemented_by` | %d |" % t_skipped["real"])
    w("| … references only | %d |" % t_skipped["ref"])
    w("| … `implemented_by` absent or not a path (cargo-reached) | %d |" % t_skipped["absent"])
    w("| edges onto `implemented_by` the row does not declare | %d |" % t_skipped["undeclared"])
    w("| rows whose real-runner set is EMPTY | %d |" % len(orphan_skipped))
    w("")
    w("## A. Declared edges that are REFERENCES, not invocations")
    w("")
    w("These are the `wired_by` entries R3 accepts today and would refuse once the")
    w("discriminator is on. Each carries the line that decided it.")
    w("")
    w("| row | kind | subject | declared runner | evidence | why | indirect? |")
    w("|---|---|---|---|---|---|---|")
    any_ref = False
    for e in sorted(per_row, key=lambda x: x["row"]["id"]):
        for runner in e["ref"]:
            any_ref = True
            b = best(runner, e["subject"])
            where = "%s:%d" % (runner, b["line"]) if b else "(none)"
            w("| `%s` | %s | `%s` | `%s` | `%s`<br>`%s` | %s | %s |" % (
                e["row"]["id"], e["row"]["kind"], _md(e["subject"]), _md(runner),
                _md(where), _md(b["text"]) if b else "", _md(b["why"]) if b else "",
                "**yes**" if b and b["indirect"] else "-"))
    if not any_ref:
        w("| _(none)_ | | | | | | |")
    w("")
    w("## B. Real invocations the registry does not declare")
    w("")
    w("Scoped to the rows R3 judges. R3 already refuses an undeclared LOOSE edge on")
    w("those rows, and the real set is a subset of the loose set, so this table is")
    w("empty unless the discriminator has found an edge R3 itself cannot see.")
    w("`leg`/`suite-row` rows are excluded for the denominator reason above.")
    w("")
    w("| row | subject | undeclared runner | evidence | why |")
    w("|---|---|---|---|---|")
    any_und = False
    for e in sorted(judged, key=lambda x: x["row"]["id"]):
        for runner in e["undeclared"]:
            any_und = True
            b = best(runner, e["subject"])
            where = "%s:%d" % (runner, b["line"]) if b else "(none)"
            w("| `%s` | `%s` | `%s` | `%s`<br>`%s` | %s |" % (
                e["row"]["id"], _md(e["subject"]), _md(runner), _md(where),
                _md(b["text"]) if b else "", _md(b["why"]) if b else ""))
    if not any_und:
        w("| _(none)_ | | | | |")
    w("")
    w("## C. Rows left with NO real runner")
    w("")
    w("Every declared entry on these rows is a reference. For the %d `gate`/`battery`/"
      % len(orphan_judged))
    w("`tool` rows this is the disposition question step 2 owes an answer to — under")
    w("R3's existing clause, *a gate nothing runs is not a gate*: a real runner, a")
    w("`read_by` column, a reclassification, or a waiver with an owner and an expiry.")
    w("The %d `leg`/`suite-row` rows below are the cargo-reached denominator described"
      % len(orphan_skipped))
    w("above, not findings.")
    w("")
    w("| row | kind | claims | subject | declared (all references) |")
    w("|---|---|---|---|---|")
    if not orphaned:
        w("| _(none)_ | | | | |")
    for e in sorted(orphaned, key=lambda x: (
            x["row"]["kind"] in ("leg", "suite-row"), x["row"]["kind"], x["row"]["id"])):
        w("| `%s` | %s | %s | `%s` | %s |" % (
            e["row"]["id"], e["row"]["kind"], e["row"]["claims"], _md(e["subject"]),
            ", ".join("`%s`" % _md(r) for r in e["ref"] + e["absent"]) or "-"))
    w("")
    w("## D. Every row, measured")
    w("")
    w("| row | kind | subject | real | ref-only | absent | undeclared |")
    w("|---|---|---|---:|---:|---:|---:|")
    for e in sorted(per_row, key=lambda x: (x["row"]["kind"], x["row"]["id"])):
        w("| `%s` | %s | `%s` | %d | %d | %d | %d |" % (
            e["row"]["id"], e["row"]["kind"], _md(e["subject"]) or "-",
            len(e["real"]), len(e["ref"]), len(e["absent"]), len(e["undeclared"])))
    w("")
    w("## E. What this measurement does NOT claim")
    w("")
    w("* It does not claim a reference-only edge is *wrong to record* — only that it")
    w("  is not an invocation. Step 2 decides whether it becomes `read_by`, stays")
    w("  with a note, or goes.")
    w("* `kind: leg` and `kind: suite-row` rows are measured through their")
    w("  `implemented_by`, because that is where the runner edge actually lands. R3")
    w("  skips those rows entirely today, so their numbers here are informational.")
    w("* An `indirect?` edge is unresolved, not refuted.")
    w("* **Cross-file indirection is out of scope and is the known blind spot.** A")
    w("  Rust `consts.rs` that only *defines* `const DENY_SORRY_GATE_PATH` is")
    w("  correctly a reference *as a file* — the `Command::new` that consumes it")
    w("  lives in another module, and this scan is bounded to the runner files on")
    w("  purpose (it runs in the pre-push hook). Those rows are exactly the ones")
    w("  step 2 must decide by reading, not by counting.")
    w("* **A prose class the LOOSE scan still counts, found by this measurement:**")
    w("  `_code_lines` skips a Python docstring only while the triple-quoted block")
    w("  is UNCLOSED, so a *one-line* docstring reaches R3 as code. The live")
    w("  instance is in this very file — `check_script_selftests <-")
    w("  scripts/check_gate_registry.py` is declared, and the whole edge is the")
    w("  one-line docstring of `selftest_suite_files`. The discriminator reports it")
    w("  as prose; the loose scan does not.")
    w("")
    return "\n".join(out) + "\n", head


def cmd_wiring_audit(root: Path, out_path) -> int:
    """`--wiring-audit`. Exit status is 0 whatever it finds: this measures, it
    does not judge. R3 is untouched until step 3 of the issue."""
    text, head = wiring_audit_report(root)
    if out_path:
        p = Path(out_path)
        if not p.is_absolute():
            p = root / p
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        print("wrote %s (%d bytes)" % (p, len(text)))
    else:
        sys.stdout.write(text)
    print("WIRING_AUDIT=reporting-only " + " ".join(
        "%s=%s" % (k, v) for k, v in sorted(head.items())), file=sys.stderr)
    return 0


def recorded_arms(row: dict, arms: dict) -> int | None:
    """How many arms data/gate_demonstrations.json records for `row` (its
    parent's, for a delegated row), or None when its demonstration is not a
    mutation record there. Notes do not state this number; this is where it
    is read (NOTES STATE NO ARM COUNTS, in the module doc)."""
    d = row.get("demonstrated") or {}
    if d.get("kind") != "mutation-record":
        return None
    if d.get("ref") != "data/gate_demonstrations.json" and not d.get("inherited_from"):
        return None
    return len(arms.get(d.get("inherited_from") or row["id"]) or [])


def cmd_list(root: Path) -> int:
    doc = load_registry(root)
    all_arms = load_demos(root)
    rows = sorted(doc["rows"], key=lambda r: (r["kind"], r["id"]))
    print(f"{'KIND':<10} {'CLAIMS':<10} {'DEMO':<16} {'ARMS':>4} {'ID':<44} WIRED-BY")
    for r in rows:
        d = r.get("demonstrated")
        tag = "-" if d is None else ("!" + d["kind"] if d["kind"] not in STRONG else d["kind"])
        if r.get("waiver"):
            tag = f"WAIVED>{r['waiver']['expires']}"
        arms = recorded_arms(r, all_arms)
        print(f"{r['kind']:<10} {r['claims']:<10} {tag:<16} {'-' if arms is None else arms:>4} "
              f"{r['id']:<44} {','.join(r['wired_by']) or '-'}")
    s = summarise(root)
    print(f"\n{s['rows']} rows: " + ", ".join(f"{k}={v}" for k, v in sorted(s['kinds'].items())))
    print(f"demonstrated={s['demonstrated']} (strong={s['strong']}, replayable={s['replayable']}) "
          f"waived={s['waived']}; soundness rows {s['soundness_demonstrated']}/{s['soundness_rows']} demonstrated")
    sc = s["source_scanners"]
    print("source scanners: " + (", ".join(f"{k}={v}" for k, v in sorted(sc.items())) or "none")
          + f"; retired={len(doc.get('retired', []))}")
    return 0


# ── the demonstration SANDBOX ────────────────────────────────────────────────
#
# `--demonstrate` never plants a mutation in THIS checkout. Several lanes commit
# to it at once, and a planted defect in a tracked file is indistinguishable from
# a real one to anybody who runs a gate, stages a file or reads `git status`
# (until 2026-08-30 it was planted here, and the R2 arm's gate-shaped plant made a
# concurrent hook run falsely red). The discipline is unchanged -- an arm still
# replays its mutation and requires the REAL gate to exit non-zero with the
# recorded diagnostic -- only the address moves. The sandbox is the repository,
# assembled per invocation from the WORKING TREE, so an uncommitted fix to a gate
# is what is tested:
#
#   .git       cloned (APFS clonefile, no new disk): nothing an arm runs can
#              write to the shared index, refs or objects.
#   target/    the sandbox's OWN (`_demo_target_dir`, also exported as
#              CARGO_TARGET_DIR by `_sandbox_env`), one per layout, never the
#              shared `<repo>/target`. Cargo's `-C metadata` hash is
#              workspace-relative, so a sandbox build writes the SAME unit names
#              as the real tree, with the sandbox's path baked in through
#              `env!("CARGO_MANIFEST_DIR")`, and cargo does not re-key a unit on
#              it: while the dir was shared (until 2026-09-15) 27 rlibs of the
#              real target were poisoned so, and the real tree linked them Fresh.
#   crates/*   in the BUILD layout (`_needs_build`) each member crate no arm
#              mutates is a symlink, so its units are the ones the sandbox cache
#              already holds; everything else is cloned.
#
# It is still the real gate: `_fidelity` re-hashes the gate script and the arm's
# file against the shared tree before each arm, the command is unchanged (only
# cwd moves), the green baseline runs in the sandbox, and `--repin` reads the pin
# state IN the sandbox before every arm (`_pin_state`). Not covered, stated: a
# gate that writes under a symlinked crate directory writes to the shared tree;
# no arm's gate does, and `_leak_check` reports such a write as an arm FAILURE.


def _clone_tree(src: Path, dst: Path) -> None:
    """Copy `src` to `dst`, preferring APFS clonefile, failing closed."""
    for flags in ("-Rpc", "-Rp"):
        try:
            source = src.resolve()
            destinations = [dst.resolve()]
            if dst.is_dir():
                # Recheck before BOTH attempts: a partial first copy can create
                # dst or its child and change cp's effective destination.
                destinations.append((dst / src.name).resolve())
            if src.is_dir() and any(p == source or source in p.parents
                                    for p in destinations):
                raise Red(f"refusing directory copy of {src} into itself or a "
                          f"descendant: {dst}")
        except (OSError, RuntimeError) as exc:
            raise Red(f"cannot resolve sandbox copy paths {src} -> {dst}: {exc}") from exc
        r = subprocess.run(["cp", flags, str(src), str(dst)],
                           capture_output=True, text=True)
        if r.returncode == 0:
            return
    raise Red(f"could not copy {src} into the demonstration sandbox: {r.stderr.strip()}")


def _sandbox_cargo_sources(real: Path, hidden: dict[Path, str],
                           what: str = "cache alias") -> None:
    """Reject declared Cargo source paths into a hidden directory, without walking one.

    `hidden` maps each RESOLVED directory the sandbox will not copy to the name
    of the rule that hides it, which a refusal quotes; `what` names the
    decision in a malformed-manifest refusal. Follow only manifests named by
    members/path dependencies/patches/replaces. This is not analysis of
    configuration/environment/compiler indirection, arbitrary build-script code
    or include!: generated outputs remain hidden.
    """
    import tomllib

    def hider(path: Path) -> str | None:
        for directory, label in hidden.items():
            if path == directory or directory in path.parents:
                return label
        return None

    pending = [real / "Cargo.toml"] if (real / "Cargo.toml").is_file() else []
    seen: set[Path] = set()
    while pending:
        manifest = pending.pop().resolve()
        if manifest in seen:
            continue
        seen.add(manifest)
        data = tomllib.loads(manifest.read_text())
        directory = manifest.parent

        def source_path(value: str, kind: str) -> Path:
            if not isinstance(value, str):
                raise Red(f"cannot validate {what}: malformed {kind} path in {manifest}")
            path = (directory / value).resolve()
            label = hider(path)
            if label:
                raise Red(f"{label} would hide Cargo {kind}: {path}")
            return path

        def enqueue(directory: Path) -> None:
            path = (directory / "Cargo.toml").resolve()
            label = hider(path)
            if label:
                raise Red(f"{label} would hide Cargo manifest: {path}")
            if path.is_relative_to(real):
                pending.append(path)

        workspace = data.get("workspace", {})
        if not isinstance(workspace, dict):
            raise Red(f"cannot validate {what}: malformed workspace table")
        members = workspace.get("members", [])
        if not isinstance(members, list) or any(not isinstance(m, str) for m in members):
            raise Red(f"cannot validate {what}: malformed workspace members")
        for member in members:
            if any(c in member for c in "*?["):
                raise Red(f"cannot validate {what} with wildcard workspace members")
            enqueue(source_path(member, "workspace member"))

        if "package" in data:
            package = data["package"]
            if not isinstance(package, dict):
                raise Red(f"cannot validate {what}: malformed package table")
            # These potential inferred source directories must not be aliases
            # into cache either. No recursive source/cache walk is performed.
            for name in ("src", "examples", "tests", "benches"):
                source_path(name, "inferred target source")
            for name in ("src/lib.rs", "src/main.rs"):
                source_path(name, "inferred target source")
            # Cargo infers named targets from immediate .rs entries or
            # <name>/main.rs. Resolve each entry before inspecting it; never
            # descend into cache, and never recursively walk these directories.
            for name in ("src/bin", "examples", "tests", "benches"):
                inferred = source_path(name, "inferred target directory")
                if inferred.is_dir():
                    for entry in inferred.iterdir():
                        resolved = source_path(str(entry), "inferred target source")
                        if resolved.is_dir():
                            source_path(str(entry / "main.rs"), "inferred target source")
            build = package.get("build", "build.rs")
            if build is not False:
                source_path("build.rs" if build is True else build, "build source")
        lib = data.get("lib", {})
        if not isinstance(lib, dict):
            raise Red(f"cannot validate {what}: malformed lib table")
        targets = [lib]
        for kind in ("bin", "example", "test", "bench"):
            entries = data.get(kind, [])
            if not isinstance(entries, list) or any(not isinstance(e, dict) for e in entries):
                raise Red(f"cannot validate {what}: malformed {kind} targets")
            targets.extend(entries)
        for target in targets:
            if "path" in target:
                source_path(target["path"], "target source")

        platforms = data.get("target", {})
        if not isinstance(platforms, dict):
            raise Red(f"cannot validate {what}: malformed target dependency table")

        def path_dependencies(dependencies: dict) -> None:
            if not isinstance(dependencies, dict):
                raise Red(f"cannot validate {what}: malformed dependencies")
            for dependency in dependencies.values():
                if not isinstance(dependency, (str, dict)):
                    raise Red(f"cannot validate {what}: malformed dependency")
                if isinstance(dependency, dict) and "path" in dependency:
                    enqueue(source_path(dependency["path"], "path dependency"))

        for table in (data, workspace, *platforms.values()):
            if not isinstance(table, dict):
                raise Red(f"cannot validate {what}: malformed dependency context")
            for kind in ("dependencies", "dev-dependencies", "build-dependencies"):
                path_dependencies(table.get(kind, {}))
        patches = data.get("patch", {})
        if not isinstance(patches, dict):
            raise Red(f"cannot validate {what}: malformed patch table")
        for dependencies in patches.values():
            path_dependencies(dependencies)
        path_dependencies(data.get("replace", {}))


def _sandbox_cache_alias(real: Path, mutated: set[str]) -> str | None:
    """Recognize only the measured root target -> target.noindex layout.

    The one directory held to a STRICTER rule than `_sandbox_exclusions`: the
    backing tree of the root `target` link is refused outright when it would
    hide tracked source, where any other build-output name that git tracks is
    simply copied as source. Unknown workspace globs fail closed here: the
    existing build-layout member selector does not resolve them, so it cannot
    justify sharing their source.
    """
    try:
        root = real.resolve()
        target = root / "target"
        cache = root / "target.noindex"
        if (not target.is_symlink() or cache.is_symlink() or not cache.is_dir()
                or target.resolve() != cache):
            return None

        def inside_cache(path: Path) -> bool:
            resolved = path.resolve()
            return resolved == cache or cache in resolved.parents

        tracked = subprocess.run(["git", "ls-files", "-z", "--"], cwd=root,
                                 capture_output=True, text=True)
        if tracked.returncode != 0:
            raise Red("cannot validate cache alias: Git tracked-source inventory failed")
        for name in filter(None, tracked.stdout.split("\0")):
            if inside_cache(root / name):
                raise Red(f"cache alias would hide tracked source: {name}")

        _sandbox_cargo_sources(root, {cache: "cache alias"})
        for name in mutated:
            path = (root / name).resolve()
            if inside_cache(path) or path in cache.parents:
                raise Red(f"cache alias overlaps declared mutation: {name}")
        return "target.noindex"
    except (OSError, RuntimeError, ValueError, ImportError) as exc:
        raise Red(f"cannot validate sandbox cache alias: {exc}") from exc


# ── what a sandbox never copies ──────────────────────────────────────────────
#
# THE ONE LIST. `_sandbox_exclusions` reads it to decide what the copy skips and
# `_sandbox_audit` reads it to check the finished sandbox, so the copier and the
# check that it worked cannot disagree. Measured 2026-09-28: a demonstration run
# with CLEAN_GATE_DEMO_ROOT inside a replay clone's `target.noindex` cloned that
# `target.noindex` -- the replay directories, EARLIER KEPT SANDBOXES among them --
# into its own `tree-build/target.noindex`, 141 GiB for one sandbox, each run
# bigger than the last; and after the root alias was skipped, the checkout this
# repo is developed in still handed every sandbox `target-quality.noindex`
# (119 GiB by du), `target-replay.noindex`, three nested `scripts/*/target`
# trees and 30 lane worktrees under `.claude/worktrees`.
# clonefile shares blocks only until the source moves on, so each copy pins the
# build tree as it was, for as long as the sandbox lives.
#
# A DIRECTORY (or a symlink to one) is never copied when its own name matches
# SANDBOX_EXCLUDED_DIR_GLOBS, its path ends in one of SANDBOX_EXCLUDED_DIR_PATHS,
# or it holds a `.git` of its own -- a nested checkout: an earlier sandbox, a
# lane's worktree, a Lean package clone; none of them is this tree. A FILE is
# never excluded (`scripts/target_census.sh` is source), and neither is anything
# git TRACKS, whatever its name (`bakeoff/target-sets/` is source): the rule
# describes build output, and build output is never tracked. The sandbox's own
# destination is excluded when it lies inside the tree, so the copy can never
# contain itself, and `_build_sandbox` refuses a destination that already exists.
SANDBOX_EXCLUDED_DIR_GLOBS = ("target*", "*.noindex")
SANDBOX_EXCLUDED_DIR_PATHS = (".lake/build",)


def _sandbox_exclusion_reason(path: Path, rel: str) -> str | None:
    """Why the entry at `path` (repo-relative `rel`) is never copied, or None.

    The caller has already ruled out tracked paths; this is the name rule alone.
    """
    try:
        if not path.is_dir():
            return None
        if any(fnmatch.fnmatchcase(path.name, glob) for glob in SANDBOX_EXCLUDED_DIR_GLOBS):
            return "build output"
        if any(rel == tail or rel.endswith("/" + tail) for tail in SANDBOX_EXCLUDED_DIR_PATHS):
            return "build output"
        if not path.is_symlink() and os.path.lexists(path / ".git"):
            return "nested checkout"
    except OSError as exc:
        raise Red(f"cannot inspect {path} while deciding what the sandbox copies: "
                  f"{exc}") from exc
    return None


def _tracked_inventory(root: Path) -> tuple[set[str], set[str]]:
    """Every tracked path under `root`, and every directory that holds one."""
    r = subprocess.run(["git", "ls-files", "-z", "--"], cwd=root,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise Red(f"cannot decide what the sandbox copies: `git ls-files` failed in "
                  f"{root}: {r.stderr.strip()[:200]}")
    files = set(filter(None, r.stdout.split("\0")))
    dirs = set()
    for name in files:
        parts = name.split("/")
        for depth in range(1, len(parts)):
            dirs.add("/".join(parts[:depth]))
    return files, dirs


def _walk_exclusions(root: Path, tracked: tuple[set[str], set[str]],
                     fixed: dict[str, str]) -> dict[str, str]:
    """rel -> reason for every entry under `root` a sandbox must not hold.

    Walks directories only, never follows a symlink, never enters `.git` or an
    excluded directory, so its cost is the source tree's directory count and not
    the build trees' file count. `fixed` entries are excluded whether or not they
    exist yet (a destination the copy is about to create).
    """
    files, dirs = tracked
    found = dict(fixed)

    def walk(path: Path, rel: str) -> None:
        try:
            with os.scandir(path) as listing:
                entries = sorted(listing, key=lambda e: e.name)
        except OSError as exc:
            raise Red(f"cannot list {path} while deciding what the sandbox copies: "
                      f"{exc}") from exc
        for entry in entries:
            child = f"{rel}/{entry.name}" if rel else entry.name
            if child == ".git" or child in found:
                continue
            if child not in files and child not in dirs:
                why = _sandbox_exclusion_reason(Path(entry.path), child)
                if why:
                    found[child] = why
                    continue
            if entry.is_dir(follow_symlinks=False):
                walk(Path(entry.path), child)

    walk(root, "")
    return found


def _sandbox_exclusions(real: Path, dest: Path, mutated: set[str],
                        cache_alias: str | None) -> dict[str, str]:
    """Every entry of `real` the sandbox at `dest` must not hold: rel -> why.

    Fails closed where excluding would hide something an arm needs: a declared
    mutation, or a Cargo source path a manifest names (the checks
    `_sandbox_cache_alias` makes for the root alias, over every exclusion).
    """
    root = real.resolve()
    fixed: dict[str, str] = {}
    own = dest.resolve()
    if own == root or own in root.parents:
        raise Red(f"the sandbox destination {dest} is the tree {real} or holds it")
    if root in own.parents:
        fixed[own.relative_to(root).as_posix()] = "this sandbox's own destination"
    found = _walk_exclusions(root, _tracked_inventory(root), fixed)
    for name in mutated:
        lexical = Path(name).as_posix()
        for rel in found:
            if lexical == rel or lexical.startswith(rel + "/"):
                raise Red(f"declared mutation {name} lies in {rel}, which the sandbox "
                          f"excluded as {found[rel]} -- the arm could never reach it")
    hidden = {}
    for rel, why in found.items():
        path = root / rel
        # The root `target` has always been skipped by name (the sandbox links
        # its own), and its alias is validated by `_sandbox_cache_alias`; a
        # symlink hides only itself, never what it points at.
        if rel in ("target", cache_alias) or path.is_symlink() or not path.is_dir():
            continue
        hidden[path.resolve()] = f"sandbox exclusion of {rel} ({why})"
    if hidden:
        try:
            _sandbox_cargo_sources(root, hidden, "sandbox exclusions")
        except (OSError, RuntimeError, ValueError, ImportError) as exc:
            raise Red(f"cannot validate sandbox exclusions: {exc}") from exc
    return found


def _sandbox_audit(real: Path, sandbox: Path) -> list[str]:
    """Every build dir or nested checkout the finished sandbox holds. Must be [].

    The same list and the same walk as the copy, run over the RESULT: a copier
    change that re-admits a build tree, or a co-tenant who creates one in the
    window between the walk and the `cp`, is a refusal naming the path rather
    than a sandbox that quietly grows. The one allowed hit is the sandbox's own
    `target` link to `_demo_target_dir`.
    """
    own = _demo_target_dir(real, sandbox.name)
    leaks = []
    for rel, why in sorted(_walk_exclusions(sandbox, _tracked_inventory(real.resolve()),
                                            {}).items()):
        entry = sandbox / rel
        if rel == "target" and entry.is_symlink() and Path(os.readlink(entry)) == own:
            continue
        leaks.append(f"{rel} ({why})")
    return leaks


def _remove_sandbox(dest: Path) -> str | None:
    """Delete a sandbox. The complaint when anything survives, else None.

    `rmtree(ignore_errors=True)` alone reported nothing when it failed, and the
    next build then copied the tree INTO the survivor (`cp -R` nests into an
    existing directory), so a failed cleanup was the start of a nested copy.
    """
    shutil.rmtree(dest, ignore_errors=True)
    if dest.exists() or dest.is_symlink():
        return (f"could not remove the sandbox at {dest}: something survived the "
                f"rmtree -- remove it by hand")
    return None


def _member_dirs(root: Path) -> set[str]:
    """Relative paths of every cargo workspace member, from the root manifest.

    These are the directories that must stay SYMLINKS: cargo keys a path
    package's `-C metadata` on its directory, so materialising one costs a
    rebuild of that crate and everything downstream of it.
    """
    try:
        text = (root / "Cargo.toml").read_text()
    except OSError:
        return set()
    m = re.search(r"^members\s*=\s*\[(.*?)\]", text, re.S | re.M)
    if not m:
        return set()
    return {p for p in re.findall(r'"([^"]+)"', m.group(1)) if "*" not in p}


def _demo_target_dir(real: Path, layout: str) -> Path:
    """The sandbox's OWN cargo target dir: `<real>/target/gate-demo-<layout>`.

    Never `<real>/target` itself -- the paragraph above `_clone_tree` records
    the 27 poisoned rlibs that sharing it cost. Under `target/` so
    `scripts/target_census.sh` counts and prunes it; flat, because that script
    globs two levels (`*/deps`, `*/*/deps`), not three; one per layout, because
    both layouts mint identical filenames with different sandbox paths baked in.
    """
    return real / "target" / f"gate-demo-{layout}"


# The file inside a sandbox target dir naming the sandbox its units were
# minted for. See `_claim_demo_target`.
_TARGET_STAMP = "GATE_DEMO_SANDBOX_ROOT"


def _claim_demo_target(demo_target: Path, sandbox: Path) -> str | None:
    """Make `demo_target` the cache for a sandbox at exactly `sandbox`.

    The units in it bake the sandbox's absolute path (CARGO_MANIFEST_DIR and
    friends), and cargo will not rebuild them when that path changes -- that is
    the mechanism behind the 2026-09-15 finding above `_clone_tree`. So the dir
    carries a stamp naming the sandbox it was minted for: the same path keeps
    the cache warm; a different one (CLEAN_GATE_DEMO_ROOT or TMPDIR moved) drops
    the whole dir, and the arm pays a cold build, which is the honest price of
    a cache whose every baked path is dead. Returns a note when it dropped one.

    The drop FAILS CLOSED. A first revision called `rmtree(ignore_errors=True)`
    and then re-stamped unconditionally, so a cache that could not be removed
    -- `rmtree` refuses a symlink outright, which is how an operator relieving
    disk pressure would leave this path after moving it to another volume --
    was re-stamped as warm with every baked path still dead, the exact class
    this function exists to close, reproduced silently. Now anything that
    survives the drop is a `Red` naming the path, and the stamp is written
    only after the directory is verifiably gone. Arm 70 pins it.
    """
    stamp = demo_target / _TARGET_STAMP
    note = None
    if demo_target.exists() or demo_target.is_symlink():
        try:
            prev = stamp.read_text().strip()
        except OSError:
            prev = ""
        if prev != str(sandbox):
            try:
                shutil.rmtree(demo_target)
            except OSError as exc:
                raise Red(f"could not drop {demo_target} (its units were minted for "
                          f"a sandbox at {prev or '(no stamp)'}, not {sandbox}): "
                          f"{exc} -- refusing to re-stamp a cache whose baked "
                          f"paths are dead; remove it by hand") from exc
            if demo_target.exists() or demo_target.is_symlink():
                raise Red(f"could not drop {demo_target}: something survived the "
                          f"rmtree -- refusing to re-stamp a cache whose baked "
                          f"paths are dead; remove it by hand")
            note = (f"dropped {demo_target}: its units were minted for a sandbox at "
                    f"{prev or '(no stamp)'}, not {sandbox}, so every path they bake "
                    f"is dead -- this run pays a cold build")
    demo_target.mkdir(parents=True, exist_ok=True)
    stamp.write_text(str(sandbox) + "\n")
    return note


def _sandbox_env(sandbox: Path) -> dict[str, str]:
    """The environment every arm and every eviction runs under.

    `CARGO_TARGET_DIR` names the sandbox's own target dir -- the directory
    `<sandbox>/target` links to -- so a cargo an arm's script runs builds there
    whatever it inherited (`scripts/self_verify_crosscheck.sh` honours an
    inherited value); the symlink covers a script that reads `target/debug/<bin>`
    by path. `CARGO_BUILD_BUILD_DIR` is pinned to the same directory: on a cargo
    that knows `build.build-dir` (this toolchain's does) the build dir receives
    `deps/` and `.fingerprint/` -- the rlibs that bake CARGO_MANIFEST_DIR -- so an
    inherited value or a global `[build] build-dir` would route them back to the
    shared cache under a green CARGO_TARGET_DIR. Arm 68 asserts both variables.
    """
    env = dict(os.environ)
    link = sandbox / "target"
    target = Path(os.readlink(link)) if link.is_symlink() else link
    env["CARGO_TARGET_DIR"] = str(target)
    env.pop("CARGO_BUILD_TARGET_DIR", None)
    env["CARGO_BUILD_BUILD_DIR"] = str(target)
    targo = _canonical_targo()
    return _with_targo(env, targo) if targo else env


# WHICH TARGO AN ARM RUNS. An arm's command says `targo`, and a shell resolves
# that through PATH -- the demonstrator's PATH. On this machine `~/.cargo/bin`
# sits ahead of the Trust sysroot and `~/.cargo/bin/targo` is a rustup symlink
# that targo refuses to run as ("not a plain regular file"), so until
# 2026-09-29 every compiling arm's BASELINE went red for one operator and green
# for another: the demonstration's verdict depended on the demonstrator's PATH
# order. The canonical targo comes from `scripts/rust_frontend.sh --targo`, the
# one place the rule lives (an explicit `$TARGO`, else
# `$(rustc +trust --print sysroot)/bin/targo`), and reaches the arm twice: as
# TARGO for the scripts that ask the frontend, and as the ONLY `targo` in a
# private directory put first on PATH for the commands that spell it. That
# directory holds a wrapper that execs the canonical binary -- never a symlink,
# which targo would refuse exactly as it refuses rustup's.
_TARGO_CACHE: list[str | None] = []


def _canonical_targo() -> str | None:
    """The canonical targo, resolved once per process; None (with a note) when
    the frontend refuses -- an arm that needs targo then fails loudly on its
    own, and one that does not is not held back."""
    if not _TARGO_CACHE:
        frontend = ROOT / "scripts" / "rust_frontend.sh"
        env = dict(os.environ)
        try:
            r = subprocess.run(["bash", str(frontend), "--targo"], cwd=ROOT,
                               capture_output=True, check=False, env=env,
                               pass_fds=_resource_fds(env))
            targo = os.fsdecode(r.stdout).removesuffix("\n") if r.returncode == 0 and os.fsdecode(r.stdout).strip() else ""
            why = " ".join(os.fsdecode(r.stderr or b"").split())
        except OSError as exc:
            targo, why = "", str(exc)
        if not targo:
            print(f"  [note] no canonical targo ({frontend.relative_to(ROOT)} --targo: "
                  f"{why[:200] or 'no output'}); arms run with the inherited PATH")
        _TARGO_CACHE.append(targo or None)
    return _TARGO_CACHE[0]


def _with_targo(env: dict[str, str], targo: str) -> dict[str, str]:
    """`env` with TARGO=`targo` and a private directory, first on PATH, whose
    only entry is a `targo` wrapper exec'ing it (see the block above)."""
    import shlex
    shim = Path(tempfile.gettempdir()) / f"clean-gate-targo-{os.getpid()}"
    wrapper = shim / "targo"
    text = f"#!/bin/sh\nexec {shlex.quote(targo)} \"$@\"\n"
    if not wrapper.is_file() or wrapper.read_text() != text:
        shim.mkdir(parents=True, exist_ok=True)
        wrapper.write_text(text)
        wrapper.chmod(0o755)
        import atexit
        atexit.register(shutil.rmtree, shim, True)
    out = dict(env)
    out["TARGO"] = targo
    out["PATH"] = f"{shim}{os.pathsep}{env.get('PATH', '')}"
    return out


# `targo --unverified <verb>` / `targo trust <verb>` / `targo tippy` since the
# 2026-09-28 Trust migration (owner directive); the stock `cargo [+chan] <verb>`
# spelling is still recognised so an arm that was not migrated keeps its layout.
BUILDS = re.compile(r"(?:targo\s+(?:(?:--unverified|trust)\s+)?|cargo\s+(?:\+\S+\s+)?)"
                    r"(build|test|check|run|bench|clippy|tippy|nextest|install|rustc)\b")


def _needs_build(command: str, arm: dict) -> bool:
    """Does this arm COMPILE? From the command, or from an explicit `sandbox`.

    `"sandbox": "clone"` forces the clone layout even for a compiling arm, and
    it is not a style preference -- MEASURED 2026-08-30 on `prelude-axiom-ratchet`
    and `soundness-cert`, both of which mutate a file under `data/` and then run
    a clean-kernel lib test. In the build layout clean-kernel is a symlink, and
    the test's `Path::new(env!("CARGO_MANIFEST_DIR")).join("../../data/...")`
    resolves into the SHARED tree -- not because cargo canonicalises the
    symlink (it does not: CARGO_MANIFEST_DIR for a symlinked crate is the
    SANDBOX path, measured 2026-09-15 in the poisoned units the block above
    `_clone_tree` records) but because the OS resolves `..` THROUGH the
    symlink, so the join lands in the shared tree's `data/`: the test read the
    unmutated file and stayed GREEN, which the harness reported as "it cannot
    fail". The mutation was never in play.
    Those arms pay a cold crate build in the clone layout, and that is the
    honest price of a demonstration that is actually about the mutation.
    `prelude-axiom-ratchet`'s arm carried the field at 30b15620e and lost it
    at 95c42f62a (a rebased lane's copy of data/gate_demonstrations.json), so
    for two weeks that arm ran in the build layout again and could report the
    vacuous green -- measured 2026-09-15 and restored the same day: field
    back, re-demonstrated in the clone layout (cold clean-kernel lib-test
    build, then red under its mutation, rc=101), row re-pinned.

    The layout is chosen by the answer, so both wrong answers cost something:
    the clone layout makes a compiling arm rebuild 27 crates from cold, and the
    build layout hides unmutated crates from a source walker.

    THE OBVIOUS MECHANICAL VERSION IS WRONG, and it was written and measured
    first: scanning the SCRIPT the command names for a cargo invocation routed
    `check_lint_coverage` and `check_extend_constants_ratchet` into the build
    layout, because both are gates ABOUT cargo commands and carry
    `cargo clippy --workspace` in a string literal. That is this repo's own
    rule -- a scanner that matches raw text counts mentions, not code -- and
    blanking literals cannot fix it either, since a python gate's REAL cargo
    invocation lives in exactly such a literal. So the derivation is over the
    arm's own command only, and an arm whose script runs cargo out of sight
    says `"sandbox": "build"` and says why. Getting that wrong is slow, never
    unsound: an undeclared compiling arm still runs, in the clone layout, and
    pays a cold build. `targo fmt` / `cargo fmt` is not a build and does not count.
    """
    if arm.get("sandbox") == "clone":
        return False
    return arm.get("sandbox") == "build" or bool(BUILDS.search(command))


def _build_sandbox(real: Path, dest: Path, build: bool, mutated: set[str]) -> None:
    """Assemble the sandbox described above. `dest` must not exist.

    DEFAULT layout: everything is cloned, so the sandbox is a fully walkable
    copy -- `os.walk`, `Path.rglob` and `walkdir` do not descend a symlinked
    directory, and three gates went wrong the hour this was first written with
    symlinks (a census lost its sources, a ratchet went GREEN under its own
    mutation, a resolved crate path pointed out of the sandbox). BUILD layout
    (`_needs_build`): member crates the arms do not mutate are symlinked, so
    cargo computes the same `-C metadata` as this tree and reuses the sandbox
    cache (a mutated clean-sys recompiled alone in 2.78 s; cloning the members
    rebuilds the workspace cold). A compiling arm leaves its mutated units in
    that cache with mtimes a later `cp -p` clone predates, so
    `_evict_mutated_units` drops them after every arm. BOTH layouts get
    `target/` as a symlink to `_demo_target_dir(real, dest.name)`, claimed for
    this path by `_claim_demo_target` before a file is copied -- never the
    shared `<real>/target` (the paragraph above `_clone_tree`).
    """
    if dest.exists() or dest.is_symlink():
        raise Red(f"the sandbox destination {dest} already exists -- `cp -R` into an "
                  f"existing directory nests the copy inside it; remove it first")
    # Validate the backing alias and every other exclusion before claiming (or
    # dropping) any private cache: tracked/Cargo/mutation source must never
    # disappear as a cache or as build output.
    cache_alias = _sandbox_cache_alias(real, mutated)
    excluded = _sandbox_exclusions(real, dest, mutated, cache_alias)
    demo_target = _demo_target_dir(real, dest.name)
    dropped = _claim_demo_target(demo_target, dest)
    if dropped:
        print(f"  [note] {dropped}")
    members = _member_dirs(real) if build else set()
    members = {m for m in members
               if not any(r == m or r.startswith(m + "/") for r in mutated)}
    ancestors = {str(Path(m).parent) for m in members} - {"."}
    # Directories holding something excluded are walked, not cloned whole.
    around = {Path(rel).parents[i].as_posix() for rel in excluded
              for i in range(len(Path(rel).parents) - 1)}

    # The shared build tree is skipped by NAME and by validated ALIAS: where
    # `target` is a symlink (`target -> target.noindex`, the Spotlight-excluded
    # layout atpkg lays out), the physical tree is a root entry under its OWN
    # name, and a name-only skip clonefile-copied the whole build tree into
    # every sandbox -- measured 2026-09-15, root entry `target.noindex`.
    # Do not skip arbitrary equal resolved paths: `target -> src` must not
    # hide the ordinary source directory from a source-reading gate.

    def emit(rel: str) -> None:
        src = real / rel if rel else real
        dst = dest / rel if rel else dest
        dst.mkdir(parents=True, exist_ok=True)
        for entry in sorted(src.iterdir()):
            child = f"{rel}/{entry.name}" if rel else entry.name
            if child == "target" or child == cache_alias or child in excluded:
                continue  # the sandbox's own is linked in below; build output never
            elif child in ancestors:
                emit(child)
            elif child in members:
                (dest / child).symlink_to(entry)
            elif child in around:
                emit(child)
            else:
                _clone_tree(entry, dest / child)

    try:
        emit("")
        (dest / "target").symlink_to(demo_target)
        # A co-tenant mid-commit leaves an index.lock in .git; cloned, it would
        # make every git command in the sandbox refuse for a reason that has
        # nothing to do with the arm. The clone is a copy, so dropping it here
        # cannot affect the real repository's lock.
        for stale in (dest / ".git").glob("*.lock"):
            stale.unlink(missing_ok=True)
        leaks = _sandbox_audit(real, dest)
        if leaks:
            raise Red(f"the sandbox at {dest} holds what it must never copy: "
                      f"{'; '.join(leaks[:8])}"
                      + (f" (and {len(leaks) - 8} more)" if len(leaks) > 8 else ""))
    except BaseException:
        # A half-built sandbox is removed here, not left for the next run to
        # copy into.
        leftover = _remove_sandbox(dest)
        if leftover:
            print(f"  [FAIL] {leftover}")
        raise


def _materialize(real: Path, sandbox: Path, rel: str) -> None:
    """Make `rel` a REAL file in the sandbox holding the shared tree's bytes.

    Walks the path, replacing any symlinked directory with a real directory
    whose other children are symlinks, so that exactly one crate is de-shared.
    The leaf is copied from the WORKING TREE every time -- not from git -- so an
    arm measures the tree as it is, and so a `_restore` (which checks out HEAD)
    cannot leave a later arm reading different bytes than the shared tree has.
    """
    parts = rel.split("/")
    for depth in range(1, len(parts)):
        d = sandbox / "/".join(parts[:depth])
        if d.is_symlink():
            src = real / "/".join(parts[:depth])
            d.unlink()
            d.mkdir()
            for entry in sorted(src.iterdir()):
                if entry.name == parts[depth]:
                    continue
                (d / entry.name).symlink_to(entry)
        elif not d.exists():
            d.mkdir(parents=True)
    leaf = sandbox / rel
    if leaf.is_symlink():
        leaf.unlink()
    if (real / rel).is_file():
        if leaf.exists():
            leaf.unlink()
        _clone_tree(real / rel, leaf)
        # `cp -p` keeps the shared tree's mtime, older than an artifact a
        # previous replay left for this file's unit, which cargo then judged
        # Fresh (measured 2026-09-08, gate::leancross). Bumping it makes the
        # bytes newer than any such artifact; `_evict_mutated_units` is the
        # fix for every other unit an arm left planted.
        os.utime(leaf, None)
    elif leaf.exists():
        leaf.unlink()


def _sha_or_none(p: Path) -> str | None:
    try:
        return hashlib.sha256(p.read_bytes()).hexdigest()
    except OSError:
        return None


def _fidelity(real: Path, sandbox: Path, rels: list[str]) -> list[str]:
    """Paths whose sandbox bytes differ from the shared tree's. Must be empty.

    This is what makes the run a demonstration ABOUT THIS TREE. It is not
    ceremony: the sandbox is assembled while other lanes are writing, so a file
    can genuinely move between the clone and the arm, and a demonstration
    against bytes nobody has is worth nothing.
    """
    bad = []
    for rel in rels:
        if not rel or not (real / rel).is_file():
            continue
        if _sha_or_none(real / rel) != _sha_or_none(sandbox / rel):
            bad.append(rel)
    return bad


def _shared_state(root: Path, rels: list[str]) -> dict:
    """What the SHARED tree says about `rels`: git's verdict plus the bytes."""
    args = ["git", "status", "--porcelain", "--"] + [r for r in rels if r]
    out = subprocess.run(args, cwd=root, capture_output=True, text=True).stdout
    return {"status": out, "sha": {r: _sha_or_none(root / r) for r in rels if r}}


def _sandbox_base() -> Path:
    """Where sandboxes live. STABLE on purpose.

    A stable base keeps the clone's own state (its .git, its cargo lock files)
    at one place between invocations. It is NOT what makes a cargo arm
    incremental -- an earlier revision of this docstring said cargo keys its
    fingerprints on the sandbox's absolute path, and that is false, measured
    2026-09-08: the `-C metadata` hash is workspace-relative, so the sandbox's
    units carry the real tree's NAMES (see `_evict_mutated_units`). Since
    2026-09-15 the stability is load-bearing for a different reason: the
    sandbox has its own target dir (`_demo_target_dir`), and every unit in it
    bakes the sandbox's absolute path through `env!("CARGO_MANIFEST_DIR")`,
    which cargo does not re-key on. A path that is the same per repository
    keeps those baked paths valid and the cache warm across demonstrations; a
    path that moved is detected by the stamp `_claim_demo_target` writes, and
    the cache is dropped rather than reused. Concurrency is handled by the
    mkdir mutex below, not by randomising the path -- macOS has no flock(1) --
    and that mutex is keyed on the CHECKOUT (`_demo_lock_dir`), not on this
    base: the cache is per checkout, so two demonstrators on one checkout
    with different bases would otherwise take different locks and share, and
    drop, one cache. `CLEAN_GATE_DEMO_ROOT` moves the sandbox; it does not
    buy a second concurrent demonstration on the same checkout.
    """
    env = os.environ.get("CLEAN_GATE_DEMO_ROOT")
    base = Path(env) if env else Path(tempfile.gettempdir()) / "clean-gate-demo"
    return base / hashlib.sha256(str(ROOT).encode()).hexdigest()[:12]


def _demo_lock_dir(real: Path) -> Path:
    """The demonstrators' mutex: `<real>/target/gate-demo.lock`.

    Keyed on the same thing the caches are keyed on -- the checkout -- and on
    nothing else. Until 2026-09-15 the lock lived under `_sandbox_base()`,
    which is keyed on TMPDIR / CLEAN_GATE_DEMO_ROOT as well as on the checkout,
    while `_demo_target_dir` is keyed on the checkout alone; so a second
    demonstrator started with `CLEAN_GATE_DEMO_ROOT=/elsewhere` (the natural
    move after the 900 s "another --demonstrate run has held" refusal) took a
    different lock, found the first one's stamp in the shared cache, and
    `rmtree`d it while the first one's cargo was mid-link inside it. Same
    checkout, same cache, same lock; a different checkout has its own of all
    three, so there is nothing to serialise across checkouts. Under `target/`
    because it is gitignored there and `scripts/target_census.sh` globs
    `*/deps` and never sees a directory with none. Arm 71 pins the keying.
    """
    return real / "target" / "gate-demo.lock"


def _lock_acquire(lock: Path, wait_s: int = 900) -> Path:
    """Atomic-mkdir mutex between demonstrators sharing one checkout's caches.

    This is NOT the "lock other lanes respect" design -- no other lane has to
    know it exists. It serialises `--demonstrate` against `--demonstrate`, which
    is the only contention a sandbox at a fixed path, and a cache at a fixed
    path, can have. `lock` is the mutex directory itself (`_demo_lock_dir`).
    """
    lock.parent.mkdir(parents=True, exist_ok=True)
    deadline = time.time() + wait_s
    while True:
        try:
            lock.mkdir()
            (lock / "pid").write_text(str(os.getpid()))
            return lock
        except FileExistsError:
            try:
                pid = int((lock / "pid").read_text().strip())
                os.kill(pid, 0)
            except (OSError, ValueError):
                # The owner is gone (or never recorded one). Steal it: a crashed
                # demonstrator must not wedge every later run.
                shutil.rmtree(lock, ignore_errors=True)
                continue
            if time.time() > deadline:
                raise Red(f"another --demonstrate run (pid {pid}) has held this "
                          f"checkout's demonstration lock {lock} for {wait_s}s -- "
                          f"the cargo caches under target/gate-demo-* are per "
                          f"checkout, so CLEAN_GATE_DEMO_ROOT does not let two "
                          f"demonstrators share them; wait for pid {pid}")
            time.sleep(2.0)


# ── replayable demonstrations ────────────────────────────────────────────────


MUT_KEYS = {"create": "content", "append": "text", "prepend": "text",
            "replace-all": "text", "regex-sub": "pattern", "json-set": "value"}


def _mut_key(mut: dict, key: str) -> str:
    """The payload of a mutation, or a `Red` -- never a KeyError.

    MEASURED 2026-08-30: three recorded arms spell an `append` payload
    `content` (the key `create` uses) instead of `text`, so `_apply` raised
    `KeyError: 'text'`. That is not a `Red`, so it escaped `demonstrate`'s
    handler and took the WHOLE sweep down with a traceback -- the identical
    failure shape recorded two days earlier for `op: "create"`, which was fixed
    only for `create`. A payload this file cannot find is now one honest [FAIL]
    for that arm, and `R5 EVIDENCE` refuses the arm statically besides, in the
    0.27 s check that actually runs, rather than at replay time that nobody
    reaches.
    """
    val = mut.get(key)
    if not isinstance(val, str):
        raise Red(
            f"the arm's `{mut.get('op')}` mutation of {mut.get('file')} has no string "
            f"`{key}` (keys: {sorted(mut)}) -- a mutation with no payload cannot "
            f"demonstrate anything")
    return val


# The bytes each mutated path held when the sandbox was BUILT, keyed by
# (sandbox root, repo-relative path). See `_restore`.
_SANDBOX_BASELINE: dict[tuple[str, str], bytes | None] = {}


def _apply(root: Path, mut: dict) -> None:
    p = root / mut["file"]
    op = mut["op"]
    # Remember the pre-mutation bytes ONCE per path, so `_restore` can put back
    # what the sandbox started with rather than what git happens to hold.
    key = (str(root), mut["file"])
    if key not in _SANDBOX_BASELINE:
        try:
            _SANDBOX_BASELINE[key] = p.read_bytes()
        except OSError:
            _SANDBOX_BASELINE[key] = None
    # TWO STRUCTURAL REFUSALS, both about WHERE the mutation lands (2026-08-30).
    #
    # The first is the whole point of the sandbox: a mutation must never be
    # written into the shared checkout, whatever a caller passes. The second is
    # the one that is easy to miss and would silently undo the first -- the
    # sandbox is a symlink FARM, and `write_text` through a symlink writes the
    # REAL file. Every path an arm touches is materialised first, so a symlink
    # here means the materialisation was skipped, and the correct answer is to
    # refuse rather than to plant a defect in a co-tenant's tree.
    if root.resolve() == ROOT:
        raise Red(
            f"refusing to plant {mut['file']} in the shared checkout at {ROOT} -- "
            f"demonstrations run in a sandbox (see `_build_sandbox`)")
    if p.is_symlink():
        raise Red(
            f"refusing to mutate {mut['file']}: it is a symlink in the sandbox, so "
            f"the write would land in the shared tree it points at")
    if op == "create":
        # A PLANT, not an edit, and it must be handled BEFORE the read below.
        # The whole point of an R2 INVENTORY arm is that the file is NOT in the
        # tree, so `read_text()` raises FileNotFoundError -- which is not `Red`,
        # so it escapes `demonstrate`'s `except Red` and kills the entire sweep
        # with a traceback instead of one honest [FAIL].
        #
        # MEASURED 2026-08-28: the registry's OWN arm (recorded 2026-08-27,
        # `scripts/check_demo_planted_gate.py`) was written with this op, which
        # `_apply` never implemented. It had never been observed because a
        # standing R7 red made every replay bail at the baseline check first --
        # so the row that exists to prove gates are replayable carried an arm
        # that could not run, and the masking red hid it.
        if p.exists():
            raise Red(
                f"the arm creates {mut['file']}, which is already in the tree -- a "
                f"plant that overwrites an existing file is an edit, and restoring "
                f"it would not put the original back"
            )
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(_mut_key(mut, "content"))
        return
    text = p.read_text()
    if op == "regex-sub":
        new, n = re.subn(mut["pattern"], mut["replacement"], text, count=mut.get("count", 1))
        if n == 0:
            raise Red(
                f"the arm's mutation did not apply: pattern {mut['pattern']!r} does not "
                f"match {mut['file']}. A mutation that silently no-ops turns the whole "
                f"demonstration vacuous -- this is exactly instance 4."
            )
        text = new
    elif op == "append":
        text = text + _mut_key(mut, "text")
    elif op == "prepend":
        text = _mut_key(mut, "text") + text
    elif op == "json-set":
        doc = json.loads(text)
        cur = doc
        keys = mut["path"]
        for k in keys[:-1]:
            cur = cur[k]
        if keys[-1] not in cur:
            raise Red(f"the arm targets {'.'.join(map(str, keys))}, absent from {mut['file']}")
        cur[keys[-1]] = mut["value"]
        text = json.dumps(doc, indent=2) + "\n"
    elif op == "replace-all":
        text = _mut_key(mut, "text")
    else:
        raise Red(f"unknown mutation op {op!r}")
    p.write_text(text)


def _evict_mutated_units(sandbox: Path, root: Path, rel: str) -> None:
    """Drop the sandbox target dir's artifacts for the crate a compiling arm mutated.

    MEASURED 2026-09-08 (gate::leancross, then replayed on a two-crate workspace
    with the same cargo binary): cargo's `-C metadata` hash is WORKSPACE-RELATIVE,
    so a sandbox build of a mutated crate writes the same unit name the real
    tree would -- the same `deps/<crate>-<hash>`, the same `.fingerprint/` dir,
    the same uplifted bin -- and the dep-info it leaves names package-relative
    paths only. While the target dir was SHARED (until 2026-09-15) that unit WAS
    the real tree's: after `_restore` the pristine source was OLDER than the
    artifact, so the real tree's next `targo --unverified build` reported `Fresh`, re-linked
    the PLANT into the uplift, and a working-tree gate failed for a reason the
    tree did not have. Fail-closed, but false, and `git checkout --` cannot undo
    a build. The sandbox now owns its target dir, and the same mechanism still
    applies INSIDE it: the next demonstration re-clones the sandbox with `cp -p`
    mtimes older than the plant and would run it as its unmutated baseline. So
    after every restore the mutated crate's units are evicted with cargo's own
    `clean -p`, in both profiles a gate builds, under `_sandbox_env` so the
    eviction reaches the same directory the build did; the next build
    recompiles the crate from the bytes the tree has. One crate recompile per
    compiling arm is what a demonstration honestly costs.
    """
    members = _member_dirs(root)
    crate = next((m for m in sorted(members, key=len, reverse=True)
                  if rel == m or rel.startswith(m + "/")), None)
    if crate is None:
        return
    try:
        import tomllib
        name = tomllib.loads((root / crate / "Cargo.toml").read_text())["package"]["name"]
    except Exception as exc:  # noqa: BLE001 -- a note, never a silent skip
        print(f"  [note] could not read the package name under {crate}: {exc} -- "
              f"its planted units may survive in the sandbox's own target dir "
              f"{_sandbox_env(sandbox)['CARGO_TARGET_DIR']} (never the shared "
              f"target/, which no sandbox build reaches)")
        return
    for extra in ((), ("--release",)):
        # The canonical targo (see `_canonical_targo`), never PATH's first one.
        env = _sandbox_env(sandbox)
        r = subprocess.run([_canonical_targo() or "targo", "clean", "-p", name, *extra],
                           cwd=sandbox, env=env, pass_fds=_resource_fds(env),
                           capture_output=True, text=True)
        if r.returncode != 0:
            print(f"  [note] targo clean -p {name} {' '.join(extra)} failed in the "
                  f"sandbox: {(r.stderr or '').strip()[:160]}")


def _restore(root: Path, rel: str) -> None:
    # Restore to what the SANDBOX started with (`_SANDBOX_BASELINE`), not to
    # git's HEAD: the sandbox is cloned from the working tree, so on a dirty file
    # `git checkout --` reverted every later arm's copy to bytes the run was never
    # about (measured 2026-09-14, --demonstrate check_hook_coverage arms 3-4).
    baseline = _SANDBOX_BASELINE.get((str(root), rel))
    if baseline is not None:
        target = root / rel
        try:
            if target.read_bytes() != baseline:
                target.write_bytes(baseline)
            return
        except OSError as exc:
            raise Red(f"could not restore {rel} in {root}: {exc} "
                      f"-- the mutation is still in place") from exc
    co = subprocess.run(["git", "checkout", "--", rel], cwd=root, check=False,
                        capture_output=True, text=True)
    # A failed restore is a plant left behind, never a no-op (measured
    # 2026-08-30 in the shared tree: 29 of 40 `git checkout --` calls lost the
    # index.lock race to concurrent `git status` readers and left the plant).
    if co.returncode != 0 and _tracked(root, rel):
        raise Red(
            f"could not restore {rel} in {root}: {(co.stderr or '').strip()[:200]} "
            f"-- the mutation is still in place")
    # `git checkout --` is a no-op for an untracked path, so a `create` arm's
    # gate-shaped plant would survive and leave R2 INVENTORY red for everyone;
    # remove what git will not (`_dirty` refused the arm if anything was here).
    p = root / rel
    if p.is_file() and not _tracked(root, rel):
        p.unlink()


def _tracked(root: Path, rel: str) -> bool:
    return subprocess.run(["git", "ls-files", "--error-unmatch", "--", rel],
                          cwd=root, check=False,
                          capture_output=True).returncode == 0


def _dirty(root: Path, rel: str) -> bool:
    out = subprocess.run(["git", "status", "--porcelain", "--", rel], cwd=root,
                         capture_output=True, text=True).stdout.strip()
    return bool(out)


def _demo_python() -> str:
    """A python >= 3.11 for the arms, resolved the way local_gate.sh resolves one.

    /usr/bin/python3 on this machine is 3.9 and sits ahead of Homebrew on PATH,
    while five of these gates need `tomllib`. An arm that dies at import would
    be a non-zero exit for the WRONG reason -- which `expect_contains` catches,
    but only after wasting the run.
    """
    import shutil
    for cand in ("python3", "python3.14", "python3.13", "python3.12", "python3.11",
                 "/opt/homebrew/bin/python3", "/usr/local/bin/python3"):
        exe = shutil.which(cand) or (cand if Path(cand).exists() else None)
        if not exe:
            continue
        probe = subprocess.run([exe, "-c", "import tomllib"], capture_output=True)
        if probe.returncode == 0:
            return exe
    return sys.executable


def _leak_check(root: Path, before: dict, rels: list[str]) -> list[str]:
    """Did the arm reach the SHARED tree after all? Must return [].

    The sandbox is supposed to make this impossible, which is exactly why it is
    measured rather than asserted: `_apply` refuses two ways, and this is the
    third, from the outside, on the paths the arm actually touched.
    """
    after = _shared_state(root, rels)
    bad = []
    if after["status"] != before["status"]:
        bad.append(f"git status for {rels} moved from {before['status']!r} to "
                   f"{after['status']!r}")
    for rel, sha in before["sha"].items():
        if after["sha"].get(rel) != sha:
            bad.append(f"{rel} changed in the shared checkout ({sha} -> "
                       f"{after['sha'].get(rel)})")
    return bad


def demonstrate(root: Path, only: str | None, keep: bool = False,
                ran_over: list | None = None) -> int:
    doc = load_registry(root)
    demos = load_demos(root)
    rows = {r["id"]: r for r in doc["rows"]}
    targets = [only] if only else sorted(demos)
    py = _demo_python()
    failures = 0
    total = 0
    base = _sandbox_base()
    lock = _lock_acquire(_demo_lock_dir(root))
    built: dict[bool, Path] = {}

    def sandbox_for(build: bool, mutated: set[str]) -> Path:
        """One sandbox per LAYOUT per invocation, built on first use.

        The paths are stable across invocations on purpose: for the clone's
        own state, and since 2026-09-15 for the sandbox's own target dir
        (`<root>/target/gate-demo-<layout>`, persistent), whose units bake the
        sandbox path and stay valid only while it does not move. Incrementality
        within that dir comes from cargo's workspace-relative `-C metadata`
        hash, which gives the sandbox's units the real tree's NAMES -- measured
        2026-09-08, and the reason `_evict_mutated_units` exists; an earlier
        revision of this docstring had it backwards. The tree itself is deleted
        on the way out, on failure too; the target dir is not. A tree that
        cannot be deleted is a refusal, never a destination to copy into.
        """
        if build not in built:
            dest = base / ("tree-build" if build else "tree")
            leftover = _remove_sandbox(dest)
            if leftover:
                raise Red(leftover)
            t0 = time.time()
            _build_sandbox(root, dest, build, mutated)
            # Say what is true. This line used to read "{root} is never written
            # to" beside the name of a directory under {root} this very call
            # had just created and stamped (`_claim_demo_target`).
            print(f"  sandbox{' (build layout)' if build else ''}: {dest} "
                  f"({time.time() - t0:.1f}s) -- every mutation below lands "
                  f"there; no tracked path under {root} is written; cargo builds "
                  f"into {_sandbox_env(dest)['CARGO_TARGET_DIR']} (gitignored, "
                  f"persistent), never {root / 'target'} itself")
            built[build] = dest
        return built[build]

    leftovers: list[str] = []
    try:
        failures, total = _demonstrate_arms(
            root, sandbox_for, py, targets, demos, rows, failures, total, ran_over)
    finally:
        for dest in built.values():
            if keep:
                # What is kept is source only: `target` is a link to the
                # persistent per-layout cache, and `_sandbox_audit` refused any
                # build tree or nested checkout when the sandbox was built.
                print(f"  sandbox kept at {dest} (--keep-sandbox)")
                continue
            leftover = _remove_sandbox(dest)
            if leftover:
                print(f"  [FAIL] {leftover}")
                leftovers.append(leftover)
        shutil.rmtree(lock, ignore_errors=True)
    failures += len(leftovers)
    print(f"GATE_DEMOS arms={total} failed={failures}")
    return 1 if failures else 0


# ── every demonstration command runs under heavy_gate ─────────────────────────
#
# WHY (2026-10-01). An arm's `command` (a baseline and a mutated run per arm) and
# a row's `ref` (what `--repin` runs) are builds and test runs -- `targo
# --unverified test -p clean-mathverse ...` in a sandbox with its own cold target
# dir -- and this runner executed them DIRECTLY, outside scripts/heavy_gate.sh.
# So `--demonstrate` / `--repin` could run exactly the unbounded memory-heavy
# fleet that panicked this box (reports/kernel-panic-rca-2026-08-19.md),
# invisible to every other lane's admission. The fix is here, once, not per row:
# every command this runner executes for a demonstration goes through
# `_demo_argv`, which wraps it in `heavy_gate.sh run auto:gate-demo-<row>:<gb>`.
#
#   * ONE CLASS PER ROW, `gate-demo-<row>`: its weight is DERIVED from that
#     row's recorded peaks (heavy_gate_weights.sh: ceil(1.3 x the largest of the
#     last 10 COMPLETED runs)). A green baseline is a completed run and teaches
#     the weight; a red mutated run measured only part of a job and may raise
#     it, never lower it. An unseen row reserves the fallback, sized by whether
#     the arm compiles.
#   * NO CONCURRENCY beyond the gate: arms run one after another, each under
#     its own admission, queued FIFO with every other lane.
#   * THE GATE IS THE SHARED TREE'S (`ROOT/scripts/heavy_gate.sh`), never the
#     sandbox's copy, so an arm that mutates the gate cannot ungate itself.
#   * AN ENCLOSING RESERVATION IS HONOURED. `heavy_gate.sh run` exports
#     HEAVY_GATE_HELD to its command; under it, a second reservation would wait
#     for capacity its own parent holds, so the command runs in the caller's
#     reservation instead (one reservation around the whole replay, sized by the
#     caller from recorded peaks).
# `_selftest_heavy_gated` is RED if any of this regresses.
HEAVY_GATE_SCRIPT = ROOT / "scripts/heavy_gate.sh"
HEAVY_GATE_OVERRIDE = "CLEAN_GATE_HEAVY_GATE"  # TEST SEAM: the gate script to wrap with
HEAVY_GATE_HELD = "HEAVY_GATE_HELD"            # set by `heavy_gate.sh run` for its command
DEMO_FALLBACK_GB_BUILD = 16
DEMO_FALLBACK_GB = 12


def _demo_class(rid: str) -> str:
    """The heavy_gate class (and label) of a row's demonstration commands."""
    return "gate-demo-" + (re.sub(r"[^A-Za-z0-9_.-]+", "-", rid).strip("-") or "row")


def _demo_argv(argv: list[str], rid: str, builds: bool,
               env: dict[str, str] | None = None) -> list[str]:
    """`argv` as this runner must execute it: under a heavy_gate reservation."""
    if (env if env is not None else os.environ).get(HEAVY_GATE_HELD):
        return list(argv)
    gate = os.environ.get(HEAVY_GATE_OVERRIDE) or str(HEAVY_GATE_SCRIPT)
    cls = _demo_class(rid)
    fallback = DEMO_FALLBACK_GB_BUILD if builds else DEMO_FALLBACK_GB
    return ["bash", gate, "run", f"auto:{cls}:{fallback}", cls, "--", *argv]


def _arm_command(command: str, py: str) -> str:
    """An arm's recorded `python3 ...` command with `py` as its interpreter,
    QUOTED: the command runs under `/bin/sh -c`, and an interpreter path can hold
    a space (atpkg's CPython lives under `~/Library/Application Support`, where
    an unquoted path made every arm's baseline exit 127, 2026-11-06)."""
    return command.replace("python3 ", f"{shlex.quote(py)} ")


def _run_demo_command(command: str, rid: str, builds: bool, cwd: Path,
                      env: dict[str, str]) -> subprocess.CompletedProcess:
    """Run one arm's shell `command` (baseline or mutated) under the gate."""
    return subprocess.run(_demo_argv(["/bin/sh", "-c", command], rid, builds, env),
                          cwd=cwd, env=env, pass_fds=_resource_fds(env),
                          capture_output=True, text=True)


def _last_command_line(blob: str) -> str:
    """The last line the COMMAND printed: the gate's own report lines (its
    weight basis, its peak line and their indented continuations) come after
    the command's output and are not the command's reason for failing."""
    lines = [ln for ln in blob.strip().splitlines()
             if not ln.startswith("heavy_gate:") and not ln.startswith(" " * 12)]
    return lines[-1][:240] if lines else "(no output)"


def _demonstrate_arms(root: Path, sandbox_for, py: str, targets, demos, rows,
                      failures: int, total: int,
                      ran_over: list | None = None) -> tuple[int, int]:
    mutated = {a["mutate"]["file"] for rid in targets for a in (demos.get(rid) or [])}
    for rid in targets:
        arms = demos.get(rid)
        if not arms:
            print(f"  [FAIL] {rid}: no recorded arms")
            failures += 1
            continue
        row = rows.get(rid)
        if row is None:
            print(f"  [FAIL] {rid}: arms recorded for a gate with no registry row")
            failures += 1
            continue
        for arm in arms:
            total += 1
            f = arm["mutate"]["file"]
            label = f"{rid} :: {arm['arm']}"
            if _dirty(root, f):
                # NOT a refusal any more. It was one only because the arm used to
                # restore the SHARED file from git and would have thrown away a
                # co-tenant's edit; the sandbox copies the working-tree bytes and
                # clobbers nothing, so a dirty target is now a fact worth printing
                # rather than a reason to skip. If the edit genuinely breaks the
                # gate, the green-baseline check below says so, with the reason.
                print(f"  [note] {label}: {f} is modified in the shared tree; the "
                      f"sandbox takes the WORKING-TREE bytes, so this arm measures "
                      f"the tree as it is")
            command = _arm_command(arm["command"], py)
            # The bytes the arm will mutate, and the bytes of the gate itself,
            # must be the shared tree's. Otherwise this is a demonstration about
            # a copy, which is the one thing a sandbox must not become.
            build = _needs_build(command, arm)
            try:
                sandbox = sandbox_for(build, mutated)
                _materialize(root, sandbox, f)
            except Red as exc:
                print(f"  [FAIL] {label}: {exc}")
                failures += 1
                continue
            watched = [f, row.get("path") or "", row.get("implemented_by") or ""]
            diverged = _fidelity(root, sandbox, watched)
            if diverged:
                print(f"  [FAIL] {label}: the sandbox has DIVERGED from the shared "
                      f"tree at {diverged} -- refusing to demonstrate a gate against "
                      f"bytes this repository does not have")
                failures += 1
                continue
            if ran_over is not None:
                # What this arm runs over, read in the sandbox (see `_pin_state`).
                ran_over.append(_pin_state(sandbox, _subject(row)))
            before = _shared_state(root, watched)
            # The sandbox's own target dir, by env as well as by symlink -- see
            # `_sandbox_env` for the two routes a script can take to a cargo.
            env = _sandbox_env(sandbox)
            baseline = _run_demo_command(command, rid, build, sandbox, env)
            if baseline.returncode == 75 and "heavy_gate: REFUSED" in (baseline.stderr or ""):
                print(f"  [FAIL] {label}: heavy_gate REFUSED the arm on this box (exit "
                      f"75) -- it cannot fit here; nothing was measured")
                failures += 1
                continue
            if baseline.returncode != 0:
                # SAY WHY: a red baseline is a broken arm, the gate correctly
                # refusing a red tree, or an absent prerequisite, and an exit code
                # alone cannot tell them apart.
                why = _last_command_line((baseline.stdout or "") + (baseline.stderr or ""))
                print(f"  [FAIL] {label}: the UNMUTATED gate already exits "
                      f"{baseline.returncode} -- a red arm on a red tree proves nothing"
                      f"\n         its last line was: {why}")
                failures += 1
                continue
            try:
                _apply(sandbox, arm["mutate"])
                got = _run_demo_command(command, rid, build, sandbox, env)
            except Red as exc:
                print(f"  [FAIL] {label}: {exc}")
                _restore(sandbox, f)
                failures += 1
                continue
            finally:
                # Restore and evict IN the sandbox (its cloned .git, its files).
                _restore(sandbox, f)
                # The source is pristine again; the sandbox's target dir is not.
                # Not gated on `build`: an arm whose script runs cargo out of
                # sight reads as non-building (gate::leancross, 2026-09-09), and
                # evicting a crate that was never built costs nothing.
                _evict_mutated_units(sandbox, root, f)
            leaked = _leak_check(root, before, watched)
            if leaked:
                print(f"  [FAIL] {label}: the arm reached the SHARED checkout -- "
                      + "; ".join(leaked))
                failures += 1
                continue
            blob = (got.stdout or "") + (got.stderr or "")
            # A CONTROL arm (`expect: green`) must leave the gate green -- the
            # control that makes another arm's red mean what it says.
            if arm.get("expect") == "green":
                if got.returncode != 0:
                    print(f"  [FAIL] {label}: this is a CONTROL arm -- it must leave "
                          f"the gate GREEN, and the gate exited {got.returncode}")
                    failures += 1
                    continue
                needle = arm.get("expect_contains")
                if needle and needle not in blob:
                    print(f"  [FAIL] {label}: stayed green but never said {needle!r}")
                    failures += 1
                    continue
                print(f"  [ok]   {label}: CONTROL, stayed green")
                continue
            if got.returncode == 0:
                # A build-layout arm mutating a file outside every member crate
                # is vacuous when a test reads that file through
                # CARGO_MANIFEST_DIR: the crates are symlinks to the shared tree.
                hint = ""
                if build and not any(
                        f == m or f.startswith(m + "/") for m in _member_dirs(root)):
                    hint = (f"\n         {f} is outside every member crate, and this "
                            f"arm ran in the BUILD layout where crates are symlinks -- "
                            f"a test resolving it through CARGO_MANIFEST_DIR read the "
                            f"SHARED tree's copy. Try \"sandbox\": \"clone\" on the arm.")
                print(f"  [FAIL] {label}: the gate stayed GREEN under its own "
                      f"mutation -- it cannot fail, so its green means nothing{hint}")
                failures += 1
                continue
            needle = arm.get("expect_contains")
            if needle and needle not in blob:
                print(f"  [FAIL] {label}: exited {got.returncode} but never said "
                      f"{needle!r} -- it failed for some other reason")
                failures += 1
                continue
            print(f"  [ok]   {label}: rc={got.returncode}")
    return failures, total


def repin(root: Path, rid: str, undemonstrated: bool = False) -> int:
    """Move a row's pin -- its script sha and, for a subject that derives them,
    its input set -- over a demonstration run IN THIS PROCESS.

    `--repin` moves nothing unless the row's demonstration was RUN (a `ref`
    naming a script in this tree must exit 0) or REPLAYED (`--demonstrate`
    green) right here, pins only the bytes that run was over (`_pin_state`), and
    records that replay beside the pin (`replayed`, which R7 and R10 read).
    History, each measured: a blind re-hash re-greened a gutted self-test (audit
    r3), 47 of 63 rows were blind re-hashes (audit r9), a neutered `exit 1` in
    kernel_soundness_gate.sh re-greened on one `--repin` (audit r10), the
    undemonstrated account moved a DERIVED input set over arms that did not
    replay (verifier r9 recheck), and a scanner edited during a replay was
    pinned though no arm ran over it (verifier r10).

    `undemonstrated=True` (`--repin-undemonstrated`) is the separate verb for a
    row nothing here can run or replay: it moves the script sha on a STRUCTURED,
    EXPIRING, OWNED account (CLEAN_REPIN_UNDEMONSTRATED='<why>',
    CLEAN_REPIN_OWNER) that R4b polices -- one renewal at most, the first issue
    date and the sha it excused kept -- drops any replay record, never moves an
    input set, never moves the row's `date` (the last time it was SEEN to fail,
    which an account is not), and refuses a row with a replay route when it or a
    row inheriting its pin claims soundness (R4b)."""
    doc = load_registry(root)
    row = next((r for r in doc["rows"] if r["id"] == rid), None)
    if row is None:
        print(f"no registry row {rid}", file=sys.stderr)
        return 1
    d = row.get("demonstrated")
    if d is None:
        print(f"{rid} has no demonstration to re-pin", file=sys.stderr)
        return 1
    # `_subject`, not `path`: a leg/suite-row's pinned file is its implemented_by.
    subject = _subject(row)
    if not subject:
        print(f"{rid} names neither a path nor an implemented_by to pin", file=sys.stderr)
        return 1
    derives = _answers_pinned_inputs(root, subject)
    how = None
    ran_over: list = []  # the pin state each demonstration step ran over
    if undemonstrated:
        if derives or d.get("inputs") is not None:
            print(f"{rid}: refusing -- it pins the files {subject} derives "
                  f"({PINNED_INPUTS_FLAG}), and those move only over a replay "
                  f"(`--repin {rid}`), never on an account", file=sys.stderr)
            return 1
        sound = _soundness_under_account(doc["rows"], row)
        if sound and _has_replay_route(root, d):
            print(f"{rid}: refusing -- {', '.join(sound)} claims soundness on this pin and "
                  f"{rid} has a replay route; re-pin it over a replay (--repin {rid}) where "
                  f"its demonstration runs, never on an account (R4b)", file=sys.stderr)
            return 1
        why = os.environ.get("CLEAN_REPIN_UNDEMONSTRATED", "").strip()
        owner = os.environ.get("CLEAN_REPIN_OWNER", "").strip()
        prev = d.get("repinned_without_demonstration") or {}
        if not isinstance(prev, dict):
            print(f"{rid}: refusing -- its existing undemonstrated-pin account is free text, "
                  f"not an object R4b can read; fix it by hand first", file=sys.stderr)
            return 1
        if not why or not owner:
            print(f"{rid}: refusing -- an undemonstrated pin needs "
                  f"CLEAN_REPIN_UNDEMONSTRATED='<why>' and a named CLEAN_REPIN_OWNER",
                  file=sys.stderr)
            return 1
        if prev.get("renewals", 0) >= 1:
            print(f"{rid}: refusing -- this row already carries a RENEWED undemonstrated-pin "
                  f"account (first issued {prev.get('first_issued')}); demonstrate it",
                  file=sys.stderr)
            return 1
        d["repinned_without_demonstration"] = {
            "reason": why,
            "owner": owner,
            "first_issued": prev.get("first_issued") or date.today().isoformat(),
            "expires": (date.today() + timedelta(days=180)).isoformat(),
            "pinned_sha256": prev.get("pinned_sha256") or _sha256(root, subject),
            "renewals": prev.get("renewals", 0) + (1 if prev else 0),
        }
        d.pop("replayed", None)
        print(f"{rid}: re-pinning WITHOUT a demonstration; an expiring account is recorded "
              f"in the row and R4b will refuse it once it lapses")
    else:
        ref = str(d.get("ref") or "")
        words = ref.split()
        if words and words[0] in ("python3", "bash", "sh"):
            words = words[1:]
        runnable = bool(words) and words[0].startswith("scripts/") and (root / words[0]).exists()
        if runnable:
            # The run is in this tree, so what it ran over is read around it.
            ran_over.append(_pin_state(root, subject))
            try:
                env = dict(os.environ)
                result = subprocess.run(_demo_argv(ref.split(), rid, False, env), cwd=root,
                                        capture_output=True, env=env,
                                        pass_fds=_resource_fds(env))
                rc = result.returncode
            except OSError as exc:
                print(f"{rid}: refusing to re-pin -- its demonstration `{ref}` cannot run: "
                      f"{exc}", file=sys.stderr)
                return 1
            if rc != 0:
                print(f"{rid}: refusing to re-pin -- its own demonstration `{ref}` exits "
                      f"{rc} on this tree; fix that first", file=sys.stderr)
                for output in (result.stdout, result.stderr):
                    if output:
                        print(output.decode("utf-8", errors="replace"),
                              end="" if output.endswith(b"\n") else "\n", file=sys.stderr)
                return 1
            ran_over.append(_pin_state(root, subject))
            how = f"`{ref}` exited 0"
        elif d.get("replayable"):
            # A row naming `inherited_from` keeps its arms under the row it names
            # (R5 reads them there), and R7c judges it on any pin of its own, so
            # `--repin` replays those arms -- but only when that row pins the very
            # same subject: its arms run over its own file, which demonstrates
            # this row's pin only when the two are one file. Before this, such a
            # row could be discharged by no verb: `--repin` found no arms under
            # its own id, and the account refuses a soundness row with a route.
            arm_key = d.get("inherited_from") or rid
            if arm_key != rid:
                parent = next((r for r in doc["rows"] if r.get("id") == arm_key), None)
                parent_subject = _subject(parent) if parent is not None else None
                if parent_subject != subject:
                    seen = ("is no registry row" if parent is None
                            else f"pins {parent_subject or 'nothing'}, not {subject}")
                    print(f"{rid}: refusing to re-pin -- its arms are those of {arm_key} "
                          f"(inherited_from), which {seen}; those arms never ran over "
                          f"this row's pin", file=sys.stderr)
                    return 1
            print(f"{rid}: replaying its recorded demonstration"
                  f"{'' if arm_key == rid else f' (the arms of {arm_key})'} before the pin moves")
            if demonstrate(root, arm_key, ran_over=ran_over) != 0:
                # Often the UNMUTATED gate is red for someone else's change -- a red
                # arm on a red tree proves nothing, and it is still no licence to
                # move the pin.
                print(f"{rid}: refusing to re-pin -- its recorded demonstration does NOT "
                      f"replay on this tree", file=sys.stderr)
                return 1
            how = ("its recorded arms replayed green" if arm_key == rid else
                   f"the arms of {arm_key}, which pins the same subject, replayed green")
        else:
            print(f"{rid}: refusing to re-pin -- its demonstration `{ref}` can be neither run "
                  f"nor replayed here, and --repin moves a pin only over a demonstration it "
                  f"ran. For a row nothing can replay, `--repin-undemonstrated {rid}` records "
                  f"an owned, expiring account instead.", file=sys.stderr)
            return 1
        d.pop("repinned_without_demonstration", None)  # discharged by the run above
    live = _pin_state(root, subject)
    if how and (not ran_over or any(state != live for state in ran_over)):
        print(f"{rid}: refusing to re-pin -- this tree does not hold the bytes its "
              f"demonstration ran over: {subject} or a file it derives changed here while "
              f"the demonstration ran (or before its sandbox was cloned). Run --repin {rid} "
              f"again on a quiet tree.", file=sys.stderr)
        return 1
    if how:
        print(f"{rid}: {how} over the bytes this tree holds -- pin may move")
    if derives:
        if not isinstance(live[1], dict):
            print(f"{rid}: refusing to re-pin -- {live[1]}", file=sys.stderr)
            return 1
        d["inputs"] = dict(sorted(live[1].items()))
    elif d.get("inputs") is not None:
        print(f"{rid}: refusing to re-pin -- the row pins a derived input set and {subject} "
              f"no longer declares one; remove `inputs` by hand if that is meant",
              file=sys.stderr)
        return 1
    d["script_sha256"] = live[0]
    if not undemonstrated:
        # `date` is when a mutation last made it say no; an account saw no such
        # thing, and it carries its own first_issued (review of d5619e490).
        d["date"] = date.today().isoformat()
    if how:
        d["replayed"] = _replay_record(d, how)
    # indent=2 is how data/gate_registry.json is STORED: a re-pin's diff must be
    # the fields it moved, not a whole-file reformat. Round-trip the TRACKED file
    # before changing it.
    (root / "data/gate_registry.json").write_text(json.dumps(doc, indent=2) + "\n")
    # The registry first (review of R7c): the row's record is what discharges
    # it, so an anchor write that fails after it leaves a stale entry R7c names,
    # never an unrecorded row the anchor has already dropped.
    _discharge_replay_debt(root, rid)
    if undemonstrated:
        acct = d["repinned_without_demonstration"]
        print(f"re-pinned {rid} -> sha256:{d['script_sha256'][:12]} on an account issued "
              f"{acct['first_issued']}, expiring {acct['expires']}; its demonstration date "
              f"stays {d.get('date')}")
    else:
        print(f"re-pinned {rid} -> sha256:{d['script_sha256'][:12]} on {d.get('date')}")
    return 0


# ── self-test ────────────────────────────────────────────────────────────────
#
# The demonstrator has to demonstrate itself, or this file is instance number
# seven. The arms (see the derived count the selftest prints) build a synthetic repo, mutate one thing, and
# require the named rule to fire. Arms 1, 25, 30 and 31 require the tree to be
# GREEN, so an arm that reds for an unrelated reason cannot be mistaken for a
# working rule.
#
# Arms 38-43 (`_selftest_mutations`) are a different KIND and that is the point:
# they test the mutation ENGINE rather than a rule. Every other arm here proves
# a rule can say no; those six prove the machinery that REPLAYS the recorded
# arms can still apply and undo a mutation at all. The gap was real -- an arm
# recorded with an op `_apply` did not implement crashed the sweep instead of
# failing it.
# ~0.1 s, and it runs FIRST on every gate invocation.


def _mini(tmp: Path) -> Path:
    root = tmp / "repo"
    (root / "scripts/githooks").mkdir(parents=True)
    (root / "data").mkdir(parents=True)
    (root / "scripts/check_alpha.py").write_text("#!/usr/bin/env python3\n# --selftest\nprint('a')\n")
    # A gate that READS RUST SOURCE, for the R9 arms. `strip_noncode` is in the
    # body, so the unmutated tree is honestly `lexed`.
    (root / "scripts/check_scan.py").write_text(
        "#!/usr/bin/env python3\n# --selftest\n"
        "for p in root.rglob('*.rs'):\n"
        "    hits = strip_noncode(p.read_text())\n"
    )
    # A RUST BATTERY that reads Rust source with its OWN walker (lane LOOSE,
    # 2026-08-25). R9 could not see this shape at all: no rglob, no
    # collect_rust_source_files, no shell grep. The stripper name appears in
    # CODE, so the unmutated row is honestly `lexed`.
    (root / "crates/x/tests").mkdir(parents=True)
    (root / "crates/x/tests/scan_battery.rs").write_text(
        "// walks crates/**/*.rs and counts a forbidden call\n"
        "fn collect_rust_files(root: &Path, out: &mut Vec<PathBuf>) {}\n"
        "fn scan(src: &str) -> usize { blank_noncode(src).matches(\"bad(\").count() }\n"
        "#[test]\nfn two_way_arm() { assert_eq!(scan(\"// bad(\"), 0); }\n"
    )
    (root / "scripts/beta_gate.sh").write_text("#!/usr/bin/env bash\necho b\n")
    # A committed mutation-proof record, for the R7b arms (audit r9 M-3): a
    # row's pin must be backed by SOME cited record that demonstrates it.
    (root / "reports").mkdir(exist_ok=True)
    # the soundness-claim anchor (audit r11 M11-8): rows claiming soundness in
    # this fixture must be listed, or R11 correctly reports the set unanchored
    (root / "data/soundness_claims_ratchet.json").write_text(json.dumps({
        "schema": "clean.gate.soundness-claims.v1",
        "soundness_rows": ["check_alpha", "check_scan", "check_rs_scan", "alpha"],
    }) + "\n")
    (root / "reports/mutation-proof-beta.json").write_text(json.dumps({
        "schema_version": "Clean-srcelab-mutation-proof-v1",
        "script_sha256": _sha256(root, "scripts/beta_gate.sh"),
        "purpose": "selftest fixture",
    }) + "\n")
    (root / "scripts/test_beta_gate.sh").write_text("# self-test for beta\n")
    (root / "scripts/check_script_selftests.sh").write_text("#!/usr/bin/env bash\n# runs scripts/test_*\n")
    (root / "scripts/local_gate.sh").write_text(
        "#!/usr/bin/env bash\n"
        "# GATE-LEG: alpha\n"
        '"$GATE_PYTHON" scripts/check_alpha.py\n'
        "bash scripts/beta_gate.sh\n"
        '"$GATE_PYTHON" scripts/check_scan.py\n'
        "bash scripts/check_script_selftests.sh\n"
    )
    (root / "scripts/githooks/pre-push").write_text(
        "#!/usr/bin/env bash\nleg_alpha() { \"$PY\" scripts/check_alpha.py; }\n"
    )
    (root / "scripts/verify_runner.py").write_text('        "id": "gate::fmt",\n')
    (root / "Justfile").write_text("gate:\n    bash scripts/local_gate.sh\n")
    rows = [
        {"id": "check_alpha", "path": "scripts/check_alpha.py", "kind": "gate",
         "claims": "soundness",
         "wired_by": ["scripts/githooks/pre-push", "scripts/local_gate.sh"],
         "demonstrated": {"kind": "selftest-inline", "flag": "--selftest",
                          "ref": "scripts/check_alpha.py --selftest", "date": "2026-08-24",
                          "script_sha256": _sha256(root, "scripts/check_alpha.py")},
         "waiver": None},
        {"id": "beta_gate", "path": "scripts/beta_gate.sh", "kind": "gate",
         "claims": "quality", "wired_by": ["scripts/local_gate.sh"],
         "demonstrated": {"kind": "selftest-file", "ref": "scripts/test_beta_gate.sh",
                          "date": "2026-08-24",
                          "note": "demonstrated by reports/mutation-proof-beta.json",
                          "script_sha256": _sha256(root, "scripts/beta_gate.sh")},
         "waiver": None},
        {"id": "check_scan", "path": "scripts/check_scan.py", "kind": "gate",
         "claims": "soundness", "wired_by": ["scripts/local_gate.sh"],
         "source_scan": {"kind": "lexed", "note": "selftest scanner"},
         "demonstrated": {"kind": "selftest-inline", "flag": "--selftest",
                          "ref": "scripts/check_scan.py --selftest", "date": "2026-08-24",
                          "script_sha256": _sha256(root, "scripts/check_scan.py")},
         "waiver": None},
        {"id": "check_rs_scan", "path": "crates/x/tests/scan_battery.rs", "kind": "battery",
         "claims": "soundness", "wired_by": [],
         "source_scan": {"kind": "lexed", "note": "selftest Rust battery"},
         "demonstrated": {"kind": "selftest-inline", "flag": "two_way_arm",
                          "ref": "targo --unverified test -p x --test scan_battery", "date": "2026-08-25",
                          "script_sha256": _sha256(root, "crates/x/tests/scan_battery.rs")},
         "waiver": None},
        {"id": "check_script_selftests", "path": "scripts/check_script_selftests.sh",
         "kind": "gate", "claims": "hygiene", "wired_by": ["scripts/local_gate.sh"],
         "demonstrated": None, "waiver": None},
        {"id": "local_gate", "path": "scripts/local_gate.sh", "kind": "gate",
         "claims": "hygiene", "wired_by": ["Justfile"],
         "demonstrated": None, "waiver": None},
        # A leg has no path, so R7 reaches its implementation through
        # `implemented_by`. This one DELEGATES its pin to `check_alpha`, the row
        # whose `path` is that very file -- the shape twenty of the real rows
        # use, and the green control for arms 44-49.
        {"id": "alpha", "path": "", "kind": "leg", "claims": "soundness",
         "wired_by": ["scripts/local_gate.sh"], "implemented_by": "scripts/check_alpha.py",
         "demonstrated": {"kind": "selftest-inline", "flag": "--selftest",
                          "ref": "scripts/check_alpha.py --selftest", "date": "2026-08-24",
                          "inherited_from": "check_alpha"},
         "waiver": None},
        {"id": "gate::fmt", "path": "", "kind": "suite-row", "claims": "hygiene",
         "wired_by": ["scripts/verify_runner.py"], "demonstrated": None, "waiver": None},
    ]
    retired = [
        {"id": "old_gate", "path": "scripts/old_gate.sh", "retired": "2026-08-25",
         "by": "selftest", "reason": "superseded", "superseded_by": ["beta_gate"]},
    ]
    (root / "data/gate_registry.json").write_text(
        json.dumps({"rows": rows, "retired": retired}, indent=2))
    (root / "data/gate_demonstrations.json").write_text(json.dumps({"arms": {}}, indent=2))
    # audit r14 M14-5: the mini-repo anchors an EMPTY R7b reach, so the rule is
    # live in every arm and the two arms below can move it.
    (root / "data/r7b_record_coverage.json").write_text(
        json.dumps({"count": 0, "rows": []}, indent=2))
    # R7c: check_alpha, check_scan and check_rs_scan claim soundness on pins of
    # their own and carry no replay record, as the real legacy rows do
    # (check_rs_scan has no replay route at all; R7c does not ask).
    (root / REPLAY_DEBT_REL).write_text(json.dumps(
        {"count": 3, "rows": ["check_alpha", "check_scan", "check_rs_scan"]}, indent=2))
    return root


def _mkpkg(root: Path, rel: str, main: bool = True) -> None:
    """Create a Python PACKAGE under scripts/ in the self-test mini-repo.

    `main=True` writes a `__main__.py`, which is what makes the directory an
    ARTIFACT (`python3 -m scripts.<name>` runs it) rather than a library.
    """
    d = root / rel
    d.mkdir(parents=True, exist_ok=True)
    (d / "detect.py").write_text("# detector\n")
    if main:
        (d / "__main__.py").write_text("from .cli import main\n")
    else:
        (d / "__init__.py").write_text("# library\n")


def _reg(root: Path) -> dict:
    return json.loads((root / "data/gate_registry.json").read_text())


def _put(root: Path, doc: dict) -> None:
    (root / "data/gate_registry.json").write_text(json.dumps(doc, indent=2))


def _selftest_mutations() -> tuple[int, int]:
    """Arms for the mutation ENGINE -- `_apply` and `_restore` themselves.

    Recorded 2026-08-28, after the registry's own R2 arm was found unrunnable.
    It was written with `op: "create"`, which `_apply` never implemented, and
    the failure mode was an UNCAUGHT FileNotFoundError rather than a `Red`, so
    it would have taken the whole `--demonstrate` sweep down with a traceback
    instead of reporting one honest [FAIL]. Nobody had seen it because a
    standing R7 red made every replay bail at the baseline check first.

    Arms 38 and 39 are the two that would have caught it. The rest exist so the
    fix cannot quietly widen into "any op writes anywhere": 40 keeps `create` a
    plant rather than an overwrite, 41 and 42 are the pre-existing refusals
    (unknown op, and the no-op regex that is the vacuity guard), and 43 is the
    control that `_restore` still restores a file git DOES track -- the path the
    untracked-cleanup could most easily have broken.
    """
    failures = 0
    arms = 0
    plant = {"file": "scripts/check_planted.py", "op": "create",
             "content": "#!/usr/bin/env python3\nimport sys\nsys.exit(0)\n"}

    def run(name, fn):
        nonlocal failures, arms
        arms += 1
        with tempfile.TemporaryDirectory() as td:
            root = _mini(Path(td))
            _git_run(root, "init", "-q", "-b", "main")
            _git_run(root, "add", "-A")
            _git_run(root, "commit", "-qm", "green")
            try:
                fn(root)
            except AssertionError as exc:
                print(f"  [FAIL] {name}: {exc}")
                failures += 1
                return
            except Exception as exc:  # noqa: BLE001
                print(f"  [FAIL] {name}: unexpected {type(exc).__name__}: {exc}")
                failures += 1
                return
        print(f"  [ok]   {name}")

    def a_create(root):
        p = root / plant["file"]
        assert not p.exists(), "precondition: the plant must not already be there"
        _apply(root, plant)
        assert p.is_file(), "`create` did not write the file"
        assert p.read_text() == plant["content"], "`create` wrote the wrong bytes"

    def a_restore_untracked(root):
        _apply(root, plant)
        _restore(root, plant["file"])
        assert not (root / plant["file"]).exists(), (
            "`_restore` left an untracked plant behind -- every later run is R2 red")

    def a_create_refuses_existing(root):
        try:
            _apply(root, {**plant, "file": "scripts/check_alpha.py"})
        except Red:
            return
        raise AssertionError("`create` overwrote a file that was already in the tree")

    def a_unknown_op(root):
        try:
            _apply(root, {"file": "scripts/check_alpha.py", "op": "teleport"})
        except Red:
            return
        raise AssertionError("an unknown mutation op was not refused")

    def a_regex_noop(root):
        try:
            _apply(root, {"file": "scripts/check_alpha.py", "op": "regex-sub",
                          "pattern": "ZZZ_not_present", "replacement": "x"})
        except Red:
            return
        raise AssertionError("a no-op regex mutation was not refused")

    def a_restore_tracked(root):
        p = root / "scripts/check_alpha.py"
        before = p.read_text()
        _apply(root, {"file": "scripts/check_alpha.py", "op": "append",
                      "text": "# edit\n"})
        assert p.read_text() != before, "precondition: the edit must land"
        _restore(root, "scripts/check_alpha.py")
        assert p.read_text() == before, "`_restore` no longer restores a TRACKED file"

    # ── isolation: arms 60-69 ────────────────────────────────────────────────
    #
    # 60+, not 44+, because THREE arm groups share one numbering space here (the
    # rule arms, `_selftest_wiring`, and this function), and 38-50 was already
    # taken twice over. A registry note that says "arm 46" has to mean one arm.
    #
    # Recorded 2026-08-30, with the sandbox. These are the arms that say the
    # demonstrator cannot reach the shared checkout, and each one is written so
    # that removing the thing it guards turns it red -- an observer that cannot
    # see a plant would score a broken sandbox as a working one, so 63 plants
    # the mutation the OLD way and requires the observer to notice.
    #
    # They run on a real `git init` repository (~40 ms) because the claim is
    # about what `git status` says, which is the form the harm took: a lane
    # reading `git status`, staging a file, or running a gate during the window.

    def a_apply_refuses_shared(root):
        # The one arm that aims at the REAL repository, because that is the
        # thing being claimed. The path is deliberately untracked, not
        # gate-shaped, and inside a directory this repo already writes to, so
        # the blast radius of a removed guard is one ignorable temp file -- and
        # the arm DELETES it on the failing path. That cleanup is not tidiness:
        # measured 2026-08-30 while mutation-proving this very arm, the first
        # version left the probe behind when the guard was removed, and every
        # later run then failed on the leftover rather than on the guard.
        probe = {"file": "reports/.gate-demo-selftest-probe.tmp", "op": "create",
                 "content": "probe\n"}
        target = ROOT / probe["file"]
        existed = target.exists()
        try:
            _apply(ROOT, probe)
        except Red as exc:
            assert "shared checkout" in str(exc), f"refused for the wrong reason: {exc}"
            assert target.exists() == existed, "it refused AND still wrote"
            return
        if not existed:
            target.unlink(missing_ok=True)
        raise AssertionError(
            "`_apply` wrote into the shared checkout -- the sandbox is bypassable")

    def a_apply_refuses_symlink(root):
        (root / "outside.txt").write_text("real bytes\n")
        (root / "link.txt").symlink_to(root / "outside.txt")
        try:
            _apply(root, {"file": "link.txt", "op": "append", "text": "planted\n"})
        except Red as exc:
            assert "symlink" in str(exc), f"refused for the wrong reason: {exc}"
            assert (root / "outside.txt").read_text() == "real bytes\n", (
                "the write went THROUGH the symlink into the file it points at")
            return
        raise AssertionError(
            "a mutation was written through a symlink -- in the sandbox that "
            "symlink points at the shared tree")

    def a_sandbox_isolates(root):
        sand = root.parent / "sandbox"
        _build_sandbox(root, sand, build=False, mutated=set())
        _materialize(root, sand, "scripts/check_alpha.py")
        before = _shared_state(root, ["scripts/check_alpha.py"])
        _apply(sand, {"file": "scripts/check_alpha.py", "op": "append",
                      "text": "\n# planted\n"})
        assert "# planted" in (sand / "scripts/check_alpha.py").read_text(), (
            "the mutation did not reach the sandbox, so the arm proves nothing")
        assert _leak_check(root, before, ["scripts/check_alpha.py"]) == [], (
            "the mutation reached the shared tree")
        assert "planted" not in (root / "scripts/check_alpha.py").read_text()

    def a_in_tree_plant_is_visible(root):
        # THE CONTROL for 62 and 66. Same mutation, applied the way it was
        # applied until 2026-08-30, and the observer must see it -- otherwise
        # 62's silence would be the silence of a blind check.
        before = _shared_state(root, ["scripts/check_alpha.py"])
        _apply(root, {"file": "scripts/check_alpha.py", "op": "append",
                      "text": "\n# planted\n"})
        leaks = _leak_check(root, before, ["scripts/check_alpha.py"])
        assert leaks, "an in-tree plant was NOT visible in git status or the digest"
        assert any("git status" in x for x in leaks), (
            f"the plant was seen, but not as a working-tree change: {leaks}")

    def a_fidelity_catches_drift(root):
        sand = root.parent / "sandbox"
        _build_sandbox(root, sand, build=False, mutated=set())
        _materialize(root, sand, "scripts/check_alpha.py")
        assert _fidelity(root, sand, ["scripts/check_alpha.py"]) == [], (
            "a freshly materialised file already reads as diverged")
        (sand / "scripts/check_alpha.py").write_text("something else\n")
        assert _fidelity(root, sand, ["scripts/check_alpha.py"]) == [
            "scripts/check_alpha.py"], (
            "a sandbox that no longer holds this tree's bytes was not caught -- "
            "the demonstration would be about a copy")

    def a_build_layout_symlinks_members(root):
        (root / "Cargo.toml").write_text('[workspace]\nmembers = ["crates/a"]\n')
        (root / "crates/a").mkdir(parents=True)
        (root / "crates/a/lib.rs").write_text("fn main() {}\n")
        sand = root.parent / "sandbox"
        _build_sandbox(root, sand, build=True, mutated=set())
        assert (sand / "crates/a").is_symlink(), (
            "the build layout did not symlink an unmutated member crate, so every "
            "package path moves and cargo rebuilds the workspace from cold")
        shutil.rmtree(sand)
        _build_sandbox(root, sand, build=True, mutated={"crates/a/lib.rs"})
        assert not (sand / "crates/a").is_symlink(), (
            "the crate an arm MUTATES was symlinked -- the mutation would be "
            "written through it, into the shared tree")

    def a_sandbox_owns_its_target(root):
        # THE 2026-09-15 FINDING, in miniature (see the paragraph above
        # `_clone_tree`): with `target/` symlinked to the shared dir, a sandbox
        # build overwrote the real tree's units with units whose
        # CARGO_MANIFEST_DIR named a sandbox that was then deleted -- 27
        # poisoned rlibs, from BOTH layouts. So in both layouts the sandbox's
        # `target/` must be its OWN directory, under the real `target/` (so the
        # census sees it), exported as CARGO_TARGET_DIR (so a script that
        # honours an inherited value cannot be handed the shared cache), and a
        # write into it must not reach the shared one.
        (root / "Cargo.toml").write_text('[workspace]\nmembers = ["crates/a"]\n')
        (root / "crates/a").mkdir(parents=True)
        (root / "crates/a/lib.rs").write_text("fn main() {}\n")
        shared = root / "target"
        (shared / "debug").mkdir(parents=True)
        (shared / "debug/libreal.rlib").write_text("the shared tree's unit\n")
        # The two layouts at the names `demonstrate` really uses, `tree` and
        # `tree-build`, NOT one name twice: both mint identical unit filenames
        # with different sandbox paths baked in, so "one cache per layout" is a
        # property the arm must hold, and a first revision that reused one
        # `sandbox` name for both iterations exercised `_demo_target_dir` with
        # one layout and could not have seen it collapse.
        owns: dict[str, Path] = {}
        for build in (True, False):
            layout = "tree-build" if build else "tree"
            sand = root.parent / layout
            shutil.rmtree(sand, ignore_errors=True)
            _build_sandbox(root, sand, build=build, mutated=set())
            link = sand / "target"
            assert link.is_symlink(), (
                f"{layout} layout: the sandbox has no target symlink -- a script "
                f"reading target/debug/<bin> by path would find nothing")
            own = Path(os.readlink(link))
            owns[layout] = own
            assert own.resolve() != shared.resolve(), (
                f"{layout} layout: the sandbox's target IS the shared target dir -- "
                f"a sandbox build would overwrite this tree's units with units "
                f"whose CARGO_MANIFEST_DIR names the sandbox")
            assert own.resolve().is_relative_to(shared.resolve()), (
                f"{layout} layout: the sandbox's target {own} is not under the real "
                f"target/, so `scripts/target_census.sh` never counts or prunes it")
            assert own.is_dir(), f"{layout} layout: {own} was not created"
            assert not (own / "debug/libreal.rlib").exists(), (
                f"{layout} layout: the sandbox's target can see the shared tree's "
                f"units -- it is the shared dir under another name")
            env = _sandbox_env(sand)
            assert env.get("CARGO_TARGET_DIR") == str(own), (
                f"{layout} layout: the arm's environment carries "
                f"CARGO_TARGET_DIR={env.get('CARGO_TARGET_DIR')!r}, not the "
                f"sandbox's own {own} -- a script that honours an inherited value "
                f"builds into whatever the demonstrator inherited")
            assert env.get("CARGO_BUILD_BUILD_DIR") == str(own), (
                f"{layout} layout: the arm's environment carries "
                f"CARGO_BUILD_BUILD_DIR={env.get('CARGO_BUILD_BUILD_DIR')!r}, not "
                f"the sandbox's own {own} -- on a cargo that knows build.build-dir "
                f"the deps/ and .fingerprint/ that bake CARGO_MANIFEST_DIR go "
                f"wherever that names, under a green CARGO_TARGET_DIR")
            (own / "debug").mkdir(exist_ok=True)
            (own / "debug/libplant.rlib").write_text("a sandbox unit\n")
            assert not (shared / "debug/libplant.rlib").exists(), (
                f"{layout} layout: a write into the sandbox's target reached the "
                f"shared target dir")
            (own / "debug/libplant.rlib").unlink()
        assert owns["tree"].resolve() != owns["tree-build"].resolve(), (
            f"both layouts resolve to ONE cache, {owns['tree']} -- the clone "
            f"layout's units bake .../tree/... and the build layout's "
            f".../tree-build/... under identical filenames, so each would link "
            f"the other's dead paths: the 2026-09-15 poisoning, between sandboxes")
        assert (shared / "debug/libreal.rlib").read_text() == "the shared tree's unit\n"

    def a_moved_sandbox_drops_its_cache(root):
        # The units in a sandbox target dir bake the sandbox's absolute path and
        # cargo does not re-key on it (that is the whole finding), so a cache
        # minted for a sandbox at ANOTHER path must be dropped, and -- the
        # control -- one minted for THIS path must be kept, or every compiling
        # arm pays a cold build on every demonstration.
        sand = root.parent / "sandbox"
        own = _demo_target_dir(root, sand.name)
        (own / "debug").mkdir(parents=True)
        (own / "debug/libstale.rlib").write_text("minted for another sandbox path\n")
        (own / _TARGET_STAMP).write_text("/somewhere/else/sandbox\n")
        _build_sandbox(root, sand, build=False, mutated=set())
        assert not (own / "debug/libstale.rlib").exists(), (
            "a cache minted for a sandbox at ANOTHER path was reused -- every "
            "CARGO_MANIFEST_DIR it bakes names a directory that does not exist")
        assert (own / _TARGET_STAMP).read_text().strip() == str(sand), (
            "the cache was not re-stamped with the sandbox it now serves")
        (own / "debug").mkdir(parents=True, exist_ok=True)
        (own / "debug/libwarm.rlib").write_text("minted for this sandbox path\n")
        shutil.rmtree(sand)
        _build_sandbox(root, sand, build=False, mutated=set())
        assert (own / "debug/libwarm.rlib").exists(), (
            "CONTROL: a cache minted for THIS sandbox path was dropped -- every "
            "compiling arm pays a cold build on every demonstration")

    def a_undroppable_cache_is_refused(root):
        # A mismatched cache that CANNOT be dropped must be a refusal, never a
        # re-stamp. The shape an operator produces: the cache moved to another
        # volume with a symlink left at its path -- `shutil.rmtree` refuses a
        # symlink with OSError, and a first revision swallowed that with
        # `ignore_errors=True` and then stamped the dead units as warm.
        sand = root.parent / "sandbox"
        own = _demo_target_dir(root, sand.name)
        elsewhere = root.parent / "other-volume-cache"
        (elsewhere / "debug").mkdir(parents=True)
        (elsewhere / "debug/libstale.rlib").write_text("minted for another path\n")
        (elsewhere / _TARGET_STAMP).write_text("/somewhere/else/sandbox\n")
        own.parent.mkdir(parents=True, exist_ok=True)
        own.symlink_to(elsewhere)
        try:
            _build_sandbox(root, sand, build=False, mutated=set())
        except Red as exc:
            assert str(own) in str(exc), (
                f"the refusal does not name the cache it could not drop: {exc}")
        else:
            raise AssertionError(
                "a cache that could not be dropped was silently re-stamped -- its "
                "every baked CARGO_MANIFEST_DIR is dead and the next compiling "
                "arm links it")
        assert (elsewhere / _TARGET_STAMP).read_text().strip() == "/somewhere/else/sandbox", (
            "the undroppable cache was RE-STAMPED for this sandbox despite the "
            "refusal -- the next run would take it as warm")
        assert (elsewhere / "debug/libstale.rlib").exists(), (
            "the refusal path deleted units through the symlink it refused")

    def a_lock_is_keyed_on_the_checkout(root):
        # The mutex and the cache must be keyed on the SAME thing. The cache is
        # per checkout; a lock keyed on the sandbox base (TMPDIR /
        # CLEAN_GATE_DEMO_ROOT) let two demonstrators on one checkout take two
        # locks and drop each other's cache mid-build.
        saved = os.environ.get("CLEAN_GATE_DEMO_ROOT")
        try:
            os.environ["CLEAN_GATE_DEMO_ROOT"] = str(root.parent / "base-a")
            base_a, lock_a = _sandbox_base(), _demo_lock_dir(root)
            os.environ["CLEAN_GATE_DEMO_ROOT"] = str(root.parent / "base-b")
            base_b, lock_b = _sandbox_base(), _demo_lock_dir(root)
        finally:
            if saved is None:
                os.environ.pop("CLEAN_GATE_DEMO_ROOT", None)
            else:
                os.environ["CLEAN_GATE_DEMO_ROOT"] = saved
        assert base_a != base_b, "precondition: CLEAN_GATE_DEMO_ROOT moves the sandbox"
        assert lock_a == lock_b, (
            f"the demonstrators' lock moved with CLEAN_GATE_DEMO_ROOT ({lock_a} vs "
            f"{lock_b}) while the cache did not -- two demonstrators on this "
            f"checkout would hold two locks and share one cache")
        assert lock_a.parent == _demo_target_dir(root, "tree").parent, (
            f"the lock {lock_a} is not keyed where the caches are "
            f"({_demo_target_dir(root, 'tree').parent})")
        held = _lock_acquire(lock_a, wait_s=1)
        try:
            assert held == lock_a and (held / "pid").read_text() == str(os.getpid())
        finally:
            shutil.rmtree(held, ignore_errors=True)

    run("38 _apply `create` plants a file that is not in the tree", a_create)
    run("39 _restore removes an untracked plant", a_restore_untracked)
    run("40 `create` refuses a file that already exists", a_create_refuses_existing)
    run("41 an unknown mutation op is refused", a_unknown_op)
    run("42 a no-op regex mutation is refused", a_regex_noop)
    def a_restore_uncommitted(root):
        # AUDIT r17: a sandbox is cloned from the WORKING TREE, so a tracked file
        # with uncommitted content differs from the sandbox's HEAD. `_restore`
        # used `git checkout --`, which put back HEAD -- silently reverting every
        # LATER arm's copy to bytes the run was never about, while the harness's
        # own per-arm note promised "the sandbox takes the WORKING-TREE bytes".
        # Measured on --demonstrate check_hook_coverage: arms 1-2 mutate
        # gate-legs.txt and passed, arms 3-4 then died on "the UNMUTATED gate
        # already exits 1" because the uncommitted row they depend on was gone.
        p = root / "scripts/check_alpha.py"
        uncommitted = p.read_text() + "# uncommitted, as a dirty working tree has\n"
        p.write_text(uncommitted)
        _apply(root, {"file": "scripts/check_alpha.py", "op": "append",
                      "text": "# arm edit\n"})
        assert p.read_text() != uncommitted, "precondition: the edit must land"
        _restore(root, "scripts/check_alpha.py")
        assert p.read_text() == uncommitted, (
            "`_restore` put back git's bytes, not the sandbox's -- an uncommitted "
            "change is lost for every arm after the first")
        _SANDBOX_BASELINE.pop((str(root), "scripts/check_alpha.py"), None)
        subprocess.run(["git", "checkout", "--", "scripts/check_alpha.py"],
                       cwd=root, check=False, capture_output=True)

    run("43 _restore still restores a TRACKED file", a_restore_tracked)
    run("43b _restore puts back the SANDBOX's bytes, not git's", a_restore_uncommitted)
    def a_payload_missing(root):
        # MEASURED 2026-08-30: three recorded arms spelled an `append` payload
        # `content`, so `_apply` raised KeyError('text') -- not a `Red`, so it
        # escaped `demonstrate`'s handler and took the whole sweep down with a
        # traceback. The identical shape was recorded for `op: "create"` two
        # days earlier and fixed only for `create`.
        try:
            _apply(root, {"file": "scripts/check_alpha.py", "op": "append",
                          "content": "# wrong key\n"})
        except Red as exc:
            assert "no string `text`" in str(exc), f"wrong refusal: {exc}"
            return
        except Exception as exc:  # noqa: BLE001
            raise AssertionError(
                f"a payload-less mutation raised {type(exc).__name__}, which is not "
                f"`Red` -- it would kill the whole --demonstrate sweep") from exc
        raise AssertionError("a mutation with no payload was applied anyway")

    def a_restore_failure_is_loud(root):
        # THE MEASURED ONE. `git checkout --` needs .git/index.lock, and any
        # other git command in the repository can be holding it -- 29 of 40
        # attempts failed under four concurrent `git status` readers on
        # 2026-08-30. Holding the lock is a deterministic stand-in for losing
        # that race, and the old code answered it by returning normally, which
        # is how a plant would outlive its own demonstration.
        p = root / "scripts/check_alpha.py"
        before = p.read_text()
        _apply(root, {"file": "scripts/check_alpha.py", "op": "append",
                      "text": "# planted\n"})
        # The restore no longer goes through git for a path with a recorded
        # baseline (audit r17), so a stale index.lock is no longer what stops
        # it -- an unwritable target is. The PROPERTY is unchanged and is the
        # only one that ever mattered: a restore that cannot put the bytes back
        # says so, rather than reporting success over a live plant.
        (root / ".git/index.lock").write_text("")
        p.chmod(0o444)
        try:
            _restore(root, "scripts/check_alpha.py")
        except Red as exc:
            assert "still in place" in str(exc), f"wrong refusal: {exc}"
            return
        finally:
            p.chmod(0o644)
            (root / ".git/index.lock").unlink(missing_ok=True)
            _SANDBOX_BASELINE.pop((str(root), "scripts/check_alpha.py"), None)
            p.write_text(before)
        raise AssertionError(
            "a restore that could not run reported success, and the mutation "
            "stayed in the tree")

    def a_symlinked_target_is_not_cloned(root):
        # `target -> target.noindex` (the Spotlight-excluded layout atpkg lays
        # out; this box): the physical build tree is a root entry under its OWN
        # name. The walk skipped only the NAME `target`, so every sandbox
        # received a clonefile copy of the whole build tree -- measured
        # 2026-09-15 -- and the walk now skips the validated backing alias too,
        # without hiding a tracked or Cargo source at that path.
        (root / "Cargo.toml").write_text('[workspace]\nmembers = ["crates/a"]\n')
        (root / "crates/a").mkdir(parents=True)
        (root / "crates/a/Cargo.toml").write_text(
            '[package]\nname="a"\nversion="0.1.0"\n[lib]\npath="lib.rs"\n')
        (root / "crates/a/lib.rs").write_text("fn main() {}\n")
        physical = root / "target.noindex"
        (physical / "debug").mkdir(parents=True)
        (physical / "debug/libreal.rlib").write_text("the shared tree's unit\n")
        (root / "target").symlink_to("target.noindex")
        for build in (True, False):
            layout = "tree-build" if build else "tree"
            sand = root.parent / layout
            shutil.rmtree(sand, ignore_errors=True)
            _build_sandbox(root, sand, build=build, mutated=set())
            assert not (sand / "target.noindex").exists(), (
                f"{layout} layout: the physical build tree behind the `target` "
                f"symlink was cloned into the sandbox under its own name")
            link = sand / "target"
            assert link.is_symlink(), f"{layout} layout: no target symlink"
            assert not (link / "debug/libreal.rlib").exists(), (
                f"{layout} layout: the sandbox's target reaches the shared tree's units")
            shutil.rmtree(sand, ignore_errors=True)

    def a_sandbox_holds_no_build_output(root):
        # Measured 2026-09-28 (see the block above `SANDBOX_EXCLUDED_DIR_GLOBS`):
        # every sandbox cloned the build trees skipped by neither the name
        # `target` nor its alias -- `target-*.noindex`, nested `*/target`,
        # `.lake/build` -- and every nested checkout, EARLIER SANDBOXES among
        # them, so a kept sandbox inside the tree grew with each run. Both
        # halves: the copy omits them, and a copier that admits one is REFUSED
        # by the audit rather than handed to an arm.
        planted = ("target-quality.noindex/debug", "tools/x/target/debug",
                   "lean/.lake/build/lib", "evidence/sandboxes/tree/.git")
        for rel in planted:
            (root / rel).mkdir(parents=True)
            (root / rel / "unit").write_text("build output\n")
        sand = root.parent / "tree"
        shutil.rmtree(sand, ignore_errors=True)
        _build_sandbox(root, sand, build=False, mutated=set())
        for rel in ("target-quality.noindex", "tools/x/target", "lean/.lake/build",
                    "evidence/sandboxes/tree"):
            assert not (sand / rel).exists(), f"the sandbox holds {rel}"
        assert (sand / "scripts/check_alpha.py").is_file(), "the sandbox lost source"
        assert _sandbox_audit(root, sand) == [], "the audit flags a clean sandbox"
        shutil.rmtree(sand)
        real = globals()["_sandbox_exclusions"]
        globals()["_sandbox_exclusions"] = lambda *args: {}
        try:
            _build_sandbox(root, sand, build=False, mutated=set())
        except Red as exc:
            assert "target-quality.noindex" in str(exc), f"refused for the wrong reason: {exc}"
            assert not sand.exists(), "a refused sandbox was left on disk"
            return
        finally:
            globals()["_sandbox_exclusions"] = real
            shutil.rmtree(sand, ignore_errors=True)
        raise AssertionError("a copier that admits build output was not refused")

    run("60 _apply REFUSES the shared checkout", a_apply_refuses_shared)
    run("61 _apply refuses to write THROUGH a symlink", a_apply_refuses_symlink)
    run("62 a sandboxed mutation leaves the tree byte-identical", a_sandbox_isolates)
    run("63 CONTROL: an in-tree plant IS visible to the observer",
        a_in_tree_plant_is_visible)
    run("64 _fidelity catches a sandbox that has drifted", a_fidelity_catches_drift)
    run("65 the build layout symlinks members but never the mutated crate",
        a_build_layout_symlinks_members)
    run("66 a restore that CANNOT RUN is loud, not silent", a_restore_failure_is_loud)
    run("67 a payload-less mutation is a Red, not a KeyError", a_payload_missing)
    run("68 the sandbox's cargo target dir is its OWN, under target/, never the "
        "shared one, in both layouts and in the arm's environment",
        a_sandbox_owns_its_target)
    run("69 a cache minted for a sandbox at another path is dropped; one minted "
        "for this path is kept", a_moved_sandbox_drops_its_cache)
    run("70 a mismatched cache that cannot be dropped is REFUSED, never re-stamped",
        a_undroppable_cache_is_refused)
    run("71 the demonstrators' mutex is keyed on the checkout, like the caches, "
        "not on CLEAN_GATE_DEMO_ROOT", a_lock_is_keyed_on_the_checkout)
    run("72 the physical directory behind a `target` symlink is never cloned "
        "into the sandbox", a_symlinked_target_is_not_cloned)
    run("73 a sandbox never holds a build dir or a nested checkout, and a copier "
        "that admits one is refused", a_sandbox_holds_no_build_output)

    def a_arm_targo_is_canonical_not_path(root):
        # 2026-09-29: an arm's `targo` was the demonstrator's PATH's first one,
        # a rustup symlink targo refuses, so a baseline's colour depended on
        # the operator's PATH order. A decoy symlink sits FIRST on the
        # inherited PATH here; the arm's `targo` must be the canonical one.
        work = root / "targo-arm"
        (work / "decoy").mkdir(parents=True)
        (work / "decoy" / "real-decoy").write_text("#!/bin/sh\necho DECOY\nexit 99\n")
        (work / "decoy" / "real-decoy").chmod(0o755)
        (work / "decoy" / "targo").symlink_to(work / "decoy" / "real-decoy")
        canon = work / "sys root" / "bin" / "targo"   # a space, as Application Support has
        canon.parent.mkdir(parents=True)
        canon.write_text('#!/bin/sh\necho "CANONICAL $*"\n')
        canon.chmod(0o755)
        (work / "target").mkdir()
        cached = list(_TARGO_CACHE)
        saved_path = os.environ.get("PATH", "")
        _TARGO_CACHE[:] = [str(canon)]
        os.environ["PATH"] = f"{work / 'decoy'}{os.pathsep}/usr/bin:/bin"
        try:
            env = _sandbox_env(work)
        finally:
            _TARGO_CACHE[:] = cached
            os.environ["PATH"] = saved_path
        assert env.get("TARGO") == str(canon), f"TARGO is {env.get('TARGO')!r}"
        found = shutil.which("targo", path=env["PATH"])
        assert found and not Path(found).is_symlink(), (
            f"the arm's first `targo` is {found!r} -- a symlink, or none")
        r = subprocess.run("targo clean -p x", cwd=work, shell=True, env=env,
                           capture_output=True, text=True)
        assert r.returncode == 0 and r.stdout.strip() == "CANONICAL clean -p x", (
            f"an arm's `targo` ran {r.stdout.strip() or r.stderr.strip()!r} "
            f"(rc {r.returncode}), not the canonical one")

    run("74 an arm's `targo` is the canonical one, never the demonstrator's PATH's "
        "first (a rustup symlink targo refuses)", a_arm_targo_is_canonical_not_path)
    return arms, failures


def _selftest_sandbox_cache() -> tuple[int, int]:
    """Run the maintained filesystem regression suite without compiling Rust."""
    import runpy
    import unittest
    path = Path(__file__).resolve().parent / "tests/test_gate_registry_sandbox_cache.py"
    namespace = runpy.run_path(str(path), run_name="sandbox_cache_selftest")
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(namespace["SandboxCacheTests"])
    count = suite.countTestCases()
    result = unittest.TextTestRunner(stream=sys.stdout, verbosity=1).run(suite)
    failures = (len(result.failures) + len(result.errors) + len(result.skipped)
                + len(result.expectedFailures) + len(result.unexpectedSuccesses))
    if count == 0 or result.testsRun != count:
        failures += 1
    print(f"GATE_SANDBOX_CACHE_SELFTEST tests={count} failed={failures}")
    return count, failures


def selftest() -> int:
    """`--selftest`. Its arms re-pin and demonstrate MINI repositories whose
    commands are trivial scripts, so they run inside one notional reservation
    (HEAVY_GATE_HELD): routed through `_demo_argv` as production does, they would
    otherwise each take a REAL machine-wide reservation and queue behind every
    lane on a busy box. `_selftest_heavy_gated` clears the marker to test the
    gating itself against a stand-in gate."""
    global _REPLAY_DEBT_FIXTURE
    held = os.environ.get(HEAVY_GATE_HELD)
    os.environ[HEAVY_GATE_HELD] = "check_gate_registry-selftest"
    # The mini-repo's own debt (`_mini`), minted for these arms only.
    _REPLAY_DEBT_FIXTURE = frozenset({"check_alpha", "check_scan", "check_rs_scan"})
    try:
        return _selftest_body()
    finally:
        _REPLAY_DEBT_FIXTURE = frozenset()
        if held is None:
            os.environ.pop(HEAVY_GATE_HELD, None)
        else:
            os.environ[HEAVY_GATE_HELD] = held


def _valid_account(root: Path, subject: str) -> dict:
    """A well-formed, unexpired undemonstrated-pin account for `subject`'s live sha."""
    return {"reason": "self-test: nothing replays it here", "owner": "self-test",
            "first_issued": date.today().isoformat(),
            "expires": (date.today() + timedelta(days=30)).isoformat(),
            "pinned_sha256": _sha256(root, subject), "renewals": 0}


def _selftest_body() -> int:
    arms: list[tuple[str, str, object]] = [
        ("1  baseline green", "", None),
        ("2  R2 new gate-shaped file, no row", "R2 INVENTORY",
         lambda r: (r / "scripts/check_gamma.py").write_text("# new\n")),
        ("3  R2 row points at a deleted file", "R2 INVENTORY",
         lambda r: (r / "scripts/beta_gate.sh").unlink()),
        ("4  R3 gate with empty wired_by", "R3 WIRED",
         lambda r: _edit(r, "beta_gate", "wired_by", [])),
        ("5  R3 runner no longer invokes it", "R3 WIRED",
         lambda r: _sub(r, "scripts/local_gate.sh", "bash scripts/beta_gate.sh\n", "")),
        ("6  R3 an undeclared runner invokes it", "R3 WIRED",
         lambda r: _sub(r, "Justfile", "bash scripts/local_gate.sh\n",
                        "bash scripts/local_gate.sh\n    bash scripts/beta_gate.sh\n")),
        ("7  R4 soundness row, no demo, no waiver", "R4 DEMO",
         lambda r: _edit(r, "check_alpha", "demonstrated", None)),
        ("8  R4 expired waiver", "R4 DEMO",
         lambda r: (_edit(r, "check_alpha", "demonstrated", None),
                    _edit(r, "check_alpha", "waiver",
                          {"owner": "x", "expires": "2001-01-01", "reason": "old"}))),
        ("7d R12 a soundness gate with many refusals and one arm", "R12 ARM COVERAGE",
         lambda r: (_sub(r, "scripts/check_alpha.py", "print('a')",
                         "if x:\n    return 1\nif y:\n    return 1\nprint('a')"),
                    _edit(r, "check_alpha", "demonstrated",
                          {"kind": "mutation-record", "ref": "data/gate_demonstrations.json",
                           "date": "2026-08-24",
                           "script_sha256": _sha256(r, "scripts/check_alpha.py")}))),
        ("7e R12 a debt row whose recorded sites/arms are not the measured ones",
         "R12 ARM COVERAGE",
         lambda r: (_sub(r, "scripts/check_alpha.py", "print('a')",
                         "if x:\n    return 1\nif y:\n    return 1\nprint('a')"),
                    _edit(r, "check_alpha", "demonstrated",
                          {"kind": "mutation-record", "ref": "data/gate_demonstrations.json",
                           "date": "2026-08-24",
                           "script_sha256": _sha256(r, "scripts/check_alpha.py")}),
                    _demos_debt(r, "check_alpha", sites=2, arms=2))),
        ("7f R12 a debt row understating the REFUSAL COUNT it owes arms for",
         "R12 ARM COVERAGE",
         lambda r: (_sub(r, "scripts/check_alpha.py", "print('a')",
                         "if x:\n    return 1\nif y:\n    return 1\nprint('a')"),
                    _edit(r, "check_alpha", "demonstrated",
                          {"kind": "mutation-record", "ref": "data/gate_demonstrations.json",
                           "date": "2026-08-24",
                           "script_sha256": _sha256(r, "scripts/check_alpha.py")}),
                    _demos_debt(r, "check_alpha", sites=1, arms=0))),
        ("7j R12 refusals RESPELLED as a named constant still count",
         "R12 ARM COVERAGE",
         lambda r: (_sub(r, "scripts/check_alpha.py", "print('a')",
                         "EXIT_FAIL = 1\ndef a():\n    return EXIT_FAIL\n"
                         "def b():\n    return EXIT_FAIL\nprint('a')"),
                    _edit(r, "check_alpha", "demonstrated",
                          {"kind": "mutation-record", "ref": "data/gate_demonstrations.json",
                           "date": "2026-08-24",
                           "script_sha256": _sha256(r, "scripts/check_alpha.py")}))),
        ("7k R12 a raise of the gate's OWN exception type counts as a refusal",
         "R12 ARM COVERAGE",
         lambda r: (_sub(r, "scripts/check_alpha.py", "print('a')",
                         "class Red(Exception):\n    pass\ndef a():\n    raise Red('x')\n"
                         "def b():\n    raise Red('y')\nprint('a')"),
                    _edit(r, "check_alpha", "demonstrated",
                          {"kind": "mutation-record", "ref": "data/gate_demonstrations.json",
                           "date": "2026-08-24",
                           "script_sha256": _sha256(r, "scripts/check_alpha.py")}))),
        ("7g R7b an anchored row loses its record backing", "R7b REACH",
         lambda r: (r / "data/r7b_record_coverage.json").write_text(
             json.dumps({"count": 1, "rows": ["check_alpha"]}, indent=2))),
        ("7h R7b the reach anchor is missing", "R7b REACH",
         lambda r: (r / "data/r7b_record_coverage.json").unlink()),
        ("7i R7b the anchor's count disagrees with its own rows", "R7b REACH",
         lambda r: (r / "data/r7b_record_coverage.json").write_text(
             json.dumps({"count": 3, "rows": []}, indent=2))),
        ("7b R11 a row silently stops claiming soundness", "R11 CLAIMS",
         lambda r: _edit(r, "check_alpha", "claims", "quality")),
        ("7c R11 the soundness-claim anchor is missing", "R11 CLAIMS",
         lambda r: (r / "data/soundness_claims_ratchet.json").unlink()),
        # 8c/8d sit on beta_gate, a quality row nothing inherits, where an
        # account may stand, so the lapse checks are tested where they matter.
        ("8c R4b undemonstrated-pin account EXPIRED",
         "R4b UNDEMONSTRATED: beta_gate was re-pinned without a demonstration and that "
         "account EXPIRED",
         lambda r: _demo_set(r, "beta_gate", "repinned_without_demonstration",
                             {**_valid_account(r, "scripts/beta_gate.sh"),
                              "expires": "2001-01-01"})),
        ("8d R4b undemonstrated-pin excuse does not travel to a later sha",
         "R4b UNDEMONSTRATED: beta_gate carries an undemonstrated-pin account written for",
         lambda r: _demo_set(r, "beta_gate", "repinned_without_demonstration",
                             {**_valid_account(r, "scripts/beta_gate.sh"),
                              "pinned_sha256": "0" * 64})),
        # 2026-11-13 (review of d5619e490): an account never stands under a
        # soundness claim, its own or an inheriting row's, on a row with a
        # replay route. 8g and 8h are the controls: an account on a quality row
        # nothing inherits, and on a soundness row nothing can run or replay.
        ("8e R4b an account under the row's own soundness claim",
         "R4b UNDEMONSTRATED: check_alpha carries an undemonstrated-pin account under "
         "check_alpha's soundness claim",
         lambda r: _demo_set(r, "check_alpha", "repinned_without_demonstration",
                             _valid_account(r, "scripts/check_alpha.py"))),
        ("8f R4b an account under an inheriting soundness leg's claim",
         "R4b UNDEMONSTRATED: check_alpha carries an undemonstrated-pin account under "
         "alpha's soundness claim",
         lambda r: (_edit(r, "check_alpha", "claims", "quality"),
                    _demo_set(r, "check_alpha", "repinned_without_demonstration",
                              _valid_account(r, "scripts/check_alpha.py")))),
        ("8g a valid account on a quality row nothing inherits stays green", "",
         lambda r: _demo_set(r, "beta_gate", "repinned_without_demonstration",
                             _valid_account(r, "scripts/beta_gate.sh"))),
        ("8h a valid account on a soundness row nothing can run or replay stays green", "",
         lambda r: (_demo_set(r, "check_rs_scan", "repinned_without_demonstration",
                              _valid_account(r, "crates/x/tests/scan_battery.rs")),
                    # ... an account is the row's record, so it leaves the debt (R7c)
                    _discharge_replay_debt(r, "check_rs_scan"))),
        # R7c (2026-11-13): the hand edit d5619e490's review found -- a pin moved
        # with its replay record deleted -- reads as an unrecorded pin, so the
        # unrecorded pins are named and nothing else may lack a record.
        ("8i R7c a recorded row's pin moved by hand with its replay record deleted",
         "R7c REPLAY RECORD: check_alpha has a soundness claim on a pin",
         lambda r: (_hand_moved_alpha(r), _demo_drop(r, "check_alpha", "replayed"))),
        ("8j R7c a debt entry for a row that now has its replay record",
         "R7c REPLAY RECORD: check_alpha is listed",
         lambda r: _demo_set(r, "check_alpha", "replayed", _replay_record(
             _reg(r)["rows"][0]["demonstrated"], "self-test fixture"))),
        ("8k R7c the debt anchor is missing", "R7c REPLAY RECORD: data/replay_record_debt.json is missing",
         lambda r: (r / REPLAY_DEBT_REL).unlink()),
        ("8l R7c the anchor's count disagrees with its rows", "R7c REPLAY RECORD: data/replay_record_debt.json says count",
         lambda r: (r / REPLAY_DEBT_REL).write_text(
             json.dumps({"count": 3, "rows": ["check_alpha", "check_scan"]}, indent=2))),
        ("8m R7c a recorded row discharged from the debt is green", "",
         lambda r: (_demo_set(r, "check_alpha", "replayed", _replay_record(
                        _reg(r)["rows"][0]["demonstrated"], "self-test fixture")),
                    _discharge_replay_debt(r, "check_alpha"))),
        # Review of R7c (2026-11-14): each way a hand edit stepped around it.
        ("8n R7c a hand-moved pin whose record is set to null, not deleted",
         "R7c REPLAY RECORD: check_alpha has a soundness claim on a pin",
         lambda r: (_hand_moved_alpha(r), _demo_set(r, "check_alpha", "replayed", None))),
        ("8n2 R7 ... and R7 reads a null record as a disagreement, not as none",
         "R7 FRESH: check_alpha carries a null `replayed` record",
         lambda r: (_hand_moved_alpha(r), _demo_set(r, "check_alpha", "replayed", None))),
        ("8o R7c a hand-moved pin that also names itself under inherited_from",
         "R7c REPLAY RECORD: check_alpha has a soundness claim on a pin",
         lambda r: (_hand_moved_alpha(r), _demo_drop(r, "check_alpha", "replayed"),
                    _demo_set(r, "check_alpha", "inherited_from", "check_alpha"))),
        ("8p R7c a hand-moved pin whose ref is reworded so nothing can run it",
         "R7c REPLAY RECORD: check_alpha has a soundness claim on a pin",
         lambda r: (_hand_moved_alpha(r), _demo_drop(r, "check_alpha", "replayed"),
                    _demo_set(r, "check_alpha", "ref", "./scripts/check_alpha.py --selftest"))),
        ("8q R7c a soundness pin with no replay route still owes a record",
         "R7c REPLAY RECORD: check_rs_scan has a soundness claim on a pin",
         lambda r: _discharge_replay_debt(r, "check_rs_scan")),
        ("8r R7c a pin only an inheriting leg's soundness claim stands on",
         "R7c REPLAY RECORD: check_alpha has a soundness claim on a pin",
         lambda r: (_edit(r, "check_alpha", "claims", "quality"),
                    _drop_soundness_anchor(r, "check_alpha"),
                    _discharge_replay_debt(r, "check_alpha"))),
        ("8s R7c ... and with the inheriting leg demoted too it owes nothing", "",
         lambda r: (_edit(r, "check_alpha", "claims", "quality"),
                    _drop_soundness_anchor(r, "check_alpha"),
                    _edit(r, "alpha", "claims", "quality"),
                    _drop_soundness_anchor(r, "alpha"),
                    _discharge_replay_debt(r, "check_alpha"))),
        ("8t R7c a row added to the debt anchor outside the minted debt",
         "R7c REPLAY RECORD: beta_gate is listed in data/replay_record_debt.json but was not "
         "in the debt minted",
         lambda r: (_edit(r, "beta_gate", "claims", "soundness"),
                    (r / REPLAY_DEBT_REL).write_text(json.dumps({"count": 4, "rows": [
                        "check_alpha", "check_scan", "check_rs_scan", "beta_gate"]})))),
        ("8u R7c the debt anchor is not valid JSON",
         "R7c REPLAY RECORD: data/replay_record_debt.json is not valid JSON",
         lambda r: (r / REPLAY_DEBT_REL).write_text("<<<<<<< HEAD\n{}\n")),
        ("8v R7c the debt anchor is not an object",
         "R7c REPLAY RECORD: data/replay_record_debt.json must be a JSON object",
         lambda r: (r / REPLAY_DEBT_REL).write_text("[]\n")),
        ("8w R7c the debt anchor carries no list of row ids",
         "R7c REPLAY RECORD: data/replay_record_debt.json must carry a list",
         lambda r: (r / REPLAY_DEBT_REL).write_text(json.dumps({"count": 0, "rows": {}}))),
        ("8b R4 waiver beyond the 180-day horizon", "R4 DEMO",
         lambda r: (_edit(r, "check_alpha", "demonstrated", None),
                    _edit(r, "check_alpha", "waiver",
                          {"owner": "x", "expires": "2999-12-31", "reason": "forever"}))),
        ("9  R4 waiver AND demonstration", "R4 DEMO",
         lambda r: _edit(r, "check_alpha", "waiver",
                         {"owner": "x", "expires": (date.today() + timedelta(days=90)).isoformat(), "reason": "belt and braces"})),
        ("10 R5 inline self-test the script lacks", "R5 EVIDENCE",
         lambda r: _sub(r, "scripts/check_alpha.py", "# --selftest\n", "")),
        ("11 R5 self-test file that does not exist", "R5 EVIDENCE",
         lambda r: (r / "scripts/test_beta_gate.sh").unlink()),
        ("12 R7 script gutted, badge kept", "R7 FRESH",
         lambda r: _sub(r, "scripts/check_alpha.py", "print('a')", "pass")),
        ("12b R7b pin moved past its cited evidence record", "R7b RECORD",
         lambda r: (_edit(r, "beta_gate", "demonstrated",
                          {**{"kind": "selftest-file", "ref": "scripts/test_beta_gate.sh",
                              "date": "2026-08-24",
                              "note": "demonstrated by reports/mutation-proof-beta.json"},
                            "script_sha256": _sha256(r, "scripts/beta_gate.sh")}),
                    _sub(r, "reports/mutation-proof-beta.json",
                         _sha256(r, "scripts/beta_gate.sh"), "0" * 64))),
        ("12c R7b ... still read on a self-pinned row that also names inherited_from",
         "R7b RECORD",
         lambda r: (_edit(r, "beta_gate", "demonstrated",
                          {**{"kind": "selftest-file", "ref": "scripts/test_beta_gate.sh",
                              "date": "2026-08-24", "inherited_from": "check_alpha",
                              "note": "demonstrated by reports/mutation-proof-beta.json"},
                            "script_sha256": _sha256(r, "scripts/beta_gate.sh")}),
                    _sub(r, "reports/mutation-proof-beta.json",
                         _sha256(r, "scripts/beta_gate.sh"), "0" * 64))),
        ("12d R7 a self-pinned row whose inherited_from names the row itself",
         "R7 FRESH: beta_gate pins its own subject and names inherited_from 'beta_gate'",
         lambda r: _demo_set(r, "beta_gate", "inherited_from", "beta_gate")),
        ("12e R7 a self-pinned row whose inherited_from names no row",
         "R7 FRESH: beta_gate pins its own subject and names inherited_from 'no_such_row'",
         lambda r: _demo_set(r, "beta_gate", "inherited_from", "no_such_row")),
        ("13 R6 a leg with no registry row", "R6 IDS",
         lambda r: _sub(r, "scripts/local_gate.sh", "# GATE-LEG: alpha\n",
                        "# GATE-LEG: alpha\n# GATE-LEG: delta\n")),
        ("14 R6 a registry leg local_gate dropped", "R6 IDS",
         lambda r: _sub(r, "scripts/local_gate.sh", "# GATE-LEG: alpha\n", "")),
        ("15 R1 malformed row", "R1 SHAPE",
         lambda r: _drop(r, "beta_gate", "claims")),
        ("16 R1 tool with no reason", "R1 SHAPE",
         lambda r: _edit(r, "beta_gate", "kind", "tool")),
        ("17 R8 retired file still in the tree", "R8 RETIRED",
         lambda r: (r / "scripts/old_gate.sh").write_text("# back from the dead\n")),
        ("18 R8 successor has no registry row", "R8 RETIRED",
         lambda r: _ret(r, "old_gate", "superseded_by", ["no_such_gate"])),
        ("19 R8 superseded by an UNWIRED gate", "R8 RETIRED",
         lambda r: (_edit(r, "beta_gate", "wired_by", []),
                    _edit(r, "beta_gate", "waiver",
                          {"owner": "x", "expires": (date.today() + timedelta(days=90)).isoformat(), "reason": "orphan"}),
                    _edit(r, "beta_gate", "demonstrated", None),
                    _sub(r, "scripts/local_gate.sh", "bash scripts/beta_gate.sh\n", ""))),
        ("20 R8 supersedes nothing, does not say so", "R8 RETIRED",
         lambda r: _ret(r, "old_gate", "superseded_by", [])),
        ("21 R8 retired AND live at once", "R8 RETIRED",
         lambda r: _ret(r, "old_gate", "id", "beta_gate")),
        # ── R9 SCANNER: the anti-correlation rule ─────────────────────────
        ("22 R9 source-reading gate with no declaration", "R9 SCANNER",
         lambda r: _drop(r, "check_scan", "source_scan")),
        ("23 R9 declares lexed, does not lex", "R9 SCANNER",
         lambda r: _sub(r, "scripts/check_scan.py",
                        "hits = strip_noncode(p.read_text())", "hits = p.read_text()")),
        ("24 R9 raw-lines CANNOT claim soundness", "R9 SCANNER",
         lambda r: (_sub(r, "scripts/check_scan.py",
                         "hits = strip_noncode(p.read_text())", "hits = p.read_text()"),
                    _edit(r, "check_scan", "source_scan",
                          {"kind": "raw-lines", "note": "counts every mention"}))),
        ("25 R9 raw-lines IS allowed for a non-soundness row", "",
         lambda r: (_sub(r, "scripts/check_scan.py",
                         "hits = strip_noncode(p.read_text())", "hits = p.read_text()"),
                    _edit(r, "check_scan", "claims", "quality"),
                    # a demotion is only honest if the anchor moves WITH it
                    # (audit r11 M11-8 / R11 CLAIMS)
                    _drop_soundness_anchor(r, "check_scan"),
                    # ... and the replay-record debt it no longer owes (R7c)
                    _discharge_replay_debt(r, "check_scan"),
                    _edit(r, "check_scan", "source_scan",
                          {"kind": "raw-lines", "note": "counts every mention"}),
                    _resha(r, "check_scan"))),
        # 2026-11-01: a gate that lexes THROUGH an input it derives (R9's
        # `_lexes_through`): green when that input strips in code, red when it
        # names a stripper only in a comment.
        ("25b R9 lexed through a derived input that lexes is green", "",
         lambda r: _scan_through(r, "    return strip_noncode(text)\n")),
        ("25c R9 lexed through a derived input that names a stripper only in a comment",
         "R9 SCANNER: check_scan declares", lambda r: _scan_through(r, "    return text  # strip_noncode\n")),
        # 2026-11-01 review: the derived input must be one the gate's code names, and must USE the
        # stripper -- the reference lexer pinned beside a walker that never calls it is no lexing.
        ("25d R9 a derived lexer the gate never names does not lex for its walker",
         "R9 SCANNER: check_scan declares", lambda r: _scan_through(
             r, "    return text\n", lexer="def strip_noncode(text):\n    return text\n\n\nCODE = strip_noncode('')\n")),
        ("25e R9 a walker that defines a stripper and never uses it does not lex",
         "R9 SCANNER: check_scan declares",
         lambda r: _scan_through(r, "    return text\n\n\ndef strip_noncode(text):\n    return text\n")),
        ("26 R9 a declaration left behind by a scanner that is gone", "R9 SCANNER",
         lambda r: _sub(r, "scripts/check_scan.py",
                        "for p in root.rglob('*.rs'):", "for p in ():")),
        ("27 R1 source_scan with no note", "R1 SHAPE",
         lambda r: _edit(r, "check_scan", "source_scan", {"kind": "lexed"})),
        ("28 R1 source_scan.kind not in the enum", "R1 SHAPE",
         lambda r: _edit(r, "check_scan", "source_scan",
                         {"kind": "grep", "note": "n/a"})),
        # ── R2, the PACKAGE form: what hid scripts/masquerade_gate/ ────────
        ("29 R2 a gate-shaped PACKAGE with no row", "R2 INVENTORY",
         lambda r: (_mkpkg(r, "scripts/delta_gate"))),
        ("30 R2 a library package is NOT a gate (no __main__.py)", "",
         lambda r: (_mkpkg(r, "scripts/epsilon_audit", main=False))),
        ("31 R2 a package whose NAME is not gate-shaped is not a gate", "",
         lambda r: (_mkpkg(r, "scripts/helpers"))),
        # ── R9 over RUST rows (lane LOOSE, 2026-08-25) ────────────────────
        #
        # 32 pins the widened READS_SOURCE: a Rust battery that walks the tree
        # with its OWN recursor (no rglob, no collect_rust_source_files, no
        # shell grep) was INVISIBLE to R9 -- it could have declared nothing.
        # 33 pins the other half: `script_code_only` now blanks Rust comments
        # and literals before the detectors run, so a stripper NAMED in a doc
        # comment can no longer certify a row `lexed`. A rule against reading
        # prose as code may not read prose as code, and that applies to the
        # Rust rows too.
        ("32 R9 a RUST battery with its own walker and no declaration",
         "R9 SCANNER", lambda r: _drop(r, "check_rs_scan", "source_scan")),
        ("33 R9 a RUST row whose only stripper is in a COMMENT", "R9 SCANNER",
         lambda r: _sub(r, "crates/x/tests/scan_battery.rs",
                        "fn scan(src: &str) -> usize { blank_noncode(src)",
                        "// blank_noncode is the RIGHT way\nfn scan(src: &str) -> usize { (src)")),
        # ── R9 over `implemented_by` (audit r17, 2026-09-14) ──────────────
        #
        # R9 resolved a row's subject as `path` alone while every other rule
        # read `path OR implemented_by`, so all 57 leg/suite-rows -- 22 of which
        # satisfy its own READS_SOURCE detector -- were SKIPPED: no declaration
        # demanded, and the raw-lines-for-a-soundness-row refusal never reached.
        # Exactly the defect found and fixed for R7 on 2026-08-30 and never
        # carried across. 50 pins the DEMAND reaching a leg at all. 51 carries
        # both remaining halves in one arm, which is why there is no third: its
        # message is the raw-lines refusal and NOT "declares no source_scan", so
        # the leg must have inherited its gate sibling's declaration to be judged
        # at all -- and it is judged at the LEG's claims, not the sibling's, so a
        # `raw-lines` scanner that is legal for a `quality` gate is refused for
        # the `soundness` leg standing on it.
        ("50 R9 a LEG whose implementation reads source and declares nothing",
         "R9 SCANNER: alpha ",
         lambda r: (_sub(r, "scripts/check_alpha.py", "print('a')",
                         "import pathlib\nlist(pathlib.Path('.').rglob('*.rs'))"),
                    _drop(r, "check_alpha", "source_scan"),
                    _row(r, "check_alpha", "claims", "quality"))),
        ("51 R9 an inherited raw-lines declaration is still refused for a SOUNDNESS leg",
         "R9 SCANNER: alpha ",
         lambda r: (_sub(r, "scripts/check_alpha.py", "print('a')",
                         "import pathlib\nlist(pathlib.Path('.').rglob('*.rs'))"),
                    _row(r, "check_alpha", "claims", "quality"),
                    _row(r, "check_alpha", "source_scan",
                         {"kind": "raw-lines", "note": "selftest: legal for a quality gate"}))),
        # ── R7 over `implemented_by` (2026-08-30) ─────────────────────────
        #
        # Every one of these expects a message that NAMES THE LEG
        # ("R7 FRESH: alpha "), never the bare rule tag. Arm 46 gutting
        # scripts/check_alpha.py also reds `check_alpha`, whose own path pin has
        # caught that since the rule was written; matching on the prefix is what
        # makes the arm prove the LEG is watched rather than re-proving the
        # gate. All six pass green on the old checker, which is the point:
        # `path` was falsy for these rows and R7 skipped them entirely.
        ("44 R7 a leg with neither a pin nor an inheritance", "R7 FRESH: alpha ",
         lambda r: _demo_drop(r, "alpha", "inherited_from")),
        ("45 R7 a leg delegating to a row that pins a DIFFERENT file",
         "R7 FRESH: alpha ",
         lambda r: _demo_set(r, "alpha", "inherited_from", "beta_gate")),
        ("46 R7 a leg's IMPLEMENTATION gutted under a self-pin",
         "R7 FRESH: alpha ",
         lambda r: (_demo_drop(r, "alpha", "inherited_from"), _resha(r, "alpha"),
                    _sub(r, "scripts/check_alpha.py", "print('a')", "pass"))),
        ("47 R7 an EMPTY script_sha256 is not a pin", "R7 FRESH: alpha ",
         lambda r: (_demo_drop(r, "alpha", "inherited_from"),
                    _demo_set(r, "alpha", "script_sha256", ""))),
        ("48 R7 a leg delegating to a row that does not exist", "R7 FRESH: alpha ",
         lambda r: _demo_set(r, "alpha", "inherited_from", "no_such_row")),
        ("49 R7 a leg SELF-PINNED to its implementation is green", "",
         lambda r: (_demo_drop(r, "alpha", "inherited_from"), _resha(r, "alpha"),
                    # pinned as --repin would: with the record of its run (R7c)
                    _demo_set(r, "alpha", "replayed", _replay_record(
                        next(x for x in _reg(r)["rows"] if x["id"] == "alpha")["demonstrated"],
                        "self-test fixture")))),
        # ── R7 over a DERIVED input set (verifier r8b, 2026-09-25) ────────
        #
        # `check_alpha` becomes a gate that RUNS a file besides itself and
        # derives it (`--pinned-inputs`). Each red arm names the gate row, and
        # each re-pins the script sha where it edits the script, so what reds
        # it is the input rule and not the script pin.
        ("50 R7 a subject that derives its inputs, and a row pinning them, is green", "",
         lambda r: _derive_alpha(r)),
        ("51 R7 the subject derives its inputs and the row pins only the script",
         "R7 FRESH: check_alpha ", lambda r: _derive_alpha(r, pin_inputs=False)),
        ("52 R7 a derived input edited under the pin (the r8b shape: the projector "
         "changed, the script did not)", "R7 FRESH: check_alpha ",
         lambda r: (_derive_alpha(r), (r / "data/alpha_input.txt").write_text("edited\n"))),
        ("53 R7 the derived set grows by a file nobody pinned", "R7 FRESH: check_alpha ",
         lambda r: (_derive_alpha(r), (r / "data/alpha_input2.txt").write_text("x\n"),
                    _sub(r, "scripts/check_alpha.py", "print('data/alpha_input.txt')",
                         "print('data/alpha_input.txt'); print('data/alpha_input2.txt')"),
                    _resha(r, "check_alpha"))),
        ("54 R7 inputs pinned while the subject stopped declaring them",
         "R7 FRESH: check_alpha ",
         lambda r: (_derive_alpha(r),
                    _sub(r, "scripts/check_alpha.py", "ANSWERS_PINNED_INPUTS = True\n", ""),
                    _resha(r, "check_alpha"))),
        ("55 R7 a derivation that fails is not a pin", "R7 FRESH: check_alpha ",
         lambda r: (_derive_alpha(r),
                    _sub(r, "scripts/check_alpha.py", "sys.exit(0)", "sys.exit(3)"),
                    _resha(r, "check_alpha"))),
        # verifier r9 recheck (2026-09-25): a derived input that is a directory
        # symlink hashed as "" when pinned and "" ever after, whatever changed
        # behind it -- GATE_REGISTRY=ok over an edited module.
        ("55b R7 a derived input reached through a directory symlink is not a pin",
         "R7 FRESH: check_alpha ", lambda r: _symlinked_alpha_input(r)),
        # lane r10: a pin is tied to the replay that moved it.
        ("55c R7 a derived input set pinned with no replay recorded",
         "R7 FRESH: check_alpha pins a derived input set that no recorded replay",
         lambda r: (_derive_alpha(r), _demo_drop(r, "check_alpha", "replayed"))),
        ("55d R7 a script pin hand-moved past its replay record (the script edited, the sha "
         "re-typed)", "R7 FRESH: check_alpha's pin is not the one its last recorded replay",
         lambda r: (_derive_alpha(r),
                    _sub(r, "scripts/check_alpha.py", "print('a')", "print('b')"),
                    _resha(r, "check_alpha"))),
        ("55e R7 an input pin hand-moved past its replay record (a merge that took one "
         "side's inputs)", "R7 FRESH: check_alpha's pin is not the one its last recorded replay",
         lambda r: (_derive_alpha(r), (r / "data/alpha_input.txt").write_text("edited\n"),
                    _demo_set(r, "check_alpha", "inputs", _derived_inputs(
                        r, "scripts/check_alpha.py")[0]))),
    ]
    failures = 0
    # These arms exercise the WORKING-TREE rules on a synthetic directory that
    # is not a git repository. Run under the pre-push hook they would inherit
    # its exported CLEAN_PUSH_RANGES and be judged against a commit that has
    # nothing to do with them -- which is exactly what happened on this rule's
    # first hook run and reddened all four green controls. R10 gets its own
    # arms, with their own ranges, below.
    inherited = os.environ.pop("CLEAN_PUSH_RANGES", None)
    for name, expect, mutate in arms:
        with tempfile.TemporaryDirectory() as td:
            root = _mini(Path(td))
            if mutate is not None:
                mutate(root)
            try:
                problems = check(root)
            except Red as exc:
                problems = [str(exc)]
            hit = [p for p in problems if p.startswith(expect)] if expect else []
            if not expect:
                if problems:
                    print(f"  [FAIL] {name}: expected a clean tree, got:")
                    for p in problems:
                        print(f"           {p}")
                    failures += 1
                else:
                    print(f"  [ok]   {name}")
                continue
            if hit:
                print(f"  [ok]   {name} -> {hit[0][:96]}")
            else:
                print(f"  [FAIL] {name}: expected {expect}, got {problems or ['(green)']}")
                failures += 1
    if inherited is not None:
        os.environ["CLEAN_PUSH_RANGES"] = inherited
    git_arms, git_failures = _selftest_pushed()
    wire_arms, wire_failures = _selftest_wiring()
    mut_arms, mut_failures = _selftest_mutations()
    rep_arms, rep_failures = _selftest_repin()
    cnt_arms, cnt_failures = _selftest_recorded_arms()
    hg_arms, hg_failures = _selftest_heavy_gated()
    total = len(arms) + git_arms + wire_arms + mut_arms + rep_arms + cnt_arms + hg_arms
    failures += (git_failures + wire_failures + mut_failures + rep_failures + cnt_failures
                 + hg_failures)
    print(f"GATE_REGISTRY_LEGACY_SELFTEST arms={total} failed={failures}")
    cache_tests, cache_failures = _selftest_sandbox_cache()
    total += cache_tests
    failures += cache_failures
    print(f"GATE_REGISTRY_SELFTEST arms={total} failed={failures}")
    return 1 if failures else 0


def _selftest_recorded_arms() -> tuple[int, int]:
    """A row's arm count is RENDERED from data/gate_demonstrations.json
    (NOTES STATE NO ARM COUNTS): its own arms, its parent's for a delegated
    row, and none for a demonstration that is not a mutation record there.
    Verifier r7b (2026-09-24) found parity-tiers-check's note saying "two
    replayed arms" beside three recorded, with GATE_REGISTRY=ok."""
    arms = {"parity_tiers": [{}, {}, {}]}
    rows = [
        ({"id": "parity_tiers", "demonstrated": {
            "kind": "mutation-record", "ref": "data/gate_demonstrations.json",
            "note": "Inherits nothing; says two"}}, 3),
        ({"id": "parity-tiers-check", "demonstrated": {
            "kind": "mutation-record", "ref": "data/gate_demonstrations.json",
            "inherited_from": "parity_tiers"}}, 3),
        ({"id": "x", "demonstrated": {"kind": "selftest-inline", "ref": "x --selftest"}}, None),
        ({"id": "y", "demonstrated": {"kind": "mutation-record", "ref": "reports/y.json"}}, None),
    ]
    failures = 0
    for row, want in rows:
        got = recorded_arms(row, arms)
        ok = got == want
        failures += not ok
        print(f"  [{'ok' if ok else 'FAIL'}]   recorded arms of {row['id']}: {got} (want {want})")
    return len(rows), failures


_DEMO_EXECUTORS = ("_demonstrate_arms", "repin", "_run_demo_command")
_DEMO_PAYLOADS = {"command", "ref"}
_SUBPROCESS_RUNNERS = {"run", "Popen", "call", "check_call", "check_output"}


def _ungated_demo_calls(source: str) -> list[str]:
    """`subprocess` calls in the demonstration executors that run an arm's
    `command` or a row's `ref` NOT through `_demo_argv`. A parse, never a grep:
    a comment or a string naming the call is not the call."""
    found: list[str] = []
    for fn in ast.walk(ast.parse(source)):
        if not (isinstance(fn, ast.FunctionDef) and fn.name in _DEMO_EXECUTORS):
            continue
        for call in ast.walk(fn):
            if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Attribute)
                    and isinstance(call.func.value, ast.Name)
                    and call.func.value.id == "subprocess"
                    and call.func.attr in _SUBPROCESS_RUNNERS):
                continue
            first = call.args[0] if call.args else next(
                (k.value for k in call.keywords if k.arg == "args"), None)
            if first is None:
                continue
            if (isinstance(first, ast.Call) and isinstance(first.func, ast.Name)
                    and first.func.id == "_demo_argv"):
                continue
            if any(isinstance(n, ast.Name) and n.id in _DEMO_PAYLOADS for n in ast.walk(first)):
                found.append(f"{fn.name}:{call.lineno}")
    return found


def _selftest_heavy_gated() -> tuple[int, int]:
    """Every demonstration command runs under heavy_gate (2026-10-01). Each arm
    here is RED on a runner that executes an arm's `command` or a row's `ref`
    directly: (1) a `--repin` whose ref exits 0 only when a gate launched it;
    (2) an arm's shell command through `_run_demo_command`; (3) a parse of this
    file for any executor that bypasses `_demo_argv`. Plus the contract: the
    row's own class, the fallback by layout, an enclosing reservation honoured
    rather than nested, and the shared tree's gate by default."""
    failures = arms = 0

    def check(name: str, ok: bool, detail: str = "") -> None:
        nonlocal failures, arms
        arms += 1
        failures += not ok
        print(f"  [{'ok' if ok else 'FAIL'}] heavy-gated: {name}"
              + ("" if ok else f" -- {detail}"))

    keys = (HEAVY_GATE_OVERRIDE, HEAVY_GATE_HELD, "FAKE_GATE_LOG")
    saved = {k: os.environ.get(k) for k in keys}
    try:
        os.environ.pop(HEAVY_GATE_HELD, None)
        with tempfile.TemporaryDirectory() as td:
            tdp = Path(td)
            log = tdp / "gate.log"
            fake = tdp / "fake_gate.sh"
            # A stand-in gate: records how it was called, then runs the command
            # after `--` with a marker only a gated command can see.
            fake.write_text(
                "#!/bin/bash\n"
                "printf '%s\\n' \"$*\" >> \"$FAKE_GATE_LOG\"\n"
                "while [ $# -gt 0 ] && [ \"$1\" != \"--\" ]; do shift; done\n"
                "shift\n"
                "GATED_BY_FAKE=1 exec \"$@\"\n")
            os.chmod(fake, 0o755)
            os.environ[HEAVY_GATE_OVERRIDE] = str(fake)
            os.environ["FAKE_GATE_LOG"] = str(log)

            root = _mini(tdp)
            script = root / "scripts/check_alpha.py"
            script.write_text("#!/usr/bin/env python3\n# --selftest\nimport os, sys\n"
                              "sys.exit(0 if os.environ.get('GATED_BY_FAKE') == '1' else 1)\n")
            os.chmod(script, 0o755)
            reg = root / "data/gate_registry.json"
            doc = json.loads(reg.read_text())
            for row in doc["rows"]:
                if row["id"] == "check_alpha":
                    row["demonstrated"]["ref"] = "scripts/check_alpha.py --selftest"
            reg.write_text(json.dumps(doc, indent=2) + "\n")
            with contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                rc = repin(root, "check_alpha")
            logged = log.read_text() if log.exists() else ""
            check("--repin runs a row's ref under heavy_gate (an ungated ref exits 1)",
                  rc == 0 and "-- scripts/check_alpha.py --selftest" in logged,
                  f"repin rc={rc}, gate log={logged!r}")
            check("... in the row's own class, at the non-build fallback",
                  f"run auto:gate-demo-check_alpha:{DEMO_FALLBACK_GB} gate-demo-check_alpha --"
                  in logged, repr(logged))

            log.write_text("")
            res = _run_demo_command(
                "test \"$GATED_BY_FAKE\" = 1 && echo armran", "x::y z", True, tdp,
                dict(os.environ))
            logged = log.read_text()
            check("an arm's command runs under heavy_gate (an ungated one prints nothing)",
                  res.returncode == 0 and "armran" in res.stdout, f"rc={res.returncode}")
            check("... a compiling arm at the build fallback, in a sanitised class",
                  f"run auto:gate-demo-x-y-z:{DEMO_FALLBACK_GB_BUILD} gate-demo-x-y-z -- /bin/sh -c"
                  in logged, repr(logged))
            spaced = tdp / "interp dir" / "python3"
            spaced.parent.mkdir()
            spaced.write_text('#!/bin/sh\necho "interp-ran $*"\n')
            os.chmod(spaced, 0o755)
            res = _run_demo_command(_arm_command("python3 scripts/x.py --check", str(spaced)),
                                    "x", False, tdp, dict(os.environ))
            check("an arm's interpreter path holding a space runs as one word",
                  res.returncode == 0 and "interp-ran scripts/x.py --check" in res.stdout,
                  f"rc={res.returncode} out={res.stdout[-120:]!r} err={res.stderr[-120:]!r}")
            held = _demo_argv(["true"], "x", True, {HEAVY_GATE_HELD: "16:outer"})
            check("an enclosing reservation is honoured, never nested", held == ["true"],
                  repr(held))
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
    check("the default gate is the shared tree's scripts/heavy_gate.sh",
          HEAVY_GATE_SCRIPT.is_file(), str(HEAVY_GATE_SCRIPT))
    bypass = _ungated_demo_calls(Path(__file__).read_text())
    check("no executor runs an arm's command or a row's ref outside _demo_argv (a parse)",
          not bypass, ", ".join(bypass))
    old_shape = ("def _demonstrate_arms(command):\n"
                 "    subprocess.run(command, shell=True)\n")
    check("... and that parse sees the old direct call",
          _ungated_demo_calls(old_shape) == ["_demonstrate_arms:2"],
          repr(_ungated_demo_calls(old_shape)))
    return arms, failures


# -- R10 arms ----------------------------------------------------------------
#
# These three need a real repository, because R10's whole point is that it reads
# a COMMIT rather than a directory. `git init` in a temp dir is ~40 ms, so all
# three together stay inside the leg's budget.
#
# Arm 34 is the one that matters and it is written to fail on the OLD checker:
# the working tree is left GREEN and only the pushed commit is stale, which is
# precisely the shape that let 7c0801a9e through. Arm 36 is the green control --
# without it, a checker that simply always said R10 would score two out of three.


def _git_run(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=str(root), check=True,
                   capture_output=True, env={**os.environ,
                                             "GIT_AUTHOR_NAME": "selftest",
                                             "GIT_AUTHOR_EMAIL": "selftest@example.invalid",
                                             "GIT_COMMITTER_NAME": "selftest",
                                             "GIT_COMMITTER_EMAIL": "selftest@example.invalid"})


def _hand_moved_alpha(root: Path) -> None:
    """check_alpha as --repin leaves it (a replay record, out of the debt), then
    its script edited and its pin re-hashed BY HAND: the starting point of every
    R7c hand-edit arm, which then disguises the stale record its own way."""
    _demo_set(root, "check_alpha", "replayed", _replay_record(
        _reg(root)["rows"][0]["demonstrated"], "self-test fixture"))
    _discharge_replay_debt(root, "check_alpha")
    _sub(root, "scripts/check_alpha.py", "print('a')", "print('moved')")
    _resha(root, "check_alpha")


def _drop_soundness_anchor(root: Path, rid: str) -> None:
    """Remove a row from the mini repo's soundness-claim anchor.

    A real demotion edits data/soundness_claims_ratchet.json in the same change
    (R11 CLAIMS); an arm that demotes without it is testing an incomplete act.
    """
    p = root / "data/soundness_claims_ratchet.json"
    d = json.loads(p.read_text())
    d["soundness_rows"] = [r for r in d["soundness_rows"] if r != rid]
    p.write_text(json.dumps(d) + "\n")


def _minigit(tmp: Path) -> tuple[Path, str]:
    """A mini repo with one commit, plus a SECOND commit that edits a pinned
    script without repinning. The working tree is left on the good commit."""
    root = _mini(tmp)
    _git_run(root, "init", "-q", "-b", "main")
    _git_run(root, "add", "-A")
    _git_run(root, "commit", "-qm", "green")
    _sub(root, "scripts/check_alpha.py", "print('a')", "print('a')  # a real, legitimate edit")
    _git_run(root, "add", "-A")
    _git_run(root, "commit", "-qm", "edit the script, forget the repin")
    stale = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(root),
                           capture_output=True, text=True, check=True).stdout.strip()
    # Put the working tree BACK on the consistent commit: the pusher's tree is
    # green, only the object being shipped is not.
    _git_run(root, "checkout", "-q", "HEAD~1")
    return root, stale


def _selftest_repin() -> tuple[int, int]:
    """Arms for the repin GUARD itself (audit r4 minor 9, wf_4769693f): the
    guard that runs a selftest-inline row's demonstration before moving its
    pin had never itself been demonstrated -- in the file whose philosophy is
    that a refusal nobody has seen fire is exit 0. Covers a failing
    demonstration REFUSES and the pin does not move; a passing one moves it;
    the interpreter-prefixed ref shape is guarded too (audit r4 minor 2: the
    bare startswith test silently bypassed 7 runnable `python3 scripts/...`
    refs); a non-executable direct ref is a refusal, not a traceback; and
    failure diagnostics survive without moving the registry.
    """
    failures = arms = 0

    def run(name, body, ref, mode, expect_ok, expect_moved, expected_output=()):
        nonlocal failures, arms
        arms += 1
        with tempfile.TemporaryDirectory() as td:
            root = _mini(Path(td))
            script = root / "scripts/check_alpha.py"
            script.write_text(body)
            os.chmod(script, mode)
            reg = root / "data/gate_registry.json"
            doc = json.loads(reg.read_text())
            old_pin = None
            for row in doc["rows"]:
                if row["id"] == "check_alpha":
                    row["demonstrated"]["ref"] = ref
                    old_pin = row["demonstrated"]["script_sha256"]
            reg.write_text(json.dumps(doc, indent=2) + "\n")
            before = reg.read_bytes()
            debt_before = (root / REPLAY_DEBT_REL).read_bytes()
            if expected_output:
                import contextlib
                import io
                output = io.StringIO()
                with contextlib.redirect_stderr(output):
                    rc = repin(root, "check_alpha")
                diagnostics_ok = all(text in output.getvalue() for text in expected_output)
            else:
                rc = repin(root, "check_alpha")
                diagnostics_ok = True
            new_pin = next(r["demonstrated"]["script_sha256"]
                           for r in json.loads(reg.read_text())["rows"]
                           if r["id"] == "check_alpha")
            ok = (((rc == 0) == expect_ok) and ((new_pin != old_pin) == expect_moved)
                  and diagnostics_ok
                  and (expect_ok or (reg.read_bytes() == before
                                     and (root / REPLAY_DEBT_REL).read_bytes() == debt_before)))
            print(f"  [{'ok' if ok else 'FAIL'}] repin-guard {name}")
            if not ok:
                failures += 1

    RED = "#!/usr/bin/env python3\n# --selftest\nraise SystemExit(1)\n"
    GREEN = "#!/usr/bin/env python3\n# --selftest\nprint('a')  # edited\n"
    run("refuses failing demonstration, pin unmoved",
        RED, "scripts/check_alpha.py --selftest", 0o755, False, False)
    run("moves pin on passing demonstration",
        GREEN, "scripts/check_alpha.py --selftest", 0o755, True, True)
    run("guards interpreter-prefixed ref",
        RED, "python3 scripts/check_alpha.py --selftest", 0o644, False, False)
    run("non-executable direct ref refuses, no traceback",
        GREEN, "scripts/check_alpha.py --selftest", 0o644, False, False)
    run("failed ref retains both diagnostic streams, including non-UTF8 bytes, pin unmoved",
        "#!/usr/bin/env python3\nimport os\nos.write(1, b'child stdout reason')\n"
        "os.write(2, b'\\xffchild stderr reason')\nraise SystemExit(7)\n",
        "scripts/check_alpha.py --selftest", 0o755, False, False,
        ("exits 7", "child stdout reason\n\ufffdchild stderr reason\n"))

    # verifier r9 recheck (2026-09-25): the undemonstrated account moved a
    # DERIVED input set over arms that did not replay -- measured, a projector
    # mechanism deleted with its test, `--repin` with CLEAN_REPIN_UNDEMONSTRATED
    # and CLEAN_REPIN_OWNER set, GATE_REGISTRY fail -> ok. Lane r10: `--repin`
    # moves NO pin without a green run or replay in the same process, and the
    # account is a separate verb that never moves an input set. The replay is
    # stubbed to fail here, as the real one does over such a tree.
    def pins(reg: Path) -> tuple:
        row = next(r for r in json.loads(reg.read_text())["rows"] if r["id"] == "check_alpha")
        d = row["demonstrated"]
        return (d.get("inputs"), d.get("script_sha256"), d.get("replayed"),
                d.get("repinned_without_demonstration"), d.get("date"))

    # The last field edits the fixture's claims: "keep" leaves check_alpha and
    # the leg alpha that inherits its pin claiming soundness; "heir" makes
    # check_alpha claim quality, so only alpha's claim stands on its pin. An
    # account never stands under a soundness claim on a row with a replay
    # route (R4b); with no route it is the row's only verb.
    cases = (
        ("a row pinning DERIVED inputs is not re-pinned by --repin when its replay FAILS",
         True, True, True, False, False, "keep"),
        ("a row pinning DERIVED inputs is not re-pinned by --repin when it has no replay",
         True, False, True, False, False, "keep"),
        ("--repin-undemonstrated never moves a DERIVED input set",
         True, False, True, True, False, "keep"),
        ("a row nothing can replay is not re-pinned by --repin, account variables or not",
         False, False, True, False, False, "keep"),
        ("--repin-undemonstrated moves such a row on an owned account, drops its replay "
         "record and leaves its date", False, False, True, True, True, "keep"),
        ("the account needs its variables", False, False, False, True, False, "keep"),
        ("--repin-undemonstrated refuses a soundness row that has a replay route",
         False, True, True, True, False, "keep"),
        ("--repin-undemonstrated refuses a replayable row whose pin a soundness leg inherits",
         False, True, True, True, False, "heir"),
    )
    for label, derived, replayable, with_env, undemonstrated, expect_moved, sound in cases:
        arms += 1
        with tempfile.TemporaryDirectory() as td:
            root = _mini(Path(td))
            if sound == "heir":
                _edit(root, "check_alpha", "claims", "quality")
            if derived:
                _derive_alpha(root)
            else:
                _demo_set(root, "check_alpha", "replayed", {"stale": "record"})
            _demo_set(root, "check_alpha", "ref", "data/gate_demonstrations.json")
            _demo_set(root, "check_alpha", "replayable", replayable)
            reg = root / "data/gate_registry.json"
            before = pins(reg)
            (root / "data/alpha_input.txt").write_text("a mechanism and its test, deleted\n")
            _sub(root, "scripts/check_alpha.py", "print('a')", "print('gutted')")
            keys = ("CLEAN_REPIN_UNDEMONSTRATED", "CLEAN_REPIN_OWNER")
            saved = {k: os.environ.get(k) for k in keys}
            for k in keys:
                os.environ.pop(k, None)
            if with_env:
                os.environ.update(CLEAN_REPIN_UNDEMONSTRATED="self-test: the arms do not replay",
                                  CLEAN_REPIN_OWNER="self-test")
            real_demonstrate = globals()["demonstrate"]
            globals()["demonstrate"] = lambda *_a, **_k: 1
            try:
                rc = repin(root, "check_alpha", undemonstrated=undemonstrated)
            finally:
                globals()["demonstrate"] = real_demonstrate
                for k, v in saved.items():
                    if v is None:
                        os.environ.pop(k, None)
                    else:
                        os.environ[k] = v
            after = pins(reg)
            if expect_moved:
                ok = (rc == 0 and after[1] != before[1] and after[2] is None
                      and (after[3] or {}).get("owner") == "self-test"
                      and after[4] == before[4])
            else:
                ok = rc != 0 and after == before
            print(f"  [{'ok' if ok else 'FAIL'}] repin-guard {label}")
            if not ok:
                failures += 1

    # ... and a green --repin records the replay it moved the pin over.
    arms += 1
    with tempfile.TemporaryDirectory() as td:
        root = _mini(Path(td))
        (root / "scripts/check_alpha.py").write_text(GREEN)
        _demo_set(root, "check_alpha", "ref", "scripts/check_alpha.py --selftest")
        os.chmod(root / "scripts/check_alpha.py", 0o755)
        rc = repin(root, "check_alpha")
        d = next(r for r in json.loads((root / "data/gate_registry.json").read_text())["rows"]
                 if r["id"] == "check_alpha")["demonstrated"]
        debt = json.loads((root / REPLAY_DEBT_REL).read_text())
        ok = (rc == 0 and (d.get("replayed") or {}).get("script_sha256") == d["script_sha256"]
              and debt == {"count": 2, "rows": ["check_scan", "check_rs_scan"]}
              and not [p for p in check(root) if p.startswith("R7c")])
        print(f"  [{'ok' if ok else 'FAIL'}] repin-guard a green --repin records its replay "
              f"and discharges the row's replay-record debt")
        if not ok:
            failures += 1

    # A self-pinned inheritor (R7c judges it on its own pin) re-pins over the
    # arms of the row it names when both pin one file, and is refused before any
    # replay when they do not. The replay is the real arm loop over a sandbox of
    # the mini-repo, so arms looked up under the inheritor's own id find none.
    heir_demos = {"check_alpha": [{
        "arm": "the gate is planted to exit 1",
        "mutate": {"file": "scripts/check_alpha.py", "op": "append",
                   "text": "\nraise SystemExit(1)\n"},
        "command": "python3 scripts/check_alpha.py"}]}
    for label, own_subject, expect_moved in (
            ("an inheritor pinning its parent's subject re-pins over the parent's arms "
             "and discharges its debt", "scripts/check_alpha.py", True),
            ("an inheritor pinning a file its parent does not is refused before any replay, "
             "registry and anchor untouched", "scripts/check_scan.py", False)):
        arms += 1
        with tempfile.TemporaryDirectory() as td:
            root = _mini(Path(td))
            for rid in ("check_alpha", "alpha"):
                _demo_set(root, rid, "ref", "data/gate_demonstrations.json")
                _demo_set(root, rid, "replayable", True)
            _edit(root, "alpha", "implemented_by", own_subject)
            _demo_set(root, "alpha", "script_sha256", _sha256(root, own_subject))
            anchor = root / REPLAY_DEBT_REL
            owed = json.loads(anchor.read_text())
            owed["rows"].append("alpha")
            owed["count"] = len(owed["rows"])
            anchor.write_text(json.dumps(owed, indent=2) + "\n")
            for argv in (("init", "-q", "-b", "main"), ("add", "-A"), ("commit", "-qm", "g")):
                _git_run(root, *argv)
            reg = root / "data/gate_registry.json"
            before = (reg.read_bytes(), anchor.read_bytes())
            called: list = []

            def heir_replay(r, rid, keep=False, ran_over=None):
                called.append(rid)
                sand = Path(td) / "sandbox"
                _build_sandbox(r, sand, build=False, mutated=set())
                rows = {row["id"]: row for row in load_registry(r)["rows"]}
                failed, total = _demonstrate_arms(r, lambda _b, _m: sand, sys.executable,
                                                  [rid], heir_demos, rows, 0, 0, ran_over)
                return 1 if failed or not total else 0
            real_demonstrate = globals()["demonstrate"]
            globals()["demonstrate"] = heir_replay
            err = io.StringIO()
            try:
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                    rc = repin(root, "alpha")
            finally:
                globals()["demonstrate"] = real_demonstrate
            d = next(r for r in load_registry(root)["rows"] if r["id"] == "alpha")["demonstrated"]
            left = json.loads(anchor.read_text())["rows"]
            if expect_moved:
                ok = (rc == 0 and called == ["check_alpha"]
                      and (d.get("replayed") or {}).get("script_sha256") == d["script_sha256"]
                      and "check_alpha" in (d["replayed"].get("by") or "")
                      and "alpha" not in left)
            else:
                ok = (rc != 0 and not called and (reg.read_bytes(), anchor.read_bytes()) == before
                      and "never ran over this row's pin" in err.getvalue())
            print(f"  [{'ok' if ok else 'FAIL'}] repin-guard {label}")
            if not ok:
                failures += 1

    # verifier r10: `--repin` hashed the pin AFTER a multi-minute replay whose
    # sandbox was cloned before the first arm, so a pinned input edited in the tree
    # meanwhile was pinned with a replay record though no arm ran over it. The
    # replay here is the real arm loop (`_demonstrate_arms`) over a real sandbox
    # of the mini-repo; the input is edited after the sandbox is cloned, or before
    # it and put back before the pin is read (a stash and its pop); the control
    # replays over the tree's own bytes and moves the pin.
    demos = {"check_alpha": [{
        "arm": "the gate is planted to exit 1",
        "mutate": {"file": "scripts/check_alpha.py", "op": "append",
                   "text": "\nraise SystemExit(1)\n"},
        "command": "python3 scripts/check_alpha.py"}]}
    for label, when, expect_moved in (
            ("a derived input edited in the tree while its replay runs is not pinned",
             "after-clone", False),
            ("a derived input edited before its sandbox is cloned and put back before the "
             "pin is read is not pinned", "undone", False),
            ("CONTROL: a green replay over the tree's own bytes moves the derived pin",
             None, True)):
        arms += 1
        with tempfile.TemporaryDirectory() as td:
            root = _mini(Path(td))
            _derive_alpha(root)
            _demo_set(root, "check_alpha", "ref", "data/gate_demonstrations.json")
            _demo_set(root, "check_alpha", "replayable", True)
            for argv in (("init", "-q", "-b", "main"), ("add", "-A"), ("commit", "-qm", "g")):
                _git_run(root, *argv)
            inp = root / "data/alpha_input.txt"
            inp.write_text("edited, to be replayed\n")
            reg = root / "data/gate_registry.json"
            before = pins(reg)

            def replay(r, rid, keep=False, ran_over=None):
                kept = inp.read_bytes()
                if when == "undone":
                    inp.write_text("stashed, then popped\n")
                sand = Path(td) / "sandbox"
                _build_sandbox(r, sand, build=False, mutated=set())
                if when == "undone":
                    inp.write_bytes(kept)
                rows = {row["id"]: row for row in load_registry(r)["rows"]}
                failed, total = _demonstrate_arms(r, lambda _b, _m: sand, sys.executable,
                                                  [rid], demos, rows, 0, 0, ran_over)
                if when == "after-clone":
                    inp.write_text("edited under the replay\n")
                return 1 if failed or not total else 0
            real_demonstrate = globals()["demonstrate"]
            globals()["demonstrate"] = replay
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    rc = repin(root, "check_alpha")
            finally:
                globals()["demonstrate"] = real_demonstrate
            after = pins(reg)
            if expect_moved:
                ok = (rc == 0 and after[0] != before[0]
                      and after[0] == _derived_inputs(root, "scripts/check_alpha.py")[0]
                      and (after[2] or {}).get("inputs_sha256") == _inputs_digest(after[0]))
            else:
                ok = rc != 0 and after == before
            print(f"  [{'ok' if ok else 'FAIL'}] repin-guard {label}")
            if not ok:
                failures += 1
    return arms, failures


def _selftest_pushed() -> tuple[int, int]:
    arms = [
        ("34 R10 the PUSHED commit is stale while the working tree is green",
         "R10 PUSHED", "stale"),
        ("35 R10 the pushed commit has no registry at all",
         "R10 PUSHED", "noregistry"),
        ("36 R10 a consistent pushed commit is green", "", "clean"),
        ("37 R10 a sha that is not a commit HERE says so, not 'no registry'",
         "R10 PUSHED", "notcommit"),
        # verifier r8b (2026-09-25): a derived input set exists only in a
        # checkout of the pushed commit, which is where the hook runs R10.
        ("37b R10 a pushed row pinning DERIVED inputs, judged outside a checkout of it",
         "R10 PUSHED: check_alpha pins a derived input set", "inputs-elsewhere"),
        ("37c R10 the same push judged IN a clean checkout of it is green", "", "inputs-here"),
    ]
    failures = 0
    saved = os.environ.get("CLEAN_PUSH_RANGES")
    for name, expect, mode in arms:
        with tempfile.TemporaryDirectory() as td:
            try:
                root, stale = _minigit(Path(td))
            except Exception as exc:  # git absent or refusing: say so, do not pass
                print(f"  [FAIL] {name}: could not build the mini repo ({exc})")
                failures += 1
                continue
            head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(root),
                                  capture_output=True, text=True, check=True).stdout.strip()
            if mode == "stale":
                tip = stale
            elif mode == "noregistry":
                _git_run(root, "rm", "-q", "data/gate_registry.json")
                _git_run(root, "commit", "-qm", "drop the registry")
                tip = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(root),
                                     capture_output=True, text=True,
                                     check=True).stdout.strip()
                _git_run(root, "checkout", "-q", head)
            elif mode == "notcommit":
                tip = "0" * 39 + "1"  # well-formed, and not in this repository
            elif mode in ("inputs-elsewhere", "inputs-here"):
                _derive_alpha(root)
                _git_run(root, "add", "-A")
                _git_run(root, "commit", "-qm", "derive the inputs")
                tip = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(root),
                                     capture_output=True, text=True,
                                     check=True).stdout.strip()
                if mode == "inputs-elsewhere":
                    _git_run(root, "checkout", "-q", head)
            else:
                tip = head
            os.environ["CLEAN_PUSH_RANGES"] = f"{GIT_ZERO} {tip}\n"
            try:
                problems = check(root)
            except Red as exc:
                problems = [str(exc)]
            finally:
                if saved is None:
                    os.environ.pop("CLEAN_PUSH_RANGES", None)
                else:
                    os.environ["CLEAN_PUSH_RANGES"] = saved
            hit = [p for p in problems if p.startswith(expect)] if expect else []
            if not expect:
                if problems:
                    print(f"  [FAIL] {name}: expected a clean tree, got:")
                    for pr in problems:
                        print(f"           {pr}")
                    failures += 1
                else:
                    print(f"  [ok]   {name}")
                continue
            if hit:
                print(f"  [ok]   {name} -> {hit[0][:96]}")
            else:
                print(f"  [FAIL] {name}: expected {expect}, got {problems or ['(green)']}")
                failures += 1
    return len(arms), failures


# -- wiring-discriminator arms ------------------------------------------------
#
# The discriminator is REPORTING-ONLY, so no `check()` arm can reach it -- and
# an unfalsifiable measurement is the thing this whole file exists to refuse.
# These arms run it directly, in BOTH directions, on bodies that are the exact
# shapes the 2026-08-27 issue names.
#
# Every path below is INVENTED (`scripts/wire_*`). That is not cosmetic: this
# file is itself a declared runner of `local_gate`, so a literal naming a real
# script here would mint a live runner edge out of a self-test fixture and R3
# would report the fixture as an undeclared runner.
#
# Each arm also re-derives the LOOSE set from the same body and requires the
# records to cover it exactly. The discriminator may only ever be a filter on
# `invocations_in`; a record set that drifted from it would be measuring a
# different denominator than R3 uses, and the audit would be comparing two
# different questions.

_WIRE_ARMS = (
    ("a DATA string is NOT an edge", "scripts/w.py", """
row = {
    "id": "demo",
    "wired_by": ["scripts/wire_alpha.sh"],
}
""", [("scripts/wire_alpha.sh", False)]),
    ("a subprocess call IS an edge", "scripts/w.py", """
def go():
    subprocess.run(["bash", "scripts/wire_alpha.sh"], check=True)
""", [("scripts/wire_alpha.sh", True)]),
    ("a single-line command VECTOR is an edge", "scripts/w.py", """
PLAN = {"id": "gate::x", "argv": ["scripts/wire_alpha.sh", "--jobs", "2"]}
""", [("scripts/wire_alpha.sh", True)]),
    ("a MULTI-LINE command vector is an edge", "scripts/w.py", """
PLAN = {
    "id": "gate::x",
    "argv": [
        "scripts/wire_alpha.sh",
        "--jobs",
        "2",
    ],
}
""", [("scripts/wire_alpha.sh", True)]),
    ("a shell BARE PATH is an edge", "scripts/w.sh", """
set -euo pipefail
bash scripts/wire_alpha.sh || fail "the gate said no"
""", [("scripts/wire_alpha.sh", True)]),
    ("a command RECORDED for a human is not an edge", "scripts/w.py", """
def row():
    return unknown_row(
        name="x",
        mint_command="scripts/wire_alpha.sh --jobs 2 --update",
    )
""", [("scripts/wire_alpha.sh", False)]),
    ("a non-head element of a dependency list is not an edge", "scripts/w.py", """
PLAN = {"_extra_paths": ["data/wire.json", "scripts/wire_alpha.sh"]}
""", [("scripts/wire_alpha.sh", False)]),
    ("a MULTI-LINE list that is not command-bound is not an edge", "scripts/w.py", """
PLAN = {
    "_extra_paths": [
        "scripts/wire_alpha.sh",
    ],
}
""", [("scripts/wire_alpha.sh", False)]),
    ("a LAUNCHER head does not hide the command word", "scripts/w.py", """
PLAN = {"argv": ["python3", "scripts/wire_beta.py"]}
""", [("scripts/wire_beta.py", True)]),
    ("an exec context OPENED ON A PREVIOUS LINE is an edge", "scripts/w.py", """
def go():
    result = subprocess.run(
        [PY, "scripts/wire_beta.py", "--check"],
        check=False,
    )
""", [("scripts/wire_beta.py", True)]),
    ("prose inside an EMITTED artifact is not an edge", "scripts/w.py", """
DOC = {
    "destination": "rows live here and scripts/wire_gamma.sh reads them from here",
}
""", [("scripts/wire_gamma.sh", False)]),
    ("a Rust const is not an edge, and is flagged indirect", "crates/x/src/w.rs", """
const SCRIPT: &str = "scripts/wire_alpha.sh";
fn go(root: &Path) {
    let script = root.join(SCRIPT);
    let status = Command::new("bash").arg(&script).status();
}
""", [("scripts/wire_alpha.sh", False)]),
    ("data and command in ONE file are told apart", "scripts/w.py", """
PLAN = {
    "argv": ["scripts/wire_alpha.sh", "--check"],
    "_extra_paths": ["scripts/wire_beta.py"],
}
""", [("scripts/wire_alpha.sh", True), ("scripts/wire_beta.py", False)]),
)


def _selftest_wiring() -> tuple:
    failures = 0
    for i, (name, rel, body, expect) in enumerate(_WIRE_ARMS, 38):
        label = "%d WIRING %s" % (i, name)
        recs = wiring_records(rel, body)
        got = [(r["target"], r["real"]) for r in recs]
        loose = set()
        for _, line in _code_lines(rel, body):
            for m in INVOCATION.finditer(line):
                if m.start(1) > 0 and line[m.start(1) - 1] == "`":
                    continue
                loose.add(m.group(1))
        if loose != {r["target"] for r in recs}:
            print("  [FAIL] %s: the records do not cover the LOOSE set "
                  "(loose=%s records=%s) -- the discriminator would be filtering a "
                  "different denominator than R3 uses"
                  % (label, sorted(loose), sorted({r["target"] for r in recs})))
            failures += 1
            continue
        if got != expect:
            print("  [FAIL] %s: expected %s, got %s (%s)"
                  % (label, expect, got, "; ".join(r["why"] for r in recs)))
            failures += 1
            continue
        if "indirect" in name and not any(r["indirect"] for r in recs):
            print("  [FAIL] %s: the binding was not flagged indirect, so an "
                  "invocation through a NAME would be silently downgraded" % label)
            failures += 1
            continue
        print("  [ok]   %s -> %s" % (label, ", ".join(
            "%s %s" % ("RUNS" if r["real"] else "names", r["target"]) for r in recs)))
    target = "scripts/" + "wire_alpha.sh"
    runner = VERIFY_RUNNER
    plain = "print(" + repr(target) + ")\n"
    bound = "SCRIPT = " + repr(target) + "\ndef go():\n    return subprocess.run(['bash', SCRIPT])\n"
    direct = 'subprocess.run(["bash", ' + repr(target) + "])\n"
    report_cases = (
        ("late indirect evidence survives an earlier reference", plain + bound, 1, 0),
        ("indirect evidence survives reversed reference order", bound + plain, 1, 0),
        ("real invocation evidence keeps precedence", plain + bound + direct, 0, 1),
    )
    scratch = Path(tempfile.gettempdir()) / ".ubd"
    scratch.mkdir(exist_ok=True)
    for name, body, indirect, real in report_cases:
        try:
            with tempfile.TemporaryDirectory(prefix="wiring-report-", dir=scratch) as td:
                root = Path(td)
                (root / "data").mkdir()
                (root / "scripts").mkdir()
                (root / target).write_text("#!/bin/sh\nexit 0\n")
                (root / runner).write_text(body)
                (root / "scripts" / "check_gate_registry.py").write_text("# fixture\n")
                row = {"id": "wire", "path": target, "kind": "gate", "claims": "quality",
                       "wired_by": [] if real else [runner], "demonstrated": None, "waiver": None}
                (root / "data/gate_registry.json").write_text(json.dumps({"rows": [row]}))
                report, head = wiring_audit_report(root)
                assert head["indirect_flagged"] == indirect, head
                if real:
                    assert head["judged_undeclared_real"] == 1, head
                    assert 'subprocess.run(["bash",' in report, report
                else:
                    assert head["judged_references_only"] == 1, head
                    assert "SCRIPT =" in report, report
        except Exception as exc:
            print(f"  [FAIL] WIRING REPORT {name}: {exc}")
            failures += 1
        else:
            print(f"  [ok]   WIRING REPORT {name}")
    return len(_WIRE_ARMS) + len(report_cases), failures


def _resha(root: Path, rid: str) -> None:
    """Re-pin a mini-repo row's demonstration sha after an arm edits its script,
    so an arm that is SUPPOSED to be green is not reddened by R7 instead.

    `_subject`, matching `repin()`: for a leg the pinned file is its
    `implemented_by`, and pinning `path` here would hash the empty string.
    """
    doc = _reg(root)
    for row in doc["rows"]:
        if row["id"] == rid and row.get("demonstrated"):
            row["demonstrated"]["script_sha256"] = _sha256(root, _subject(row))
    _put(root, doc)


_DERIVING_ALPHA = (
    "#!/usr/bin/env python3\n# --selftest\nimport sys\n"
    "ANSWERS_PINNED_INPUTS = True\n"
    "if '--pinned-inputs' in sys.argv:\n"
    "    print('data/alpha_input.txt')\n"
    "    sys.exit(0)\n"
    "print('a')\n"
)


def _derive_alpha(root: Path, pin_inputs: bool = True) -> None:
    """Make the mini-repo's `check_alpha` a gate that derives its inputs, and
    pin its script -- and, unless told not to, its input set -- as `--repin`
    would."""
    (root / "data/alpha_input.txt").write_text("input\n")
    (root / "scripts/check_alpha.py").write_text(_DERIVING_ALPHA)
    _resha(root, "check_alpha")
    if pin_inputs:
        derived, why = _derived_inputs(root, "scripts/check_alpha.py")
        if derived is None:
            raise Red(f"self-test fixture: {why}")
        _demo_set(root, "check_alpha", "inputs", derived)
        row = next(r for r in _reg(root)["rows"] if r["id"] == "check_alpha")
        _demo_set(root, "check_alpha", "replayed",
                  _replay_record(row["demonstrated"], "self-test fixture"))
        _discharge_replay_debt(root, "check_alpha")


def _scan_through(root: Path, walker_body: str, lexer: str | None = None) -> None:
    """Make the mini-repo's `check_scan` a gate that holds no stripper and reads
    Rust through `scripts/scan_walk.py`, an input it derives, whose `lexed`
    has `walker_body`; with `lexer`, the walker also lists `scripts/ref_lexer.py`
    (that source) among the inputs the gate prints, which the gate's code never
    names; pin all as `--repin` would."""
    inputs = ("scripts/scan_walk.py",) + (("scripts/ref_lexer.py",) if lexer is not None else ())
    if lexer is not None:
        (root / "scripts/ref_lexer.py").write_text(lexer)
    (root / "scripts/scan_walk.py").write_text(f"INPUTS = {inputs!r}\n\n\ndef lexed(text):\n" + walker_body)
    (root / "scripts/check_scan.py").write_text(
        "#!/usr/bin/env python3\n# --selftest\nimport runpy\nimport sys\n"
        "ANSWERS_PINNED_INPUTS = True\n"
        "walker = runpy.run_path('scripts/scan_walk.py')\n"
        "if '--pinned-inputs' in sys.argv:\n"
        "    print(*walker['INPUTS'], sep='\\n')\n"
        "    sys.exit(0)\n"
        "for p in root.rglob('*.rs'):\n"
        "    hits = walker['lexed'](p.read_text())\n"
    )
    _resha(root, "check_scan")
    derived, why = _derived_inputs(root, "scripts/check_scan.py")
    if derived is None:
        raise Red(f"self-test fixture: {why}")
    _demo_set(root, "check_scan", "inputs", derived)
    row = next(r for r in _reg(root)["rows"] if r["id"] == "check_scan")
    _demo_set(root, "check_scan", "replayed", _replay_record(row["demonstrated"], "self-test fixture"))
    _discharge_replay_debt(root, "check_scan")


def _symlinked_alpha_input(root: Path) -> None:
    """The r9-recheck P4 shape: `check_alpha`'s derived input is a symlink to a
    directory holding the code, pinned as the "" such a path used to hash to,
    and the code behind it edited since."""
    _derive_alpha(root)
    (root / "data/alpha_real").mkdir()
    (root / "data/alpha_real/mod.rs").write_text("fn edited_after_the_pin() {}\n")
    (root / "data/alpha_input.txt").unlink()
    (root / "data/alpha_input.txt").symlink_to("alpha_real", target_is_directory=True)
    _demo_set(root, "check_alpha", "inputs", {"data/alpha_input.txt": ""})


def _demo_set(root: Path, rid: str, key: str, value) -> None:
    """Set one field INSIDE a mini-repo row's `demonstrated` block."""
    doc = _reg(root)
    for row in doc["rows"]:
        if row["id"] == rid and row.get("demonstrated"):
            row["demonstrated"][key] = value
    _put(root, doc)


def _demo_drop(root: Path, rid: str, key: str) -> None:
    doc = _reg(root)
    for row in doc["rows"]:
        if row["id"] == rid and row.get("demonstrated"):
            row["demonstrated"].pop(key, None)
    _put(root, doc)


def _demos_debt(root: Path, rid: str, sites: int, arms: int,
                expires: str = "2027-01-01") -> None:
    """Give the mini-repo an arm-coverage debt row (audit r14 M14-4)."""
    path = root / "data/gate_demonstrations.json"
    doc = json.loads(path.read_text())
    doc.setdefault("arm_coverage_debt", {}).setdefault("rows", {})[rid] = {
        "owner": "selftest", "expires": expires, "sites": sites, "arms": arms,
        "owed": "selftest fixture row",
    }
    path.write_text(json.dumps(doc, indent=2))


def _edit(root: Path, rid: str, key: str, value) -> None:
    doc = _reg(root)
    for row in doc["rows"]:
        if row["id"] == rid:
            row[key] = value
    _put(root, doc)


def _ret(root: Path, rid: str, key: str, value) -> None:
    doc = _reg(root)
    for ent in doc.get("retired", []):
        if ent["id"] == rid:
            ent[key] = value
    _put(root, doc)


def _drop(root: Path, rid: str, key: str) -> None:
    doc = _reg(root)
    for row in doc["rows"]:
        if row["id"] == rid:
            row.pop(key, None)
    _put(root, doc)


def _row(root: Path, rid: str, key: str, value) -> None:
    """Set a top-level key on a row (the sibling of _drop)."""
    doc = _reg(root)
    for row in doc["rows"]:
        if row["id"] == rid:
            row[key] = value
    _put(root, doc)


def _sub(root: Path, rel: str, old: str, new: str) -> None:
    p = root / rel
    text = p.read_text()
    if old not in text:
        raise Red(f"self-test arm could not find {old!r} in {rel} -- the arm is vacuous")
    p.write_text(text.replace(old, new, 1))


# ── entry point ──────────────────────────────────────────────────────────────


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--selftest", action="store_true",
                    help="mutation arms on this checker; the count is the live "
                         "GATE_REGISTRY_SELFTEST arms=N line, never a number typed here")
    ap.add_argument("--list", action="store_true", help="print the registry as a table")
    ap.add_argument("--json", action="store_true", help="print the summary as JSON")
    ap.add_argument("--demonstrate", nargs="?", const="", metavar="ID",
                    help="replay the recorded mutation arms in a sandbox built from "
                         "this working tree (no tracked path in the shared checkout is "
                         "written; cargo builds into <repo>/target/gate-demo-<layout>, "
                         "gitignored and persistent)")
    ap.add_argument("--keep-sandbox", action="store_true",
                    help="do not delete the demonstration sandbox afterwards")
    ap.add_argument("--repin", metavar="ID",
                    help="run or replay a row's demonstration and, only if it is green, "
                         "move its pin and record that replay")
    ap.add_argument("--repin-undemonstrated", metavar="ID",
                    help="move the script pin of a row nothing here can run or replay, on "
                         "an owned, expiring account (CLEAN_REPIN_UNDEMONSTRATED, "
                         "CLEAN_REPIN_OWNER); never an input set")
    ap.add_argument("--wiring-audit", action="store_true",
                    help="REPORTING ONLY: re-derive which declared wired_by entries "
                         "are real invocations and which are references, for every "
                         "row. Never changes the gate's verdict; always exits 0.")
    ap.add_argument("--wiring-audit-out", metavar="PATH",
                    help="write the wiring audit to PATH instead of stdout")
    ap.add_argument("--pushed-in", metavar="CHECKOUT",
                    help="R10 ALONE, over the commits CLEAN_PUSH_RANGES names, read "
                         "from CHECKOUT (a clean checkout of them): what the pre-push "
                         "hook's outer role runs with ITS OWN copy of this script")
    args = ap.parse_args(argv)

    if args.selftest:
        return selftest()
    if args.pushed_in is not None:
        # See `check_pushed_tips`: the hook's OUTER role runs this with the
        # pusher's copy of the script, so a pushed commit that edits its own
        # gates -- this file included -- is judged by code it did not write.
        if not pushed_tips():
            print("GATE_REGISTRY_PUSHED=fail CLEAN_PUSH_RANGES names no pushed commit -- "
                  "nothing was judged, and that is not a pass", file=sys.stderr)
            return 1
        problems = check_pushed_tips(Path(args.pushed_in).resolve())
        for p in problems:
            print(f"  {p}", file=sys.stderr)
        print(f"GATE_REGISTRY_PUSHED={'fail' if problems else 'ok'} "
              f"tips={len(pushed_tips())} problems={len(problems)}")
        return 1 if problems else 0
    if args.wiring_audit:
        return cmd_wiring_audit(ROOT, args.wiring_audit_out)
    if args.list:
        return cmd_list(ROOT)
    if args.repin or args.repin_undemonstrated:
        try:
            if args.repin:
                return repin(ROOT, args.repin)
            return repin(ROOT, args.repin_undemonstrated, undemonstrated=True)
        except Red as exc:
            print(f"GATE_REGISTRY=fail {exc}", file=sys.stderr)
            return 1
    if args.demonstrate is not None:
        try:
            return demonstrate(ROOT, args.demonstrate or None, args.keep_sandbox)
        except Red as exc:
            print(f"GATE_DEMOS=fail {exc}", file=sys.stderr)
            return 1

    try:
        problems = check(ROOT)
    except Red as exc:
        print(f"GATE_REGISTRY=fail {exc}", file=sys.stderr)
        return 1
    s = summarise(ROOT)
    if args.json:
        print(json.dumps({"summary": s, "problems": problems}, indent=2))
        return 1 if problems else 0
    if problems:
        print(f"GATE_REGISTRY=fail problems={len(problems)}", file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
        return 1
    print(
        f"GATE_REGISTRY=ok rows={s['rows']} "
        + " ".join(f"{k}={v}" for k, v in sorted(s["kinds"].items()))
        + f" demonstrated={s['demonstrated']}(strong={s['strong']},replay={s['replayable']}) "
        f"waived={s['waived']} soundness={s['soundness_demonstrated']}/{s['soundness_rows']} "
        f"r7b-reach={s['r7b_backed']}/{s['r7b_eligible']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
