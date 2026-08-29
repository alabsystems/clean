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
  R7 FRESH       a demonstration is pinned to the sha256 of the script it
                 demonstrated. Gut the script, keep the badge -> RED. This is
                 the half a dated note in a header can never do.
  R8 RETIRED     a `retired` entry still has its file in the tree, or names a
                 successor that does not exist / is itself unwired.
  R10 PUSHED     R7, re-derived over the COMMIT BEING PUSHED rather than over
                 the working tree. Only active when the pre-push hook exports
                 CLEAN_PUSH_RANGES; see the block above `check_pushed_tips`.

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

DEMONSTRATIONS ARE REPLAYED, NOT CITED
--------------------------------------
`--demonstrate` applies each recorded mutation to the real tree, runs the real
gate, and requires a non-zero exit and the recorded diagnostic; then it restores
the file from git. It refuses to touch a file that is already dirty. A
demonstration in this repo is therefore a thing that RUNS, not a sentence in a
header that was true once.

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
    scripts/check_gate_registry.py --selftest      # 56 mutation arms on itself
    scripts/check_gate_registry.py --list          # the registry, as a table
    scripts/check_gate_registry.py --demonstrate   # replay every recorded arm
    scripts/check_gate_registry.py --demonstrate <id>
    scripts/check_gate_registry.py --repin <id>    # after a genuine re-demo
    scripts/check_gate_registry.py --wiring-audit  # REPORTING ONLY, always 0
    scripts/check_gate_registry.py --wiring-audit --wiring-audit-out <path>
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "data/gate_registry.json"
DEMOS = ROOT / "data/gate_demonstrations.json"

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
)


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
    out = set()
    for p in sorted((root / "scripts").glob("test_*.py")) + sorted((root / "scripts").glob("test_*.sh")):
        out.add(str(p.relative_to(root)))
    return out


# ── the rules ────────────────────────────────────────────────────────────────

REQUIRED = ("id", "path", "kind", "claims", "wired_by", "demonstrated", "waiver")
RETIRED_REQUIRED = ("id", "path", "retired", "by", "reason", "superseded_by")


def check(root: Path) -> list[str]:
    doc = load_registry(root)
    rows = doc["rows"]
    demos = load_demos(root)
    problems: list[str] = []
    today = date.today().isoformat()

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

    # R2 INVENTORY -- the anti-#7 clause. Two independent sources, unioned: a
    # gate-shaped NAME, and anything the enforcement path actually runs.
    shaped = gate_shaped_files(root)
    on_path = enforcement_path_scripts(root)
    for f in sorted(shaped | on_path):
        if f not in by_path:
            why = "gate-shaped by name" if f in shaped else "run by the enforcement path"
            if f in shaped and f in on_path:
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
        # R7 FRESH
        pinned = d.get("script_sha256")
        if row["path"] and pinned:
            live = _sha256(root, row["path"])
            if live and live != pinned:
                problems.append(
                    f"R7 FRESH: {rid} was demonstrated against {row['path']} at "
                    f"sha256:{pinned[:12]}, the tree has sha256:{live[:12]}. The script "
                    f"changed since it was last seen to fail -- re-demonstrate "
                    f"(scripts/check_gate_registry.py --demonstrate {rid}) then "
                    f"--repin {rid}."
                )
        elif row["path"] and row["kind"] in ("gate", "battery"):
            problems.append(f"R1 SHAPE: {rid} demonstration has no script_sha256 pin")

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
    for row in rows:
        rel = row.get("path")
        decl = row.get("source_scan")
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
            if decl is not None:
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
        if kind == "lexed" and not strips:
            problems.append(
                f"R9 SCANNER: {rid} declares source_scan.kind=\"lexed\", and {rel} "
                f"contains no recognised comment/literal stripper. Either it does not "
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
    problems.extend(check_pushed_tips(root))
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
        for row in rows:
            if not isinstance(row, dict):
                continue
            d = row.get("demonstrated")
            if not isinstance(d, dict):
                continue
            pinned = d.get("script_sha256")
            rel = row.get("path") or ""
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


def cmd_list(root: Path) -> int:
    doc = load_registry(root)
    rows = sorted(doc["rows"], key=lambda r: (r["kind"], r["id"]))
    print(f"{'KIND':<10} {'CLAIMS':<10} {'DEMO':<16} {'ID':<44} WIRED-BY")
    for r in rows:
        d = r.get("demonstrated")
        tag = "-" if d is None else ("!" + d["kind"] if d["kind"] not in STRONG else d["kind"])
        if r.get("waiver"):
            tag = f"WAIVED>{r['waiver']['expires']}"
        print(f"{r['kind']:<10} {r['claims']:<10} {tag:<16} {r['id']:<44} {','.join(r['wired_by']) or '-'}")
    s = summarise(root)
    print(f"\n{s['rows']} rows: " + ", ".join(f"{k}={v}" for k, v in sorted(s['kinds'].items())))
    print(f"demonstrated={s['demonstrated']} (strong={s['strong']}, replayable={s['replayable']}) "
          f"waived={s['waived']}; soundness rows {s['soundness_demonstrated']}/{s['soundness_rows']} demonstrated")
    sc = s["source_scanners"]
    print("source scanners: " + (", ".join(f"{k}={v}" for k, v in sorted(sc.items())) or "none")
          + f"; retired={len(doc.get('retired', []))}")
    return 0


# ── replayable demonstrations ────────────────────────────────────────────────


def _apply(root: Path, mut: dict) -> None:
    p = root / mut["file"]
    op = mut["op"]
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
        p.write_text(mut["content"])
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
        text = text + mut["text"]
    elif op == "prepend":
        text = mut["text"] + text
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
        text = mut["text"]
    else:
        raise Red(f"unknown mutation op {op!r}")
    p.write_text(text)


def _restore(root: Path, rel: str) -> None:
    subprocess.run(["git", "checkout", "--", rel], cwd=root, check=False,
                   capture_output=True)
    # `git checkout --` is a NO-OP for a path git does not track, so a `create`
    # arm's plant would SURVIVE its own restore. That is not a cosmetic leak: the
    # thing planted is by construction a gate-shaped file with no registry row,
    # which is exactly what R2 INVENTORY refuses -- so the demonstration would
    # leave the tree permanently RED for every other lane, and the next person to
    # run the gate would be debugging a file the demonstrator dropped. Remove
    # what git will not, and only that: a path git tracks is restored above, and
    # `_dirty` has already refused the arm if anything was sitting here first.
    p = root / rel
    if p.is_file():
        tracked = subprocess.run(["git", "ls-files", "--error-unmatch", "--", rel],
                                 cwd=root, check=False, capture_output=True)
        if tracked.returncode != 0:
            p.unlink()


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


def demonstrate(root: Path, only: str | None) -> int:
    doc = load_registry(root)
    demos = load_demos(root)
    rows = {r["id"]: r for r in doc["rows"]}
    targets = [only] if only else sorted(demos)
    py = _demo_python()
    failures = 0
    total = 0
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
                print(f"  [SKIP] {label}: {f} is already modified in this tree; "
                      f"the arm restores from git and refuses to clobber your edit")
                failures += 1
                continue
            command = arm["command"].replace("python3 ", f"{py} ")
            baseline = subprocess.run(command, cwd=root, shell=True,
                                      capture_output=True, text=True)
            if baseline.returncode != 0:
                # SAY WHY. Measured 2026-08-24: `trust_verify_ratchet` is red at
                # HEAD on any machine with a Trust stage1, and an arm for it
                # reported only "already exits 2" -- which reads as a broken arm
                # and is actually the gate correctly refusing. The same line also
                # covers an absent prerequisite (an arm whose dump/corpus/binary
                # is not on this machine), which is a THIRD thing, and none of
                # the three can be told apart from an exit code alone.
                blob0 = ((baseline.stdout or "") + (baseline.stderr or "")).strip()
                why = blob0.splitlines()[-1][:240] if blob0 else "(no output)"
                print(f"  [FAIL] {label}: the UNMUTATED gate already exits "
                      f"{baseline.returncode} -- a red arm on a red tree proves nothing"
                      f"\n         its last line was: {why}")
                failures += 1
                continue
            try:
                _apply(root, arm["mutate"])
                got = subprocess.run(command, cwd=root, shell=True,
                                     capture_output=True, text=True)
            except Red as exc:
                print(f"  [FAIL] {label}: {exc}")
                _restore(root, f)
                failures += 1
                continue
            finally:
                _restore(root, f)
            blob = (got.stdout or "") + (got.stderr or "")
            if got.returncode == 0:
                print(f"  [FAIL] {label}: the gate stayed GREEN under its own "
                      f"mutation -- it cannot fail, so its green means nothing")
                failures += 1
                continue
            needle = arm.get("expect_contains")
            if needle and needle not in blob:
                print(f"  [FAIL] {label}: exited {got.returncode} but never said "
                      f"{needle!r} -- it failed for some other reason")
                failures += 1
                continue
            print(f"  [ok]   {label}: rc={got.returncode}")
    print(f"GATE_DEMOS arms={total} failed={failures}")
    return 1 if failures else 0


def repin(root: Path, rid: str) -> int:
    doc = load_registry(root)
    for row in doc["rows"]:
        if row["id"] != rid:
            continue
        d = row.get("demonstrated")
        if d is None:
            print(f"{rid} has no demonstration to re-pin", file=sys.stderr)
            return 1
        d["script_sha256"] = _sha256(root, row["path"])
        d["date"] = date.today().isoformat()
        # indent=2, matching how data/gate_registry.json is actually STORED, and
        # matching the two other write sites in this file. A re-pin must be
        # REVIEWABLE — its real change is two fields, script_sha256 and date — so
        # writing a different indent than the file carries turns it into a
        # whole-file reformat that nobody can read, which defeats the point of
        # pinning a sha instead of trusting a badge.
        #
        # RE-MEASURE BEFORE CHANGING THIS. On 2026-08-27 a sweep proposed indent=1
        # on the strength of a round-trip test that genuinely passed — against the
        # PRE-REBASE registry, which was stored that way. In the 122 upstream
        # commits since, the file was re-serialised at indent=2, so applying that
        # answer here reformatted all 4,480 lines on the next re-pin: the exact
        # defect it was meant to remove. Round-trip the TRACKED file
        # (`git show HEAD:data/gate_registry.json`) against each candidate indent;
        # do not carry a previous answer forward.
        (root / "data/gate_registry.json").write_text(json.dumps(doc, indent=2) + "\n")
        print(f"re-pinned {rid} -> sha256:{d['script_sha256'][:12]} on {d['date']}")
        return 0
    print(f"no registry row {rid}", file=sys.stderr)
    return 1


# ── self-test ────────────────────────────────────────────────────────────────
#
# The demonstrator has to demonstrate itself, or this file is instance number
# seven. Fifty-six arms build a synthetic repo, mutate one thing, and
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
                          "ref": "cargo test -p x --test scan_battery", "date": "2026-08-25",
                          "script_sha256": _sha256(root, "crates/x/tests/scan_battery.rs")},
         "waiver": None},
        {"id": "check_script_selftests", "path": "scripts/check_script_selftests.sh",
         "kind": "gate", "claims": "hygiene", "wired_by": ["scripts/local_gate.sh"],
         "demonstrated": None, "waiver": None},
        {"id": "local_gate", "path": "scripts/local_gate.sh", "kind": "gate",
         "claims": "hygiene", "wired_by": ["Justfile"],
         "demonstrated": None, "waiver": None},
        {"id": "alpha", "path": "", "kind": "leg", "claims": "soundness",
         "wired_by": ["scripts/local_gate.sh"], "implemented_by": "scripts/check_alpha.py",
         "demonstrated": {"kind": "selftest-inline", "flag": "--selftest",
                          "ref": "scripts/check_alpha.py --selftest", "date": "2026-08-24"},
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

    run("38 _apply `create` plants a file that is not in the tree", a_create)
    run("39 _restore removes an untracked plant", a_restore_untracked)
    run("40 `create` refuses a file that already exists", a_create_refuses_existing)
    run("41 an unknown mutation op is refused", a_unknown_op)
    run("42 a no-op regex mutation is refused", a_regex_noop)
    run("43 _restore still restores a TRACKED file", a_restore_tracked)
    return arms, failures


def selftest() -> int:
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
        ("9  R4 waiver AND demonstration", "R4 DEMO",
         lambda r: _edit(r, "check_alpha", "waiver",
                         {"owner": "x", "expires": "2099-01-01", "reason": "belt and braces"})),
        ("10 R5 inline self-test the script lacks", "R5 EVIDENCE",
         lambda r: _sub(r, "scripts/check_alpha.py", "# --selftest\n", "")),
        ("11 R5 self-test file that does not exist", "R5 EVIDENCE",
         lambda r: (r / "scripts/test_beta_gate.sh").unlink()),
        ("12 R7 script gutted, badge kept", "R7 FRESH",
         lambda r: _sub(r, "scripts/check_alpha.py", "print('a')", "pass")),
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
                          {"owner": "x", "expires": "2099-01-01", "reason": "orphan"}),
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
                    _edit(r, "check_scan", "source_scan",
                          {"kind": "raw-lines", "note": "counts every mention"}),
                    _resha(r, "check_scan"))),
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
    total = len(arms) + git_arms + wire_arms + mut_arms
    failures += git_failures + wire_failures + mut_failures
    print(f"GATE_REGISTRY_SELFTEST arms={total} failed={failures}")
    return 1 if failures else 0


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


def _selftest_pushed() -> tuple[int, int]:
    arms = [
        ("34 R10 the PUSHED commit is stale while the working tree is green",
         "R10 PUSHED", "stale"),
        ("35 R10 the pushed commit has no registry at all",
         "R10 PUSHED", "noregistry"),
        ("36 R10 a consistent pushed commit is green", "", "clean"),
        ("37 R10 a sha that is not a commit HERE says so, not 'no registry'",
         "R10 PUSHED", "notcommit"),
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
    return len(_WIRE_ARMS), failures


def _resha(root: Path, rid: str) -> None:
    """Re-pin a mini-repo row's demonstration sha after an arm edits its script,
    so an arm that is SUPPOSED to be green is not reddened by R7 instead."""
    doc = _reg(root)
    for row in doc["rows"]:
        if row["id"] == rid and row.get("demonstrated"):
            row["demonstrated"]["script_sha256"] = _sha256(root, row["path"])
    _put(root, doc)


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


def _sub(root: Path, rel: str, old: str, new: str) -> None:
    p = root / rel
    text = p.read_text()
    if old not in text:
        raise Red(f"self-test arm could not find {old!r} in {rel} -- the arm is vacuous")
    p.write_text(text.replace(old, new, 1))


# ── entry point ──────────────────────────────────────────────────────────────


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--selftest", action="store_true", help="21 mutation arms on this checker")
    ap.add_argument("--list", action="store_true", help="print the registry as a table")
    ap.add_argument("--json", action="store_true", help="print the summary as JSON")
    ap.add_argument("--demonstrate", nargs="?", const="", metavar="ID",
                    help="replay the recorded mutation arms against the real tree")
    ap.add_argument("--repin", metavar="ID", help="re-pin a demonstration after re-running it")
    ap.add_argument("--wiring-audit", action="store_true",
                    help="REPORTING ONLY: re-derive which declared wired_by entries "
                         "are real invocations and which are references, for every "
                         "row. Never changes the gate's verdict; always exits 0.")
    ap.add_argument("--wiring-audit-out", metavar="PATH",
                    help="write the wiring audit to PATH instead of stdout")
    args = ap.parse_args(argv)

    if args.selftest:
        return selftest()
    if args.wiring_audit:
        return cmd_wiring_audit(ROOT, args.wiring_audit_out)
    if args.list:
        return cmd_list(ROOT)
    if args.repin:
        return repin(ROOT, args.repin)
    if args.demonstrate is not None:
        return demonstrate(ROOT, args.demonstrate or None)

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
        f"waived={s['waived']} soundness={s['soundness_demonstrated']}/{s['soundness_rows']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
