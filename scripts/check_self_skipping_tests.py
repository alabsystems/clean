#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Tests that can SKIP THEIR OWN ASSERTIONS at run time, MEASURED.

WHY THIS EXISTS
---------------
CLAUDE.md records the class and how one instance of it was found (2026-09-15,
the nullary `macro_rules` finding):

    The test had THREE nested `if let Ok(...)` guards and passed by skipping
    all three. A sweep for that shape over every `#[test]` in the workspace
    returned 17 candidates, of which 11 state a genuine disjunction in prose
    ... and 6 were silently skipping their own subject. One of the 6 was not
    an elaborator gap at all but a broken FIXTURE ... its one assertion had
    never run in the test's life.

That sweep was a CENSUS: it fixes the instances it finds, and nothing stops
the next one. The shape is invisible in every runner's output -- a test that
skips its own assertions prints `ok`, is counted in `N passed`, and keeps its
green in `data/suite_state/` for as long as it exists. It is the failure the
gate registry names for gates ("a gate nobody has seen fail is
indistinguishable from `exit 0`") one level down: here the test cannot fail,
because its assertions are conditional on the very thing they measure.

WHAT IT MEASURES
----------------
Three shapes, inside the body of a `#[test]` / `#[tokio::test]` function. All
three are reported ONLY when assertions are actually skippable -- that
discriminator is what keeps this from flagging half the workspace:

  * SILENT_MATCH_ARM   `match e { Ok(v) => { assert..; } Err(_) => {} }`
    An arm whose pattern is `Err(..)` or the catch-all `_`, whose body cannot
    fail, beside a sibling arm that asserts.
  * GUARDED_ASSERTIONS `if let Ok(v) = e { assert..; }` with no `else`, or
    with an `else` chain that cannot fail.
  * EARLY_RETURN       a `return;` / `return Ok(..)` at test level with
    assertions after it: the escape hatch that makes the rest optional.

NOT reported, deliberately. A gate that flags everything is switched off as
fast as one that flags nothing, so each of these has a self-test arm asserting
it stays GREEN (SHAPE_CASES below, the `[]` rows):

  * a silent arm beside a sibling whose body is a PURE failure
    (`Ok(_) => panic!("expected an error"), Err(_) => {}`): there the match IS
    the assertion and the silent arm is the expected outcome;
  * `if let .. { .. } else { panic!(..) }`, or any else chain that can fail;
  * a guarded block with no assertions in it -- setup, cleanup, a best-effort
    `let _ = fs::remove_file(p)` -- which skips nothing;
  * a test body whose LAST statement is an unconditional failure
    (`... panic!("expected simplified projection")`), the fall-through idiom:
    every skip path in such a body lands on that panic, so nothing is skipped.
    MEASURED on this tree 2026-09-16: without this rule the count is 1,018
    instead of 978 -- 40 hits across 9 files, e.g.
    crates/clean-compiler/src/opt/simp_value/tests.rs;
  * an `if let` whose scrutinee was already asserted (`assert!(r.is_ok());
    if let Ok(v) = r { .. }`), the destructure-after-assert idiom -- the guard
    cannot fail without the assert having failed first. MEASURED the same way:
    1,014 without it, 36 hits across 17 files, e.g.
    crates/clean-elab/src/infer/tests/instance.rs;
  * a `return` out of a branch that ASSERTS on its way out -- the skip path is
    not silent, and this is the same rule `can_fail` already applies to a match
    arm and to an `if let` else. MEASURED 2026-09-16: without this rule the
    count is 978 instead of 969 -- 9 hits across 8 files, every one of them a
    false positive. Two are
    crates/clean-compiler/src/emit_wasm_tests.rs, whose skip branch asserts the
    emitted module is well formed and says so in a comment -- "so this test is
    never a silent no-op" -- which is precisely the remediation this gate's own
    failure message prescribes; another is
    crates/clean-cli/src/cmd_replacement/tests/part_08.rs, an ordinary two-way
    branch asserting on both paths. An assertion earlier in the TEST does not
    excuse a nested skip: the window is the enclosing branch's own block.
  * `return Err(..)` from a `-> Result<..>` test, and `?` -- both FAIL the
    test, which is the opposite of skipping it;
  * a `return` inside a closure, an `async` block or a nested `fn`: it returns
    from THAT, not from the test.

HOW IT READS SOURCE
-------------------
CLAUDE.md: "A gate's verdict comes from a parse, never a line count ... Any
gate that reads Rust or Lean source must blank comments and string literals
first (`scripts/check_add_decl_ratchet.py` is the reference) ... Never
`split("//")`."

`strip_noncode` here is that reference's `NONCODE_RE`, unchanged: block
comments, line comments, raw strings, strings and char literals are blanked to
spaces BEFORE anything is matched, so line and column geometry survive and a
reported line still indexes the original file. Everything after that is
delimiter matching over the blanked text -- the `#[test]` attribute, the
signature, the body span, match arms, `if let` blocks and the enclosing-scope
stack of a `return` are all extracted by balanced `{}`/`()`/`[]`, never by a
line pattern. A raw substring PREFILTER decides only which files to open the
lexer on; it can cause extra work, never a verdict. Self-test arms 21-24 pin
this: a comment, a block comment and a string literal containing the exact
flagged shape are all GREEN, and a real construct carrying a trailing comment
is still RED.

THE RATCHET
-----------
The tree has a live population, so this is a ratchet and not a flag day, in
the shape of `data/unchecked_decl_ratchet.json`:

  * `budget_total` -- every measured hit, reviewed or not, counts against it,
    and it may only go DOWN. Moving a site onto the allowlist therefore
    creates NO headroom for a new one: an allowlist entry changes who must
    look at a hit, never the accounting.
  * `per_file_caps` -- a cap per file, so a new skipping test cannot be paid
    for by a fix somewhere else. This is the `occurrences` discipline of the
    add_decl ratchet at file granularity, and it is what makes the ratchet
    bite on net-zero churn.
  * `shape_caps` -- the same, per shape.
  * `reviewed_sites` -- the allowlist for the genuine disjunctions (CLAUDE.md's
    11 of 17), keyed (file, test, shape) with an `occurrences` cap and a
    `reason`, and corroborated AT THE SITE: the test must carry a
    `// SELF-SKIP OK:` comment within SELF_SKIP_WINDOW lines above the flagged
    construct. A row in a JSON file cannot legalise a skip by itself -- that is
    the half of "only goes down" a number can never enforce, and it is the rule
    CLAUDE.md states as "a skip list that names a file is a suppression; a row
    that names a site, caps it, and points at the comment is an account".

`--update` re-mints the artifact from the tree and REFUSES to raise any cap or
the budget, so "only goes down" is mechanical rather than remembered.

PIN-LOCKED SITES
----------------
`reviewed_sites` needs a comment AT the construct, and the budget needs a fix
to come down. Neither is possible in a file this repository may not edit:
Trust pins Clean main only while `crates/clean-kernel` and
`crates/clean-features` stay byte-identical to the copies trust-ir pins, so a
change there waits for a cross-repo pin train (docs/DECISIONS.md R90). Until
2026-10-16 that left one honest answer to a hit there -- raise the budget --
and that is the answer this gate exists to refuse. Measured that day: 968
against 967, the one new hit being
`crates/clean-kernel/src/tc/deadline_tests.rs:88`.

`pin_locked_sites` is the account for exactly that case and nothing wider.
A row names ONE construct -- file, test, shape and LINE -- in a file under
PIN_LOCKED_PREFIXES, with the sha256 of that file's bytes, `genuine_skip` and
a reason that say whether the guard is a genuine skip path, the exact test
edit owed at the next pin train (`owed_edit`), and the document recording that
debt (`recorded_in`, which must name both the file and the test: the
corroboration the at-site comment would have been). The construct it names is
accounted by the row instead of by the budget, so the row creates no
headroom: the budget, the shape caps and the per-file caps still bind every
other hit, a second construct in the same file is a new uncapped hit, and ANY
edit to the file -- which is to say the pin train itself -- moves its digest
and turns the row RED until the owed edit lands and the row is deleted. A row
outside PIN_LOCKED_PREFIXES is refused: a file this repository can edit takes
a fix or a `// SELF-SKIP OK:` comment, never an account in a JSON file. A row
that fails any check accounts for nothing, so its construct falls back on the
budget and the caps.

Exit codes: 0 accounted, 1 over budget / over a cap / stale row / missing
corroboration / unreadable file, 2 self-test failure.

Usage:
    python3 scripts/check_self_skipping_tests.py
    python3 scripts/check_self_skipping_tests.py --list
    python3 scripts/check_self_skipping_tests.py --json
    python3 scripts/check_self_skipping_tests.py --update
    python3 scripts/check_self_skipping_tests.py --selftest
"""

from __future__ import annotations

import contextlib
import datetime
import hashlib
import io
import json
import os
import re
import shutil
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_REL = Path("data") / "self_skipping_test_ratchet.json"

# The scope, PINNED IN CODE and re-derived against the artifact's own
# `scan_roots` on every run, so widening or narrowing it is a reviewed edit in
# two places rather than a silent one in either. `crates` is the cargo
# workspace; `bench-runner` and `fuzz` are workspace-EXCLUDED (Cargo.toml
# `exclude`) but hold real `#[test]`s that a lane runs by hand. Deliberately
# out of scope: `scratch/`, `scripts/*/`, `.claude/` (agent scratch and helper
# projects, none of them on a runner's path) and any untracked sandbox a lane
# leaves in the repo root -- measured 2026-09-16, a `scratchpad/` holding seven
# clones of this repo was present and would have multiplied every count by 8.
SCAN_ROOTS = ("crates", "bench-runner", "fuzz")

# Directories never walked. `target` is pruned for COST, not policy: it held
# 2,340,398 entries on this box (CLAUDE.md, *Machine limits*).
SKIP_DIRS = {"target", "node_modules"}

SELF_SKIP_WINDOW = 12
SELF_SKIP_RE = re.compile(r"//.*\bSELF-SKIP OK\b")

# The paths this repository may not edit outside a cross-repo pin train
# (docs/DECISIONS.md R90, and the PIN-LOCKED SITES section above). The ONLY
# files a `pin_locked_sites` row may name. Widening this is a decision, not a
# convenience: a file outside it takes a fix or a `// SELF-SKIP OK:` comment.
PIN_LOCKED_PREFIXES = ("crates/clean-kernel/", "crates/clean-features/")
_SHA256_HEX_RE = re.compile(r"\A[0-9a-f]{64}\Z")
PIN_LOCKED_TEXT_FIELDS = ("file", "test", "shape", "reason", "owed_edit",
                          "reviewed_by", "recorded_in")

SHAPES = ("SILENT_MATCH_ARM", "GUARDED_ASSERTIONS", "EARLY_RETURN")

# ---------------------------------------------------------------------------
# the lexer: comments and literals blanked, line geometry preserved
# ---------------------------------------------------------------------------

# Byte-identical to scripts/check_add_decl_ratchet.py's NONCODE_RE. Ordered
# alternation matters: a `//` inside a string literal must not win, so block
# and line comments come first, then raw strings (whose `#`-fence
# backreference makes them unambiguous), then plain strings, then chars.
NONCODE_RE = re.compile(
    r"/\*.*?\*/"                    # block comment (non-nested)
    r"|//[^\n]*"                    # line comment
    r'|(?:b?r)(#*)"(?:.|\n)*?"\1'   # raw string   r"..."  r#"..."#
    r'|b?"(?:\\.|[^"\\])*"'         # string literal
    r"|'(?:\\.|[^\\'])'",           # char literal
    re.DOTALL,
)


def _blank(match: re.Match[str]) -> str:
    """Replace a non-code span with spaces, preserving newlines, so a hit's
    reported line still indexes the ORIGINAL file."""
    return "".join("\n" if ch == "\n" else " " for ch in match.group(0))


def strip_noncode(text: str) -> str:
    """Blank out comments and string/raw-string/char literals."""
    return NONCODE_RE.sub(_blank, text)


# ---------------------------------------------------------------------------
# balanced-delimiter primitives
#
# `finditer` over the delimiter class rather than a per-character Python loop:
# the same answer, and it moves the scan into the regex engine. Measured over
# this tree, 54,259 test functions: 7.9 s -> 1.6 s.
# ---------------------------------------------------------------------------

_BRACE_RE = re.compile(r"[{}]")
_PAREN_RE = re.compile(r"[()]")
_DELIMS = {"{": _BRACE_RE, "(": _PAREN_RE, "[": re.compile(r"[\[\]]")}


def _bal(src: str, open_idx: int) -> int:
    """Index of the delimiter closing the one at `open_idx`, or -1."""
    opener = src[open_idx]
    rx = _DELIMS.get(opener)
    if rx is None:
        return -1
    depth = 0
    for m in rx.finditer(src, open_idx):
        depth += 1 if m.group() == opener else -1
        if depth == 0:
            return m.start()
    return -1


def _skip_ws(src: str, i: int) -> int:
    n = len(src)
    while i < n and src[i].isspace():
        i += 1
    return i


def _rfind_open(src: str, close_idx: int) -> int:
    """Index of the `(` matching the `)` at `close_idx`, or -1."""
    depth = 0
    i = close_idx
    while i >= 0:
        if src[i] == ")":
            depth += 1
        elif src[i] == "(":
            depth -= 1
            if depth == 0:
                return i
        i -= 1
    return -1


# ---------------------------------------------------------------------------
# finding `#[test]` functions
# ---------------------------------------------------------------------------

# `#[test]`, `#[tokio::test]`, `#[async_std::test]`. NOT `#[cfg(test)]`: the
# pattern admits only a `::`-path before `test`, and `cfg(test)` carries a
# paren. Pinned by self-test arm 24.
TEST_ATTR_RE = re.compile(r"#\[\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*test\s*\]")
_FN_RE = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)")
# What may sit between the attribute and its `fn`: more attributes, doc
# comments (already blanked), visibility, `async`, `unsafe`, `extern "C"`.
_ATTR_TO_FN_RE = re.compile(r"[\s\]\[#!,:()=<>\"'A-Za-z0-9_.+*/-]*")


def find_test_fns(code: str) -> list[dict]:
    """Every `#[test]` function in the BLANKED text, with its body span."""
    out = []
    for m in TEST_ATTR_RE.finditer(code):
        i = m.end()
        fnm = _FN_RE.search(code, i, i + 600)
        if not fnm:
            continue
        between = code[i:fnm.start()]
        # A `{`, a `;` or another `fn` between the attribute and this `fn`
        # means the attribute does not annotate it.
        if "{" in between or ";" in between or not _ATTR_TO_FN_RE.fullmatch(between):
            continue
        j = code.find("(", fnm.end())
        if j < 0:
            continue
        k = _bal(code, j)
        if k < 0:
            continue
        b = code.find("{", k)
        if b < 0:
            continue
        end = _bal(code, b)
        if end < 0:
            continue
        out.append(
            {
                "name": fnm.group(1),
                "body_start": b,
                "body_end": end,
            }
        )
    return out


# ---------------------------------------------------------------------------
# what counts as an assertion, and what counts as a failure
# ---------------------------------------------------------------------------

ASSERT_RE = re.compile(
    r"\b(?:debug_)?assert(?:_eq|_ne|_matches)?\s*!"
    r"|\bpanic\s*!"
    r"|\bunreachable\s*!"
    r"|\btodo\s*!"
    r"|\bunimplemented\s*!"
    r"|\.\s*unwrap\s*\("
    r"|\.\s*expect\s*\("
    r"|\.\s*unwrap_err\s*\("
    r"|\.\s*expect_err\s*\("
)

# A body that can make the test FAIL. `return Err(` fails a `-> Result` test,
# which is the opposite of skipping it.
FAILS_RE = re.compile(
    ASSERT_RE.pattern
    + r"|\breturn\s+Err\s*\("
    + r"|\bstd\s*::\s*process\s*::\s*exit\s*\("
    + r"|\bbail\s*!"
)

_PURE_FAILURE_RE = re.compile(
    r"\A\s*(?:panic|unreachable|todo|unimplemented)\s*!\s*[\(\[\{].*[\)\]\}]\s*;?\s*\Z",
    re.DOTALL,
)
_PURE_ASSERT_FALSE_RE = re.compile(
    r"\A\s*(?:debug_)?assert\s*!\s*\(\s*false\b.*\)\s*;?\s*\Z", re.DOTALL
)
# Deliberately NOT `assert`: `assert!(cond)` as the last statement fails only
# when `cond` is false, so it does not make the fall-through path fail. Reading
# it as one cost a self-test arm before it cost anything else -- the let-else
# case below went silently GREEN because its trailing `assert!(shim.exists())`
# was read as an unconditional failure. `assert!(false ..)` IS one and is
# matched separately.
_FAIL_MACRO_HEAD_RE = re.compile(
    r"(?:panic|unreachable|todo|unimplemented)\s*!\s*\Z"
)
_TAIL_ASSERT_FALSE_RE = re.compile(r"(?:debug_)?assert\s*!\s*\(\s*false\b")

# ASSERT_RE without `.unwrap(` / `.expect(`: a REAL assertion about the subject,
# not an incidental unwrap on setup I/O. Used only by the early-return rule
# below, where the looser spelling would let a `let _ = fs::write(p).expect(..)`
# in a skip branch excuse the skip it is performing.
_REAL_ASSERT_RE = re.compile(
    r"\b(?:debug_)?assert(?:_eq|_ne|_matches)?\s*!"
    r"|\bpanic\s*!"
    r"|\bunreachable\s*!"
    r"|\btodo\s*!"
    r"|\bunimplemented\s*!"
)


def _unbrace(block: str) -> str:
    b = block.strip()
    if b.startswith("{") and b.endswith("}"):
        return b[1:-1]
    return b


def can_fail(block: str) -> bool:
    return bool(FAILS_RE.search(block))


def asserts(block: str) -> bool:
    return bool(ASSERT_RE.search(block))


def is_pure_failure(block: str) -> bool:
    """A body that does nothing but fail.

    `Ok(_) => panic!("expected an error")` beside `Err(_) => {}` is a match
    that IS an assertion: one arm always runs and the outcome is decided
    either way. Flagging it would be flagging the correct spelling.
    """
    inner = _unbrace(block)
    return bool(_PURE_FAILURE_RE.match(inner) or _PURE_ASSERT_FALSE_RE.match(inner))


def tail_is_unconditional_failure(body_inner: str) -> bool:
    """Does the body's LAST statement fail unconditionally?

    The fall-through idiom:

        if let Code::Let(..) = x { .. assert_eq!(..); return; }
        panic!("Expected simplified projection");

    Every skip path in such a body lands on that panic, so no assertion is
    skippable and none of the three shapes applies. Measured 2026-09-16:
    40 hits across 9 files in this tree are of exactly this shape.
    """
    s = body_inner.rstrip()
    if s.endswith(";"):
        s = s[:-1].rstrip()
    if not s.endswith(")"):
        return False
    o = _rfind_open(s, len(s) - 1)
    if o < 0:
        return False
    if _FAIL_MACRO_HEAD_RE.search(s[:o]):
        return True
    return bool(_TAIL_ASSERT_FALSE_RE.search(s[max(0, o - 40):]))


# ---------------------------------------------------------------------------
# shape 1: a silent `Err(..)` / `_` match arm beside an asserting sibling
# ---------------------------------------------------------------------------

_MATCH_RE = re.compile(r"\bmatch\b")
_ERR_PAT_RE = re.compile(r"\bErr\b")
_WILDCARD_PAT_RE = re.compile(r"\A\s*_\s*\Z")


def _match_body(code: str, at: int, hi: int) -> tuple[int, int]:
    """(open, close) of the `{ .. }` of the `match` whose keyword is at `at`.

    Rust forbids a bare struct expression in scrutinee position, so the first
    `{` at paren/bracket depth zero after the keyword opens the arm list.
    """
    i = at + 5
    depth = 0
    while i < hi:
        ch = code[i]
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ch == "{" and depth <= 0:
            return (i, _bal(code, i))
        elif ch == ";" and depth <= 0:
            return (-1, -1)
        i += 1
    return (-1, -1)


def _split_arms(code: str, open_idx: int, close_idx: int) -> list[dict] | None:
    """Arms of a match body, or None when the shape is not parseable."""
    arms: list[dict] = []
    i = open_idx + 1
    while True:
        i = _skip_ws(code, i)
        if i >= close_idx:
            break
        depth = 0
        j = i
        arrow = -1
        while j < close_idx:
            ch = code[j]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == "=" and depth == 0 and code[j + 1:j + 2] == ">":
                arrow = j
                break
            j += 1
        if arrow < 0:
            return None
        pattern = code[i:arrow]
        b = _skip_ws(code, arrow + 2)
        if b >= close_idx:
            return None
        if code[b] == "{":
            e = _bal(code, b)
            if e < 0 or e > close_idx:
                return None
            body = code[b:e + 1]
            nxt = _skip_ws(code, e + 1)
            if nxt < close_idx and code[nxt] == ",":
                nxt += 1
        else:
            depth = 0
            j = b
            while j < close_idx:
                ch = code[j]
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                elif ch == "," and depth == 0:
                    break
                j += 1
            body = code[b:j]
            nxt = j + 1
        arms.append({"pattern": pattern, "body": body, "at": i})
        i = nxt
    return arms


def _silent_match_arms(code: str, lo: int, hi: int) -> list[tuple[int, str]]:
    out = []
    for m in _MATCH_RE.finditer(code, lo, hi):
        open_idx, close_idx = _match_body(code, m.start(), hi)
        if open_idx < 0 or close_idx < 0 or close_idx > hi:
            continue
        arms = _split_arms(code, open_idx, close_idx)
        if arms is None:
            continue
        if not any(asserts(a["body"]) and not is_pure_failure(a["body"]) for a in arms):
            continue
        for a in arms:
            if can_fail(a["body"]):
                continue
            pat = a["pattern"]
            if _ERR_PAT_RE.search(pat):
                out.append((a["at"], "silent `Err` arm beside an asserting arm"))
            elif _WILDCARD_PAT_RE.match(pat):
                out.append((a["at"], "silent catch-all `_` arm beside an asserting arm"))
    return out


# ---------------------------------------------------------------------------
# shape 2: `if let Ok(..) = e { assert.. }` with no failing else
# ---------------------------------------------------------------------------

_IF_LET_RE = re.compile(r"\bif\s+let\b")
_GUARD_CTOR_RE = re.compile(r"\A\s*(?:&\s*)?(?:Ok|Some)\s*\(")
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_PREASSERT_RE = re.compile(r"\b(?:debug_)?assert(?:_eq|_ne)?\s*!\s*\(")


def _preasserted(code: str, lo: int, at: int, scrutinee: str) -> bool:
    """Was the scrutinee already asserted present before the guard?

        assert!(result.is_some(), "...");
        if let Some(inst) = result { assert_eq!(..); }

    The guard cannot fail without the assert having failed first, so nothing
    is skipped. Measured 2026-09-16: 36 hits across 17 files in this tree,
    e.g. crates/clean-elab/src/infer/tests/instance.rs.
    """
    idents = set(_IDENT_RE.findall(scrutinee))
    if not idents:
        return False
    for a in _PREASSERT_RE.finditer(code, lo, at):
        o = code.find("(", a.end() - 1)
        c = _bal(code, o)
        if c < 0:
            continue
        arg = code[o:c]
        if ("is_some" in arg or "is_ok" in arg or "matches!" in arg) and (
            idents & set(_IDENT_RE.findall(arg))
        ):
            return True
    return False


def _else_chain_end(code: str, at: int, hi: int) -> int:
    """End index of an `else ...` chain starting at `at`."""
    i = _skip_ws(code, at + 4)
    while i < hi:
        if code[i] == "{":
            e = _bal(code, i)
            if e < 0:
                return hi
            nxt = _skip_ws(code, e + 1)
            if code[nxt:nxt + 4] == "else":
                i = _skip_ws(code, nxt + 4)
                continue
            return e + 1
        i += 1
    return hi


def _guarded_assertions(code: str, lo: int, hi: int) -> list[tuple[int, str]]:
    out = []
    for m in _IF_LET_RE.finditer(code, lo, hi):
        depth = 0
        j = m.end()
        eq = -1
        while j < hi:
            ch = code[j]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == "=" and depth == 0:
                if code[j + 1:j + 2] in ("=", ">") or code[j - 1:j] in ("=", "!", "<", ">"):
                    j += 1
                    continue
                eq = j
                break
            j += 1
        if eq < 0:
            continue
        pattern = code[m.end():eq]
        if not _GUARD_CTOR_RE.match(pattern):
            continue
        depth = 0
        j = eq + 1
        blk = -1
        while j < hi:
            ch = code[j]
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            elif ch == "{" and depth <= 0:
                blk = j
                break
            elif ch == ";" and depth <= 0:
                break
            j += 1
        if blk < 0:
            continue
        end = _bal(code, blk)
        if end < 0 or end > hi:
            continue
        block = code[blk:end + 1]
        if not asserts(block) or is_pure_failure(block):
            continue
        if _preasserted(code, lo, m.start(), code[eq + 1:blk]):
            continue
        nxt = _skip_ws(code, end + 1)
        if code[nxt:nxt + 4] == "else" and not (code[nxt + 4:nxt + 5] or " ").isalnum():
            if can_fail(code[nxt:_else_chain_end(code, nxt, hi)]):
                continue
            out.append((m.start(), "`if let` guard whose else chain cannot fail"))
        else:
            out.append((m.start(), "`if let` guard with assertions and no else"))
    return out


# ---------------------------------------------------------------------------
# shape 3: an early `return` that makes the rest of the test optional
# ---------------------------------------------------------------------------

_SCOPE_RE = re.compile(r"[{}]|\breturn\b")
_CLOSURE_HEAD_RE = re.compile(r"\|\s*(?:->\s*[^{;|]*?\s*)?\Z", re.DOTALL)
_ASYNC_HEAD_RE = re.compile(r"\basync\s*(?:move\s*)?\Z")
_FN_HEAD_RE = re.compile(r"\bfn\s+[A-Za-z_][A-Za-z0-9_]*\s*(?:<[^{};]*>)?\s*\Z")
_FN_TAIL_RE = re.compile(r"\)\s*(?:->[^{};]*)?\Z")
_RETURN_OK_RE = re.compile(r"\A(?:\(\s*\)|Ok\s*[\(\{])")
_RETURN_ERR_RE = re.compile(r"\AErr\s*\(")


def _is_foreign_block(code: str, lo: int, open_idx: int) -> bool:
    """Does the `{` at `open_idx` open a closure, an `async` block or a
    nested `fn`? A `return` inside one returns from THAT, not from the test."""
    pre = code[max(lo, open_idx - 200):open_idx]
    if _CLOSURE_HEAD_RE.search(pre) or _ASYNC_HEAD_RE.search(pre):
        return True
    r = pre.rstrip()
    if _FN_HEAD_RE.search(r):
        return True
    # `fn helper(x: u32) {` and `fn helper(x: u32) -> u32 {`: the head ends
    # with a parameter list, optionally followed by a return type.
    m = _FN_TAIL_RE.search(r)
    if m:
        o = _rfind_open(r, m.start())
        if o >= 0 and _FN_HEAD_RE.search(r[:o]):
            return True
    return False


def _early_returns(code: str, lo: int, hi: int) -> list[tuple[int, str]]:
    """One left-to-right pass: brace positions and `return`s together."""
    out = []
    foreign_depth = 0
    stack: list[tuple[int, bool]] = []
    for m in _SCOPE_RE.finditer(code, lo, hi):
        tok = m.group()
        if tok == "{":
            foreign = _is_foreign_block(code, lo, m.start())
            stack.append((m.start(), foreign))
            if foreign:
                foreign_depth += 1
            continue
        if tok == "}":
            if stack and stack.pop()[1]:
                foreign_depth -= 1
            continue
        if foreign_depth:
            continue
        # The skip path is not SILENT if the branch taking it asserts on its way
        # out. This is the rule `can_fail` already applies to a silent match arm
        # and to an `if let` else chain, applied to the third shape for the same
        # reason -- and without it this gate flags the very remediation its own
        # failure message prescribes. MEASURED 2026-09-16, nine hits across
        # eight files, e.g. crates/clean-compiler/src/emit_wasm_tests.rs, whose
        # skip branch asserts the module is well formed and says in a comment
        # that it does so "so this test is never a silent no-op", and
        # crates/clean-cli/src/cmd_replacement/tests/part_08.rs, an ordinary
        # two-way branch that asserts on both paths.
        #
        # `stack` is empty when the `return` sits at TEST level rather than in a
        # branch, and the window starts at the enclosing block's own `{`: an
        # assertion earlier in the TEST does not excuse a nested skip, which is
        # pinned in both directions by the two SHAPE_CASES rows named
        # "a return whose own skip path asserts" / "an assertion BEFORE the
        # branch".
        if stack and _REAL_ASSERT_RE.search(code[stack[-1][0] + 1:m.start()]):
            continue
        depth = 0
        j = m.end()
        while j < hi:
            ch = code[j]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                if depth == 0:
                    break
                depth -= 1
            elif ch == ";" and depth == 0:
                break
            j += 1
        expr = code[m.end():j].strip()
        if can_fail(expr) or _RETURN_ERR_RE.match(expr):
            continue
        if expr and not _RETURN_OK_RE.match(expr):
            # returning some other value: not the silent-pass shape
            continue
        if not ASSERT_RE.search(code[j:hi]):
            continue
        what = "bare `return`" if not expr else "`return " + expr[:16].strip() + "`"
        out.append((m.start(), what + " skips the assertions after it"))
    return out


# ---------------------------------------------------------------------------
# per-file scan
# ---------------------------------------------------------------------------


def _line_of(text: str, idx: int) -> int:
    return text.count("\n", 0, idx) + 1


def scan_text(text: str, rel: str) -> list[dict]:
    """Every self-skipping construct in one file's ORIGINAL text."""
    code = strip_noncode(text)
    hits: list[dict] = []
    for fn in find_test_fns(code):
        lo, hi = fn["body_start"] + 1, fn["body_end"]
        if tail_is_unconditional_failure(code[lo:hi]):
            continue
        found = (
            [(p, w, "SILENT_MATCH_ARM") for p, w in _silent_match_arms(code, lo, hi)]
            + [(p, w, "GUARDED_ASSERTIONS") for p, w in _guarded_assertions(code, lo, hi)]
            + [(p, w, "EARLY_RETURN") for p, w in _early_returns(code, lo, hi)]
        )
        for pos, why, shape in found:
            hits.append(
                {
                    "file": rel,
                    "test": fn["name"],
                    "shape": shape,
                    "line": _line_of(text, pos),
                    "why": why,
                }
            )
    hits.sort(key=lambda h: (h["line"], h["shape"]))
    return hits


def iter_rust_files(root: Path):
    """Every `.rs` file under `root`, with build and dot directories pruned.

    The walk prunes and the `glob("*.rs")` selects: the pruning is what keeps
    this off `target/`, and the glob is the spelling `check_gate_registry.py`'s
    R9 `READS_SOURCE` detector recognises, so this gate's `source_scan`
    declaration is re-derived from the code rather than taken on trust.
    """
    for dirpath, dirnames, _filenames in os.walk(root):
        dirnames[:] = sorted(
            d for d in dirnames if d not in SKIP_DIRS and not d.startswith(".")
        )
        for path in sorted(Path(dirpath).glob("*.rs")):
            yield path


def measure(root: Path) -> tuple[list[dict], list[str]]:
    hits: list[dict] = []
    errors: list[str] = []
    for sub in SCAN_ROOTS:
        base = root / sub
        if not base.is_dir():
            continue
        for path in iter_rust_files(base):
            rel = str(path.relative_to(root)).replace("\\", "/")
            try:
                text = path.read_text(errors="strict")
            except (OSError, UnicodeDecodeError) as exc:
                # fail closed: a file this cannot read is not a clean one
                errors.append(f"cannot read {rel}: {exc}")
                continue
            if not TEST_ATTR_RE.search(text):
                continue
            hits.extend(scan_text(text, rel))
    hits.sort(key=lambda h: (h["file"], h["line"], h["shape"]))
    return hits, errors


# ---------------------------------------------------------------------------
# the ratchet
# ---------------------------------------------------------------------------


def load_ratchet(root: Path) -> dict | None:
    try:
        return json.loads((root / RATCHET_REL).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def has_self_skip_comment(root: Path, rel: str, lineno: int) -> bool:
    """A `// SELF-SKIP OK:` comment within SELF_SKIP_WINDOW lines above the
    construct. The corroboration an allowlist row cannot supply itself."""
    try:
        lines = (root / rel).read_text(errors="strict").splitlines()
    except (OSError, UnicodeDecodeError):
        return False
    lo = max(0, lineno - 1 - SELF_SKIP_WINDOW)
    return any(SELF_SKIP_RE.search(x) for x in lines[lo:lineno])


def _hit_key(h: dict) -> tuple:
    return (h["file"], h["test"], h["shape"], h["line"])


def pin_locked_accounts(root: Path, ratchet: dict, hits: list[dict]) -> tuple[set, list[str]]:
    """The live constructs `pin_locked_sites` accounts for, and every problem
    with the rows.

    A key is covered only by a row that passes EVERY check below; a row that
    fails one covers nothing, so its construct falls back on the budget and
    the caps -- a broken account never hides a hit.
    """
    rows = ratchet.get("pin_locked_sites", [])
    if not isinstance(rows, list):
        return set(), [f"pin_locked_sites is {type(rows).__name__}, not a list"]
    live = {_hit_key(h) for h in hits}
    covered: set = set()
    problems: list[str] = []
    for row in rows:
        if not isinstance(row, dict):
            problems.append(f"pin_locked_sites carries a non-object row {row!r}")
            continue
        label = (f"{row.get('file')}:{row.get('line')} / {row.get('test')} / "
                 f"{row.get('shape')}")
        bad = [f for f in PIN_LOCKED_TEXT_FIELDS if not str(row.get(f) or "").strip()]
        if bad:
            problems.append(f"pin_locked_sites row {label} has no {', '.join(bad)}")
            continue
        line, digest = row.get("line"), row.get("file_sha256")
        if not isinstance(line, int) or isinstance(line, bool) or line < 1:
            problems.append(f"pin_locked_sites row {label} has line={line!r}; it names "
                            f"ONE construct by its line")
            continue
        if not isinstance(digest, str) or not _SHA256_HEX_RE.match(digest):
            problems.append(f"pin_locked_sites row {label} has no 64-hex file_sha256")
            continue
        if not isinstance(row.get("genuine_skip"), bool):
            problems.append(f"pin_locked_sites row {label} has no boolean genuine_skip: "
                            f"the review must say whether the guard can skip at all")
            continue
        if "occurrences" in row:
            problems.append(f"pin_locked_sites row {label} carries `occurrences`; a "
                            f"pin-locked row accounts for exactly one construct")
            continue
        rel = row["file"]
        if not rel.startswith(PIN_LOCKED_PREFIXES):
            problems.append(
                f"pin_locked_sites row {label} names a file outside "
                f"{', '.join(PIN_LOCKED_PREFIXES)}. This repository can edit it: fix the "
                f"skip, or review it into reviewed_sites with a `// SELF-SKIP OK:` comment.")
            continue
        if row["shape"] not in SHAPES:
            problems.append(f"pin_locked_sites row {label} names an unknown shape")
            continue
        key = (rel, row["test"], row["shape"], line)
        if key in covered:
            problems.append(f"pin_locked_sites names {label} twice")
            continue
        if key not in live:
            problems.append(
                f"pin_locked_sites row {label} matches no live construct. If the pin train "
                f"paid the owed edit, delete the row; if the construct moved, it is a new "
                f"review, not a carried-over one.")
            continue
        try:
            now = hashlib.sha256((root / rel).read_bytes()).hexdigest()
        except OSError as exc:
            problems.append(f"pin_locked_sites row {label}: cannot read {rel}: {exc}")
            continue
        if now != digest:
            problems.append(
                f"pin_locked_sites row {label}: {rel} is no longer the file the row "
                f"reviewed (sha256 {digest[:12]} -> {now[:12]}). A pin-locked file changes "
                f"only in a pin train, and that train owes this edit: "
                f"{row['owed_edit']}")
            continue
        rec = Path(row["recorded_in"])
        if rec.is_absolute() or ".." in rec.parts:
            problems.append(f"pin_locked_sites row {label}: recorded_in "
                            f"{row['recorded_in']!r} is not a path inside this repository")
            continue
        doc = root / rec
        try:
            text = doc.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            problems.append(f"pin_locked_sites row {label}: recorded_in "
                            f"{row['recorded_in']!r} cannot be read")
            continue
        if rel not in text or row["test"] not in text:
            problems.append(
                f"pin_locked_sites row {label}: {row['recorded_in']} does not name both "
                f"{rel} and {row['test']}. The owed edit is recorded there, or the row is "
                f"an unrecorded debt.")
            continue
        covered.add(key)
    return covered, problems


def _mint(hits: list[dict], prev: dict | None, root: Path | None = None) -> dict:
    from collections import Counter

    prev = prev or {}
    if root is not None:
        covered, _problems = pin_locked_accounts(root, prev, hits)
        hits = [h for h in hits if _hit_key(h) not in covered]
    per_file = Counter(h["file"] for h in hits)
    per_shape = Counter(h["shape"] for h in hits)
    return {
        "schema": "clean.self-skipping-test-ratchet/v1",
        "what_this_is": (
            "Tests that can skip their own assertions at run time, measured by "
            "scripts/check_self_skipping_tests.py. Every hit counts toward "
            "budget_total and its file's cap whether or not it is allowlisted, so "
            "reviewing a site creates no headroom for a new one. Caps only go DOWN: "
            "`--update` refuses to raise any of them. The one exception is a "
            "pin_locked_sites row: one construct in a file this repository may not "
            "edit outside a pin train, pinned by line and by the file's sha256, with "
            "the test edit that train owes; it turns RED the moment the file changes."
        ),
        "scan_roots": list(SCAN_ROOTS),
        "shapes": list(SHAPES),
        "budget_total": len(hits),
        "shape_caps": {s: per_shape.get(s, 0) for s in SHAPES},
        "per_file_caps": dict(sorted(per_file.items())),
        "reviewed_sites": prev.get("reviewed_sites", []),
        "pin_locked_sites": prev.get("pin_locked_sites", []),
        "last_updated": datetime.date.today().isoformat(),
    }


def run(root: Path, list_only: bool = False, as_json: bool = False) -> int:
    ratchet = load_ratchet(root)
    if ratchet is None:
        print(f"FAIL: cannot read {RATCHET_REL} (a ratchet that cannot be read is "
              f"not an empty one)", file=sys.stderr)
        return 1
    hits, errors = measure(root)

    if as_json:
        print(json.dumps({"hits": hits, "errors": errors}, indent=2))
        return 0
    if list_only:
        for h in hits:
            print(f"{h['file']}:{h['line']}  {h['test']}  {h['shape']}  -- {h['why']}")
        print(f"total: {len(hits)}")
        return 0

    ok = True
    for e in errors:
        ok = False
        print(f"FAIL: {e}", file=sys.stderr)

    declared_roots = ratchet.get("scan_roots")
    if declared_roots != list(SCAN_ROOTS):
        ok = False
        print(
            f"FAIL: {RATCHET_REL} declares scan_roots={declared_roots!r} but this "
            f"scanner scans {list(SCAN_ROOTS)!r}. The scope is an account: widening "
            f"or narrowing it is a reviewed edit in BOTH places, never a silent one "
            f"in either.",
            file=sys.stderr,
        )

    from collections import Counter

    # A pin-locked row accounts for its ONE construct; every other hit -- a
    # second one in the same file included -- is counted below as before.
    pin_locked, pin_problems = pin_locked_accounts(root, ratchet, hits)
    for p in pin_problems:
        ok = False
        print(f"FAIL: {p}", file=sys.stderr)
    all_hits = hits
    hits = [h for h in hits if _hit_key(h) not in pin_locked]

    per_file = Counter(h["file"] for h in hits)
    per_shape = Counter(h["shape"] for h in hits)
    caps = ratchet.get("per_file_caps") or {}
    budget = ratchet.get("budget_total")

    if not isinstance(budget, int):
        ok = False
        print(f"FAIL: {RATCHET_REL} has no integer budget_total", file=sys.stderr)
    elif len(hits) > budget:
        ok = False
        print(
            f"FAIL: {len(hits)} tests can skip their own assertions; the ratchet "
            f"budget_total is {budget}. A test whose assertions are conditional on "
            f"the thing they measure reports `ok` forever -- make the skip path FAIL "
            f"(panic/assert in the else or Err arm), or review the site into "
            f"reviewed_sites with a reason AND a `// SELF-SKIP OK:` comment at the "
            f"construct.",
            file=sys.stderr,
        )

    for f, n in sorted(per_file.items()):
        cap = caps.get(f)
        if cap is None:
            ok = False
            print(
                f"FAIL: {f} has {n} self-skipping test construct(s) and NO cap in "
                f"{RATCHET_REL}. A new one must be justified and ratcheted, never "
                f"absorbed.",
                file=sys.stderr,
            )
            for h in hits:
                if h["file"] == f:
                    print(f"    {f}:{h['line']}  {h['test']}  {h['shape']}  -- {h['why']}",
                          file=sys.stderr)
        elif n > cap:
            ok = False
            print(
                f"FAIL: {f} has {n} self-skipping test construct(s), capped at {cap}. "
                f"A fix somewhere else does not pay for a new one here.",
                file=sys.stderr,
            )
            for h in hits:
                if h["file"] == f:
                    print(f"    {f}:{h['line']}  {h['test']}  {h['shape']}  -- {h['why']}",
                          file=sys.stderr)

    shape_caps = ratchet.get("shape_caps") or {}
    for s in SHAPES:
        cap = shape_caps.get(s)
        if not isinstance(cap, int):
            ok = False
            print(f"FAIL: {RATCHET_REL} has no integer shape_caps[{s}]", file=sys.stderr)
        elif per_shape.get(s, 0) > cap:
            ok = False
            print(
                f"FAIL: shape {s} measured {per_shape.get(s, 0)}, capped at {cap}.",
                file=sys.stderr,
            )

    # The allowlist. A row must name a LIVE site, cap it, carry a reason, and be
    # corroborated by a `// SELF-SKIP OK:` comment at the construct itself.
    live = Counter((h["file"], h["test"], h["shape"]) for h in hits)
    for row in ratchet.get("reviewed_sites") or []:
        if not isinstance(row, dict):
            ok = False
            print(f"FAIL: reviewed_sites carries a non-object row {row!r}", file=sys.stderr)
            continue
        key = (row.get("file"), row.get("test"), row.get("shape"))
        label = f"{key[0]} / {key[1]} / {key[2]}"
        if not str(row.get("reason") or "").strip():
            ok = False
            print(f"FAIL: reviewed_sites row {label} has no reason", file=sys.stderr)
        if not str(row.get("reviewed_by") or "").strip():
            ok = False
            print(f"FAIL: reviewed_sites row {label} has no reviewed_by", file=sys.stderr)
        seen = live.get(key, 0)
        if seen == 0:
            ok = False
            print(
                f"FAIL: reviewed_sites row {label} matches no live construct. If the "
                f"skip was fixed, remove the row and lower the caps (the ratchet only "
                f"goes down); debt is not allowed to evaporate unremarked.",
                file=sys.stderr,
            )
            continue
        occ = row.get("occurrences", 1)
        if not isinstance(occ, int) or occ < 1:
            ok = False
            print(
                f"FAIL: reviewed_sites row {label} has occurrences={occ!r}; a cap of "
                f"zero or a missing cap is not unlimited.",
                file=sys.stderr,
            )
        elif seen > occ:
            ok = False
            print(
                f"FAIL: reviewed_sites row {label} covers {occ} construct(s) but {seen} "
                f"are live. A reviewed site does not license further copies of itself.",
                file=sys.stderr,
            )
        for h in hits:
            if (h["file"], h["test"], h["shape"]) != key:
                continue
            if not has_self_skip_comment(root, h["file"], h["line"]):
                ok = False
                print(
                    f"FAIL: {h['file']}:{h['line']} is allowlisted in {RATCHET_REL} but "
                    f"carries no `// SELF-SKIP OK:` comment within {SELF_SKIP_WINDOW} "
                    f"lines above the construct. A JSON row cannot legalise a skip by "
                    f"itself.",
                    file=sys.stderr,
                )

    if ok:
        slack = budget - len(hits)
        shapes = ", ".join(f"{s.lower()}={per_shape.get(s, 0)}" for s in SHAPES)
        print(
            f"OK: self-skipping tests {len(hits)}/{budget} across {len(per_file)} files "
            f"({shapes}); {len(ratchet.get('reviewed_sites') or [])} reviewed."
            + (f" {len(pin_locked)} of {len(all_hits)} measured pin-locked, each owed "
               f"at the next pin train (pin_locked_sites)." if pin_locked else "")
            + (f" {slack} under budget -- run --update to bank it." if slack else "")
        )
        return 0
    return 1


def update(root: Path) -> int:
    """Re-mint the artifact, REFUSING to raise any cap or the budget."""
    hits, errors = measure(root)
    if errors:
        for e in errors:
            print(f"FAIL: {e}", file=sys.stderr)
        return 1
    prev = load_ratchet(root) or {}
    doc = _mint(hits, prev, root)
    problems = []
    if isinstance(prev.get("budget_total"), int) and doc["budget_total"] > prev["budget_total"]:
        problems.append(
            f"budget_total {prev['budget_total']} -> {doc['budget_total']}")
    for f, n in doc["per_file_caps"].items():
        old = (prev.get("per_file_caps") or {}).get(f)
        if isinstance(old, int) and n > old:
            problems.append(f"per_file_caps[{f}] {old} -> {n}")
    for s, n in doc["shape_caps"].items():
        old = (prev.get("shape_caps") or {}).get(s)
        if isinstance(old, int) and n > old:
            problems.append(f"shape_caps[{s}] {old} -> {n}")
    if problems:
        print(
            "FAIL: --update refuses to RAISE a ratchet. This is the mechanism, not a "
            "hiccup: a new self-skipping test is a reviewed change, not a re-mint.",
            file=sys.stderr,
        )
        for p in problems:
            print(f"  {p}", file=sys.stderr)
        return 1
    (root / RATCHET_REL).write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    print(f"minted {RATCHET_REL}: budget_total={doc['budget_total']}, "
          f"{len(doc['per_file_caps'])} files")
    return 0


# ---------------------------------------------------------------------------
# self-test: a gate that has never been shown to fail is not a gate, and a gate
# that has never been shown to stay QUIET on the correct spelling gets deleted
# ---------------------------------------------------------------------------

# (name, rust snippet, expected shapes). The `[]` rows are the second
# direction: legitimate code this must NOT flag.
SHAPE_CASES: tuple[tuple[str, str, list[str]], ...] = (
    # ---- positives -------------------------------------------------------
    ("if-let guard with no else", """
#[test]
fn t() {
    let r = parse("x");
    if let Ok(v) = r {
        assert_eq!(v, 1);
    }
}
""", ["GUARDED_ASSERTIONS"]),
    ("if-let guard whose else cannot fail", """
#[test]
fn t() {
    if let Ok(v) = parse("x") {
        assert_eq!(v, 1);
    } else {
        eprintln!("skipped");
    }
}
""", ["GUARDED_ASSERTIONS"]),
    ("nested if-let guards", """
#[test]
fn t() {
    if let Ok(a) = one() {
        if let Ok(b) = two(a) {
            assert_eq!(b, 3);
        }
    }
}
""", ["GUARDED_ASSERTIONS", "GUARDED_ASSERTIONS"]),
    ("silent Err arm", """
#[test]
fn t() {
    match parse("x") {
        Ok(v) => {
            assert_eq!(v, 1);
        }
        Err(_) => {}
    }
}
""", ["SILENT_MATCH_ARM"]),
    ("silent catch-all arm", """
#[test]
fn t() {
    match kind() {
        Kind::A(v) => {
            assert_eq!(v, 1);
        }
        _ => {}
    }
}
""", ["SILENT_MATCH_ARM"]),
    ("Err arm that only logs", """
#[test]
fn t() {
    match parse("x") {
        Ok(v) => assert_eq!(v, 1),
        Err(e) => {
            eprintln!("skipping: {e}");
        }
    }
}
""", ["SILENT_MATCH_ARM"]),
    ("let-else with a bare return", """
#[test]
fn t() {
    let Some(shim) = sibling_shim() else {
        eprintln!("test skipped: shim not built");
        return;
    };
    assert!(shim.exists());
}
""", ["EARLY_RETURN"]),
    ("guarded early return", """
#[test]
fn t() {
    if fixture_is_stub() {
        eprintln!("SKIP: fixture is a stub");
        return;
    }
    validate(report()).expect("report should validate");
}
""", ["EARLY_RETURN"]),
    ("return Ok(()) from a Result test", """
#[test]
fn t() -> Result<(), String> {
    if !ready() {
        return Ok(());
    }
    assert_eq!(go()?, 1);
    Ok(())
}
""", ["EARLY_RETURN"]),
    ("tokio::test is a test too", """
#[tokio::test]
async fn t() {
    if let Ok(v) = fetch().await {
        assert_eq!(v, 1);
    }
}
""", ["GUARDED_ASSERTIONS"]),
    # ---- negatives: the correct spellings, which must stay quiet ----------
    ("if-let with a failing else", """
#[test]
fn t() {
    if let Ok(v) = parse("x") {
        assert_eq!(v, 1);
    } else {
        panic!("parse must succeed");
    }
}
""", []),
    ("if-let with an else-if chain that fails", """
#[test]
fn t() {
    if let Ok(v) = parse("x") {
        assert_eq!(v, 1);
    } else if slow() {
        assert!(false, "unreachable");
    } else {
        unreachable!();
    }
}
""", []),
    ("Err arm that panics", """
#[test]
fn t() {
    match parse("x") {
        Ok(v) => assert_eq!(v, 1),
        Err(e) => panic!("parse failed: {e}"),
    }
}
""", []),
    ("silent Err arm beside a PURE-failure Ok arm", """
#[test]
fn t() {
    match parse("bad") {
        Ok(_) => panic!("expected a parse error"),
        Err(_) => {}
    }
}
""", []),
    ("guarded block with no assertions", """
#[test]
fn t() {
    if let Ok(path) = tmp() {
        let _ = std::fs::remove_file(path);
    }
    assert_eq!(go(), 1);
}
""", []),
    ("fall-through to an unconditional panic", """
#[test]
fn t() {
    if let Code::Let(_, body) = simplified {
        match &body.value {
            LetValue::FVar { fvar: f, .. } => {
                assert_eq!(*f, fvar(10));
                return;
            }
            _ => {}
        }
    }
    panic!("Expected simplified projection");
}
""", []),
    ("destructure after asserting the scrutinee", """
#[test]
fn t() {
    let result = ctx.resolve_instance(&ty);
    assert!(result.is_some(), "Should resolve");
    if let Some(inst) = result {
        assert_eq!(inst.name(), "instAddNat");
    }
}
""", []),
    ("a return whose own skip path asserts is not a silent skip", """
#[test]
fn t() {
    let Some(actual) = run_on_host() else {
        assert_eq!(&module[0..4], b"\\0asm");
        eprintln!("NOTE: no host; execution leg SKIPPED, structure checked");
        return;
    };
    assert_eq!(actual, expected());
}
""", []),
    ("an assertion BEFORE the branch does not excuse a nested skip", """
#[test]
fn t() {
    assert_eq!(setup(), 1);
    if !ready() {
        eprintln!("SKIP");
        return;
    }
    assert_eq!(go(), 2);
}
""", ["EARLY_RETURN"]),
    ("return Err from a Result test FAILS it", """
#[test]
fn t() -> Result<(), String> {
    if !ready() {
        return Err("fixture missing".to_string());
    }
    assert_eq!(go(), 1);
    Ok(())
}
""", []),
    ("a return inside a closure returns from the closure", """
#[test]
fn t() {
    let f = |x: u32| {
        if x == 0 {
            return 0;
        }
        x + 1
    };
    assert_eq!(f(1), 2);
}
""", []),
    ("a return inside a nested fn", """
#[test]
fn t() {
    fn helper(x: u32) -> u32 {
        if x == 0 {
            return 0;
        }
        x
    }
    assert_eq!(helper(1), 1);
}
""", []),
    # ---- the anti-correlation arms: prose is not code ---------------------
    ("the shape inside a line comment is not code", """
#[test]
fn t() {
    // if let Ok(v) = parse("x") { assert_eq!(v, 1); }
    assert_eq!(go(), 1);
}
""", []),
    ("the shape inside a block comment is not code", """
#[test]
fn t() {
    /* match parse("x") { Ok(v) => { assert_eq!(v, 1); } Err(_) => {} } */
    assert_eq!(go(), 1);
}
""", []),
    ("the shape inside a string literal is not code", """
#[test]
fn t() {
    let doc = "if let Ok(v) = p { assert_eq!(v, 1); }";
    assert_eq!(doc.len(), 37);
}
""", []),
    ("a real construct with a comment after it is still flagged", """
#[test]
fn t() {
    if let Ok(v) = parse("x") { // no else on purpose
        assert_eq!(v, 1);
    }
}
""", ["GUARDED_ASSERTIONS"]),
    ("#[cfg(test)] is not #[test]", """
#[cfg(test)]
fn helper() {
    if let Ok(v) = parse("x") {
        assert_eq!(v, 1);
    }
}
""", []),
    ("a non-test fn beside a test is out of scope", """
fn helper() {
    if let Ok(v) = parse("x") {
        assert_eq!(v, 1);
    }
}

#[test]
fn t() {
    assert_eq!(helper2(), 1);
}
""", []),
)


def shape_case_failures() -> list[str]:
    """Cases this scanner answers differently from the table. Empty is right."""
    bad = []
    for name, src, want in SHAPE_CASES:
        got = sorted(h["shape"] for h in scan_text(src, "probe.rs"))
        if got != sorted(want):
            bad.append(f"{name}: got {got}, want {sorted(want)}")
    return bad


def _selftest_tree() -> Path:
    tmp = Path(tempfile.mkdtemp(prefix="self_skip_selftest_"))
    (tmp / "data").mkdir()
    src = tmp / "crates" / "c" / "src"
    src.mkdir(parents=True)
    (src / "lib.rs").write_text(
        "pub fn clean() {}\n"
        "\n"
        "#[cfg(test)]\n"
        "mod tests {\n"
        "    #[test]\n"
        "    fn honest() {\n"
        "        assert_eq!(super::clean(), ());\n"
        "    }\n"
        "}\n"
    )
    (tmp / RATCHET_REL).write_text(json.dumps(_mint([], None), indent=2) + "\n")
    return tmp


def _quiet(root: Path) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root)
    return rc, buf.getvalue()


PLANT_GUARD = (
    "\n#[test]\nfn planted() {\n"
    "    if let Ok(v) = parse() {\n        assert_eq!(v, 1);\n    }\n}\n"
)


def selftest() -> int:
    passed = failed = 0

    bad = shape_case_failures()
    if bad:
        print("  [FAIL] shape table:")
        for b in bad:
            print(f"      {b}")
        failed += 1
    else:
        pos = sum(1 for _, _, w in SHAPE_CASES if w)
        print(f"  [ok  ] shape table: {len(SHAPE_CASES)} known answers "
              f"({pos} must flag, {len(SHAPE_CASES) - pos} must NOT)")
        passed += 1

    root = _selftest_tree()
    lib = root / "crates" / "c" / "src" / "lib.rs"
    base = lib.read_text()
    ratchet_path = root / RATCHET_REL

    def arm(name: str, expect: int) -> None:
        nonlocal passed, failed
        rc, out = _quiet(root)
        good = rc == expect
        print(f"  [{'ok ' if good else 'FAIL'}] {name}: exit {rc} (expected {expect})")
        if not good:
            for line in out.rstrip("\n").splitlines():
                print(f"      {line}")
        passed += 1 if good else 0
        failed += 0 if good else 1

    def write_ratchet(doc: dict) -> None:
        ratchet_path.write_text(json.dumps(doc, indent=2) + "\n")

    def read_ratchet() -> dict:
        return json.loads(ratchet_path.read_text())

    try:
        arm("pristine tree with an honest test is green", 0)

        lib.write_text(base + PLANT_GUARD)
        arm("a NEW self-skipping test in an uncapped file is RED", 1)

        doc = read_ratchet()
        doc["budget_total"] = 1
        doc["shape_caps"]["GUARDED_ASSERTIONS"] = 1
        doc["per_file_caps"] = {"crates/c/src/lib.rs": 1}
        write_ratchet(doc)
        arm("the same site, capped and budgeted, is green", 0)

        lib.write_text(base + PLANT_GUARD + PLANT_GUARD.replace("planted", "planted2"))
        arm("a SECOND site in a capped file exceeds its cap and is RED", 1)

        lib.write_text(base + PLANT_GUARD)
        doc = read_ratchet()
        doc["budget_total"] = 0
        write_ratchet(doc)
        arm("a measured hit over budget_total is RED", 1)

        doc["budget_total"] = 1
        doc["shape_caps"]["GUARDED_ASSERTIONS"] = 0
        write_ratchet(doc)
        arm("a measured hit over its shape cap is RED", 1)

        doc["shape_caps"]["GUARDED_ASSERTIONS"] = 1
        doc["scan_roots"] = ["crates", "bench-runner"]
        write_ratchet(doc)
        arm("an artifact whose scan_roots disagree with the scanner is RED", 1)

        doc["scan_roots"] = list(SCAN_ROOTS)
        doc["reviewed_sites"] = [
            {
                "file": "crates/c/src/lib.rs",
                "test": "planted",
                "shape": "GUARDED_ASSERTIONS",
                "occurrences": 1,
                "reason": "selftest",
                "reviewed_by": "selftest",
            }
        ]
        write_ratchet(doc)
        arm("an allowlisted site with NO `// SELF-SKIP OK:` comment is RED", 1)

        lib.write_text(
            base
            + "\n#[test]\nfn planted() {\n"
            + "    // SELF-SKIP OK: selftest justification.\n"
            + "    if let Ok(v) = parse() {\n        assert_eq!(v, 1);\n    }\n}\n"
        )
        arm("an allowlisted site WITH the comment at the construct is green", 0)

        doc["reviewed_sites"][0].pop("reason")
        write_ratchet(doc)
        arm("an allowlist row with no reason is RED", 1)

        doc["reviewed_sites"][0]["reason"] = "selftest"
        doc["reviewed_sites"][0]["test"] = "gone"
        write_ratchet(doc)
        arm("an allowlist row matching no live construct is STALE and RED", 1)

        doc["reviewed_sites"] = []
        write_ratchet(doc)
        lib.write_text(base)
        doc["budget_total"] = 1
        doc["per_file_caps"] = {"crates/c/src/lib.rs": 1}
        write_ratchet(doc)
        arm("a fixed tree under an unlowered budget is green (a ratchet, not a pin)", 0)

        # --update refuses to raise
        lib.write_text(base + PLANT_GUARD)
        doc = {
            "schema": "clean.self-skipping-test-ratchet/v1",
            "scan_roots": list(SCAN_ROOTS),
            "budget_total": 0,
            "shape_caps": {s: 0 for s in SHAPES},
            "per_file_caps": {},
            "reviewed_sites": [],
        }
        write_ratchet(doc)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = update(root)
        good = rc == 1 and read_ratchet()["budget_total"] == 0
        print(f"  [{'ok ' if good else 'FAIL'}] --update REFUSES to raise a cap: "
              f"exit {rc} (expected 1), artifact unchanged")
        passed += 1 if good else 0
        failed += 0 if good else 1

        lib.write_text(base)
        doc["budget_total"] = 5
        doc["shape_caps"] = {s: 5 for s in SHAPES}
        doc["per_file_caps"] = {"crates/c/src/lib.rs": 5}
        write_ratchet(doc)
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            rc = update(root)
        after = read_ratchet()
        good = rc == 0 and after["budget_total"] == 0 and after["per_file_caps"] == {}
        print(f"  [{'ok ' if good else 'FAIL'}] --update LOWERS a cap the tree has "
              f"earned: exit {rc}, budget_total {after.get('budget_total')}")
        passed += 1 if good else 0
        failed += 0 if good else 1

        # a missing artifact is not an empty one
        ratchet_path.unlink()
        arm("an unreadable ratchet artifact is RED, never an empty allowlist", 1)
    finally:
        shutil.rmtree(root, ignore_errors=True)

    p_ok, p_bad = _selftest_pin_locked()
    passed += p_ok
    failed += p_bad

    print(f"selftest: {passed} passed, {failed} failed")
    return 0 if failed == 0 else 2


PIN_LOCKED_REL = "crates/clean-kernel/src/locked_tests.rs"
PIN_LOCKED_SRC = (
    "#[test]\nfn honest_locked() {\n    assert_eq!(1, 1);\n}\n"
    "\n#[test]\nfn locked_guard() {\n"
    "    if let Some(v) = probe() {\n        assert_eq!(v, 1);\n    }\n}\n"
)
PIN_LOCKED_LINE = 8  # the `if let` of locked_guard in PIN_LOCKED_SRC


def _selftest_pin_locked() -> tuple[int, int]:
    """Arms for `pin_locked_sites`: the account covers exactly one construct
    in a pin-locked file, by line and by the file's bytes, and nothing else --
    in particular a NEW instance anywhere is still caught."""
    passed = failed = 0
    root = _selftest_tree()
    ratchet_path = root / RATCHET_REL
    locked = root / PIN_LOCKED_REL
    locked.parent.mkdir(parents=True)
    lib = root / "crates" / "c" / "src" / "lib.rs"
    base_lib = lib.read_text()
    (root / "docs").mkdir()
    record = root / "docs" / "DECISIONS.md"

    def arm(name: str, expect: int, why: str = "") -> None:
        # `why`: the refusal must be THIS one, not some other red the arm's
        # tree happens to carry.
        nonlocal passed, failed
        rc, out = _quiet(root)
        good = rc == expect and why in out
        print(f"  [{'ok ' if good else 'FAIL'}] pin-locked: {name}: exit {rc} "
              f"(expected {expect}{', naming ' + repr(why) if why else ''})")
        if not good:
            for line in out.rstrip("\n").splitlines():
                print(f"      {line}")
        passed += 1 if good else 0
        failed += 0 if good else 1

    def digest(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def row(**over) -> dict:
        r = {
            "file": PIN_LOCKED_REL,
            "test": "locked_guard",
            "shape": "GUARDED_ASSERTIONS",
            "line": PIN_LOCKED_LINE,
            "file_sha256": digest(locked),
            "genuine_skip": True,
            "reason": "selftest: a genuine skip path in a file only a pin train edits",
            "owed_edit": "selftest: give the guard a failing else",
            "reviewed_by": "selftest",
            "recorded_in": "docs/DECISIONS.md",
        }
        r.update(over)
        return r

    def ratchet(rows: list, budget: int = 0) -> None:
        doc = _mint([], None)
        doc["budget_total"] = budget
        doc["pin_locked_sites"] = rows
        ratchet_path.write_text(json.dumps(doc, indent=2) + "\n")

    try:
        locked.write_text(PIN_LOCKED_SRC)
        record.write_text(f"Owed at the next pin train: {PIN_LOCKED_REL}, locked_guard.\n")
        found = [_hit_key(h) for h in scan_text(PIN_LOCKED_SRC, PIN_LOCKED_REL)]
        good = found == [(PIN_LOCKED_REL, "locked_guard", "GUARDED_ASSERTIONS",
                          PIN_LOCKED_LINE)]
        print(f"  [{'ok ' if good else 'FAIL'}] pin-locked: the planted construct is "
              f"measured where the rows below say: {found}")
        passed += 1 if good else 0
        failed += 0 if good else 1

        ratchet([])
        arm("a construct in a pin-locked file with NO row is RED", 1,
            f"{PIN_LOCKED_REL} has 1 self-skipping test construct(s) and NO cap")

        ratchet([row()])
        arm("one complete row accounts for it at budget 0 -- no budget raised", 0)

        ratchet([row()])
        lib.write_text(base_lib + PLANT_GUARD)
        arm("NEGATIVE CONTROL: a new unlisted construct in another file is still RED", 1,
            "crates/c/src/lib.rs has 1 self-skipping test construct(s) and NO cap")
        lib.write_text(base_lib)

        good_row = row()
        locked.write_text(PIN_LOCKED_SRC + PLANT_GUARD.replace("planted", "locked2"))
        ratchet([good_row])
        arm("a second construct in the same pin-locked file is RED", 1,
            f"{PIN_LOCKED_REL} has 2 self-skipping test construct(s) and NO cap")

        locked.write_text(PIN_LOCKED_SRC + "// touched\n")
        arm("any edit to the pin-locked file (the pin train) turns the row RED", 1,
            "is no longer the file the row reviewed")
        locked.write_text(PIN_LOCKED_SRC)

        ratchet([row(line=PIN_LOCKED_LINE + 1)])
        arm("a row whose line names no construct is RED", 1, "matches no live construct")

        ratchet([row(), row()])
        arm("the same construct named twice is RED", 1, "twice")

        ratchet([row(occurrences=2)])
        arm("a row carrying `occurrences` is RED", 1, "carries `occurrences`")

        ratchet([row(owed_edit="")])
        arm("a row with no owed_edit is RED", 1, "has no owed_edit")

        ratchet([row(genuine_skip="yes")])
        arm("a row that does not say whether the guard skips is RED", 1,
            "has no boolean genuine_skip")

        ratchet([row(file_sha256="0" * 63)])
        arm("a row with a malformed file_sha256 is RED", 1, "has no 64-hex file_sha256")

        ratchet([row(recorded_in="../outside/DECISIONS.md")])
        arm("a recorded_in outside the repository is RED", 1,
            "is not a path inside this repository")

        record.write_text(f"Owed at the next pin train: {PIN_LOCKED_REL}.\n")
        ratchet([row()])
        arm("a recorded_in document that does not name the test is RED", 1, "does not name both")
        record.write_text(f"Owed at the next pin train: {PIN_LOCKED_REL}, locked_guard.\n")

        lib.write_text(base_lib + PLANT_GUARD)
        planted_line = scan_text(base_lib + PLANT_GUARD, "crates/c/src/lib.rs")[0]["line"]
        ratchet([row(), row(file="crates/c/src/lib.rs", test="planted", line=planted_line,
                            file_sha256=digest(lib))])
        record.write_text(f"{PIN_LOCKED_REL} locked_guard; crates/c/src/lib.rs planted\n")
        arm("a row naming a file outside the pin-locked paths is RED", 1, "names a file outside")
        lib.write_text(base_lib)
        record.write_text(f"Owed at the next pin train: {PIN_LOCKED_REL}, locked_guard.\n")

        stale = row()
        locked.write_text(PIN_LOCKED_SRC.replace(
            "    }\n}\n", "    } else {\n        panic!(\"probe\");\n    }\n}\n"))
        ratchet([stale])
        arm("a row whose construct was fixed (the owed edit paid) is STALE and RED", 1,
            "matches no live construct")

        locked.write_text(PIN_LOCKED_SRC)
        ratchet([row()], budget=3)
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            rc = update(root)
        after = json.loads(ratchet_path.read_text())
        good = (rc == 0 and after["budget_total"] == 0 and after["per_file_caps"] == {}
                and after["pin_locked_sites"] == [row()])
        print(f"  [{'ok ' if good else 'FAIL'}] pin-locked: --update keeps the row and "
              f"counts its construct in no cap: exit {rc}, budget_total "
              f"{after.get('budget_total')}, rows {len(after.get('pin_locked_sites') or [])}")
        passed += 1 if good else 0
        failed += 0 if good else 1
        arm("the tree --update minted is green", 0)
    finally:
        shutil.rmtree(root, ignore_errors=True)
    return passed, failed


def main(argv: list[str]) -> int:
    if "--selftest" in argv:
        return selftest()
    if "--update" in argv:
        return update(REPO_ROOT)
    return run(REPO_ROOT, list_only="--list" in argv, as_json="--json" in argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
