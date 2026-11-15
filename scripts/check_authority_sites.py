#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The census of authority sites, re-derived from source (self-proof plan, unit P1).

An authority site is a place in production Rust where an authority-shaped
acceptance is minted, or where the checker behind one is chosen. This gate
holds `data/authority_sites.json` to the source it describes, so the later
flip to `kcheck` (plan lane P) has a map that cannot rot silently. It sees
the sites SPELLED IN ITS VOCABULARY (below); what that leaves out is listed
under WHAT IT DOES NOT MEASURE and in the artifact's `limits`:

  * a site the tree has and the artifact does not name fails the gate;
  * a named site whose count moved, or that is gone, fails the gate;
  * a named mint whose recorded checker evidence left its function ("the
    site moved checker") fails the gate;
  * a mint classified `clean-kernel` whose function calls (in code position)
    no kernel entry of KERNEL_ENTRY_CALLS, nor a declared wrapper whose own
    chain of checked calls reaches one, fails the gate (KERNEL EVIDENCE);
  * a mint or root row with no classification fails the gate, and so does a
    Trust row that does not say what Trust's docs/TCB.md says about it;
  * the header list of sites that mint an authority-shaped label with no
    Clean-kernel check behind them must equal what the rows derive, and its
    length may not exceed `first_risk_limit` (a ceiling that only falls,
    except through a recorded `--rebase-risk` census correction);
  * a Trust manifest that links one of Clean's checker crates, or an outside
    crate recorded as carrying them, and that the artifact does not name
    fails the gate (the route into Clean's checkers through another
    repository), and so does a named link whose set of names moved.

WHAT IS MEASURED
----------------
Three token families, matched in CODE position only: comments and string, raw
string and char literals are blanked first, test files are excluded by the
target-side classification of scripts/check_add_decl_ratchet.py, and inline
`#[cfg(test)]` items are excluded by brace tracking.

  label  an enum variant whose NAME is authority-shaped (LABEL_RE below:
         `KernelVerified`, `KernelChecked...`, `KernelProved`, `KernelBridged`,
         `KernelCertified`, `KernelAccepted`, `Certified`, `SourceVerified`,
         the sibling tiers `AxiomDependent`, `CertificateReplayed`,
         `AxiomDischarged`, `AxiomAccepted`, `UnsafeAccepted`, `StructuralProved`, and on the
         Trust side `KernelReferenceChecked`/`KernelReconstructed`).
         The name is matched whatever enum carries it and whatever path spells
         it, so a new enum with such a variant is a new site.
  producer  a WRITE to a snake_case field or local whose name says
         kernel_[re]verified/checked/certified/proved (PRODUCER_RE: `+=`,
         `.push/.extend/.insert/.append(`, `= true`, `: true`), the replay
         lane's per-constant verdict among them. Always `construct`.
  root   the selectors of the checker behind an acceptance: the fenced
         reference entry (`ReferenceKernel`, `ReferenceAccepted`, its
         `add_checked`/`check_closed_term` family), the Lean-order replay base
         (`for_lean_replay`), an explicit `KernelTheory::<variant>`, and on the
         Trust side the certificate seam (`ReferenceCertificate`,
         `reference_certificate_for`, `from_accepted`).

Each occurrence gets a ROLE from its syntax, never from prose:

  def        a bare variant inside its `enum` body
  read       a match-arm or `matches!` pattern, a `let` pattern, or an operand
             of `==`/`!=`/`<=`/`>=`
  import     inside a `use` item
  mention    a root type named in a signature, field or bound
  construct  a label in value position: everything that is not provably one
             of the above (the classifier fails toward this role)
  call       a root invoked: `ReferenceKernel::new(`, `.check_closed_term(`,
             `Environment::for_lean_replay(`; a `KernelTheory::X` in value
             position is `construct`

A site is one (file, enclosing symbol, token, role) group with its count.
`construct` and `call` sites need a classification (what is minted, the
checker and theory behind it, who can reach it, the rung that must hold
before it requires `kcheck`); the other roles are pinned by count only, which
is what keeps a mint misread as a read from landing unseen.

WHAT IT DOES NOT MEASURE
------------------------
  * Acceptance by exit status or by a printed line (`clean check` succeeding,
    `clean lake build` writing an `.olean`). Those are the `entries` rows of
    the artifact: hand-anchored to a function, and the gate checks only that
    the anchor still exists and still shows its recorded checker evidence. A
    new verb that reaches the kernel through an already-counted helper is not
    detected.
  * An environment built without a censused root. Such an environment runs
    `KernelTheory::Extended`, the enum's `#[default]`; the census does not
    list the hundreds of `Environment::new()` calls.
  * Scripts, and Rust outside crates/. A label written by a shell or Python
    script, or in scripts/crystal_a2_project, is out of scope.
  * Names left out on purpose, with their counts in the artifact's `limits`:
    clean-verify's `ProofStatus::DerivedProved`, the generic outcome
    variants (`Verified`, `Proved`, `Checked`, `Accepted`, `Valid`), a
    kernel-named field assigned anything but `true`, and checked/verified
    fields whose name lacks `kernel` (`family_checked: true`).
  * Which function a citing site's call resolves to. A wrapper is matched by
    name, so a same-named function elsewhere would satisfy it.
  * The SOURCE of an outside carrier. The link census sees that a Trust
    manifest names `tla-check` (ty's crate, which links `clean-kernel` and
    `clean-ck0` under its `clean-cic` feature); it does not read ty. The
    acceptance sites inside the carrier are recorded by hand in the link
    row's `route`, with the commit they were read at.
  * The Trust half is a census of ONE Trust commit, the one the artifact
    names. Run at that commit it is a consistency check of the artifact; it
    sees a new Trust site only when run with `--trust-ref <newer ref>`, which
    is how the pin is moved. Trust's own `tcb_document_exhaustiveness` owns
    its authority table. When no Trust checkout holds the commit, the Trust
    half reports `unknown` and the gate still decides the Clean half;
    `--require-trust` turns that into a failure.

Exit codes: 0 the artifact matches the tree; 1 it does not; 2 the self-test
failed; 3 `--require-trust` and the Trust half is not knowable here.

Usage:
    python3 scripts/check_authority_sites.py              # check
    python3 scripts/check_authority_sites.py --selftest   # mutation arms on a synthetic tree
    python3 scripts/check_authority_sites.py --list       # the measured sites
    python3 scripts/check_authority_sites.py --clean-only # the Clean half only (no sibling checkout; `just ci`)
    python3 scripts/check_authority_sites.py --write      # refresh derived fields, keep classifications
    python3 scripts/check_authority_sites.py --write --rebase-risk '<why>'   # raise the first-risk ceiling for a census correction
    python3 scripts/check_authority_sites.py --write --trust-ref origin/main   # move the Trust pin
    python3 scripts/check_authority_sites.py --pinned-inputs
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_add_decl_ratchet as lexer  # noqa: E402  (the reference lexer and test classification)

# check_gate_registry.py R7 pins what `--pinned-inputs` prints: the lexer and
# the target-side test classification this gate imports and runs.
ANSWERS_PINNED_INPUTS = True
PINNED_INPUTS = ("scripts/check_add_decl_ratchet.py",)

REPO_ROOT = Path(__file__).resolve().parent.parent
ARTIFACT_REL = Path("data") / "authority_sites.json"
SCHEMA = "clean.authority_sites.v1"

# ---------------------------------------------------------------------------
# The vocabulary. Editing it is a reviewed change to this gate: its sha is
# pinned in data/gate_registry.json.
# ---------------------------------------------------------------------------

# Authority-shaped variant NAMES. Matched as the last segment of a path, or
# bare; the qualifier is recorded, never required. The second line holds the
# sibling tiers of the same enums, added 2026-11-12 after the P1 review found
# them minted unnamed: `AxiomDependent` and `CertificateReplayed` (TrustLevel,
# "verified with known axiom dependencies" / "certificate replayed"), and
# AddConstResult's `AxiomDischarged`, `AxiomAccepted` and `UnsafeAccepted`,
# and clean-c-sem ProofStatus's `StructuralProved` (the sibling of its
# `KernelVerified`, printed as "proved" by the server's verify_c).
# Left out by name, with their counts in the artifact's `limits`: clean-verify
# ProofStatus's `DerivedProved` (spec-table metadata, 1516 literals), and the
# generic Verified / Proved / Checked / Accepted / Valid.
LABEL_NAMES = (
    r"Kernel(?:Verified|Checked|Proved|Bridged|Certified|Accepted|ReferenceChecked|Reconstructed)"
    r"[A-Za-z0-9]*"
    r"|Certified"
    r"|SourceVerified"
    r"|AxiomDependent|CertificateReplayed|AxiomDischarged|AxiomAccepted|UnsafeAccepted"
    r"|StructuralProved"
)
LABEL_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?P<qual>(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*)(?P<name>" + LABEL_NAMES + r")(?![A-Za-z0-9_])"
)
# The names with no suffix. A SUFFIXED name (`KernelVerifiedWithProof`) is a
# label only as a path's last segment or inside an enum body: bare, it is a
# type name (`KernelVerifiedManifest`), and a type that is itself a site is a
# root identifier below.
_LABEL_CORE_RE = re.compile(
    r"\A(?:Kernel(?:Verified|Checked|Proved|Bridged|Certified|Accepted|ReferenceChecked|Reconstructed)"
    r"|Certified|SourceVerified"
    r"|AxiomDependent|CertificateReplayed|AxiomDischarged|AxiomAccepted|UnsafeAccepted"
    r"|StructuralProved)\Z"
)

# Producer shapes: a verdict recorded by writing a snake_case field or local
# whose name says kernel, rather than by constructing a variant. The replay
# lane's per-constant mint is one (`v.kernel_verified += 1;
# v.kernel_verified_names.push(name)` in parallel_verify_replay.rs
# check_value_bearing). The token is the name and the write, normalized:
# `kernel_verified+=`, `kernel_verified_names.push`, `kernel_checked=true`.
# A `re`/`re_` before the verb counts too: Trust's temporal lane accepts a
# certificate with `bound.kernel_rechecked = true` (found 2026-11-12 reading
# trust-spec-temporal for the P1 review). Every hit is a `construct`. Not scanned (named in the artifact's `limits`): a
# field so named assigned anything but `true`, and a write to a field whose
# name says checked or verified without `kernel` (`family_checked: true`).
PRODUCER_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?P<field>[a-z0-9_]*kernel_(?:re_?)?(?:verified|checked|certified|proved)[a-z0-9_]*)"
    r"\s*(?P<op>\+=|\.\s*(?:push|extend|insert|append)\s*\(|(?<![=!<>])=(?!=)\s*true(?![A-Za-z0-9_])"
    r"|:\s*true(?![A-Za-z0-9_]))"
)
_PRODUCER_PREFILTER = r"kernel_(?:re_?)?(?:verified|checked|certified|proved)"

# Checker roots, Clean side and Trust side. `KernelTheory::<Variant>` keeps its
# variant in the token; the others are bare identifiers.
ROOT_IDENTS = (
    "ReferenceKernel",
    "ReferenceAccepted",
    "ReferenceCertificate",
    "for_lean_replay",
    "add_checked",
    "add_inductive_checked",
    "add_quot_checked",
    "check_closed_term",
    "reference_certificate_for",
    "reference_certificate_for_parts",
    "from_accepted",
    "KernelVerifiedManifest",
)
ROOT_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:(?P<theory>(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*KernelTheory\s*::\s*[A-Z][A-Za-z0-9]*)"
    r"|(?P<ident>" + "|".join(ROOT_IDENTS) + r"))(?![A-Za-z0-9_])"
)
# A cheap prefilter over RAW text: blanking only removes characters, so a file
# with no raw hit has no code hit.
PREFILTER_RE = re.compile(LABEL_NAMES + r"|KernelTheory|" + "|".join(ROOT_IDENTS) + "|" + _PRODUCER_PREFILTER)

# The Clean kernel's checking entries: a mint classified `clean-kernel` must
# name at least one of these, or a declared wrapper of one, as an evidence token
# that its function CALLS in code position (`name(` or `name::<..>(`). A
# variable, a field or a parameter that happens to be named like a check does
# not count (the P1 review found `report`, `checked`/`family_checked` and the
# token's own struct fields standing as evidence). Not entries, on purpose:
# `add_decl_structural` and `add_decl_unchecked` (the bypasses), `add_quot`
# (installs the builtin), `for_lean_replay` (builds a base, checks nothing),
# `whnf`.
KERNEL_ENTRY_CALLS = (
    # clean_kernel::env::Environment
    "add_decl",
    "add_decl_if_absent",
    "upgrade_axiom_to_checked_decl",
    "check_decl_readonly",
    "check_decl_readonly_with_heartbeat",
    "check_decl_readonly_strict",
    "add_inductive",
    "add_inductive_core",
    # clean_kernel::tc::TypeChecker
    "infer_type",
    "infer_type_full",
    "infer_type_with_cert",
    "infer_type_with_cert_full",
    "check_type",
    "is_def_eq",
    # clean_kernel::reference::ReferenceKernel (the fenced entry)
    "add_checked",
    "add_inductive_checked",
    "add_quot_checked",
    "check_closed_term",
)
WRAPPER_FIELDS = ("name", "file", "symbol", "calls", "detail")

# The link census (Trust half). Clean's checker crates, and the crates of a
# THIRD repository recorded as linking them: a Trust manifest that names either
# kind is a route into Clean's checkers, whatever vocabulary the code on that
# route uses (docs/DECISIONS.md 2026-11-12, "`clean-ck0` is linked in
# production outside this workspace"). A new carrier is added here when found.
CHECKER_CRATES = ("clean-kernel", "clean-ck0")
OUTSIDE_CARRIERS = ("tla-check",)
_LINK_RE = re.compile(
    r"(?<![A-Za-z0-9_-])(" + "|".join(CHECKER_CRATES + OUTSIDE_CARRIERS) + r")(?![A-Za-z0-9_-])"
)
# A link row naming one of these needs a hand-written `route`.
ROUTED_NAMES = ("clean-ck0",) + OUTSIDE_CARRIERS
ROUTE_FIELDS = ("via", "reaches", "what", "examined")

CLASSIFIED_ROLES = ("construct", "call")
COUNTED_ROLES = ("def", "read", "import", "mention")

# What a classified row may say. `class` is what the site does; `checker.kind`
# is whose verdict the minted label rests on.
CLASSES = (
    "mint",        # an authority-shaped label is created from a verdict
    "relabel",     # an existing label is carried into another spelling (decode, map, serialize)
    "threshold",   # the label is a policy value, a filter, a default or a comparison operand
    "root",        # a checker is selected or the fenced entry is invoked
)
CHECKER_KINDS = (
    "clean-kernel",     # the Clean kernel decided: `entry` says through which door
    "in-repo-checker",  # trusted Rust that is not the kernel (a proof-format checker, a step validator)
    "external-tool",    # a tool outside this repository decided
    "none",             # nothing checks at this site: import or source confidence, a policy mapping
    "inherits",         # carries a label minted elsewhere; no verdict of its own
    "not-a-mint",       # the label is a value being compared or configured, nothing is accepted
    "unexamined",       # Trust rows only: the census did not read behind this site; no claim either way
)
KERNEL_ENTRIES = ("add_decl", "replay", "reference", "typecheck")
THEORIES = ("Extended", "Lean", "LeanReference", "caller-selected", "n/a")
REACH = ("user", "trust", "user+trust", "internal", "example", "bench")
# A mint whose checker is one of these is "an authority-shaped label with no
# Clean-kernel check behind it": the first risk the header lists.
FIRST_RISK_KINDS = ("none", "external-tool", "in-repo-checker")

# ---------------------------------------------------------------------------
# Lexing and structure.
# ---------------------------------------------------------------------------

_STRUCT_RE = re.compile(
    r"(?P<attr>#\[\s*cfg\s*\(\s*test\s*\)\s*\])"
    r"|(?P<fn>(?<![A-Za-z0-9_])fn\s+(?P<fname>[A-Za-z_][A-Za-z0-9_]*))"
    r"|(?P<item>(?<![A-Za-z0-9_])(?P<ikw>enum|struct|union|trait|mod|impl)(?![A-Za-z0-9_]))"
    r"|(?P<open>\{)|(?P<close>\})|(?P<semi>;)|(?P<po>[(\[])|(?P<pc>[)\]])"
)
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_USE_TAIL_RE = re.compile(r"(?:^|[;{}\s])(?:pub(?:\s*\([^)]*\))?\s+)?use\s[^;=()]*\Z")


def _impl_name(header: str) -> str:
    """The implementing type of an `impl` header (text after the keyword)."""
    if re.search(r"(?<![A-Za-z0-9_])for(?![A-Za-z0-9_])", header):
        header = re.split(r"(?<![A-Za-z0-9_])for(?![A-Za-z0-9_])", header)[-1]
    else:
        header = header.lstrip()
        if header.startswith("<"):
            depth = 0
            for i, ch in enumerate(header):
                depth += ch == "<"
                depth -= ch == ">"
                if depth == 0:
                    header = header[i + 1 :]
                    break
    header = re.split(r"(?<![A-Za-z0-9_])where(?![A-Za-z0-9_])", header)[0]
    head = header.split("<")[0]
    names = _IDENT_RE.findall(head)
    names = [n for n in names if n not in ("dyn", "mut", "const", "unsafe")]
    return names[-1] if names else "?"


_ATTR_GROUP_RE = re.compile(r"\s*#\s*\[")
_QUALIFIER_RE = re.compile(
    r"\s*(?:pub(?:\s*\([^)]*\))?|default|const|async|unsafe|extern)(?![A-Za-z0-9_])"
)
_NEXT_WORD_RE = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)")


def _cfg_test_target(text: str, at: int) -> int:
    """Where the item a `#[cfg(test)]` ending at `at` annotates starts its keyword.

    The attribute binds to the ONE thing that follows it: further attributes,
    a visibility and the qualifiers `default`/`const`/`async`/`unsafe`/`extern`
    are skipped, and the next word is read. Only when that word is `fn`, `mod`
    or `impl` (the items whose bodies this file tracks) is its position
    returned; anything else (a struct field, an enum variant, a match arm, a
    block or `let` statement, a `use`, a `const` item, a macro invocation or a
    `macro_rules!`) returns -1, so the attribute marks nothing. Before
    2026-11-12 the attribute stayed armed until the next `fn`, item keyword or
    top-level `;`, so a `#[cfg(test)]` on a field or a variant marked the NEXT
    production `impl` or `fn` as test code and hid every site in it
    (reports/self-proof-audit-2026-11-12/reviews/P1-authority-sites-review.md).
    """
    i = at
    while True:
        m = _ATTR_GROUP_RE.match(text, i)
        if m:
            i = _skip_group(text, m.end() - 1)
            continue
        m = _QUALIFIER_RE.match(text, i)
        if m:
            i = m.end()
            continue
        break
    m = _NEXT_WORD_RE.match(text, i)
    if m and m.group(1) in ("fn", "mod", "impl"):
        return m.start(1)
    return -1


class Structure:
    """Brace-tracked item spans of one blanked file.

    `symbol_at(pos)` names the innermost enclosing `fn` (qualified by its
    `impl`/`trait` when it has one), else the innermost item. `is_test(pos)`
    is true inside an item annotated `#[cfg(test)]` (a `mod`, `fn` or `impl`):
    the attribute binds only to the item whose keyword immediately follows it
    (`_cfg_test_target`). Raises ValueError when braces do not balance: an
    unreadable file is not a clean one.
    """

    def __init__(self, text: str, rel: str):
        self.spans: list[tuple[int, int, str, str, bool]] = []  # (start, end, kind, name, test)
        stack: list[list] = []  # [kind, name, open_pos, test]
        pending: list | None = None  # [kind, name, test]
        test_kw_at = -1  # keyword position of the item the last #[cfg(test)] annotates
        paren = 0
        for m in _STRUCT_RE.finditer(text):
            if m.group("attr"):
                test_kw_at = _cfg_test_target(text, m.end())
            elif m.group("fn"):
                pending = ["fn", m.group("fname"), m.start() == test_kw_at]
                paren = 0
            elif m.group("item"):
                if pending is not None and pending[0] == "fn":
                    continue  # `impl Trait` in a signature, not an item
                if paren:
                    continue
                kw = m.group("ikw")
                stop = len(text)
                for ch in "{;":
                    at = text.find(ch, m.end())
                    if at != -1:
                        stop = min(stop, at)
                header = text[m.end() : stop]
                if kw == "impl":
                    name = _impl_name(header)
                else:
                    found = _IDENT_RE.search(header)
                    name = found.group(0) if found else "?"
                pending = [kw, name, m.start() == test_kw_at and kw in ("mod", "impl")]
                paren = 0
            elif m.group("po"):
                paren += 1
            elif m.group("pc"):
                paren = max(0, paren - 1)
            elif m.group("semi"):
                if paren == 0:
                    pending = None
            elif m.group("open"):
                inherited = bool(stack and stack[-1][3])
                if pending is not None:
                    stack.append([pending[0], pending[1], m.start(), pending[2] or inherited])
                    pending = None
                else:
                    stack.append(["block", "", m.start(), inherited])
                paren = 0
            elif m.group("close"):
                if not stack:
                    raise ValueError(f"{rel}: a `}}` with no opener (brace tracking failed)")
                kind, name, start, test = stack.pop()
                if kind != "block":
                    self.spans.append((start, m.end(), kind, name, test))
        if stack:
            raise ValueError(
                f"{rel}: {len(stack)} block(s) never closed (brace tracking ran off the end "
                f"of the file). Refusing to classify this file."
            )
        self.spans.sort(key=lambda s: (s[0], -s[1]))

    def _enclosing(self, pos: int) -> list[tuple[int, int, str, str, bool]]:
        return [s for s in self.spans if s[0] <= pos < s[1]]

    def is_test(self, pos: int) -> bool:
        return any(s[4] for s in self._enclosing(pos))

    def symbol_at(self, pos: int) -> tuple[str, tuple[int, int] | None]:
        chain = self._enclosing(pos)
        fns = [i for i, s in enumerate(chain) if s[2] == "fn"]
        if fns:
            i = fns[-1]
            span = chain[i]
            owner = next((s for s in reversed(chain[:i]) if s[2] in ("impl", "trait")), None)
            name = f"{owner[3]}::{span[3]}" if owner else span[3]
            return name, (span[0], span[1])
        items = [s for s in chain if s[2] != "mod"]
        if items:
            span = items[-1]
            return f"{span[2]} {span[3]}", (span[0], span[1])
        return "<module>", None

    def in_enum_body(self, pos: int) -> bool:
        chain = self._enclosing(pos)
        return bool(chain) and chain[-1][2] == "enum"


def _skip_group(text: str, at: int) -> int:
    """Index just past the balanced `(...)`/`{...}`/`[...]` opening at `at`."""
    pairs = {"(": ")", "{": "}", "[": "]"}
    close = pairs[text[at]]
    depth = 0
    for i in range(at, min(len(text), at + 4000)):
        if text[i] == text[at]:
            depth += 1
        elif text[i] == close:
            depth -= 1
            if depth == 0:
                return i + 1
    return at + 1


def _after_reads(text: str, end: int) -> bool:
    """True when what FOLLOWS the path puts it in pattern or comparison position."""
    i = end
    n = len(text)
    while i < n and text[i].isspace():
        i += 1
    if i < n and text[i] in "({":
        i = _skip_group(text, i)
    while i < n and (text[i].isspace() or text[i] in ")]"):
        i += 1
    rest = text[i : i + 400]
    if rest.startswith("=>"):
        return True
    if rest.startswith(("==", "!=", "<=", ">=")):
        return True
    if rest.startswith("=") and not rest.startswith("=="):
        return True  # `let P = e`, `if let P = e`: a variant path is never assigned to
    if rest.startswith("|") and not rest.startswith("||"):
        return True
    if re.match(r"if(?![A-Za-z0-9_])", rest):
        arrow = rest.find("=>")
        stop = min((p for p in (rest.find(";"), rest.find("{")) if p != -1), default=len(rest))
        return arrow != -1 and arrow < stop
    return False


def _before_reads(text: str, start: int) -> bool:
    """True when what PRECEDES the path puts it in pattern or comparison position."""
    window = text[max(0, start - 600) : start]
    stripped = window.rstrip()
    while stripped.endswith(("(", "&", "[")):
        stripped = stripped[:-1].rstrip()
    if stripped.endswith(("==", "!=", "<=", ">=")):
        return True
    # `name @ Path { .. }` binds a pattern; `@` has no value-position use.
    if stripped.endswith("@"):
        return True
    # `A | B` in a pattern: exactly one bar since the last `,` `(` `{` `;` or
    # `=>`. A closure head (`|x| V`, `|| V`) has two and stays a construct.
    seg_start = max(stripped.rfind(c) for c in (",", "(", "{", ";", "=>"))
    segment = stripped[seg_start + 1 :] if seg_start != -1 else stripped
    if stripped.endswith("|") and not stripped.endswith("||") and segment.count("|") == 1:
        return True
    # inside an unclosed `matches!(` of the same statement
    stmt = max(window.rfind(";"), window.rfind("{"), window.rfind("}"))
    head = window[stmt + 1 :]
    at = head.rfind("matches!")
    if at != -1:
        tail = head[at:]
        if tail.count("(") > tail.count(")"):
            return True
    return False


def scan_text(raw: str, rel: str) -> list[dict]:
    """Every production occurrence in one file, with role and enclosing symbol."""
    if not PREFILTER_RE.search(raw):
        return []
    text = lexer.strip_noncode(raw)
    if not PREFILTER_RE.search(text):
        return []
    structure = Structure(text, rel)
    hits: list[dict] = []

    def line_of(pos: int) -> int:
        return text.count("\n", 0, pos) + 1

    def add(family: str, token: str, role: str, pos: int) -> None:
        if structure.is_test(pos):
            return
        symbol, span = structure.symbol_at(pos)
        hits.append(
            {
                "file": rel,
                "symbol": symbol,
                "family": family,
                "token": token,
                "role": role,
                "line": line_of(pos),
                "_span": span,
            }
        )

    for m in LABEL_RE.finditer(text):
        qual = re.sub(r"\s+", "", m.group("qual"))
        segments = [s for s in qual.split("::") if s]
        token = f"{segments[-1]}::{m.group('name')}" if segments else m.group("name")
        start, end = m.start(), m.end()
        if re.match(r"\s*::", text[end : end + 40]):
            continue  # a type or module path (`KernelVerifiedManifest::from_file`), not a variant
        if not segments and not structure.in_enum_body(start) and not _LABEL_CORE_RE.match(m.group("name")):
            continue  # a bare suffixed name outside an enum body is a type name
        if m.group("name") in ROOT_IDENTS:
            continue  # a type that is itself a site: the root family counts it
        if _USE_TAIL_RE.search(text[max(0, start - 400) : start]):
            role = "import"
        elif not segments and structure.in_enum_body(start):
            role = "def"
        elif _after_reads(text, end) or _before_reads(text, start):
            role = "read"
        else:
            role = "construct"
        add("label", token, role, start)

    for m in ROOT_RE.finditer(text):
        start, end = m.start(), m.end()
        before = text[max(0, start - 400) : start]
        if m.group("theory"):
            token = "KernelTheory::" + re.sub(r"\s+", "", m.group("theory")).rsplit("::", 1)[1]
            if _USE_TAIL_RE.search(before):
                role = "import"
            elif _after_reads(text, end) or _before_reads(text, start):
                role = "read"
            else:
                role = "construct"
        else:
            token = m.group("ident")
            rest = text[end : end + 200]
            if _USE_TAIL_RE.search(before):
                role = "import"
            elif re.search(r"(?<![A-Za-z0-9_])fn\s+\Z", before):
                role = "def"
            elif re.search(r"(?<![A-Za-z0-9_])(?:struct|enum|impl|trait|for)\s+\Z", before):
                role = "def"
            else:
                assoc = re.match(r"\s*::\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^>]*>\s*)?\(", rest)
                if assoc:
                    token = f"{token}::{assoc.group(1)}"
                    role = "call"
                elif re.match(r"\s*(?:::\s*<[^>]*>\s*)?\(", rest) and token[0].islower():
                    role = "call"
                elif token[0].islower():
                    role = "call"  # a function named as a value (`.map(Reference…::from_accepted)`)
                elif re.match(r"\s*\{", rest) and not re.search(
                    r"->\s*(?:&\s*(?:'\s*[A-Za-z_]*\s+)?(?:mut\s+)?)?\Z", before
                ):
                    role = "construct"  # a struct literal: the token itself is made here
                else:
                    role = "mention"
        add("root", token, role, start)

    for m in PRODUCER_RE.finditer(text):
        op = re.sub(r"\s+", "", m.group("op")).rstrip("(")
        add("producer", f"{m.group('field')}{op}", "construct", m.start())
    for hit in hits:
        span = hit.pop("_span")
        hit["_body"] = text[span[0] : span[1]] if span else text
    return hits


def group_sites(hits: list[dict], prefix: str) -> dict[str, dict]:
    """(file, symbol, token, role) -> site row with count, lines and the body text."""
    sites: dict[str, dict] = {}
    for hit in hits:
        key = f"{prefix}:{hit['file']}#{hit['symbol']}#{hit['token']}#{hit['role']}"
        row = sites.setdefault(
            key,
            {
                "id": key,
                "file": hit["file"],
                "symbol": hit["symbol"],
                "family": hit["family"],
                "token": hit["token"],
                "role": hit["role"],
                "count": 0,
                "lines": [],
                "_body": hit["_body"],
            },
        )
        row["count"] += 1
        row["lines"].append(hit["line"])
    return sites


# ---------------------------------------------------------------------------
# The two trees.
# ---------------------------------------------------------------------------


def measure_clean(root: Path) -> tuple[dict[str, dict], list[str]]:
    lexer._CLASSIFY_CACHE.clear()
    lexer._UNRESOLVED_EDGES.clear()
    hits: list[dict] = []
    errors: list[str] = []
    for path in sorted((root / "crates").rglob("*.rs")):
        rel = path.relative_to(root)
        try:
            raw = path.read_text(errors="strict")
        except (OSError, UnicodeDecodeError) as exc:
            errors.append(f"cannot read {rel}: {exc}")
            continue
        if not PREFILTER_RE.search(raw):
            continue
        if not lexer.is_production_file(path) and lexer.is_test_like(path, rel):
            continue
        try:
            hits.extend(scan_text(raw, rel.as_posix()))
        except ValueError as exc:
            errors.append(str(exc))
    return group_sites(hits, "clean"), errors


# Trust paths that are test code by position. Trust is scanned at a commit, so
# the target-side module walk used for Clean is not available; a path
# predicate plus the inline `#[cfg(test)]` tracking is what this half has.
_TRUST_TEST_PATH_RE = re.compile(
    r"(?:^|/)(?:tests?|benches|ui)(?:/|$)|(?:^|/)(?:test_[^/]*|[^/]*_tests?|tests?|tests_[^/]*)\.rs$"
)
_TRUST_SKIP_PREFIXES = ("first-party/", "library/", "src/tools/", "src/doc/", "tests/")


def _trust_is_scanned(rel: str) -> bool:
    return (
        rel.endswith(".rs")
        and not rel.startswith(_TRUST_SKIP_PREFIXES)
        and not _TRUST_TEST_PATH_RE.search(rel)
    )


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    return subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, text=True, env=env, timeout=300
    )


def find_trust_repo(root: Path, explicit: str | None) -> Path | None:
    """The sibling Trust checkout: `--trust-repo`, `CLEAN_TRUST_REPO`, `../trust`
    beside this checkout, or `../trust` beside the main checkout of a worktree."""
    candidates: list[Path] = []
    if explicit:
        candidates.append(Path(explicit))
    elif os.environ.get("CLEAN_TRUST_REPO"):
        candidates.append(Path(os.environ["CLEAN_TRUST_REPO"]))
    else:
        candidates.append(root.parent / "trust")
        common = _git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")
        if common.returncode == 0 and common.stdout.strip():
            candidates.append(Path(common.stdout.strip()).parent.parent / "trust")
    for cand in candidates:
        if cand.is_dir():
            return cand.resolve()
    return None


def measure_trust(repo: Path, ref: str | None) -> tuple[dict[str, dict] | None, str, str]:
    """(sites, resolved commit, why-unknown). `ref is None` reads `repo` as a
    plain directory (the self-test's synthetic tree); otherwise every file is
    read at `ref` with `git show`, never from the checkout's working tree."""
    hits: list[dict] = []
    if ref is None:
        for path in sorted(repo.rglob("*.rs")):
            rel = path.relative_to(repo).as_posix()
            if _trust_is_scanned(rel):
                hits.extend(scan_text(path.read_text(errors="replace"), rel))
        return group_sites(hits, "trust"), "", ""
    resolved = _git(repo, "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}")
    if resolved.returncode != 0 or not resolved.stdout.strip():
        return None, "", f"{repo} does not hold commit {ref}"
    commit = resolved.stdout.strip()
    pattern = (
        LABEL_NAMES.replace("(?:", "(") + "|KernelTheory|" + "|".join(ROOT_IDENTS)
        + "|" + _PRODUCER_PREFILTER.replace("(?:", "(")
    )
    listed = _git(repo, "grep", "-l", "-E", pattern, commit, "--", "*.rs")
    if listed.returncode not in (0, 1):
        return None, commit, f"git grep failed in {repo}: {listed.stderr.strip()[:200]}"
    for line in listed.stdout.splitlines():
        rel = line.split(":", 1)[1] if ":" in line else line
        if not _trust_is_scanned(rel):
            continue
        shown = _git(repo, "show", f"{commit}:{rel}")
        if shown.returncode != 0:
            return None, commit, f"cannot read {rel} at {commit[:12]}"
        hits.extend(scan_text(shown.stdout, rel))
    return group_sites(hits, "trust"), commit, ""


def blank_toml_comments(text: str) -> str:
    """Drop `# ...` comments of a TOML file, leaving `#` inside a quoted string."""
    out: list[str] = []
    for line in text.splitlines():
        quote = ""
        cut = len(line)
        i = 0
        while i < len(line):
            ch = line[i]
            if quote:
                if ch == "\\" and quote == '"':
                    i += 1
                elif ch == quote:
                    quote = ""
            elif ch in ('"', "'"):
                quote = ch
            elif ch == "#":
                cut = i
                break
            i += 1
        out.append(line[:cut])
    return "\n".join(out)


def manifest_links(raw: str) -> list[str]:
    """The checker crates and outside carriers a manifest names outside comments."""
    return sorted(set(m.group(1) for m in _LINK_RE.finditer(blank_toml_comments(raw))))


def _link_row(rel: str, names: list[str]) -> dict:
    return {"id": f"trust-link:{rel}", "manifest": rel, "names": names}


def measure_trust_links(repo: Path, ref: str | None) -> dict[str, dict] | None:
    """Every Trust manifest outside the skipped prefixes that names a Clean
    checker crate or an outside carrier. `ref is None` reads a directory."""
    rows: dict[str, dict] = {}
    if ref is None:
        for path in sorted(repo.rglob("Cargo.toml")):
            rel = path.relative_to(repo).as_posix()
            names = manifest_links(path.read_text(errors="replace"))
            if names and not rel.startswith(_TRUST_SKIP_PREFIXES):
                rows[f"trust-link:{rel}"] = _link_row(rel, names)
        return rows
    resolved = _git(repo, "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}")
    if resolved.returncode != 0 or not resolved.stdout.strip():
        return None
    commit = resolved.stdout.strip()
    listed = _git(
        repo, "grep", "-l", "-E", "|".join(CHECKER_CRATES + OUTSIDE_CARRIERS), commit, "--", "*Cargo.toml"
    )
    if listed.returncode not in (0, 1):
        return None
    for line in listed.stdout.splitlines():
        rel = line.split(":", 1)[1] if ":" in line else line
        if rel.startswith(_TRUST_SKIP_PREFIXES) or not rel.endswith("Cargo.toml"):
            continue
        shown = _git(repo, "show", f"{commit}:{rel}")
        if shown.returncode != 0:
            return None
        names = manifest_links(shown.stdout)
        if names:
            rows[f"trust-link:{rel}"] = _link_row(rel, names)
    return rows


def compare_links(measured: dict[str, dict], recorded: list[dict], label: str) -> list[str]:
    problems: list[str] = []
    by_id = {r.get("id"): r for r in recorded}
    for rid, row in sorted(measured.items()):
        prior = by_id.get(rid)
        if prior is None:
            problems.append(
                f"UNNAMED LINK: {row['manifest']} in the {label} tree names {', '.join(row['names'])} "
                f"and the artifact does not list it: a route into Clean's checkers nobody has read"
            )
            continue
        if sorted(prior.get("names") or []) != row["names"]:
            problems.append(
                f"LINK MOVED: {row['manifest']} names {row['names']}; the artifact records "
                f"{prior.get('names')}"
            )
        if any(n in ROUTED_NAMES for n in row["names"]):
            route = prior.get("route")
            missing = [f for f in ROUTE_FIELDS if not str((route or {}).get(f) or "").strip()]
            if not isinstance(route, dict) or missing:
                problems.append(
                    f"UNCLASSIFIED LINK: {rid} links {[n for n in row['names'] if n in ROUTED_NAMES]} "
                    f"and its `route` lacks {missing or list(ROUTE_FIELDS)}: say through what the "
                    f"checker is reached, what it accepts and what was read"
                )
    for rid in sorted(set(by_id) - set(measured)):
        problems.append(f"STALE LINK: {rid} is in the artifact and no longer in the {label} tree")
    return problems


def _merge_links(measured: dict[str, dict], recorded: list[dict]) -> list[dict]:
    old = {r.get("id"): r for r in recorded}
    out = []
    for rid in sorted(measured):
        row = dict(measured[rid])
        if isinstance((old.get(rid) or {}).get("route"), dict):
            row["route"] = old[rid]["route"]
        out.append(row)
    return out


# ---------------------------------------------------------------------------
# The artifact.
# ---------------------------------------------------------------------------


def load_artifact(root: Path) -> dict:
    path = root / ARTIFACT_REL
    if not path.exists():
        return {"schema": SCHEMA, "clean": {"sites": [], "entries": []}, "trust": {"sites": []}}
    return json.loads(path.read_text())


def _classification_problems(row: dict) -> list[str]:
    """What is wrong with a `construct`/`call` row's classification."""
    rid = row["id"]
    out: list[str] = []
    cls = row.get("class")
    if cls not in CLASSES:
        return [f"UNCLASSIFIED: {rid} has no `class` (one of {', '.join(CLASSES)})"]
    checker = row.get("checker") or {}
    kind = checker.get("kind")
    if kind not in CHECKER_KINDS:
        out.append(f"UNCLASSIFIED: {rid} names no checker.kind (one of {', '.join(CHECKER_KINDS)})")
    if kind == "clean-kernel":
        if checker.get("entry") not in KERNEL_ENTRIES:
            out.append(f"UNCLASSIFIED: {rid} is clean-kernel with no checker.entry ({', '.join(KERNEL_ENTRIES)})")
        if checker.get("theory") not in THEORIES[:-1]:
            out.append(f"UNCLASSIFIED: {rid} is clean-kernel with no checker.theory ({', '.join(THEORIES[:-1])})")
    if kind == "unexamined":
        if not rid.startswith("trust:"):
            out.append(
                f"UNCLASSIFIED: {rid} is a Clean site with checker.kind unexamined; that kind "
                f"exists for the Trust half only, and a Clean site is read before it is named"
            )
        if not str(checker.get("detail") or "").strip():
            out.append(f"UNCLASSIFIED: {rid} is unexamined and has no checker.detail saying what the site shows")
    if rid.startswith("trust:") and not str(row.get("tcb") or "").strip():
        out.append(
            f"UNCLASSIFIED: {rid} does not say what Trust's docs/TCB.md says about it (`tcb`; "
            f"\"not named\" is an answer, an absent field is not)"
        )
    if cls == "mint" and kind in ("inherits", "not-a-mint"):
        out.append(f"INCONSISTENT: {rid} is class mint with checker.kind {kind}")
    if cls == "threshold" and kind != "not-a-mint":
        out.append(f"INCONSISTENT: {rid} is class threshold; its checker.kind must be not-a-mint")
    if cls == "relabel" and kind != "inherits":
        out.append(f"INCONSISTENT: {rid} is class relabel; its checker.kind must be inherits")
    if not str(row.get("mints") or "").strip():
        out.append(f"UNCLASSIFIED: {rid} does not say what it mints (`mints`)")
    if row.get("reach") not in REACH:
        out.append(f"UNCLASSIFIED: {rid} has no `reach` (one of {', '.join(REACH)})")
    if "kcheck_rung" not in row or row["kcheck_rung"] not in (None, 2, 3, 4, 5, 6):
        out.append(f"UNCLASSIFIED: {rid} has no `kcheck_rung` (a rung 2-6, or null with `rung_note`)")
    elif row["kcheck_rung"] is None and not str(row.get("rung_note") or "").strip():
        out.append(f"UNCLASSIFIED: {rid} has kcheck_rung null and no `rung_note` saying why")
    tokens = row.get("evidence_tokens")
    if not isinstance(tokens, list) or any(not isinstance(t, str) or not t for t in tokens):
        out.append(f"UNCLASSIFIED: {rid} needs `evidence_tokens` (a list, possibly empty)")
    elif cls == "mint" and kind == "clean-kernel" and not tokens:
        out.append(
            f"UNCLASSIFIED: {rid} claims a Clean-kernel check and names no evidence token in "
            f"its function; a kernel claim with nothing to re-derive is a label"
        )
    return out


def _has_token(body: str, token: str) -> bool:
    return re.search(r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])", body) is not None


def _has_call(body: str, name: str) -> bool:
    """`name(` or `name::<..>(` in code position (the body is already blanked)."""
    return (
        re.search(
            r"(?<![A-Za-z0-9_])" + re.escape(name) + r"\s*(?:::\s*<[^;{}()]*>\s*)?\(", body
        )
        is not None
    )


def function_body(text: str, rel: str, symbol: str) -> tuple[str | None, str]:
    """The blanked body of the ONE production fn of `text` named `symbol`
    (`fn` or `Type::fn`, as `Structure.symbol_at` names it), or (None, why)."""
    try:
        structure = Structure(text, rel)
    except ValueError as exc:
        return None, str(exc)
    spans = [
        (start, end)
        for start, end, kind, _name, test in structure.spans
        if kind == "fn" and not test and structure.symbol_at(start)[0] == symbol
    ]
    if len(spans) != 1:
        return None, f"{len(spans)} production function(s) named `{symbol}` in {rel}"
    return text[spans[0][0] : spans[0][1]], ""


def check_wrappers(
    wrappers: list[dict], read, label: str, base: frozenset[str] = frozenset()
) -> tuple[list[str], frozenset[str]]:
    """Declared wrappers of a kernel entry: each is a production function that
    calls, in code position, a kernel entry or another declared wrapper, and
    each hop is checked here. Returns (problems, the names a kernel-classified
    mint may cite as its evidence). `read(rel)` gives a file's raw text or None.
    A wrapper whose chain does not reach a KERNEL_ENTRY_CALLS member (or a name
    in `base`, wrappers already admitted from another tree) through checked
    hops is refused, so a cycle of wrappers vouching for each other admits
    nothing. A wrapper is matched by NAME at the citing site: the site's call
    is not resolved to the declared file, so a same-named function elsewhere
    would also satisfy it (stated in the artifact's limits)."""
    problems: list[str] = []
    calls_of: dict[str, set[str]] = {}
    for w in wrappers:
        wid = f"{label} wrapper {w.get('name', '?')}"
        missing = [f for f in WRAPPER_FIELDS if not w.get(f)]
        if missing:
            problems.append(f"UNCLASSIFIED: {wid} lacks {missing}")
            continue
        name = str(w["name"])
        if name in KERNEL_ENTRY_CALLS:
            problems.append(f"SHAPE: {wid} is a kernel entry itself; list it in KERNEL_ENTRY_CALLS, not as a wrapper")
            continue
        if name in calls_of:
            problems.append(f"DUPLICATE: {wid} is declared twice")
            continue
        if str(w["symbol"]).rsplit("::", 1)[-1] != name:
            problems.append(f"SHAPE: {wid} names symbol `{w['symbol']}`, whose function is not `{name}`")
            continue
        raw = read(str(w["file"]))
        if raw is None:
            problems.append(f"STALE ROW: {wid} anchors to {w['file']}, which cannot be read")
            continue
        body, why = function_body(lexer.strip_noncode(raw), str(w["file"]), str(w["symbol"]))
        if body is None:
            problems.append(f"STALE ROW: {wid} anchors to `{w['symbol']}`: {why}")
            continue
        made = {c for c in w["calls"] if isinstance(c, str) and _has_call(body, c)}
        lost = sorted(set(w["calls"]) - made)
        if lost:
            problems.append(
                f"CHECKER MOVED: {wid} records that `{w['symbol']}` calls {lost}, and it no longer "
                f"calls them in code position"
            )
        calls_of[name] = made
    admitted: set[str] = set()
    changed = True
    while changed:
        changed = False
        for name, made in calls_of.items():
            if name not in admitted and any(
                c in KERNEL_ENTRY_CALLS or c in base or c in admitted for c in made
            ):
                admitted.add(name)
                changed = True
    for name in sorted(set(calls_of) - admitted):
        problems.append(
            f"KERNEL EVIDENCE: {label} wrapper {name} reaches no kernel entry through checked "
            f"calls (it calls {sorted(calls_of[name])})"
        )
    return problems, frozenset(admitted)


def _kernel_evidence_problem(rid: str, row: dict, body: str, symbol: str, kernel_calls: frozenset[str]) -> str:
    """The tightened rule for a mint classified clean-kernel ("" when it holds)."""
    tokens = [t for t in row.get("evidence_tokens") or [] if isinstance(t, str)]
    if any(t in kernel_calls and _has_call(body, t) for t in tokens):
        return ""
    return (
        f"KERNEL EVIDENCE: {rid} is a mint classified clean-kernel, and none of its evidence "
        f"tokens {tokens} is a kernel entry (KERNEL_ENTRY_CALLS) or a declared wrapper of one "
        f"that `{symbol}` calls in code position. Re-read the site: it carries a verdict minted "
        f"elsewhere (class relabel, checker inherits), or it mints with no kernel check at the "
        f"site (checker none / in-repo-checker / external-tool, which puts it on first_risk)"
    )


def first_risk_ids(rows: list[dict]) -> list[str]:
    return sorted(
        r["id"]
        for r in rows
        if r.get("role") in CLASSIFIED_ROLES
        and r.get("class") == "mint"
        and (r.get("checker") or {}).get("kind") in FIRST_RISK_KINDS
    )


def compare(
    measured: dict[str, dict],
    recorded: list[dict],
    label: str,
    kernel_calls: frozenset[str] = frozenset(KERNEL_ENTRY_CALLS),
) -> list[str]:
    problems: list[str] = []
    by_id: dict[str, dict] = {}
    for row in recorded:
        rid = row.get("id")
        if rid in by_id:
            problems.append(f"DUPLICATE: {rid} is listed twice")
        by_id[rid] = row
    for rid, site in sorted(measured.items()):
        row = by_id.get(rid)
        where = f"{site['file']}:{site['lines'][0]}"
        if row is None:
            problems.append(
                f"UNNAMED SITE: {rid} ({where}, {site['count']} occurrence(s)) is in the "
                f"{label} tree and the artifact does not name it"
            )
            continue
        if row.get("count") != site["count"]:
            problems.append(
                f"COUNT MOVED: {rid} has {site['count']} occurrence(s) at {where}; the artifact "
                f"records {row.get('count')}"
            )
        if site["role"] in CLASSIFIED_ROLES:
            problems.extend(_classification_problems(row))
            for token in row.get("evidence_tokens") or []:
                if isinstance(token, str) and token and not _has_token(site["_body"], token):
                    problems.append(
                        f"CHECKER MOVED: {rid} records `{token}` as the evidence of its checker, "
                        f"and `{site['symbol']}` no longer names it in code. Re-read the site and "
                        f"re-classify it"
                    )
            if row.get("class") == "mint" and (row.get("checker") or {}).get("kind") == "clean-kernel":
                why = _kernel_evidence_problem(rid, row, site["_body"], site["symbol"], kernel_calls)
                if why:
                    problems.append(why)
    for rid in sorted(set(by_id) - set(measured)):
        problems.append(f"STALE ROW: {rid} is in the artifact and no longer in the {label} tree")
    return problems


def check_entries(
    root: Path, entries: list[dict], kernel_calls: frozenset[str] = frozenset(KERNEL_ENTRY_CALLS)
) -> list[str]:
    """The hand-anchored verbs: the anchor function exists and shows its evidence;
    one classified clean-kernel calls a kernel entry or a declared wrapper."""
    problems: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        eid = entry.get("id", "?")
        if eid in seen:
            problems.append(f"DUPLICATE: entry {eid} is listed twice")
        seen.add(eid)
        for field in ("verb", "file", "symbol", "accepts", "reach"):
            if not str(entry.get(field) or "").strip():
                problems.append(f"UNCLASSIFIED: entry {eid} has no `{field}`")
        probe = dict(entry, role="call", **{"class": "mint"})
        probe.setdefault("mints", entry.get("accepts"))
        problems.extend(p for p in _classification_problems(probe) if "`class`" not in p)
        path = root / str(entry.get("file"))
        if not path.is_file():
            problems.append(f"STALE ROW: entry {eid} anchors to {entry.get('file')}, which is gone")
            continue
        text = lexer.strip_noncode(path.read_text(errors="replace"))
        want = str(entry.get("symbol"))
        body, why = function_body(text, str(entry.get("file")), want)
        if body is None:
            problems.append(f"STALE ROW: entry {eid} anchors to `{want}`: {why}")
            continue
        for token in entry.get("evidence_tokens") or []:
            if not _has_token(body, token):
                problems.append(
                    f"CHECKER MOVED: entry {eid} records `{token}` as the evidence of its "
                    f"checker, and `{want}` no longer names it in code"
                )
        if (entry.get("checker") or {}).get("kind") == "clean-kernel":
            why = _kernel_evidence_problem(f"entry {eid}", entry, body, want, kernel_calls)
            if why:
                problems.append(why)
    return problems


def _reader_dir(base: Path):
    def read(rel: str) -> str | None:
        path = base / rel
        return path.read_text(errors="replace") if path.is_file() else None
    return read


def _reader_commit(repo: Path, commit: str):
    def read(rel: str) -> str | None:
        shown = _git(repo, "show", f"{commit}:{rel}")
        return shown.stdout if shown.returncode == 0 else None
    return read


def _trust_clean_wrappers(root: Path, trust: dict, dir_mode: bool) -> tuple[list[str], frozenset[str]]:
    """`trust.clean_wrappers`: Clean functions that Trust sites call, checked at
    `trust.clean_pin` in this repository (in dir mode, the self-test's Clean tree)."""
    wrappers = trust.get("clean_wrappers") or []
    if not wrappers:
        return [], frozenset()
    pin = str(trust.get("clean_pin") or "")
    if dir_mode:
        return check_wrappers(wrappers, _reader_dir(root), "Clean@trust.clean_pin")
    if not re.fullmatch(r"[0-9a-f]{40}", pin):
        return [f"SHAPE: trust.clean_wrappers needs trust.clean_pin, a full commit sha (it is {pin!r})"], frozenset()
    return check_wrappers(wrappers, _reader_commit(root, pin), f"Clean@{pin[:12]} (trust.clean_pin)")


# The first-risk ceiling (plan unit P7: "its count is a ratchet that only
# falls"). `first_risk_limit` is the ceiling and `first_risk_history` the dated
# record of every move: `--write` lowers it when mints leave the list and
# records that; it rises only through `--write --rebase-risk '<reason>'`, for a
# census correction that finds mints which were already in the tree. The last
# history entry must state the ceiling, so a hand edit of the number alone is
# refused.
def risk_ratchet_problems(artifact: dict, derived: list[str]) -> list[str]:
    limit = artifact.get("first_risk_limit")
    history = artifact.get("first_risk_history")
    if type(limit) is not int or limit < 0:
        return ["FIRST RISK RATCHET: first_risk_limit must be a nonnegative integer (the ceiling on first_risk)"]
    if not isinstance(history, list) or not history or not all(isinstance(e, dict) for e in history):
        return ["FIRST RISK RATCHET: first_risk_history is empty or malformed: every move of the ceiling is recorded"]
    out: list[str] = []
    for i, entry in enumerate(history):
        if type(entry.get("to")) is not int or not str(entry.get("date") or "").strip() or not str(
            entry.get("why") or ""
        ).strip():
            out.append(f"FIRST RISK RATCHET: first_risk_history[{i}] needs `date`, an integer `to` and `why`")
    if history[-1].get("to") != limit:
        out.append(
            f"FIRST RISK RATCHET: first_risk_limit is {limit} and the last first_risk_history entry "
            f"records {history[-1].get('to')}: the ceiling moves only through `--write` (down) or "
            f"`--write --rebase-risk '<reason>'` (up), and each records itself"
        )
    if len(derived) > limit:
        out.append(
            f"FIRST RISK RATCHET: {len(derived)} mints with no Clean-kernel check exceed the ceiling "
            f"{limit}. The list only falls (plan unit P7); a census correction that finds mints which "
            f"were already in the tree raises it only through `--write --rebase-risk '<reason>'`"
        )
    return out


def run(
    root: Path,
    trust_repo: str | None = None,
    trust_ref: str | None = None,
    require_trust: bool = False,
    trust_dir_mode: bool = False,
    clean_only: bool = False,
) -> int:
    artifact = load_artifact(root)
    problems: list[str] = []
    if artifact.get("schema") != SCHEMA:
        problems.append(f"SHAPE: {ARTIFACT_REL} schema is {artifact.get('schema')!r}, expected {SCHEMA!r}")
    clean = artifact.get("clean") or {}
    wrapper_problems, clean_wrappers = check_wrappers(
        clean.get("kernel_entry_wrappers") or [], _reader_dir(root), "Clean"
    )
    problems.extend(wrapper_problems)
    clean_calls = frozenset(KERNEL_ENTRY_CALLS) | clean_wrappers
    measured, errors = measure_clean(root)
    problems.extend(errors)
    clean_rows = clean.get("sites") or []
    problems.extend(compare(measured, clean_rows, "Clean", clean_calls))
    problems.extend(check_entries(root, clean.get("entries") or [], clean_calls))

    trust = artifact.get("trust") or {}
    trust_rows = trust.get("sites") or []
    trust_state = "unknown"
    why = ""
    repo = Path(trust_repo) if trust_dir_mode and trust_repo else find_trust_repo(root, trust_repo)
    if clean_only:
        trust_state = "skipped"
        why = "--clean-only (the Clean half needs no sibling checkout; the full-mode leg runs both halves)"
    elif repo is None:
        why = "no Trust checkout beside this one (pass --trust-repo or set CLEAN_TRUST_REPO)"
    else:
        ref = None if trust_dir_mode else (trust_ref or trust.get("commit"))
        if not trust_dir_mode and not ref:
            why = "the artifact names no Trust commit"
        else:
            trust_measured, commit, why = measure_trust(repo, ref)
            if trust_measured is not None:
                trust_state = "checked"
                reader = _reader_dir(repo) if trust_dir_mode else _reader_commit(repo, commit)
                # Clean functions a Trust site calls are read at the Clean
                # commit Trust builds against (trust.clean_pin), never at this
                # tree: the wrapper Trust links is the pinned one.
                found, pin_wrappers = _trust_clean_wrappers(root, trust, trust_dir_mode)
                more, trust_wrappers = check_wrappers(
                    trust.get("kernel_entry_wrappers") or [],
                    reader,
                    f"Trust@{commit[:12] or 'dir'}",
                    base=pin_wrappers,
                )
                found += more
                found += compare(
                    trust_measured,
                    trust_rows,
                    f"Trust@{commit[:12] or 'dir'}",
                    frozenset(KERNEL_ENTRY_CALLS) | trust_wrappers | pin_wrappers,
                )
                if trust_ref and commit != trust.get("commit"):
                    found = [f"{p} [Trust read at {trust_ref} = {commit[:12]}, pinned {str(trust.get('commit'))[:12]}]" for p in found]
                links = measure_trust_links(repo, None if trust_dir_mode else commit)
                if links is None:
                    found.append(f"TRUST LINKS: the manifests of {repo} could not be read at {commit[:12]}")
                else:
                    found.extend(compare_links(links, trust.get("links") or [], f"Trust@{commit[:12] or 'dir'}"))
                problems.extend(found)

    recorded_risk = sorted(artifact.get("first_risk") or [])
    derived_risk = first_risk_ids(clean_rows + trust_rows)
    problems.extend(risk_ratchet_problems(artifact, derived_risk))
    if recorded_risk != derived_risk:
        missing = sorted(set(derived_risk) - set(recorded_risk))
        extra = sorted(set(recorded_risk) - set(derived_risk))
        problems.append(
            "FIRST RISK: the header list of mints with no Clean-kernel check behind them is not "
            f"what the rows derive (missing {missing[:5]}{'...' if len(missing) > 5 else ''}, "
            f"extra {extra[:5]}{'...' if len(extra) > 5 else ''}); `--write` re-derives it"
        )

    counts = Counter(s["role"] for s in measured.values())
    if problems:
        print(f"AUTHORITY_SITES=fail problems={len(problems)}")
        for p in problems:
            print(f"  FAIL: {p}")
        print(
            "  A new or moved site is reviewed, not waved through: read it, then "
            "`python3 scripts/check_authority_sites.py --write` refreshes counts and lines and "
            "adds the row; a `construct`/`call` row then needs its classification by hand."
        )
        return 1
    if trust_state != "checked":
        print(f"AUTHORITY_SITES trust_half={trust_state} reason={why}")
        if require_trust:
            return 3
    classified = sum(counts[r] for r in CLASSIFIED_ROLES)
    print(
        f"AUTHORITY_SITES=ok clean_sites={len(measured)} classified={classified} "
        f"counted={sum(counts[r] for r in COUNTED_ROLES)} entries={len(clean.get('entries') or [])} "
        f"wrappers={len(clean_wrappers)} trust_half={trust_state} trust_sites={len(trust_rows)} "
        f"trust_links={len(trust.get('links') or [])} first_risk={len(derived_risk)} "
        f"first_risk_limit={artifact.get('first_risk_limit')}"
    )
    return 0


# ---------------------------------------------------------------------------
# --write: refresh what is derived, keep what was decided.
# ---------------------------------------------------------------------------

_DERIVED_FIELDS = ("id", "file", "symbol", "family", "token", "role", "count", "lines")


def _merge(measured: dict[str, dict], recorded: list[dict]) -> list[dict]:
    old = {r.get("id"): r for r in recorded}
    out: list[dict] = []
    for rid in sorted(measured):
        site = measured[rid]
        row = {k: site[k] for k in _DERIVED_FIELDS}
        prior = old.get(rid) or {}
        for key, value in prior.items():
            if key not in _DERIVED_FIELDS:
                row[key] = value
        if site["role"] in CLASSIFIED_ROLES and "class" not in row:
            row["class"] = None
        out.append(row)
    return out


def summarize(rows: list[dict]) -> dict:
    """Counts a reader wants first, derived from the rows (never hand-kept)."""
    by_role = Counter(r["role"] for r in rows)
    occurrences = Counter()
    for r in rows:
        occurrences[r["role"]] += r["count"]
    mints = [r for r in rows if r.get("role") in CLASSIFIED_ROLES and r.get("class") == "mint"]
    by_checker: dict[str, int] = Counter()
    for r in mints:
        checker = r.get("checker") or {}
        kind = checker.get("kind") or "unclassified"
        if kind == "clean-kernel":
            kind = f"clean-kernel/{checker.get('entry')}/{checker.get('theory')}"
        by_checker[kind] += 1
    return {
        "sites_by_role": dict(sorted(by_role.items())),
        "occurrences_by_role": dict(sorted(occurrences.items())),
        "classified_sites_by_class": dict(
            sorted(Counter(str(r.get("class")) for r in rows if r.get("role") in CLASSIFIED_ROLES).items())
        ),
        "mint_sites_by_checker": dict(sorted(by_checker.items())),
        "mint_sites_by_rung": dict(
            sorted(Counter(str(r.get("kcheck_rung")) for r in mints).items())
        ),
    }


def _move_risk_ceiling(artifact: dict, derived: list[str], rebase_reason: str | None) -> str:
    """Apply the ceiling's rules to `artifact` in place; "" or why --write refuses."""
    limit = artifact.get("first_risk_limit")
    history = artifact.get("first_risk_history")
    history = list(history) if isinstance(history, list) else []
    today = date.today().isoformat()
    count = len(derived)
    if rebase_reason is not None:
        if not rebase_reason.strip():
            return "--rebase-risk needs a reason: what the census now sees that was already in the tree"
        if type(limit) is int and count <= limit:
            return (
                f"--rebase-risk raises the ceiling only: {count} first-risk mints do not exceed "
                f"the ceiling {limit} (a plain --write lowers it)"
            )
        history.append({"date": today, "from": limit if type(limit) is int else None, "to": count,
                        "kind": "rebase-up", "why": rebase_reason.strip()})
    elif type(limit) is not int:
        return (
            "the artifact has no first_risk_limit: the first --write that sets the ceiling takes "
            "--rebase-risk '<what the count is and why>'"
        )
    elif count > limit:
        return (
            f"{count} first-risk mints exceed the ceiling {limit}; nothing was written. A new mint with "
            f"no kernel check is not waved through: give it a checker's token or a label that does not "
            f"say kernel. A census correction that finds mints already in the tree is "
            f"`--write --rebase-risk '<reason>'`"
        )
    elif count < limit:
        history.append({"date": today, "from": limit, "to": count, "kind": "lowered",
                        "why": f"lowered by --write: {limit - count} mint(s) left first_risk"})
    else:
        return ""
    artifact["first_risk_limit"] = count
    artifact["first_risk_history"] = history
    return ""


def write(root: Path, trust_repo: str | None, trust_ref: str | None, rebase_reason: str | None = None) -> int:
    artifact = load_artifact(root)
    measured, errors = measure_clean(root)
    if errors:
        for e in errors:
            print(f"  FAIL: {e}")
        return 1
    clean = artifact.setdefault("clean", {})
    clean["sites"] = _merge(measured, clean.get("sites") or [])
    clean.setdefault("entries", [])
    clean["summary"] = summarize(clean["sites"])
    trust = artifact.setdefault("trust", {})
    repo = find_trust_repo(root, trust_repo)
    ref = trust_ref or trust.get("commit")
    if repo is not None and ref:
        trust_measured, commit, why = measure_trust(repo, ref)
        if trust_measured is None:
            print(f"  trust half left as recorded: {why}")
        else:
            trust["commit"] = commit
            trust["sites"] = _merge(trust_measured, trust.get("sites") or [])
            trust["summary"] = summarize(trust["sites"])
            links = measure_trust_links(repo, commit)
            if links is not None:
                trust["links"] = _merge_links(links, trust.get("links") or [])
    else:
        print("  trust half left as recorded: no Trust checkout or no commit to read")
    artifact["schema"] = SCHEMA
    derived_risk = first_risk_ids(clean["sites"] + (trust.get("sites") or []))
    refused = _move_risk_ceiling(artifact, derived_risk, rebase_reason)
    if refused:
        print(f"  FAIL: FIRST RISK RATCHET: {refused}")
        return 1
    artifact["first_risk"] = derived_risk
    (root / ARTIFACT_REL).write_text(json.dumps(artifact, indent=1, ensure_ascii=False) + "\n")
    open_rows = [
        r["id"]
        for r in clean["sites"] + (trust.get("sites") or [])
        if r["role"] in CLASSIFIED_ROLES and _classification_problems(r)
    ]
    print(
        f"wrote {ARTIFACT_REL}: clean sites {len(clean['sites'])}, trust sites "
        f"{len(trust.get('sites') or [])}, rows still needing a classification {len(open_rows)}"
    )
    for rid in open_rows[:40]:
        print(f"  needs classification: {rid}")
    return 0


# ---------------------------------------------------------------------------
# Self-test: a synthetic tree, mutated one way per arm.
# ---------------------------------------------------------------------------

_SELFTEST_LIB = """\
pub enum TrustLevel {
    KernelVerified,
    Unverified,
}

pub fn stamp(env: &mut Env, d: Decl) -> TrustLevel {
    // a comment naming TrustLevel::KernelVerified is prose
    let note = "TrustLevel::KernelVerified in a string is prose";
    match env.add_decl(d) {
        Ok(()) => TrustLevel::KernelVerified,
        Err(_) => TrustLevel::Unverified,
    }
}

pub fn is_kv(t: &TrustLevel) -> bool {
    matches!(t, TrustLevel::KernelVerified)
}

pub fn replay_base() -> Environment {
    Environment::for_lean_replay()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn t() {
        let _ = TrustLevel::KernelVerified;
        let _ = Environment::for_lean_replay();
    }
}
"""

_SELFTEST_TRUST = """\
pub struct ReferenceCertificate { d: [u8; 32] }

impl ReferenceCertificate {
    pub(crate) fn from_accepted(token: ReferenceAccepted) -> Self {
        Self { d: token.decl_digest() }
    }
}

pub fn certify(kernel: &ReferenceKernel, ty: &Expr, val: &Expr) -> Option<ReferenceCertificate> {
    kernel.check_closed_term(ty, val).map(ReferenceCertificate::from_accepted).ok()
}
"""


def _classified(row: dict, **over) -> dict:
    base = {
        "class": "mint",
        "mints": "selftest label",
        "checker": {"kind": "clean-kernel", "entry": "add_decl", "theory": "Extended"},
        "evidence_tokens": ["add_decl"],
        "reach": "internal",
        "kcheck_rung": 2,
    }
    base.update(over)
    row.update(base)
    return row


def _selftest_tree() -> tuple[Path, Path]:
    tmp = Path(tempfile.mkdtemp(prefix="authority_sites_selftest_"))
    root = tmp / "clean"
    trust = tmp / "trust"
    (root / ".git").mkdir(parents=True)
    (root / "data").mkdir()
    (root / "crates" / "c" / "src").mkdir(parents=True)
    (root / "crates" / "c" / "src" / "lib.rs").write_text(_SELFTEST_LIB)
    (trust / "crates" / "trust-certify" / "src").mkdir(parents=True)
    (trust / "crates" / "trust-certify" / "src" / "reference_mint.rs").write_text(_SELFTEST_TRUST)
    measured, errors = measure_clean(root)
    assert not errors, errors
    rows = _merge(measured, [])
    for row in rows:
        if row["role"] not in CLASSIFIED_ROLES:
            continue
        if row["family"] == "label":
            _classified(row)
        else:
            _classified(
                row,
                **{
                    "class": "root",
                    "checker": {"kind": "clean-kernel", "entry": "replay", "theory": "Lean"},
                    "evidence_tokens": ["for_lean_replay"],
                },
            )
    (trust / "crates" / "trust-certify" / "Cargo.toml").write_text(
        '[dependencies]\n# clean-ck0 is named here only in a comment\n'
        'clean-kernel = { path = "../../first-party/clean/crates/clean-kernel" }\n'
    )
    (trust / "crates" / "trust-temporal").mkdir(parents=True)
    (trust / "crates" / "trust-temporal" / "Cargo.toml").write_text(
        '[dependencies]\ntla-check = { path = "../../first-party/ty/crates/tla-check", features = ["clean-cic"] }\n'
    )
    link_rows = _merge_links(measure_trust_links(trust, None) or {}, [])
    for row in link_rows:
        if any(n in ROUTED_NAMES for n in row["names"]):
            row["route"] = {"via": "selftest carrier", "reaches": "clean-kernel", "what": "selftest", "examined": "selftest"}
    trust_measured, _, _ = measure_trust(trust, None)
    trust_rows = _merge(trust_measured or {}, [])
    for row in trust_rows:
        if row["role"] in CLASSIFIED_ROLES:
            _classified(
                row,
                **{
                    "class": "root",
                    "checker": {"kind": "clean-kernel", "entry": "reference", "theory": "LeanReference"},
                    "evidence_tokens": [],
                    "reach": "trust",
                    "tcb": "selftest: not a real Trust tree",
                },
            )
    artifact = {
        "schema": SCHEMA,
        "first_risk": [],
        "first_risk_limit": 0,
        "first_risk_history": [{"date": "2026-11-12", "from": None, "to": 0, "kind": "rebase-up", "why": "selftest"}],
        "clean": {
            "sites": rows,
            "entries": [
                {
                    "id": "entry:selftest-stamp",
                    "verb": "selftest stamp",
                    "file": "crates/c/src/lib.rs",
                    "symbol": "stamp",
                    "accepts": "a declaration",
                    "mints": "a declaration",
                    "checker": {"kind": "clean-kernel", "entry": "add_decl", "theory": "Extended"},
                    "evidence_tokens": ["add_decl"],
                    "reach": "internal",
                    "kcheck_rung": 2,
                }
            ],
        },
        "trust": {"commit": "", "sites": trust_rows, "links": link_rows},
    }
    (root / ARTIFACT_REL).write_text(json.dumps(artifact, indent=1) + "\n")
    return root, trust


def _quiet(root: Path, trust: Path) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root, trust_repo=str(trust), trust_dir_mode=True)
    return rc, buf.getvalue()


_ROLE_CASES = (
    ("fn f() -> T { TrustLevel::KernelVerified }", "construct"),
    ("fn f() { let x = Some(TrustLevel::KernelVerified); }", "construct"),
    ("fn f() { xs.iter().map(|_| TrustLevel::KernelVerified); }", "construct"),
    ("fn f() { xs.iter().map(|| TrustLevel::KernelVerified); }", "construct"),
    ("fn f() { let r = Row { trust: TrustLevel::KernelVerified, n: 1 }; }", "construct"),
    ("fn f() { let b = ImportConfidence::KernelVerified as u8; }", "construct"),
    ("fn f() { set(TrustLevel::KernelVerified); }", "construct"),
    ("fn f(x: T) -> u8 { match x { A::B => TrustLevel::KernelVerified, _ => y } }", "construct"),
    ("fn f(x: T) -> u8 { match x { TrustLevel::KernelVerified => 1, _ => 0 } }", "read"),
    ("fn f(x: T) -> u8 { match x { T::A | TrustLevel::KernelVerified => 1, _ => 0 } }", "read"),
    ("fn f(x: T) -> u8 { match x { TrustLevel::KernelVerified | T::A => 1, _ => 0 } }", "read"),
    ("fn f(x: T) -> u8 { match x { TrustLevel::KernelVerified if g() => 1, _ => 0 } }", "read"),
    ("fn f(x: T) -> u8 { match x { P::KernelVerified(_) => 1, _ => 0 } }", "read"),
    ("fn f(x: T) -> u8 { match x { Ok(P::KernelVerified) => 1, _ => 0 } }", "read"),
    ("fn f(x: T) -> bool { x == TrustLevel::KernelVerified }", "read"),
    ("fn f(x: T) -> bool { TrustLevel::KernelVerified != x }", "read"),
    ("fn f(x: T) -> bool { matches!(x, Ok(TrustLevel::KernelVerified)) }", "read"),
    ("fn f(x: T) { if let Some(TrustLevel::KernelVerified) = x { g(); } }", "read"),
    ("use crate::types::TrustLevel::KernelVerified;", "import"),
    ("enum E { KernelVerified, Other }", "def"),
    ("fn f() -> E { KernelVerified }", "construct"),
    # A suffixed name is a label only as a path's last segment; bare, it is a type.
    ("fn f() -> S { S::KernelVerifiedWithProof }", "construct"),
    ("fn f(m: KernelVerifiedHolder) {}", None),
    ("fn f(x: T) { let Some(a @ P::KernelCertified { e, .. }) = x else { return; }; }", "read"),
    # A multi-line `matches!` is one statement.
    ("fn f(x: T) -> bool { matches!(\n x,\n A::B\n | TrustLevel::KernelVerified\n ) }", "read"),
    # The sibling tiers (2026-11-12): matched like the core names.
    ("fn f() -> T { TrustLevel::AxiomDependent }", "construct"),
    ("fn f() -> T { TrustLevel::CertificateReplayed }", "construct"),
    ("fn f() -> R { AddConstResult::AxiomDischarged }", "construct"),
    ("fn f() -> P { ProofStatus::StructuralProved }", "construct"),
    ("fn f(p: &P) -> bool { matches!(p, ProofStatus::StructuralProved) }", "read"),
    ("fn f() -> R { AddConstResult::AxiomAccepted { axioms } }", "construct"),
    ("fn f() -> R { AddConstResult::UnsafeAccepted }", "construct"),
    ("fn f(x: T) -> u8 { match x { TrustLevel::CertificateReplayed => 1, _ => 0 } }", "read"),
    ("enum TrustLevel { AxiomDependent, Unverified }", "def"),
    ("fn f(m: AxiomDependentSet) {}", None),
)

# (source, producer token): every write of a kernel-named field is a construct.
_PRODUCER_CASES = (
    ("fn f(v: &mut R) { v.kernel_verified += 1; }", ["kernel_verified+="]),
    ("fn f(v: &mut R, n: Name) { v.kernel_verified_names.push(n); }", ["kernel_verified_names.push"]),
    ("fn f(v: &mut R, o: R) { v.kernel_verified_names.extend(o.kernel_verified_names); }",
     ["kernel_verified_names.extend"]),
    ("fn f(s: &mut S) { s.kernel_checked = true; }", ["kernel_checked=true"]),
    ("fn f() -> S { S { kernel_certified: true, n: 0 } }", ["kernel_certified:true"]),
    ("fn f(b: &mut B) { b.kernel_rechecked = true; }", ["kernel_rechecked=true"]),
    ("fn f(r: &mut R) { r.kernel_re_verified += 1; }", ["kernel_re_verified+="]),
    ("fn f(v: &R) -> bool { v.kernel_verified == 0 || v.kernel_checked == true }", []),
    ("fn f(v: &R) -> usize { v.kernel_verified_names.len() + v.total_kernel_verified }", []),
)

# (source, root token, role): the checker-root family.
_ROOT_ROLE_CASES = (
    ("fn f() { let e = Environment::for_lean_replay(); }", "for_lean_replay", "call"),
    ("fn f(k: &ReferenceKernel) { k.check_closed_term(a, b); }", "check_closed_term", "call"),
    ("fn f(k: &ReferenceKernel) { k.check_closed_term(a, b); }", "ReferenceKernel", "mention"),
    ("fn f() { let k = ReferenceKernel::new(env); }", "ReferenceKernel::new", "call"),
    ("fn f(e: &mut Env) { e.set_kernel_theory(KernelTheory::Lean); }", "KernelTheory::Lean", "construct"),
    ("fn f(e: &Env) -> bool { e.theory() == super::KernelTheory::Extended }", "KernelTheory::Extended", "read"),
    ("fn f(e: &Env) -> bool { matches!(e.theory(), KernelTheory::Lean) }", "KernelTheory::Lean", "read"),
    ("fn token(&self) -> ReferenceAccepted { ReferenceAccepted { d: self.d } }", "ReferenceAccepted", "construct"),
    ("fn token(&self) -> ReferenceAccepted { ReferenceAccepted { d: self.d } }", "ReferenceAccepted", "mention"),
    ("use clean_kernel::reference::ReferenceKernel;", "ReferenceKernel", "import"),
    # A return type before a body brace is a mention, borrowed or not; never a struct literal.
    ("impl C { fn r(&self) -> &ReferenceCertificate { &self.r } }", "ReferenceCertificate", "mention"),
    ("impl C { fn r(&self) -> &ReferenceCertificate { &self.r } }", "ReferenceCertificate", "!construct"),
    ("impl C { fn r(&mut self) -> &mut ReferenceKernel { &mut self.k } }", "ReferenceKernel", "!construct"),
    ("impl C { fn r(self) -> ReferenceKernel { self.k } }", "ReferenceKernel", "!construct"),
    ("fn f() { let m = KernelVerifiedManifest::from_report(&r); }", "KernelVerifiedManifest::from_report", "call"),
)


# (shape, appended source, enclosing symbol of the planted mint): a
# `#[cfg(test)]` on something that is not an `fn`, `mod` or `impl`, followed by
# a production mint. None of these sources has a `;` at paren depth 0 between
# the attribute and the mint, which is what the sticky attribute of 72bb210ba
# needed to stay armed.
_CFG_TEST_NON_ITEM_SHAPES = (
    (
        "a struct field",
        "pub struct ProbeF {\n    #[cfg(test)]\n    probe: u8,\n    real: u8,\n}\n"
        "pub fn zz_after_field() -> TrustLevel { TrustLevel::KernelVerified }",
        "zz_after_field",
    ),
    (
        "a struct field before an impl",
        "pub struct ProbeI {\n    #[cfg(test)]\n    probe: u8,\n}\n"
        "impl ProbeI {\n    pub fn zz_in_impl() -> TrustLevel { TrustLevel::KernelVerified }\n}",
        "ProbeI::zz_in_impl",
    ),
    (
        "an enum variant",
        "pub enum ProbeK {\n    #[cfg(test)]\n    Probe,\n    Real,\n}\n"
        "pub fn zz_after_variant() -> TrustLevel { TrustLevel::KernelVerified }",
        "zz_after_variant",
    ),
    (
        "a block statement",
        "pub fn host_block() {\n    #[cfg(test)]\n    {\n        probe()\n    }\n}\n"
        "pub fn zz_after_block() -> TrustLevel { TrustLevel::KernelVerified }",
        "zz_after_block",
    ),
    (
        "a match arm",
        "pub fn host_arm(x: u8) -> u8 {\n    match x {\n        #[cfg(test)]\n        0 => 1,\n"
        "        _ => 2,\n    }\n}\n"
        "pub fn zz_after_arm() -> TrustLevel { TrustLevel::KernelVerified }",
        "zz_after_arm",
    ),
    (
        "a macro_rules! with no semicolon",
        "#[cfg(test)]\nmacro_rules! probe {\n    () => {}\n}\n"
        "pub fn zz_after_macro() -> TrustLevel { TrustLevel::KernelVerified }",
        "zz_after_macro",
    ),
)

# (shape, appended source): the attribute DOES bind to the item after it,
# through further attributes, a visibility and qualifiers, so the mint inside
# is test code and the gate stays green.
_CFG_TEST_ITEM_CONTROLS = (
    (
        "a #[cfg(test)] fn behind another attribute and a visibility",
        "#[cfg(test)]\n#[allow(dead_code)]\npub(crate) fn zz_test_helper() -> TrustLevel "
        "{ TrustLevel::KernelVerified }",
    ),
    (
        "a #[cfg(test)] const fn",
        "#[cfg(test)]\npub const fn zz_test_const() -> TrustLevel { TrustLevel::KernelVerified }",
    ),
    (
        "a #[cfg(test)] impl",
        "pub struct ProbeT;\n#[cfg(test)]\nimpl ProbeT {\n    fn zz() -> TrustLevel { TrustLevel::KernelVerified }\n}",
    ),
)


# The real-tree arms: one real crate file, copied into a temporary tree at its
# own path, measured by the gate's own walk and compared with the rows the
# REAL artifact holds for that file (and the real artifact's wrappers). This is
# unit P1's "a gate fails when a site is added", replayed on every --selftest
# rather than narrated. The file was chosen for a kernel-backed mint that no
# burn-down touches; its rows are read at run time, so a legitimate change to
# the file and its rows keeps the arms meaningful.
REAL_TREE_ARM_FILE = "crates/clean-mathverse/src/shard_verify/constant_verify.rs"
REAL_TREE_ARM_MINT_FN = "verify_single_constant"


def real_tree_arms() -> list[tuple[str, bool, str]]:
    rel = REAL_TREE_ARM_FILE
    source = REPO_ROOT / rel
    artifact = load_artifact(REPO_ROOT)
    clean = artifact.get("clean") or {}
    rows = [r for r in clean.get("sites") or [] if r.get("file") == rel]
    wrapper_problems, wrappers = check_wrappers(
        clean.get("kernel_entry_wrappers") or [], _reader_dir(REPO_ROOT), "Clean"
    )
    calls = frozenset(KERNEL_ENTRY_CALLS) | wrappers
    if not source.is_file() or not rows:
        return [(f"real tree: {rel} is in the tree and the real artifact names its sites", False,
                 f"file present={source.is_file()} rows={len(rows)}")]
    raw = source.read_text()

    def problems_for(text: str) -> list[str]:
        tmp = Path(tempfile.mkdtemp(prefix="authority_sites_realtree_"))
        try:
            (tmp / ".git").mkdir()
            (tmp / rel).parent.mkdir(parents=True)
            (tmp / rel).write_text(text)
            measured, errors = measure_clean(tmp)
            return errors + compare(measured, rows, "Clean (real file)", calls)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)

    control = problems_for(raw)
    out = [(
        f"real tree: a copy of {rel} matches the real artifact's {len(rows)} rows for it",
        not control and not wrapper_problems,
        "; ".join((control + wrapper_problems)[:4]),
    )]
    mint_body = f"fn {REAL_TREE_ARM_MINT_FN}("
    plants = (
        ("a new function returning ConstResult::KernelVerified",
         raw + "\npub fn zz_real_plant() -> ConstResult { ConstResult::KernelVerified }\n",
         "UNNAMED SITE: clean:" + rel + "#zz_real_plant#ConstResult::KernelVerified#construct"),
        ("a production mint after a #[cfg(test)] struct field",
         raw + "\npub struct ZzProbe {\n    #[cfg(test)]\n    probe: u8,\n}\n"
         "pub fn zz_real_after_field() -> ConstResult { ConstResult::KernelVerified }\n",
         "UNNAMED SITE: clean:" + rel + "#zz_real_after_field#ConstResult::KernelVerified#construct"),
        ("a push into kernel_verified_names",
         raw + "\npub fn zz_real_record(v: &mut Report, n: Name) { v.kernel_verified_names.push(n); }\n",
         "UNNAMED SITE: clean:" + rel + "#zz_real_record#kernel_verified_names.push#construct"),
        ("the named mint's kernel call replaced",
         raw.replace(".add_decl(", ".trust_me(") if mint_body in raw else raw,
         "CHECKER MOVED: clean:" + rel + "#" + REAL_TREE_ARM_MINT_FN),
    )
    for what, text, needle in plants:
        got = problems_for(text)
        fresh = [p for p in got if p not in control]
        out.append((
            f"real tree PLANT: {what} in a copy of {rel} is refused against the real artifact",
            any(p.startswith(needle) for p in fresh),
            "; ".join(fresh[:4]) or "no new problem",
        ))
    return out


def selftest() -> int:
    passed = failed = 0

    def record(ok: bool, name: str, detail: str = "") -> None:
        nonlocal passed, failed
        print(f"  [{'ok ' if ok else 'FAIL'}] {name}{(': ' + detail) if detail and not ok else ''}")
        passed += ok
        failed += not ok

    wrong = []
    for source, want in _ROLE_CASES:
        got = [h["role"] for h in scan_text(source, "case.rs") if h["family"] == "label"]
        if got != ([] if want is None else [want]):
            wrong.append((source, want, got))
    record(not wrong, f"role classifier: {len(_ROLE_CASES)} label spellings", str(wrong))
    wrong = []
    for source, token, want in _ROOT_ROLE_CASES:
        got = [h["role"] for h in scan_text(source, "case.rs") if h["family"] == "root" and h["token"] == token]
        if (want[1:] in got) if want.startswith("!") else (want not in got):
            wrong.append((source, token, want, [(h["token"], h["role"]) for h in scan_text(source, "case.rs")]))
    record(not wrong, f"role classifier: {len(_ROOT_ROLE_CASES)} root spellings", str(wrong))
    wrong = []
    for source, want in _PRODUCER_CASES:
        got = [(h["token"], h["role"]) for h in scan_text(source, "case.rs") if h["family"] == "producer"]
        if got != [(t, "construct") for t in want]:
            wrong.append((source, want, got))
    record(not wrong, f"producer shapes: {len(_PRODUCER_CASES)} spellings (writes are sites, reads are not)", str(wrong))
    wrong = [
        (body, name, want)
        for body, name, want in (
            ("{ env.add_decl(d) }", "add_decl", True),
            ("{ Environment::add_decl(&mut e, d) }", "add_decl", True),
            ("{ tc.infer_type::<Strict>(e) }", "infer_type", True),
            ("{ let add_decl = env.trust_me(d); add_decl }", "add_decl", False),
            ("{ xs.map(Environment::add_decl) }", "add_decl", False),
            ("{ env.add_decl_structural(d) }", "add_decl", False),
        )
        if _has_call(body, name) != want
    ]
    record(not wrong, "kernel evidence: a call in code position, not a name", str(wrong))

    try:
        Structure(lexer.strip_noncode("fn f() { if x { }"), "unbalanced.rs")
        record(False, "an unbalanced file is refused", "no error raised")
    except ValueError:
        record(True, "an unbalanced file is refused")

    lib = Path("crates") / "c" / "src" / "lib.rs"
    arms = []

    def arm(name: str, expect: int, needle: str = ""):
        def deco(fn):
            arms.append((name, expect, needle, fn))
            return fn
        return deco

    @arm("baseline: the synthetic tree matches its artifact", 0)
    def _(root, trust):
        pass

    @arm("PLANT: a new mint in a new function is refused", 1, "UNNAMED SITE")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub fn smuggle() -> TrustLevel { TrustLevel::KernelVerified }\n")

    @arm("PLANT: a second mint in an already-named function is refused", 1, "COUNT MOVED")
    def _(root, trust):
        text = (root / lib).read_text()
        (root / lib).write_text(
            text.replace("Err(_) => TrustLevel::Unverified,", "Err(_) => TrustLevel::KernelVerified,")
        )

    @arm("a mint named only in a comment and a string stays green", 0)
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write('\n// TrustLevel::KernelVerified\npub fn doc() -> &\'static str { "TrustLevel::KernelVerified" }\n')

    @arm("a mint inside #[cfg(test)] mod stays green", 0)
    def _(root, trust):
        text = (root / lib).read_text()
        (root / lib).write_text(
            text.replace("    fn t() {\n", "    fn t() {\n        let _a = TrustLevel::KernelVerified;\n")
        )

    # A #[cfg(test)] binds to the one item after it. On anything that is not
    # an `fn`, `mod` or `impl` it marks nothing, so the production mint that
    # follows each of these is a site. Each arm ended green (the mint hidden as
    # test code) under the scanner of 72bb210ba; see _cfg_test_target.
    for shape, source, symbol in _CFG_TEST_NON_ITEM_SHAPES:
        def _plant(root, trust, source=source):
            with (root / lib).open("a") as fh:
                fh.write(f"\n{source}\n")
        arms.append((f"PLANT: a #[cfg(test)] on {shape} does not hide the next production mint", 1,
                     f"UNNAMED SITE: clean:crates/c/src/lib.rs#{symbol}#TrustLevel::KernelVerified#construct",
                     _plant))

    for shape, source in _CFG_TEST_ITEM_CONTROLS:
        def _control(root, trust, source=source):
            with (root / lib).open("a") as fh:
                fh.write(f"\n{source}\n")
        arms.append((f"a mint inside {shape} stays green (the attribute binds to that item)", 0, "", _control))

    @arm("PLANT: a sibling tier (TrustLevel::AxiomDependent) minted in a new function is refused", 1,
         "UNNAMED SITE: clean:crates/c/src/lib.rs#tier#TrustLevel::AxiomDependent#construct")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub fn tier() -> TrustLevel { TrustLevel::AxiomDependent }\n")

    @arm("PLANT: AddConstResult::UnsafeAccepted minted in a new function is refused", 1,
         "UNNAMED SITE: clean:crates/c/src/lib.rs#accept#AddConstResult::UnsafeAccepted#construct")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub fn accept() -> AddConstResult { AddConstResult::UnsafeAccepted }\n")

    @arm("PLANT: a push into kernel_verified_names in a new function is refused", 1,
         "UNNAMED SITE: clean:crates/c/src/lib.rs#record#kernel_verified_names.push#construct")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub fn record(v: &mut Report, n: Name) { v.kernel_verified_names.push(n); }\n")

    @arm("PLANT: a kernel_verified += 1 in a new function is refused", 1,
         "UNNAMED SITE: clean:crates/c/src/lib.rs#count#kernel_verified+=#construct")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub fn count(v: &mut Report) { v.kernel_verified += 1; }\n")

    @arm("KERNEL EVIDENCE: a kernel mint whose only token is a parameter is refused", 1, "KERNEL EVIDENCE")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["evidence_tokens"] = ["d"]
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("KERNEL EVIDENCE: a kernel entry named as a variable, not called, is refused", 1, "KERNEL EVIDENCE")
    def _(root, trust):
        text = (root / lib).read_text()
        (root / lib).write_text(
            text.replace("match env.add_decl(d) {", "let add_decl = env.trust_me(d);\n    match add_decl {")
        )

    def _wrapped(root, wrapper_body: str, declared_calls: list[str]) -> None:
        """A mint citing a declared wrapper `recheck` whose body is `wrapper_body`."""
        with (root / lib).open("a") as fh:
            fh.write(
                f"\npub fn recheck(env: &mut Env, d: Decl) -> bool {{ {wrapper_body} }}\n"
                "pub fn stamp_via(env: &mut Env, d: Decl) -> TrustLevel {\n"
                "    if recheck(env, d) { TrustLevel::KernelVerified } else { TrustLevel::Unverified }\n}\n"
            )
        doc = json.loads((root / ARTIFACT_REL).read_text())
        doc["clean"]["sites"].append(_classified({
            "id": "clean:crates/c/src/lib.rs#stamp_via#TrustLevel::KernelVerified#construct",
            "file": "crates/c/src/lib.rs", "symbol": "stamp_via", "family": "label",
            "token": "TrustLevel::KernelVerified", "role": "construct", "count": 1, "lines": [1],
        }, evidence_tokens=["recheck"]))
        doc["clean"]["kernel_entry_wrappers"] = [{
            "name": "recheck", "file": "crates/c/src/lib.rs", "symbol": "recheck",
            "calls": declared_calls, "detail": "selftest wrapper",
        }]
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("WRAPPER: a mint citing a declared wrapper that calls add_decl stays green", 0)
    def _(root, trust):
        _wrapped(root, "env.add_decl(d).is_ok()", ["add_decl"])

    @arm("WRAPPER: a declared wrapper that stopped calling its entry is refused", 1, "CHECKER MOVED: Clean wrapper recheck")
    def _(root, trust):
        _wrapped(root, "env.trust_me(d)", ["add_decl"])

    @arm("WRAPPER: a wrapper that calls only itself admits nothing", 1, "KERNEL EVIDENCE: Clean wrapper recheck")
    def _(root, trust):
        _wrapped(root, "recheck(env, d)", ["recheck"])

    def _trust_wrapped(root, trust, where: str) -> None:
        """A Trust mint citing `clean_recheck`, a Clean function that calls
        add_decl, declared under `where` ("clean_wrappers" for Trust's Clean
        pin, "clean" for this tree's own list)."""
        with (root / lib).open("a") as fh:
            fh.write("\npub fn clean_recheck(env: &mut Env, d: Decl) -> bool { env.add_decl(d).is_ok() }\n")
        with (trust / "crates" / "trust-certify" / "src" / "reference_mint.rs").open("a") as fh:
            fh.write(
                "\npub fn grant_checked(env: &mut Env, d: Decl) -> TrustStatus {\n"
                "    if clean_recheck(env, d) { TrustStatus::Certified } else { TrustStatus::Open }\n}\n"
            )
        doc = json.loads((root / ARTIFACT_REL).read_text())
        doc["trust"]["sites"].append(_classified({
            "id": "trust:crates/trust-certify/src/reference_mint.rs#grant_checked#TrustStatus::Certified#construct",
            "file": "crates/trust-certify/src/reference_mint.rs", "symbol": "grant_checked",
            "family": "label", "token": "TrustStatus::Certified", "role": "construct", "count": 1, "lines": [1],
        }, evidence_tokens=["clean_recheck"], reach="trust", tcb="selftest: not a real Trust tree"))
        wrapper = {
            "name": "clean_recheck", "file": "crates/c/src/lib.rs", "symbol": "clean_recheck",
            "calls": ["add_decl"], "detail": "selftest wrapper",
        }
        if where == "clean_wrappers":
            doc["trust"]["clean_wrappers"] = [wrapper]
            doc["trust"]["clean_pin"] = "0" * 40
        else:
            doc["clean"]["kernel_entry_wrappers"] = [wrapper]
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("WRAPPER (Trust): a Trust mint citing a Clean wrapper declared at Trust's Clean pin stays green", 0)
    def _(root, trust):
        _trust_wrapped(root, trust, "clean_wrappers")

    @arm("WRAPPER (Trust): a Clean wrapper of this tree does not vouch for a Trust mint", 1, "KERNEL EVIDENCE: trust:")
    def _(root, trust):
        _trust_wrapped(root, trust, "clean")

    @arm("FIRST RISK RATCHET: a matching header does not let the count rise past the ceiling", 1, "FIRST RISK RATCHET")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["checker"] = {"kind": "none"}
                row["evidence_tokens"] = []
        doc["first_risk"] = first_risk_ids(doc["clean"]["sites"] + doc["trust"]["sites"])
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("FIRST RISK RATCHET: a ceiling raised by hand, with no history entry, is refused", 1, "last first_risk_history entry")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        doc["first_risk_limit"] = 5
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("FIRST RISK RATCHET: a deleted ceiling is refused", 1, "first_risk_limit must be")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        doc.pop("first_risk_limit")
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("PLANT: a new enum carrying an authority-shaped variant is refused", 1, "UNNAMED SITE")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub enum Fresh { KernelVerified }\n")

    @arm("PLANT: a new read of the label is refused (counted, so a misread mint cannot hide)", 1, "UNNAMED SITE")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub fn peek(t: TrustLevel) -> bool { t == TrustLevel::KernelVerified }\n")

    @arm("PLANT: a new checker root is refused", 1, "UNNAMED SITE")
    def _(root, trust):
        with (root / lib).open("a") as fh:
            fh.write("\npub fn other_base() -> Environment { Environment::for_lean_replay() }\n")

    @arm("CHECKER MOVED: the kernel call leaves a named mint's function", 1, "CHECKER MOVED")
    def _(root, trust):
        text = (root / lib).read_text()
        (root / lib).write_text(text.replace("match env.add_decl(d) {", "match env.trust_me(d) {"))

    @arm("CHECKER MOVED: the kernel call survives only in a comment", 1, "CHECKER MOVED")
    def _(root, trust):
        text = (root / lib).read_text()
        (root / lib).write_text(
            text.replace("match env.add_decl(d) {", "match env.trust_me(d) { // was env.add_decl(d)")
        )

    @arm("STALE ROW: a named site that is gone is refused", 1, "STALE ROW")
    def _(root, trust):
        text = (root / lib).read_text()
        (root / lib).write_text(text.replace("    Environment::for_lean_replay()\n", "    Environment::new()\n"))

    @arm("UNCLASSIFIED: a mint row with no classification is refused", 1, "UNCLASSIFIED")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["class"] = None
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("UNCLASSIFIED: a kernel claim with no evidence token is refused", 1, "names no evidence token")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["evidence_tokens"] = []
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("FIRST RISK: a no-kernel mint missing from the header list is refused", 1, "FIRST RISK")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["checker"] = {"kind": "none"}
                row["evidence_tokens"] = []
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("FIRST RISK RATCHET: even a matching header cannot raise the count", 1, "FIRST RISK RATCHET")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["checker"] = {"kind": "none"}
                row["evidence_tokens"] = []
        doc["first_risk"] = first_risk_ids(doc["clean"]["sites"] + doc["trust"]["sites"])
        (root / ARTIFACT_REL).write_text(json.dumps(doc))
        before = (root / ARTIFACT_REL).read_bytes()
        with contextlib.redirect_stdout(io.StringIO()):
            rc = write(root, None, None)
        assert rc == 1, "--write must refuse growth"
        assert before == (root / ARTIFACT_REL).read_bytes(), "refused mint must not write"

    @arm("FIRST RISK RATCHET: --write lowers the ceiling after a resolution", 0)
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        doc["first_risk_limit"] = 1
        doc["first_risk_history"][-1]["to"] = 1
        (root / ARTIFACT_REL).write_text(json.dumps(doc))
        with contextlib.redirect_stdout(io.StringIO()):
            rc = write(root, None, None)
        assert rc == 0
        assert json.loads((root / ARTIFACT_REL).read_text())["first_risk_limit"] == 0

    @arm("FIRST RISK RATCHET: deleting the ceiling is refused", 1, "FIRST RISK RATCHET")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        doc.pop("first_risk_limit")
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("UNEXAMINED: a Clean site may not be left unread", 1, "exists for the Trust half only")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["checker"] = {"kind": "unexamined", "detail": "not read"}
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("TCB: a Trust row that does not say what TCB.md says is refused", 1, "docs/TCB.md")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["trust"]["sites"]:
            row.pop("tcb", None)
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("ENTRY: a verb whose anchor function is gone is refused", 1, "STALE ROW: entry")
    def _(root, trust):
        text = (root / lib).read_text()
        (root / lib).write_text(text.replace("pub fn stamp(", "pub fn stamp_renamed("))

    @arm("ENTRY: a verb whose function lost its checker evidence is refused", 1, "CHECKER MOVED: entry")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        doc["clean"]["entries"][0]["evidence_tokens"] = ["for_lean_replay"]
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("TRUST PLANT: a second consumer of the entry's token is refused", 1, "UNNAMED SITE")
    def _(root, trust):
        with (trust / "crates" / "trust-certify" / "src" / "reference_mint.rs").open("a") as fh:
            fh.write(
                "\npub fn side_door(token: ReferenceAccepted) -> ReferenceCertificate {\n"
                "    ReferenceCertificate::from_accepted(token)\n}\n"
            )

    @arm("TRUST PLANT: a Certified status minted in a new function is refused", 1, "UNNAMED SITE")
    def _(root, trust):
        with (trust / "crates" / "trust-certify" / "src" / "reference_mint.rs").open("a") as fh:
            fh.write("\npub fn grant() -> TrustStatus { TrustStatus::Certified }\n")

    @arm("LINK PLANT: a new Trust manifest linking a carrier of Clean's checkers is refused", 1, "UNNAMED LINK")
    def _(root, trust):
        (trust / "crates" / "side").mkdir()
        (trust / "crates" / "side" / "Cargo.toml").write_text('[dependencies]\ntla-check = "1"\n')

    @arm("LINK MOVED: a named manifest that starts linking clean-ck0 is refused", 1, "LINK MOVED")
    def _(root, trust):
        with (trust / "crates" / "trust-certify" / "Cargo.toml").open("a") as fh:
            fh.write('clean-ck0 = { path = "../../first-party/clean/crates/clean-ck0" }\n')

    @arm("UNCLASSIFIED LINK: a carrier link with no route is refused", 1, "UNCLASSIFIED LINK")
    def _(root, trust):
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["trust"]["links"]:
            row.pop("route", None)
        (root / ARTIFACT_REL).write_text(json.dumps(doc))

    @arm("STALE LINK: a named link whose manifest stopped linking is refused", 1, "STALE LINK")
    def _(root, trust):
        (trust / "crates" / "trust-temporal" / "Cargo.toml").write_text("[dependencies]\n")

    @arm("a Trust test file is not scanned", 0)
    def _(root, trust):
        (trust / "crates" / "trust-certify" / "tests").mkdir()
        (trust / "crates" / "trust-certify" / "tests" / "t.rs").write_text(
            "fn t() -> TrustStatus { TrustStatus::Certified }\n"
        )

    for name, expect, needle, mutate in arms:
        root, trust = _selftest_tree()
        try:
            mutate(root, trust)
            rc, out = _quiet(root, trust)
            ok = rc == expect and (not needle or needle in out)
            record(ok, name, f"exit {rc} (expected {expect}); output: {out.strip()[:600]}")
        finally:
            shutil.rmtree(root.parent, ignore_errors=True)

    # `--write` after a new read refreshes the count and keeps every decision.
    root, trust = _selftest_tree()
    try:
        with (root / lib).open("a") as fh:
            fh.write("\npub fn peek(t: TrustLevel) -> bool { t == TrustLevel::KernelVerified }\n")
            fh.write("\npub fn smuggle() -> TrustLevel { TrustLevel::KernelVerified }\n")
        before = json.loads((root / ARTIFACT_REL).read_text())
        with contextlib.redirect_stdout(io.StringIO()):
            write(root, None, None)
        after = json.loads((root / ARTIFACT_REL).read_text())
        kept = {r["id"]: r for r in after["clean"]["sites"]}
        decisions_kept = all(
            kept[r["id"]].get("checker") == r.get("checker") for r in before["clean"]["sites"]
        )
        new_mint = [r for r in after["clean"]["sites"] if r["symbol"] == "smuggle"]
        rc, out = _quiet(root, trust)
        ok = (
            decisions_kept
            and len(new_mint) == 1
            and new_mint[0]["class"] is None
            and rc == 1
            and "UNCLASSIFIED" in out
            and "peek" not in out
        )
        record(ok, "--write adds the read, keeps decisions, and leaves a new mint unclassified and red", out[:600])
    finally:
        shutil.rmtree(root.parent, ignore_errors=True)

    # The ceiling under --write: growth is refused and writes nothing; a dated
    # --rebase-risk raises it and records why; a resolution lowers it.
    root, trust = _selftest_tree()
    try:
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["checker"] = {"kind": "none"}
                row["evidence_tokens"] = []
        (root / ARTIFACT_REL).write_text(json.dumps(doc))
        before = (root / ARTIFACT_REL).read_bytes()
        with contextlib.redirect_stdout(io.StringIO()):
            refused = write(root, None, None)
            unchanged = before == (root / ARTIFACT_REL).read_bytes()
            empty = write(root, None, None, rebase_reason="  ")
            raised = write(root, None, None, rebase_reason="selftest: a correction of the baseline")
        after = json.loads((root / ARTIFACT_REL).read_text())
        rc, out = _quiet(root, trust)
        record(
            refused == 1 and unchanged and empty == 1 and raised == 0 and rc == 0
            and after["first_risk_limit"] == 1
            and after["first_risk_history"][-1]["why"] == "selftest: a correction of the baseline",
            "FIRST RISK RATCHET: --write refuses growth and writes nothing; --rebase-risk with a reason raises and records it",
            f"refused={refused} unchanged={unchanged} empty={empty} raised={raised} rc={rc} {out[:300]}",
        )
        doc = json.loads((root / ARTIFACT_REL).read_text())
        for row in doc["clean"]["sites"]:
            if row["role"] == "construct":
                row["checker"] = {"kind": "clean-kernel", "entry": "add_decl", "theory": "Extended"}
                row["evidence_tokens"] = ["add_decl"]
        (root / ARTIFACT_REL).write_text(json.dumps(doc))
        with contextlib.redirect_stdout(io.StringIO()):
            lowered = write(root, None, None)
            again = write(root, None, None, rebase_reason="selftest: nothing to raise")
        after = json.loads((root / ARTIFACT_REL).read_text())
        rc, out = _quiet(root, trust)
        record(
            lowered == 0 and again == 1 and rc == 0 and after["first_risk_limit"] == 0
            and after["first_risk_history"][-1]["kind"] == "lowered",
            "FIRST RISK RATCHET: a resolution lowers the ceiling and records it; --rebase-risk cannot raise past the count",
            f"lowered={lowered} again={again} rc={rc} {out[:300]}",
        )
    finally:
        shutil.rmtree(root.parent, ignore_errors=True)

    # --clean-only: the Trust half is not read, so a broken Trust tree cannot
    # fail it, and a Clean plant still does.
    root, trust = _selftest_tree()
    try:
        with (trust / "crates" / "trust-certify" / "src" / "reference_mint.rs").open("a") as fh:
            fh.write("\npub fn grant() -> TrustStatus { TrustStatus::Certified }\n")
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            skipped = run(root, trust_repo=str(trust), trust_dir_mode=True, clean_only=True)
        with (root / lib).open("a") as fh:
            fh.write("\npub fn smuggle() -> TrustLevel { TrustLevel::KernelVerified }\n")
        buf2 = io.StringIO()
        with contextlib.redirect_stdout(buf2):
            planted = run(root, trust_repo=str(trust), trust_dir_mode=True, clean_only=True)
        record(
            skipped == 0 and "trust_half=skipped" in buf.getvalue() and planted == 1
            and "UNNAMED SITE" in buf2.getvalue(),
            "--clean-only skips the Trust half and still refuses a Clean plant",
            f"skipped={skipped} planted={planted} {buf.getvalue()[:200]} {buf2.getvalue()[:200]}",
        )
    finally:
        shutil.rmtree(root.parent, ignore_errors=True)

    for name, ok, detail in real_tree_arms():
        record(ok, name, detail)

    print(f"authority-sites selftest: {passed} passed, {failed} failed")
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    if "--pinned-inputs" in argv:
        print(*PINNED_INPUTS, sep="\n")
        return 0
    if "--selftest" in argv:
        return selftest()

    def value(flag: str) -> str | None:
        if flag in argv:
            at = argv.index(flag)
            if at + 1 >= len(argv):
                print(f"{flag} needs a value", file=sys.stderr)
                raise SystemExit(64)
            return argv[at + 1]
        return None

    trust_repo = value("--trust-repo")
    trust_ref = value("--trust-ref")
    rebase_reason = value("--rebase-risk")
    clean_only = "--clean-only" in argv
    if rebase_reason is not None and "--write" not in argv:
        print("--rebase-risk moves the ceiling and is only taken with --write", file=sys.stderr)
        return 64
    if clean_only and ("--require-trust" in argv or "--write" in argv or trust_ref or trust_repo):
        print("--clean-only checks the Clean half alone; it takes no Trust flag and no --write", file=sys.stderr)
        return 64
    if "--write" in argv:
        return write(REPO_ROOT, trust_repo, trust_ref, rebase_reason)
    if "--list" in argv:
        measured, errors = measure_clean(REPO_ROOT)
        for rid, site in sorted(measured.items()):
            print(f"{site['role']:9} {site['count']:3}  {rid}  lines {site['lines']}")
        for e in errors:
            print(f"ERROR {e}")
        return 1 if errors else 0
    return run(REPO_ROOT, trust_repo, trust_ref, require_trust="--require-trust" in argv, clean_only=clean_only)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
