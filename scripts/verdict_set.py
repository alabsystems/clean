#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""RING R2 foundation: derive `data/verdict_set.json` — the committed member
list of the verdict-bearing surface.

WHY THIS EXISTS
---------------
designs/2026-08-22-spine-and-lattice-program.md §5, **Ring R2** ("verdict paths,
partitioned honestly") names the surface that could mint a false verdict *even
with a proved kernel*, in three lanes:

  (a) pure-Rust verdict code   — clean-olean's decode/registration for the lanes
                                 R1 keeps structural, clean-verify's checker /
                                 census / firewall machinery, the mathverse
                                 shard-digest + KernelVerified-minting lane, and
                                 the suite runner's input-digest machinery;
  (b) IO-bearing Rust          — decode-pure separated from read-IO, the residual
                                 IO boundary contract-modeled and ledgered (§3.6);
  (c) the script surface       — the claim-owning gates themselves, either
                                 rewritten in Rust to enter lane (a), or declared
                                 TCB with a committed digest + line-count ratchet.

That member list had exactly the defect `data/spine_set.json` was built to fix:
a body set named in PROSE with no committed enumeration. Prose cannot be
gated, cannot be counted, and cannot go stale loudly. This script is the
G-SPINE-SET house pattern applied to R2: a small number of ROOTS that are
DERIVED from committed artifacts (or declared and verified present, exactly as
`spine_set.py` declares one `ROOT_SPEC`), a stated edge policy, a mechanical
closure, and provenance pins on every input.

WHAT IS DERIVED VERSUS DECLARED (read this before trusting a count)
-------------------------------------------------------------------
Derived mechanically, with no hand-listing:

  R-OLEAN-S   lane (a)/(b) roots in clean-olean = every site file under
              `crates/clean-olean/` carried by a `data/env_bypass_census.json`
              row whose classification contains `S` (load-bearing-structural) —
              i.e. exactly "the lanes R1 keeps structural". Sites outside
              `crates/<crate>/src/` (examples, benches) are recorded as
              scope exclusions, never silently dropped.
  R-MINT      lane (a)/(b) roots in clean-mathverse = every production module
              with a `TrustLevel::KernelVerified` MINT site, found by a LEXED
              scan (comments, string/char literals blanked; `#[cfg(test)] mod`
              bodies, test files by name and files headed `#![cfg(test)]`
              excluded) that distinguishes a mint (a value position) from a
              comparison or a match-arm pattern. The same scan runs over every
              crate; hits outside the declared lane are recorded
              in `mint_sites_outside_declared_lane` so the scoping is a measured
              decision rather than a silence.
  R-SUITE     lane (a)'s "suite runner's input-digest machinery" is PROBED for
              in Rust (`fn input_digest` over crates/**/*.rs). The probe is
              empty at HEAD: the machinery is Python. That is recorded as a
              dated correction and the member is routed to lane (c).
  R-GATES     lane (c) = every `data/gate_registry.json` row whose artifact is a
              script under `scripts/` and whose `claims` is not `none` — the
              claim-owning surface, by the registry's own accounting — plus the
              three Ring-R2 gate names (`spine_gate.sh`, `verdict_gate.sh`,
              `lattice_gate.sh`), present or recorded absent.

Declared, and verified present (fail-closed if a symbol moves):

  R-VERIFY    clean-verify's checker / census / firewall machinery is named by
              ROLE in the program text, not by a committed artifact, so its
              roots are the ANCHORS table below: (file, required symbol, role).
              A vanished symbol aborts the derivation naming it — the same
              posture `spine_set.py` takes when its root spec matches nothing.
  R-SHARD     the shard-digest half of the mathverse lane, same posture.

CLOSURE AND ITS HONEST LIMIT
----------------------------
From those roots the closure follows in-crate references at MODULE
granularity, transitively, to a fixed point. Two spellings are edges:
path-qualified references (`crate::`, `super::`, `self::`, including `use`
brace groups), and a BARE `foo::` in a file that itself declares `mod foo;` —
Rust resolves that first segment against the items in scope, so it is a real
use of the child module. `mod` declarations are still NOT edges on their own
(a module that declares a submodule does not thereby use it): the bare form
requires an actual `foo::` occurrence in the same file's production text.
Cross-crate references are recorded, not followed. Unresolved references are
recorded, not dropped.

The bare form was missing until audit r17 and the omission was load-bearing:
27 modules and 15,542 lines of reachable production code — including the whole
of clean-olean's `import::{load,parse,path,module_cache_direct}` IO surface and
clean-verify's `spec::core_spec` — were referenced by exactly that spelling and
counted by nothing.

That is a REFERENCE closure, not a CALL closure. The call closure needs the
per-body call graph from the same trust-host whole-crate dump `spine_set.py`
is waiting on (data/spine_set.PENDING.md). The artifact says so in
`closure_limit`, the gate refuses on it, and nobody has to re-derive that
caveat by eye.

PARTITION (a) VERSUS (b)
------------------------
Mechanical: every closure member is scanned (lexed) for IO tokens — fs, io,
process, net, `env::var`, mmap. One or more hits puts the member in lane (b)
with its sites recorded; zero hits keeps it in lane (a). Ring R2's lane (b)
sentence ("decode-pure separated from read-IO where feasible") is therefore a
measured split, not a judgement call.

PARTITION (c)'s RATCHET
-----------------------
Lane (c) is the one obligation that is cheap and immediately real, so it is
implemented rather than promised: every member carries its sha256 and line
count; the artifact pins a `line_ratchet` whose baseline may fall freely and
may only RISE through `--rebase-up "<reason>"`, which records a dated row.
`scripts/verdict_gate.sh` recomputes both from the tree at gate time, so a
drifted script is a refusal, not a stale number.

Usage:
    scripts/verdict_set.py --describe
    scripts/verdict_set.py --self-test
    scripts/verdict_set.py                       # derive + write data/verdict_set.json
    scripts/verdict_set.py --check               # derive + fail if the committed file differs
    scripts/verdict_set.py --rebase-up "reason"  # allow the lane (c) ratchet to rise, dated
    scripts/verdict_set.py --pinned-inputs       # the reference lexer this gate runs (registry R7)
"""

from __future__ import annotations

import argparse
import copy
import datetime as _dt
import hashlib
import json
import re
import sys
import types
from pathlib import Path

# The reference Rust lexer, executed from its source: ignored bytecode is not an input.
_reference_lexer = types.ModuleType("verdict_set_reference_lexer")
_reference_lexer.__file__ = str(Path(__file__).resolve().parent / "check_add_decl_ratchet.py")
exec(compile(Path(_reference_lexer.__file__).read_bytes(), _reference_lexer.__file__, "exec", dont_inherit=True),
     _reference_lexer.__dict__)

# check_gate_registry.py R7 pins what --pinned-inputs prints: the reference lexer this gate runs.
ANSWERS_PINNED_INPUTS = True
PINNED_INPUTS = ("scripts/check_add_decl_ratchet.py",)

REPO_ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "clean.verdict_set/v1"
DEFAULT_OUT = "data/verdict_set.json"

CENSUS_PATH = "data/env_bypass_census.json"
REGISTRY_PATH = "data/gate_registry.json"
SPINE_SET_PATH = "data/spine_set.json"
SPINE_PENDING_PATH = "data/spine_set.PENDING.md"
ASSUMPTION_LEDGER_PATH = "data/spine_assumption_ledger.json"
# Lane (b)'s IO-boundary contract model + its §3.6 rows, until the program-wide
# assumption ledger above exists. Presence only — the digest is deliberately NOT
# pinned here: that artifact pins THIS one, and two-way pinning is a cycle.
IO_CONTRACTS_PATH = "data/verdict_io_contracts.json"

# The three Ring-R2 gate names (program §5). Present ones join lane (c); absent
# ones are recorded as planned, never assumed.
RING_R2_GATES = ("scripts/spine_gate.sh", "scripts/verdict_gate.sh", "scripts/lattice_gate.sh")

# ---------------------------------------------------------------------------
# Declared roots (verified present; a vanished symbol is a fail-closed abort)
# ---------------------------------------------------------------------------

# clean-verify's "checker/census/firewall machinery" (program §5 Ring R2 lane a).
VERIFY_ANCHORS: tuple[tuple[str, str, str], ...] = (
    (
        "crates/clean-verify/src/vacuity_firewall.rs",
        "pub fn audit_relation",
        "firewall — decides a generated relation is non-vacuous (§8 R2: firewall on every generated relation)",
    ),
    (
        "crates/clean-verify/src/spec_axiom_closure.rs",
        "pub fn audit_definition_honesty",
        "census — transitive axiom closure vs the spec's hand-maintained honesty labels",
    ),
    (
        "crates/clean-verify/src/axiom_ratchet.rs",
        "pub fn newly_admitted_axioms",
        "census — no-new-axioms ratchet over the spec's admitted axioms",
    ),
    (
        "crates/clean-verify/src/bootstrap_checker.rs",
        "pub struct BootstrapChecker",
        "checker — bootstrap/reflection acceptance for the closed kernel core",
    ),
    (
        "crates/clean-verify/src/external_checker.rs",
        "pub struct ProcessChecker",
        "checker — external/independent backend acceptance (subprocess boundary)",
    ),
    (
        "crates/clean-verify/src/no_masquerade.rs",
        "pub fn lint_constant",
        "checker — refuses theorem-wrapping-axiom masquerade at promotion",
    ),
    (
        "crates/clean-verify/src/promotion_guard.rs",
        "pub struct PromotionGuardConfig",
        "guard — keeps unsafe KernelProved claims from passing handoff",
    ),
)

# The shard-digest half of the mathverse lane.
SHARD_ANCHORS: tuple[tuple[str, str, str], ...] = (
    (
        "crates/clean-mathverse/src/shard.rs",
        "fn from_mmap_no_checksum",
        "shard-digest — .mathverse format reader: whole-file checksum verification AND the "
        "documented checksum-skipping lazy mmap path",
    ),
    (
        "crates/clean-mathverse/src/shard_integrity.rs",
        "pub fn audit_level_param_integrity",
        "shard-integrity — level-param integrity audit/repair over a shard reader",
    ),
    (
        "crates/clean-mathverse/src/shard_verify/mod.rs",
        "pub fn verify_shard_dir",
        "KernelVerified minting lane — batch kernel re-check of shard constants via add_decl",
    ),
)

SUBLANES = (
    "a-olean-structural",
    "a-verify-checker-census-firewall",
    "a-mathverse-shard-digest-kv",
    "a-suite-runner-input-digest",
)

CRATE_OF_SUBLANE = {
    "a-olean-structural": "clean-olean",
    "a-verify-checker-census-firewall": "clean-verify",
    "a-mathverse-shard-digest-kv": "clean-mathverse",
}

# ---------------------------------------------------------------------------
# Lexing (a soundness scanner over Rust source is `lexed`, never `raw-lines` —
# gate-registry R9)
# ---------------------------------------------------------------------------

# The lexer is scripts/check_add_decl_ratchet.py's, imported and pinned (PINNED_INPUTS).
NONCODE_RE = _reference_lexer.NONCODE_RE
# The EXACT spelling, as the three bypass ratchets read it. It used to accept
# `#[cfg(any(test, ..))]` too, so the body of an inline module that a non-test
# build compiles whenever the other arm holds (`#[cfg(any(test, feature = "x"))]
# pub mod m { .. }`, three such modules in clean-kernel at 8f3129d1aa) was
# blanked as test code: its mints, IO tokens and reference edges vanished from
# every scan reading `production_text`. Any other cfg is production here.
CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\s+[A-Za-z_][A-Za-z0-9_]*")


class VerdictSetError(Exception):
    """Fail-closed derivation error; the message names the missing thing."""


def _blank(match: re.Match[str]) -> str:
    return "".join("\n" if ch == "\n" else " " for ch in match.group(0))


def strip_noncode(text: str) -> str:
    """Blank comments and string/raw-string/char literals, preserving geometry."""
    return NONCODE_RE.sub(_blank, text)


def is_test_path(rel: Path) -> bool:
    """True for test FILES. Same predicate as the two bypass ratchets, so the
    three scanners cannot drift into disagreeing about what a test is."""
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
    # AUDIT r13 M13-2: the unanchored substring, removed from four scanners at
    # r11 M11-3 and left here under a docstring claiming "same predicate as the
    # two bypass ratchets". Anchored forms only, so five live production
    # env/algebra_nat_*testbit* modules stop being excluded by their names.
    return bool(re.search(r"(^test_|_tests?\.rs$|^tests?\.rs$|^tests_)", name))


# A file whose first line that is not blank or a `//` comment is exactly
# `#![cfg(test)]` is test code, whatever route reaches it. The rule and its
# cases (`_HEAD_CASES`) are the reference lexer's, imported with it.
headed_cfg_test = _reference_lexer.headed_cfg_test


def production_text(text: str, rel: Path) -> str:
    """`text` with non-code spans AND `#[cfg(test)] mod` bodies blanked.

    Line geometry survives exactly, so a hit's line number still indexes the
    original file. Everything downstream — the mint scan, the IO scan, the
    reference closure — reads THIS, so a reference or a mint that exists only in
    test code is not production verdict surface.
    """
    lines = strip_noncode(text).splitlines()
    out: list[str] = []
    in_cfg_test = False
    depth = 0
    pending_cfg = False
    for line in lines:
        if not in_cfg_test:
            if CFG_TEST_RE.search(line):
                pending_cfg = True
                out.append("")
                continue
            if pending_cfg:
                if MOD_RE.search(line):
                    if "{" in line:
                        in_cfg_test = True
                        depth = line.count("{") - line.count("}")
                        if depth <= 0:
                            in_cfg_test = False
                    pending_cfg = False
                    out.append("")
                    continue
                if line.strip():
                    pending_cfg = False
        else:
            depth += line.count("{") - line.count("}")
            if depth <= 0:
                in_cfg_test = False
            out.append("")
            continue
        out.append(line)
    if in_cfg_test:
        raise VerdictSetError(
            f"{rel}: a #[cfg(test)] mod block never closed (brace tracking ran off the end "
            "of the file). Refusing to classify this file — an unreadable file is not a clean one."
        )
    return "\n".join(out)


def production_lines(text: str, rel: Path) -> list[tuple[int, str]]:
    """(lineno, code-only line) for lines OUTSIDE `#[cfg(test)] mod` bodies."""
    return list(enumerate(production_text(text, rel).splitlines(), 1))


# ---------------------------------------------------------------------------
# Module map + reference closure (the edge policy, in code)
# ---------------------------------------------------------------------------

PATH_REF_RE = re.compile(r"\b(crate|super|self)((?:::[A-Za-z_][A-Za-z0-9_]*)+)")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

# A file that declares `mod foo;` may then write `foo::Item` and `use foo::{..}`
# with NO `crate::`/`super::`/`self::` prefix — Rust resolves the bare first
# segment against the items in scope, and `mod foo;` puts `foo` there. Such a
# reference is a genuine USE of the child module, so it is an edge.
#
# This does NOT make a `mod` declaration an edge: the declaration alone adds
# nothing, and CHILD_USE_RE must find an actual unqualified `foo::` occurrence
# in the same file's production text. The distinction is what the two regexes
# below encode, and audit r17 measured what conflating them cost — 27 modules
# and 15,542 lines of reachable production code, including the whole of
# clean-olean's `import::{load,parse,path,module_cache_direct}` IO surface,
# were reachable by exactly this spelling and invisible to the closure.
#
# The reading is EXACT rather than heuristic: within one file `mod foo;` claims
# the name `foo`, so a colliding `use ... as foo` does not compile, and a bare
# `foo::` in that file can only mean the child module. `(?<![:A-Za-z0-9_])`
# keeps `std::path::PathBuf` from reading as a use of a child `mod path;`.
CHILD_MOD_DECL_RE = re.compile(
    r"^[ \t]*(?:pub(?:\s*\([^)]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;", re.M
)


def child_mod_uses(stripped: str) -> set[str]:
    """Names of child modules this file BOTH declares (`mod foo;`) and USES."""
    out: set[str] = set()
    for name in set(CHILD_MOD_DECL_RE.findall(stripped)):
        if re.search(rf"(?<![:A-Za-z0-9_]){re.escape(name)}::", stripped):
            out.add(name)
    return out

IO_TOKENS: tuple[tuple[str, str], ...] = (
    (r"\bstd::fs\b", "std::fs"),
    (r"\bfs::(?:read|write|create|remove|copy|rename|metadata|File)\w*", "fs::*"),
    (r"\bFile::(?:open|create)\b", "File::open/create"),
    (r"\bOpenOptions\b", "OpenOptions"),
    (r"\bread_to_string\s*\(", "read_to_string"),
    (r"\bBufReader\b", "BufReader"),
    (r"\bBufWriter\b", "BufWriter"),
    (r"\bstd::io\b", "std::io"),
    (r"\bio::(?:Read|Write|BufRead|stdin|stdout|stderr)\b", "io::*"),
    (r"\bCommand::new\b", "process::Command"),
    (r"\bstd::process\b", "std::process"),
    (r"\bstd::net\b", "std::net"),
    (r"\benv::var(?:_os)?\s*\(", "env::var"),
    (r"\bMmap\b|\bmemmap\w*\b", "mmap"),
)

# Named hazards worth surfacing per member: a verdict path that documents its own
# skip. Navigation, not verdict — the token is reported with its line.
HAZARD_TOKENS: tuple[tuple[str, str], ...] = (
    (r"\bno_checksum\b", "no_checksum"),
    (r"\b\w*_unchecked\b", "*_unchecked"),
    (r"\b\w*_unvalidated\b", "*_unvalidated"),
    (r"\bstructural\w*\b", "structural*"),
    (r"\bskip_verif\w*\b", "skip_verif*"),
)

MINT_RE = re.compile(r"\bTrustLevel::KernelVerified\b")
# A lane (c) member that offers `--self-test`/`--selftest` has an entry point a
# demonstration could USE. It is not itself a demonstration — the gate registry
# is the authority on whether anyone ever made the gate say no — but the split
# is information the refusal ledger can carry for free.
SELFTEST_FLAG_RE = re.compile(r"--self-?test\b")
COMPARE_BEFORE_RE = re.compile(r"(==|!=|<|>|matches!\s*\(|\bif\s+let\b|\bmatch\b)\s*$")


def module_map(src: Path) -> dict[tuple[str, ...], Path]:
    """module path tuple -> file, for one crate's `src/`."""
    out: dict[tuple[str, ...], Path] = {}
    for p in sorted(src.rglob("*.rs")):
        parts = list(p.relative_to(src).parts)
        if parts[-1] == "lib.rs" and len(parts) == 1:
            continue
        if parts[-1] == "mod.rs":
            parts = parts[:-1]
        else:
            parts[-1] = parts[-1][: -len(".rs")]
        if parts:
            out[tuple(parts)] = p
    return out


def _expand_use_group(text: str, brace_index: int) -> list[str]:
    """Leading identifiers of each entry in a `use a::{b, c::d};` brace group."""
    depth = 0
    cur = ""
    entries: list[str] = []
    i = brace_index
    while i < len(text):
        c = text[i]
        if c == "{":
            depth += 1
            if depth == 1:
                cur = ""
                i += 1
                continue
        elif c == "}":
            depth -= 1
            if depth == 0:
                entries.append(cur)
                break
        if depth == 1 and c == ",":
            entries.append(cur)
            cur = ""
        else:
            cur += c
        i += 1
    out: list[str] = []
    for entry in entries:
        m = IDENT_RE.match(entry.strip())
        if m:
            out.append(m.group(0))
    return out


def module_refs(
    text: str, self_mod: tuple[str, ...], mmap: dict[tuple[str, ...], Path], rel: Path
) -> tuple[set[tuple[str, ...]], set[str]]:
    """(resolved in-crate module refs, unresolved reference strings) for one file."""
    stripped = production_text(text, rel)
    candidates: set[tuple[str, ...]] = set()
    for m in PATH_REF_RE.finditer(stripped):
        kind = m.group(1)
        segs = tuple(s for s in m.group(2).split("::") if s)
        if kind == "crate":
            base = segs
        elif kind == "super":
            base = tuple(self_mod[:-1]) + segs
        else:
            base = tuple(self_mod) + segs
        candidates.add(base)
        tail = stripped[m.end() : m.end() + 48]
        if re.match(r"\s*::\s*\{", tail):
            for ident in _expand_use_group(stripped, m.end() + tail.index("{")):
                candidates.add(base + (ident,))
    for name in child_mod_uses(stripped):
        candidates.add(tuple(self_mod) + (name,))
    resolved: set[tuple[str, ...]] = set()
    unresolved: set[str] = set()
    for segs in candidates:
        hit = None
        for i in range(len(segs), 0, -1):
            if segs[:i] in mmap:
                hit = segs[:i]
                break
        if hit is not None:
            resolved.add(hit)
        else:
            unresolved.add("::".join(segs))
    return resolved, unresolved


def reference_closure(
    roots: list[tuple[str, ...]], mmap: dict[tuple[str, ...], Path], src: Path
) -> tuple[dict[tuple[str, ...], int], list[str], list[dict]]:
    """Transitive in-crate reference closure.

    Returns (module -> depth, unresolved refs, test modules referenced but not
    followed). Test modules are named, never silently followed and never
    silently dropped: production verdict surface is production code.
    """
    depth_of = {r: 0 for r in roots}
    frontier = list(roots)
    unresolved: set[str] = set()
    test_refs: dict[str, list[str]] = {}
    d = 0
    while frontier:
        d += 1
        nxt: list[tuple[str, ...]] = []
        for mod in frontier:
            path = mmap[mod]
            rel = path.relative_to(src)
            text = path.read_text(errors="replace")
            resolved, unres = module_refs(text, mod, mmap, rel)
            unresolved |= unres
            for r in sorted(resolved):
                if r in depth_of:
                    continue
                if is_test_path(mmap[r].relative_to(src)):
                    test_refs.setdefault("::".join(r), []).append("::".join(mod))
                    continue
                depth_of[r] = d
                nxt.append(r)
        frontier = nxt
    return (
        depth_of,
        sorted(unresolved),
        [
            {"module": k, "referenced_by": sorted(set(v)), "reason": "test module — not production verdict surface"}
            for k, v in sorted(test_refs.items())
        ],
    )


# ---------------------------------------------------------------------------
# Root derivation
# ---------------------------------------------------------------------------


def _read_json(root: Path, rel: str) -> object:
    path = root / rel
    if not path.is_file():
        raise VerdictSetError(
            f"required input {rel} is absent — the derivation cannot invent it "
            "(this is a fail-closed abort, not an empty partition)"
        )
    try:
        return json.loads(path.read_text())
    except ValueError as exc:
        raise VerdictSetError(f"{rel} is not valid JSON: {exc}") from exc


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def olean_structural_roots(root: Path) -> tuple[list[str], list[dict], list[dict]]:
    """R-OLEAN-S: site files of S-classified env-bypass census rows, in clean-olean."""
    census = _read_json(root, CENSUS_PATH)
    if not isinstance(census, dict) or not isinstance(census.get("rows"), list):
        raise VerdictSetError(f"{CENSUS_PATH} has no 'rows' list — schema drift; refusing to derive")
    files: dict[str, list[str]] = {}
    scope_excluded: list[dict] = []
    class_excluded: list[dict] = []
    for row in census["rows"]:
        if not isinstance(row, dict) or "classification" not in row:
            raise VerdictSetError(f"{CENSUS_PATH}: a row lacks 'classification' — schema drift")
        rid = row.get("id", "<unnamed>")
        classification = str(row["classification"])
        structural = "S" in classification
        for site in row.get("sites") or []:
            if not isinstance(site, dict) or not site.get("file"):
                raise VerdictSetError(f"{CENSUS_PATH}: row {rid!r} has a site without 'file'")
            rel = site["file"]
            if not (root / rel).is_file():
                raise VerdictSetError(
                    f"{CENSUS_PATH}: row {rid!r} names site file {rel!r}, which does not exist "
                    "in the tree — a stale census site cannot seed a verdict set"
                )
            if not structural:
                class_excluded.append(
                    {"file": rel, "census_row": rid, "classification": classification,
                     "reason": "census classification does not contain S (not a lane R1 keeps structural)"}
                )
                continue
            if not rel.startswith("crates/clean-olean/src/"):
                scope_excluded.append(
                    {"file": rel, "census_row": rid, "classification": classification,
                     "reason": "S-classified site outside crates/clean-olean/src/ — outside Ring R2 lane (a)'s "
                               "declared olean scope; recorded so the scoping is visible"}
                )
                continue
            files.setdefault(rel, []).append(f"env_bypass_census:{rid}({classification})")
    evidence = [{"file": f, "evidence": sorted(set(ev))} for f, ev in sorted(files.items())]
    return sorted(files), evidence, scope_excluded + class_excluded


def mint_sites(root: Path) -> dict[str, list[dict]]:
    """R-MINT: lexed, cfg(test)-aware `TrustLevel::KernelVerified` MINT sites, all crates.

    Test code is excluded three ways: a test FILE by name (`is_test_path`), a file
    whose head is `#![cfg(test)]` (`headed_cfg_test`), and an inline
    `#[cfg(test)] mod { .. }` body (`production_text`)."""
    hits: dict[str, list[dict]] = {}
    crates = root / "crates"
    if not crates.is_dir():
        raise VerdictSetError("crates/ is absent — this is not a clean checkout")
    for path in sorted(crates.rglob("*.rs")):
        rel = path.relative_to(root)
        if "src" not in rel.parts:
            continue
        if is_test_path(Path(*rel.parts[rel.parts.index("src") :])):
            continue
        text = path.read_text(errors="replace")
        if "KernelVerified" not in text or headed_cfg_test(text):
            continue
        for lineno, line in production_lines(text, rel):
            for m in MINT_RE.finditer(line):
                before = line[: m.start()].rstrip()
                after = line[m.end() :]
                if COMPARE_BEFORE_RE.search(before) or "=>" in after:
                    continue  # comparison or match-arm pattern: consumption, not minting
                hits.setdefault(str(rel), []).append({"line": lineno, "form": line.strip()[:120]})
    return hits


def verify_anchor_roots(root: Path, anchors: tuple[tuple[str, str, str], ...], rule: str) -> list[dict]:
    """Declared roots, each verified present with its required symbol."""
    out: list[dict] = []
    for rel, symbol, role in anchors:
        path = root / rel
        if not path.is_file():
            raise VerdictSetError(
                f"{rule}: declared anchor {rel!r} does not exist — the role {role!r} has moved; "
                "re-derive the anchor table rather than emitting a partial verdict set"
            )
        if symbol not in strip_noncode(path.read_text(errors="replace")):
            raise VerdictSetError(
                f"{rule}: anchor {rel!r} no longer defines {symbol!r} (searched code only, comments "
                "and literals blanked) — the machinery moved; refusing to attribute the role "
                f"{role!r} to a file that does not carry it"
            )
        out.append({"file": rel, "symbol": symbol, "role": role})
    return out


def rust_input_digest_probe(root: Path) -> list[dict]:
    """R-SUITE: is the suite runner's input-digest machinery Rust anywhere?"""
    found: list[dict] = []
    crates = root / "crates"
    if not crates.is_dir():
        return found
    needle = re.compile(r"\bfn\s+input_digest\b")
    for path in sorted(crates.rglob("*.rs")):
        rel = path.relative_to(root)
        text = path.read_text(errors="replace")
        if "input_digest" not in text:
            continue
        for lineno, line in enumerate(strip_noncode(text).splitlines(), 1):
            if needle.search(line):
                found.append({"file": str(rel), "line": lineno})
    return found


# ---------------------------------------------------------------------------
# Member construction
# ---------------------------------------------------------------------------


def scan_member(root: Path, rel: str) -> dict:
    """Per-file measurement: lines, digest, IO sites, hazard tokens."""
    path = root / rel
    text = path.read_text(errors="replace")
    io_sites: list[dict] = []
    hazards: dict[str, int] = {}
    for lineno, line in production_lines(text, Path(rel)):
        for pattern, label in IO_TOKENS:
            if re.search(pattern, line):
                io_sites.append({"line": lineno, "token": label})
        for pattern, label in HAZARD_TOKENS:
            if re.search(pattern, line):
                hazards[label] = hazards.get(label, 0) + 1
    return {
        "lines": len(text.splitlines()),
        "sha256": sha256_file(path),
        "io_sites": io_sites,
        "hazard_tokens": {k: hazards[k] for k in sorted(hazards)},
    }


def build_lane_ab(root: Path) -> dict:
    """Derive lanes (a) and (b): roots per sublane, closure, IO split."""
    olean_files, olean_evidence, olean_excluded = olean_structural_roots(root)
    verify_anchors = verify_anchor_roots(root, VERIFY_ANCHORS, "R-VERIFY")
    shard_anchors = verify_anchor_roots(root, SHARD_ANCHORS, "R-SHARD")
    mints = mint_sites(root)

    mv_mint_files = sorted(f for f in mints if f.startswith("crates/clean-mathverse/src/"))
    outside_rows = [
        {
            "file": f,
            "mint_sites": mints[f],
            "note": "Ring R2 lane (a) scopes the KernelVerified-minting lane to clean-mathverse; this "
            "site mints the same verdict OUTSIDE that scope. Recorded so the scoping is a measured "
            "decision, not a silence (R10: silence must mean no).",
        }
        for f in sorted(mints)
        if not f.startswith("crates/clean-mathverse/src/")
    ]

    root_spec: dict[str, list[dict]] = {
        "a-olean-structural": [
            {"file": r["file"], "why": "; ".join(r["evidence"]), "rule": "R-OLEAN-S"} for r in olean_evidence
        ],
        "a-verify-checker-census-firewall": [
            {"file": a["file"], "why": f"{a['role']} (anchor symbol {a['symbol']!r})", "rule": "R-VERIFY"}
            for a in verify_anchors
        ],
        "a-mathverse-shard-digest-kv": [
            {"file": a["file"], "why": f"{a['role']} (anchor symbol {a['symbol']!r})", "rule": "R-SHARD"}
            for a in shard_anchors
        ]
        + [
            {
                "file": f,
                "why": f"{len(mints[f])} KernelVerified mint site(s) at line(s) "
                + ",".join(str(s["line"]) for s in mints[f][:8]),
                "rule": "R-MINT",
            }
            for f in mv_mint_files
        ],
    }

    members: list[dict] = []
    unresolved_all: dict[str, list[str]] = {}
    test_refs_all: dict[str, list[dict]] = {}
    for sublane, crate in CRATE_OF_SUBLANE.items():
        src = root / "crates" / crate / "src"
        if not src.is_dir():
            raise VerdictSetError(f"{crate}: crates/{crate}/src is absent — cannot derive {sublane}")
        mmap = module_map(src)
        roots: list[tuple[str, ...]] = []
        why_of: dict[tuple[str, ...], list[str]] = {}
        for spec in root_spec[sublane]:
            rel = Path(spec["file"]).relative_to(Path("crates") / crate / "src")
            parts = list(rel.parts)
            if parts[-1] == "mod.rs":
                parts = parts[:-1]
            else:
                parts[-1] = parts[-1][: -len(".rs")]
            key = tuple(parts)
            if key not in mmap:
                raise VerdictSetError(
                    f"{sublane}: root file {spec['file']!r} does not resolve to a module in "
                    f"crates/{crate}/src — module-map drift"
                )
            if key not in why_of:
                roots.append(key)
                why_of[key] = []
            why_of[key].append(f"{spec['rule']}: {spec['why']}")
        depth_of, unresolved, test_refs = reference_closure(roots, mmap, src)
        if unresolved:
            unresolved_all[crate] = unresolved
        if test_refs:
            test_refs_all[crate] = test_refs
        for mod, depth in sorted(depth_of.items()):
            rel = str(mmap[mod].relative_to(root))
            scan = scan_member(root, rel)
            members.append(
                {
                    "path": rel,
                    "crate": crate,
                    "module": "::".join(mod),
                    "sublane": sublane,
                    "depth": depth,
                    "selector": "root" if depth == 0 else f"in-crate reference closure (depth {depth})",
                    "why": why_of.get(mod, ["reached by the in-crate reference closure from a root"]),
                    "lines": scan["lines"],
                    "sha256": scan["sha256"],
                    "io_token_count": len(scan["io_sites"]),
                    "io_sites": scan["io_sites"][:8],
                    "io_sites_truncated": max(0, len(scan["io_sites"]) - 8),
                    "hazard_tokens": scan["hazard_tokens"],
                    "chain": {
                        "status": "unchained",
                        "links_held": 0,
                        "note": "no five-link chain record names this body; Ring R2 lane (a) owes one per member",
                    },
                    "ledger_rows": [],
                }
            )
    members.sort(key=lambda m: m["path"])
    return {
        "members": members,
        "roots": root_spec,
        "olean_excluded": olean_excluded,
        "mint_outside": outside_rows,
        "unresolved_refs": unresolved_all,
        "test_modules_not_followed": test_refs_all,
    }


def build_lane_c(root: Path) -> dict:
    """R-GATES: the claim-owning script surface, from the gate registry + the R2 gates."""
    registry = _read_json(root, REGISTRY_PATH)
    if not isinstance(registry, dict) or not isinstance(registry.get("rows"), list):
        raise VerdictSetError(f"{REGISTRY_PATH} has no 'rows' list — schema drift; refusing to derive")
    members: list[dict] = []
    excluded: list[dict] = []
    seen: set[str] = set()
    for row in registry["rows"]:
        if not isinstance(row, dict):
            raise VerdictSetError(f"{REGISTRY_PATH}: a row is not an object — schema drift")
        for key in ("id", "path", "kind", "claims"):
            if key not in row:
                raise VerdictSetError(f"{REGISTRY_PATH}: row {row.get('id', '<unnamed>')!r} lacks {key!r}")
        path = row["path"]
        if not path:
            continue  # legs and suite rows carry no artifact of their own
        if not (path.startswith("scripts/") and path.endswith((".sh", ".py"))):
            excluded.append({"path": path, "id": row["id"], "reason": "not a script under scripts/"})
            continue
        if row["claims"] == "none":
            excluded.append(
                {"path": path, "id": row["id"], "reason": "registry row claims nothing — not claim-owning"}
            )
            continue
        if not (root / path).is_file():
            raise VerdictSetError(
                f"{REGISTRY_PATH}: row {row['id']!r} names {path!r}, absent from the tree — a registry "
                "that points at a missing gate cannot pin a TCB surface"
            )
        seen.add(path)
        scan_path = root / path
        text = scan_path.read_text(errors="replace")
        members.append(
            {
                "path": path,
                "registry_id": row["id"],
                "kind": row["kind"],
                "claims": row["claims"],
                "disposition": "tcb-declared",
                "lines": len(text.splitlines()),
                "sha256": sha256_file(scan_path),
                "demonstrated": bool(row.get("demonstrated")),
                "waived": bool(row.get("waiver")),
                "self_test_entry_point": bool(SELFTEST_FLAG_RE.search(text)),
                "wired_by": row.get("wired_by") or [],
            }
        )
    for path in RING_R2_GATES:
        if path in seen:
            continue
        full = root / path
        if full.is_file():
            text = full.read_text(errors="replace")
            members.append(
                {
                    "path": path,
                    "registry_id": None,
                    "kind": "gate",
                    "claims": "soundness",
                    "disposition": "tcb-declared",
                    "lines": len(text.splitlines()),
                    "sha256": sha256_file(full),
                    "demonstrated": False,
                    "waived": False,
                    "self_test_entry_point": bool(SELFTEST_FLAG_RE.search(text)),
                    "wired_by": [],
                    "note": "Ring R2 gate present in the tree with no data/gate_registry.json row yet "
                    "(the registry is wired separately); pinned here so the lane (c) inventory is complete",
                }
            )
        else:
            excluded.append(
                {
                    "path": path,
                    "id": None,
                    "reason": "Ring R2 gate named by program §5 but ABSENT from the tree — planned, "
                    "recorded, not assumed",
                }
            )
    members.sort(key=lambda m: m["path"])
    return {"members": members, "excluded": excluded}


# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------

RULES = {
    "R-OLEAN-S": "lane (a)/(b) olean roots = site files under crates/clean-olean/src/ of every "
    "data/env_bypass_census.json row whose classification contains 'S' (load-bearing-structural) — "
    "exactly 'the lanes R1 keeps structural'.",
    "R-VERIFY": "lane (a)/(b) clean-verify roots = the declared ANCHORS table (file, required symbol, "
    "role), each verified present in code; a vanished symbol aborts the derivation.",
    "R-SHARD": "lane (a)/(b) mathverse shard-digest roots = the declared ANCHORS table, same posture.",
    "R-MINT": "lane (a)/(b) mathverse KernelVerified roots = every production module with a LEXED "
    "TrustLevel::KernelVerified mint site (value position; comparisons and match-arm patterns are "
    "consumption, not minting; #[cfg(test)] mod bodies, test files by name and files headed "
    "#![cfg(test)] excluded).",
    "R-SUITE": "lane (a)'s suite-runner input-digest machinery is PROBED for in Rust (fn input_digest "
    "over crates/**/*.rs); an empty probe is recorded as a dated correction, never as a silence.",
    "R-GATES": "lane (c) = every data/gate_registry.json row whose artifact is a script under scripts/ "
    "with claims != 'none', plus the three Ring-R2 gate names, present or recorded absent.",
}

EDGE_POLICY = {
    "granularity": "module (one .rs file, or a dir with mod.rs)",
    "edges_followed": "in-crate references at module granularity, in two spellings: (1) path-qualified "
    "— crate::, super::, self::, including the identifiers of `use ...::{a, b}` brace groups; and (2) a "
    "BARE `foo::` inside a file that itself declares `mod foo;`, which Rust resolves to that child "
    "module. Both resolve to the longest prefix that names a module. A `mod` declaration alone is NOT "
    "an edge — spelling (2) requires an actual unqualified `foo::` in the same file's production text",
    "edges_not_followed": "`mod x;` declarations (declaring a submodule is not using it); references "
    "that occur only inside `#[cfg(test)] mod` bodies (test code is not production verdict surface); "
    "edges into test modules (recorded in test_modules_not_followed, never silently dropped); "
    "cross-crate paths; references that resolve to no module (recorded in unresolved_refs)",
    "termination": "transitive to a fixed point within one crate's src/; measured small (see partition counts)",
    "source_scan": "lexed — comments and string/raw-string/char literals are blanked before any match, "
    "and #[cfg(test)] mod bodies are excluded by brace tracking (gate-registry R9: a raw-lines scanner "
    "may not claim soundness)",
}

CLOSURE_LIMIT = (
    "This is a REFERENCE closure at module granularity, NOT the per-body CALL closure. The call "
    "closure needs the trust-host whole-crate dump that data/spine_set.PENDING.md records as not yet "
    "produced (the same blocker G-SPINE-SET has). Until that dump exists, lane (a)'s membership is a "
    "conservative module-level surface: it can contain bodies no verdict path reaches, and it can MISS "
    "a body reached only through a dyn/fn-pointer edge. scripts/verdict_gate.sh refuses on this."
)


def build(root: Path, previous: dict | None, rebase_reason: str | None, now_utc: str | None) -> dict:
    ab = build_lane_ab(root)
    c = build_lane_c(root)

    lane_a = [m for m in ab["members"] if m["io_token_count"] == 0]
    lane_b = [m for m in ab["members"] if m["io_token_count"] > 0]
    for m in lane_b:
        # Ring R2 lane (b): "decode-pure separated from read-IO where feasible".
        # Separation is a REFACTOR, so it cannot be measured out of the source —
        # it is recorded, per member, when someone does it and ledgers the
        # residual boundary. Nothing has been separated, so the field says so
        # rather than being absent (R10: silence must mean no).
        m["separation"] = {
            "status": "not-separated",
            "recorded_by": None,
            "note": "decode-pure half not split out; the whole module is in the IO lane",
        }

    suite_probe = rust_input_digest_probe(root)
    corrections: list[dict] = []

    outside_olean = [r for r in ab["olean_excluded"] if "outside crates/clean-olean" in r["reason"]]
    if outside_olean:
        corrections.append(
            {
                "id": "R-OLEAN-S-scope-gap",
                "date": "2026-08-25",
                "statement": "Ring R2 lane (a) names 'clean-olean's decode/registration for the lanes R1 "
                f"keeps structural'. Measured: {len(outside_olean)} S-classified env-bypass census site(s) "
                "live OUTSIDE crates/clean-olean/src — in clean-server's handlers and clean-mathverse's "
                "per-constant/closure/parallel CLI load paths. They mint the same class of admission with "
                "the same structural tier, so either the lane's scope widens to cover them or a dated "
                "decision records why it does not. Neither has happened; the sites are listed here so the "
                "gap is a number, not a silence.",
                "sites": outside_olean,
                "owed": "a scope decision (widen lane (a), or record why these are out of scope)",
            }
        )
    member_paths = {m["path"] for m in ab["members"]}
    nons_olean = [
        r
        for r in ab["olean_excluded"]
        if r["file"].startswith("crates/clean-olean/src/")
        and "classification does not contain S" in r["reason"]
        and r["file"] not in member_paths
    ]
    if nons_olean:
        corrections.append(
            {
                "id": "R-OLEAN-NONS-doors",
                "date": "2026-08-25",
                "statement": "R-OLEAN-S admits only the lanes R1 keeps STRUCTURAL, because that is the "
                "sentence Ring R2 wrote. Measured consequence: "
                f"{len(nons_olean)} clean-olean source file(s) carrying a non-S env-bypass door are outside "
                "the verdict set and are reached by no other root. A 'P' (provable-in-place) classification "
                "is an intention, not a proof — until R1's theorem lands, that door mints admissions the "
                "same way an S door does. Either the rule widens to P/unclassified doors or a dated "
                "decision records why lane (a) stops at S.",
                "sites": nons_olean,
                "owed": "a decision on non-S clean-olean doors (widen R-OLEAN-S to P/unclassified, or record why not)",
            }
        )
    if ab["mint_outside"]:
        corrections.append(
            {
                "id": "R-MINT-scope-gap",
                "date": "2026-08-25",
                "statement": "Ring R2 lane (a) scopes the KernelVerified-minting lane to clean-mathverse. "
                f"Measured: {len(ab['mint_outside'])} production module(s) in OTHER crates mint "
                "TrustLevel::KernelVerified in a value position. Same posture as the olean scope gap: the "
                "lane widens or a dated decision says why not.",
                "sites": [r["file"] for r in ab["mint_outside"]],
                "owed": "a scope decision (widen lane (a), or record why these are out of scope)",
            }
        )
    if suite_probe:
        corrections.append(
            {
                "id": "R-SUITE-rust-found",
                "date": "2026-08-25",
                "statement": "the suite runner's input-digest machinery WAS found in Rust; the "
                "2026-08-25 correction below no longer applies and the anchor table must adopt it",
                "sites": suite_probe,
            }
        )
    else:
        corrections.append(
            {
                "id": "R-SUITE-not-rust",
                "date": "2026-08-25",
                "statement": "Ring R2 lane (a) lists 'the suite runner's input-digest machinery' as "
                "PURE-RUST verdict code. Measured at HEAD: no Rust `fn input_digest` exists anywhere "
                "under crates/ (crates/clean-verify/tests/crystal_a1_lineage/freshness.rs even "
                "documents the machinery as `verify_runner.py::input_digest`). The machinery is "
                "Python, so it cannot be chained with the spine recipe and cannot enter lane (a); it "
                "is routed to lane (c) as claim-owning script surface. R6 (measurement > design doc) "
                "governs: the design's lane assignment is corrected here, dated, rather than the "
                "measurement being rounded to fit it.",
                "routed_to": "c_script_surface",
                "member": "scripts/verify_runner.py",
                "member_present": (root / "scripts/verify_runner.py").is_file(),
                "registry_row": None,
            }
        )

    # The corrected member joins lane (c) even though the registry has no row for
    # it — the absence is itself reported, never papered over.
    vr = root / "scripts/verify_runner.py"
    if vr.is_file() and not any(m["path"] == "scripts/verify_runner.py" for m in c["members"]):
        text = vr.read_text(errors="replace")
        c["members"].append(
            {
                "path": "scripts/verify_runner.py",
                "registry_id": None,
                "kind": "tool",
                "claims": "evidence",
                "disposition": "tcb-declared",
                "lines": len(text.splitlines()),
                "sha256": sha256_file(vr),
                "demonstrated": False,
                "waived": False,
                "self_test_entry_point": bool(SELFTEST_FLAG_RE.search(text)),
                "wired_by": [],
                "note": "admitted by correction R-SUITE-not-rust: it owns the suite-state freshness "
                "verdict (input_digest decides whether a GREEN survives or demotes to UNKNOWN) and has "
                "NO data/gate_registry.json row",
            }
        )
        c["members"].sort(key=lambda m: m["path"])

    measured_total = sum(m["lines"] for m in c["members"])
    prev_ratchet = (previous or {}).get("partitions", {}).get("c_script_surface", {}).get("line_ratchet")
    rebases: list[dict] = list(prev_ratchet.get("rebases", [])) if prev_ratchet else []
    if prev_ratchet:
        baseline = int(prev_ratchet["baseline_total_lines"])
        minted_utc = prev_ratchet["minted_utc"]
        if measured_total > baseline:
            if not rebase_reason:
                raise VerdictSetError(
                    f"lane (c) line ratchet EXCEEDED: measured {measured_total} > baseline {baseline} "
                    f"(+{measured_total - baseline}). The TCB script surface may shrink freely; growing "
                    "it needs an explicit dated rebase: re-run with "
                    '--rebase-up "<why this surface must grow>".'
                )
            rebases.append(
                {
                    "date": (now_utc or _dt.datetime.now(_dt.UTC).strftime("%Y-%m-%d"))[:10],
                    "from": baseline,
                    "to": measured_total,
                    "reason": rebase_reason,
                }
            )
            baseline = measured_total
        else:
            baseline = measured_total  # ratchets tighten silently
    else:
        baseline = measured_total
        minted_utc = now_utc or _dt.datetime.now(_dt.UTC).strftime("%Y-%m-%dT%H:%M:%SZ")
        if rebase_reason:
            raise VerdictSetError(
                "--rebase-up was passed but no committed line ratchet exists yet — there is nothing "
                "to rebase; mint the artifact first"
            )

    inputs = {}
    for rel in (CENSUS_PATH, REGISTRY_PATH):
        inputs[rel] = sha256_file(root / rel)

    doc = {
        "schema": SCHEMA,
        "what_this_is": (
            "The committed member list of the verdict-bearing surface — the code that could mint a "
            "false verdict even with a proved kernel — partitioned as Ring R2 demands "
            "(designs/2026-08-22-spine-and-lattice-program.md §5). Derived by scripts/verdict_set.py; "
            "quoting any count of it from prose is a bug. scripts/verdict_gate.sh owns the claim."
        ),
        "derivation": {
            "script": "scripts/verdict_set.py",
            "rules": RULES,
            "edge_policy": EDGE_POLICY,
            "closure_limit": CLOSURE_LIMIT,
            "input_pins": inputs,
            "regenerate": "scripts/verdict_set.py            (--check to verify the committed copy)",
        },
        "partitions": {
            "a_pure_rust": {
                "obligation": (
                    "every member chained with the spine recipe (five links), against the committed "
                    "spine set; Ring R2 gate: verdict_gate.sh over this artifact"
                ),
                "member_count": len(lane_a),
                "chained_count": sum(1 for m in lane_a if m["chain"]["status"] == "chained"),
                "sublane_counts": _counts(lane_a),
                "depth_histogram": _depth_histogram(lane_a),
                "members": lane_a,
            },
            "b_io_bearing": {
                "obligation": (
                    "decode-pure separated from read-IO where feasible; every residual IO boundary "
                    "contract-modeled and ledgered with a probe (program §3.6)"
                ),
                "member_count": len(lane_b),
                "ledgered_count": sum(1 for m in lane_b if m["ledger_rows"]),
                "separated_count": sum(1 for m in lane_b if m["separation"]["status"] == "separated"),
                "sublane_counts": _counts(lane_b),
                "depth_histogram": _depth_histogram(lane_b),
                "io_site_total": sum(m["io_token_count"] for m in lane_b),
                "members": lane_b,
            },
            "c_script_surface": {
                "obligation": (
                    "each member either rewritten in Rust (entering lane (a)) or declared TCB with a "
                    "committed digest + line-count ratchet; and a claim-owning gate that has never been "
                    "SEEN to refuse is an unearned claim (registry: demonstrated or waived)"
                ),
                "member_count": len(c["members"]),
                "rewritten_to_rust_count": sum(
                    1 for m in c["members"] if m["disposition"] == "rewritten-to-rust"
                ),
                "tcb_declared_count": sum(1 for m in c["members"] if m["disposition"] == "tcb-declared"),
                "demonstrated_count": sum(1 for m in c["members"] if m["demonstrated"]),
                "waived_count": sum(1 for m in c["members"] if m["waived"]),
                "undemonstrated_unwaived_count": sum(
                    1 for m in c["members"] if not m["demonstrated"] and not m["waived"]
                ),
                "undemonstrated_with_self_test_count": sum(
                    1
                    for m in c["members"]
                    if not m["demonstrated"] and not m["waived"] and m["self_test_entry_point"]
                ),
                "line_ratchet": {
                    "what": "total committed lines of the TCB script surface; may fall freely, may rise "
                    "only through scripts/verdict_set.py --rebase-up '<reason>' (recorded below)",
                    "direction": "down",
                    "baseline_total_lines": baseline,
                    "measured_total_lines": measured_total,
                    "minted_utc": minted_utc,
                    "rebases": rebases,
                },
                "members": c["members"],
                "excluded_by_rule": c["excluded"],
            },
        },
        "evidence": {
            "roots": ab["roots"],
            "corrections": corrections,
            "olean_sites_excluded_by_rule": ab["olean_excluded"],
            "mint_sites_outside_declared_lane": ab["mint_outside"],
            "unresolved_refs": ab["unresolved_refs"],
            "test_modules_not_followed": ab["test_modules_not_followed"],
            "artifacts_this_surface_depends_on": {
                SPINE_SET_PATH: (root / SPINE_SET_PATH).is_file(),
                SPINE_PENDING_PATH: (root / SPINE_PENDING_PATH).is_file(),
                ASSUMPTION_LEDGER_PATH: (root / ASSUMPTION_LEDGER_PATH).is_file(),
                IO_CONTRACTS_PATH: (root / IO_CONTRACTS_PATH).is_file(),
            },
        },
    }
    return doc


def _counts(members: list[dict]) -> dict:
    out: dict[str, int] = {}
    for m in members:
        out[m["sublane"]] = out.get(m["sublane"], 0) + 1
    return {k: out[k] for k in sorted(out)}


def _depth_histogram(members: list[dict]) -> dict:
    """How much of the partition is ANCHORED (depth 0) versus reached by the
    reference closure. A reader who wants the anchored core can take depth 0;
    the periphery is where the closure's over-approximation lives."""
    out: dict[str, int] = {}
    for m in members:
        key = f"depth_{m['depth']}"
        out[key] = out.get(key, 0) + 1
    return {k: out[k] for k in sorted(out, key=lambda s: int(s.split("_")[1]))}


def render(doc: dict) -> str:
    return json.dumps(doc, indent=1) + "\n"


# ---------------------------------------------------------------------------
# self-test: a synthetic tree + mutation arms
# ---------------------------------------------------------------------------


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def _synthetic_tree(base: Path) -> Path:
    """A minimal repo carrying every declared anchor, so the REAL anchor tables
    are exercised: adding an anchor automatically extends the fixture."""
    root = base / "repo"
    # anchors, each carrying its required symbol plus a small reference graph
    for rel, symbol, _role in VERIFY_ANCHORS + SHARD_ANCHORS:
        body = f"//! synthetic anchor\n{symbol} {{}}\n"
        if rel.endswith("vacuity_firewall.rs"):
            body += "use crate::spec::Specification;\nfn f(s: &Specification) {}\n"
        if rel.endswith("shard.rs"):
            body += "use std::fs::File;\nfn open() { let _ = File::open(\"x\"); }\n"
        _write(root / rel, body)
    _write(root / "crates/clean-verify/src/spec.rs", "//! synthetic spec\npub struct Specification;\n")
    _write(root / "crates/clean-verify/src/lib.rs", "pub mod spec;\n")
    _write(root / "crates/clean-mathverse/src/lib.rs", "pub mod shard;\n")
    _write(root / "crates/clean-olean/src/lib.rs", "pub mod import;\n")
    _write(
        root / "crates/clean-olean/src/import/load_register.rs",
        "//! synthetic loader\nuse crate::payload::decode;\npub fn load() { decode(); }\n",
    )
    _write(root / "crates/clean-olean/src/import/mod.rs", "pub mod load_register;\n")
    _write(root / "crates/clean-olean/src/payload.rs", "pub fn decode() {}\n")
    _write(
        root / "crates/clean-mathverse/src/mintlane.rs",
        "use crate::types::TrustLevel;\n"
        "pub fn mint() -> TrustLevel { TrustLevel::KernelVerified }\n"
        "pub fn is(t: TrustLevel) -> bool { t == TrustLevel::KernelVerified }\n"
        "pub fn label(t: TrustLevel) -> &'static str { match t { TrustLevel::KernelVerified => \"k\" } }\n",
    )
    _write(root / "crates/clean-mathverse/src/types.rs", "pub enum TrustLevel { KernelVerified }\n")
    _write(
        root / "data/env_bypass_census.json",
        json.dumps(
            {
                "rows": [
                    {
                        "id": "ind-meta-structural",
                        "classification": "S",
                        "sites": [{"file": "crates/clean-olean/src/import/load_register.rs"}],
                    },
                    {
                        "id": "axiom-stub-upgrade",
                        "classification": "E",
                        "sites": [{"file": "crates/clean-olean/src/payload.rs"}],
                    },
                ]
            }
        ),
    )
    _write(
        root / "data/gate_registry.json",
        json.dumps(
            {
                "rows": [
                    {
                        "id": "demo_gate",
                        "path": "scripts/demo_gate.sh",
                        "kind": "gate",
                        "claims": "soundness",
                        "demonstrated": {"date": "2026-08-25"},
                        "waiver": None,
                        "wired_by": ["scripts/local_gate.sh"],
                    },
                    {
                        "id": "undemo_gate",
                        "path": "scripts/undemo_gate.sh",
                        "kind": "gate",
                        "claims": "evidence",
                        "demonstrated": None,
                        "waiver": None,
                    },
                    {"id": "a_tool", "path": "scripts/tool.py", "kind": "tool", "claims": "none"},
                    {"id": "a_leg", "path": "", "kind": "leg", "claims": "soundness"},
                ]
            }
        ),
    )
    _write(root / "scripts/demo_gate.sh", "#!/bin/sh\nexit 0\n")
    _write(root / "scripts/undemo_gate.sh", "#!/bin/sh\nexit 0\n")
    _write(root / "scripts/tool.py", "print(1)\n")
    return root


_PASSED: list[str] = []


def _ok(arm: str) -> None:
    _PASSED.append(arm)
    print(f"  PASS  {arm}")


def _expect_raises(arm: str, fragment: str, fn, failures: list[str]) -> None:
    try:
        fn()
    except VerdictSetError as exc:
        if fragment in str(exc):
            _ok(arm)
        else:
            failures.append(f"{arm}: error text lacks {fragment!r}: {exc}")
    else:
        failures.append(f"{arm}: no error raised (fail-open)")


def self_test() -> int:
    import tempfile

    failures: list[str] = []
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        root = _synthetic_tree(base)

        def derive(r: Path = root, previous=None, rebase=None):
            return build(r, previous, rebase, now_utc="2026-08-25T00:00:00Z")

        # Arm 1: the happy path partitions -------------------------------
        doc = derive()
        a = doc["partitions"]["a_pure_rust"]
        b = doc["partitions"]["b_io_bearing"]
        c = doc["partitions"]["c_script_surface"]
        a_paths = {m["path"] for m in a["members"]}
        b_paths = {m["path"] for m in b["members"]}
        if "crates/clean-olean/src/import/load_register.rs" in a_paths and (
            "crates/clean-olean/src/payload.rs" in a_paths
        ):
            _ok("closure: an S-census root and the module it references are both members")
        else:
            failures.append(f"closure: olean members wrong: {sorted(a_paths | b_paths)}")
        if "crates/clean-mathverse/src/shard.rs" in b_paths:
            _ok("io-split: a member with File::open lands in lane (b), not lane (a)")
        else:
            failures.append(f"io-split: shard.rs not in lane (b): {sorted(b_paths)}")
        if b["separated_count"] == 0 and all(
            m["separation"]["status"] == "not-separated" for m in b["members"]
        ):
            _ok("io-split: every lane (b) member records 'not-separated' rather than omitting the field")
        else:
            failures.append("io-split: separation status missing or wrongly claimed")
        if "crates/clean-mathverse/src/mintlane.rs" in (a_paths | b_paths):
            _ok("mint: a KernelVerified mint site seeds a root (R-MINT)")
        else:
            failures.append("mint: mintlane.rs did not become a member")

        # Arm 2: mint predicate discriminates mint from consumption -------
        mints = mint_sites(root)
        rows = mints.get("crates/clean-mathverse/src/mintlane.rs", [])
        if len(rows) == 1 and rows[0]["line"] == 2:
            _ok("mint: `==` comparison and `=>` match-arm are NOT mints (1 of 3 lines)")
        else:
            failures.append(f"mint: predicate wrong, got {rows}")

        # Arm 3: lexer — a mint in a comment or a string is not a mint ----
        mutated = root / "crates/clean-mathverse/src/lexbait.rs"
        _write(
            mutated,
            '// let x = TrustLevel::KernelVerified;\nfn s() -> &\'static str { "TrustLevel::KernelVerified" }\n',
        )
        if "crates/clean-mathverse/src/lexbait.rs" not in mint_sites(root):
            _ok("lexer: a mint token in a comment or a string literal is not a mint site")
        else:
            failures.append("lexer: comment/string mint counted (raw-lines behaviour)")
        mutated.unlink()

        # Arm 3b: the lexer this gate runs is the reference's; its own cases must hold here.
        lexer_bad = _reference_lexer.lexer_failures()
        if NONCODE_RE is not _reference_lexer.NONCODE_RE:
            lexer_bad.append("NONCODE_RE is not the reference's object")
        if headed_cfg_test is not _reference_lexer.headed_cfg_test:
            lexer_bad.append("headed_cfg_test is not the reference's function")
        if lexer_bad:
            failures.append(f"lexer: read differently from rustc: {lexer_bad}")
        else:
            _ok(
                f"lexer: the reference's {len(_reference_lexer._LEXER_CASES)} readings and "
                f"{len(_reference_lexer._HEAD_CASES)} file heads hold (nested comments, raw-string prefixes)"
            )

        # Arm 4: cfg(test) blocks are excluded ---------------------------
        cfgfile = root / "crates/clean-mathverse/src/cfgbait.rs"
        _write(
            cfgfile,
            "#[cfg(test)]\nmod t {\n    fn f() { let _ = TrustLevel::KernelVerified; }\n}\n",
        )
        if "crates/clean-mathverse/src/cfgbait.rs" not in mint_sites(root):
            _ok("cfg(test): a mint inside #[cfg(test)] mod is not production surface")
        else:
            failures.append("cfg(test): test-only mint counted as production")
        cfgfile.unlink()

        # Arm 4b: only the EXACT #[cfg(test)] makes an inline body test code;
        # #[cfg(any(test, ..))] compiles in a non-test build when the other arm holds.
        cfgfile = root / "crates/clean-mathverse/src/cfgany.rs"
        _write(
            cfgfile,
            '#[cfg(any(test, feature = "x"))]\npub mod m {\n    pub fn f() { let _ = TrustLevel::KernelVerified; }\n}\n',
        )
        if "crates/clean-mathverse/src/cfgany.rs" in mint_sites(root):
            _ok("cfg(test): a mint inside #[cfg(any(test, ..))] mod stays production surface")
        else:
            failures.append("cfg(test): a #[cfg(any(test, ..))] body was blanked as test code")
        cfgfile.unlink()

        # Arm 4c: a file headed #![cfg(test)] is test code; every other head is not.
        mint_body = "pub fn m() -> TrustLevel { TrustLevel::KernelVerified }\n"
        heads = {
            "headed_plain": ("// c\n//! doc\n\n#![cfg(test)]\n", False),
            "headed_crlf": ("// c\r\n\r\n#![ cfg ( test ) ]\r\n", False),
            "headed_block_comment": ("/* c */\n#![cfg(test)]\n", True),
            "headed_other_attr": ("#![allow(dead_code)]\n#![cfg(test)]\n", True),
            "headed_any": ('#![cfg(any(test, feature = "x"))]\n', True),
            "headed_not": ("#![cfg(not(test))]\n", True),
            "headed_tool": ("#![rustfmt::cfg(test)]\n", True),
            "headed_outer": ("#[cfg(test)]\n", True),
            "headed_after_item": ("fn f() {}\n#![cfg(test)]\n", True),
            "headed_u2028": ("// c #![cfg(test)]\n", True),
        }
        for stem, (head, counted) in heads.items():
            _write(root / f"crates/clean-mathverse/src/{stem}.rs", head + mint_body)
        found = mint_sites(root)
        wrong = sorted(
            stem
            for stem, (_head, counted) in heads.items()
            if (f"crates/clean-mathverse/src/{stem}.rs" in found) is not counted
        )
        if not wrong:
            _ok(
                "cfg(test): a file headed #![cfg(test)] after only blank and // lines is test code; a block "
                "comment, another attribute or cfg, an outer attribute, an item or a U+2028 first keeps it counted"
            )
        else:
            failures.append(f"cfg(test): file-head rule misjudged {wrong}")
        for stem in heads:
            (root / f"crates/clean-mathverse/src/{stem}.rs").unlink()

        # Arm 5: fail-closed on a vanished anchor symbol -----------------
        anchor = root / VERIFY_ANCHORS[0][0]
        saved = anchor.read_text()
        anchor.write_text("//! the machinery moved\n")
        _expect_raises(
            "fail-closed: a vanished anchor symbol is named", VERIFY_ANCHORS[0][1], derive, failures
        )
        anchor.write_text(saved)

        # Arm 6: fail-closed on a missing anchor file --------------------
        anchor.unlink()
        _expect_raises("fail-closed: a missing anchor file is named", "does not exist", derive, failures)
        anchor.write_text(saved)

        # Arm 7: fail-closed on a stale census site ----------------------
        census = root / "data/env_bypass_census.json"
        doc_c = json.loads(census.read_text())
        doc_c["rows"][0]["sites"][0]["file"] = "crates/clean-olean/src/gone.rs"
        census.write_text(json.dumps(doc_c))
        _expect_raises("fail-closed: a stale census site is named", "does not exist in the tree", derive, failures)
        doc_c["rows"][0]["sites"][0]["file"] = "crates/clean-olean/src/import/load_register.rs"
        census.write_text(json.dumps(doc_c))

        # Arm 8: fail-closed on census schema drift ----------------------
        census.write_text(json.dumps({"no_rows": []}))
        _expect_raises("fail-closed: census schema drift", "no 'rows' list", derive, failures)
        census.write_text(json.dumps(doc_c))

        # Arm 9: fail-closed on a registry row pointing at a missing gate -
        reg = root / "data/gate_registry.json"
        reg_doc = json.loads(reg.read_text())
        reg_doc["rows"][0]["path"] = "scripts/vanished_gate.sh"
        reg.write_text(json.dumps(reg_doc))
        _expect_raises(
            "fail-closed: a registry gate absent from the tree is refused", "absent from the tree", derive, failures
        )
        reg_doc["rows"][0]["path"] = "scripts/demo_gate.sh"
        reg.write_text(json.dumps(reg_doc))

        # Arm 10: lane (c) selection — claims=none excluded, legs skipped -
        c_paths = {m["path"] for m in c["members"]}
        if c_paths == {"scripts/demo_gate.sh", "scripts/undemo_gate.sh"} and any(
            e["path"] == "scripts/tool.py" for e in c["excluded_by_rule"]
        ):
            _ok("lane (c): claim-owning scripts only; claims='none' excluded with a reason")
        else:
            failures.append(f"lane (c): membership wrong {c_paths}")
        if c["undemonstrated_unwaived_count"] == 1 and c["demonstrated_count"] == 1:
            _ok("lane (c): demonstrated/undemonstrated counted from the registry")
        else:
            failures.append(f"lane (c): demonstration counts wrong {c}")
        planned = [e for e in c["excluded_by_rule"] if e["reason"].startswith("Ring R2 gate named")]
        if len(planned) == 3:
            _ok("lane (c): absent Ring-R2 gates are recorded as planned, not assumed")
        else:
            failures.append(f"lane (c): planned-absent rows wrong {planned}")

        # Arm 11: the line ratchet -------------------------------------
        prev = copy.deepcopy(doc)
        (root / "scripts/demo_gate.sh").write_text("#!/bin/sh\n" + "echo x\n" * 40 + "exit 0\n")
        _expect_raises("ratchet: growth without --rebase-up is refused", "ratchet EXCEEDED", lambda: derive(previous=prev), failures)
        grown = derive(previous=prev, rebase="measured widening, self-test")
        gr = grown["partitions"]["c_script_surface"]["line_ratchet"]
        if gr["rebases"] and gr["rebases"][-1]["reason"] == "measured widening, self-test":
            _ok("ratchet: --rebase-up records a dated row and moves the baseline")
        else:
            failures.append(f"ratchet: rebase row missing {gr}")
        (root / "scripts/demo_gate.sh").write_text("#!/bin/sh\nexit 0\n")
        shrunk = derive(previous=grown)
        sr = shrunk["partitions"]["c_script_surface"]["line_ratchet"]
        if sr["baseline_total_lines"] < gr["baseline_total_lines"]:
            _ok("ratchet: the baseline tightens silently when the surface shrinks")
        else:
            failures.append(f"ratchet: did not tighten {sr}")

        # Arm 12: the R-SUITE correction is emitted, not assumed ---------
        corr = {c0["id"] for c0 in doc["evidence"]["corrections"]}
        if corr == {"R-SUITE-not-rust"}:
            _ok("correction: the absent-Rust suite-digest probe is recorded as a dated row")
        else:
            failures.append(f"correction: wrong rows {corr}")

        # Arm 12b: a cfg(test)-only reference is NOT a closure edge -------
        loader = root / "crates/clean-olean/src/import/load_register.rs"
        loader_saved = loader.read_text()
        _write(root / "crates/clean-olean/src/testonly.rs", "pub fn helper() {}\n")
        loader.write_text(
            loader_saved + "\n#[cfg(test)]\nmod t {\n    use crate::testonly::helper;\n    fn f() { helper(); }\n}\n"
        )
        after = derive()
        reached = {
            m["path"]
            for part in ("a_pure_rust", "b_io_bearing")
            for m in after["partitions"][part]["members"]
        }
        if "crates/clean-olean/src/testonly.rs" not in reached:
            _ok("closure: a reference that exists only inside #[cfg(test)] mod is not an edge")
        else:
            failures.append("closure: cfg(test)-only reference pulled a module into the surface")
        loader.write_text(loader_saved)
        (root / "crates/clean-olean/src/testonly.rs").unlink()

        # Arm 12b2: a BARE `foo::` in a file declaring `mod foo;` IS an edge,
        # and the declaration WITHOUT such a reference still is not. Both
        # halves in one derive, because the defect this arm pins was a rule
        # that got the second half right and never asked the first.
        _write(root / "crates/clean-olean/src/import/load_register/childused.rs", "pub fn helper() {}\n")
        _write(root / "crates/clean-olean/src/import/load_register/childunused.rs", "pub fn idle() {}\n")
        loader.write_text(
            loader_saved
            + "\nmod childused;\nmod childunused;\npub fn probe() { childused::helper(); }\n"
        )
        after_bare = derive()
        reached_bare = {
            m["path"]
            for part in ("a_pure_rust", "b_io_bearing")
            for m in after_bare["partitions"][part]["members"]
        }
        used = "crates/clean-olean/src/import/load_register/childused.rs"
        unused = "crates/clean-olean/src/import/load_register/childunused.rs"
        if used in reached_bare and unused not in reached_bare:
            _ok("closure: a bare `foo::` under `mod foo;` is an edge; the bare declaration is not")
        elif used not in reached_bare:
            failures.append("closure: a bare child-module reference was not followed")
        else:
            failures.append("closure: an unreferenced `mod foo;` declaration became an edge")
        loader.write_text(loader_saved)
        (root / "crates/clean-olean/src/import/load_register/childused.rs").unlink()
        (root / "crates/clean-olean/src/import/load_register/childunused.rs").unlink()
        (root / "crates/clean-olean/src/import/load_register").rmdir()

        # Arm 12c: scope gaps are emitted as dated corrections ------------
        doc_c2 = json.loads(census.read_text())
        _write(root / "crates/clean-server/src/handlers/admin.rs", "pub fn install() {}\n")
        doc_c2["rows"].append(
            {
                "id": "env-serde-load",
                "classification": "S",
                "sites": [{"file": "crates/clean-server/src/handlers/admin.rs"}],
            }
        )
        census.write_text(json.dumps(doc_c2))
        _write(
            root / "crates/clean-cli/src/mint_elsewhere.rs",
            "use crate::types::TrustLevel;\npub fn m() -> TrustLevel { TrustLevel::KernelVerified }\n",
        )
        gapped = derive()
        gap_ids = {c0["id"] for c0 in gapped["evidence"]["corrections"]}
        if {"R-OLEAN-S-scope-gap", "R-MINT-scope-gap"} <= gap_ids:
            _ok("scope: an S-site outside olean and a mint outside mathverse each raise a dated gap row")
        else:
            failures.append(f"scope: gap rows missing {gap_ids}")
        census.write_text(json.dumps(doc_c))
        (root / "crates/clean-cli/src/mint_elsewhere.rs").unlink()

        # Arm 13: determinism -------------------------------------------
        if render(derive()) == render(derive()):
            _ok("determinism: identical output for identical inputs")
        else:
            failures.append("determinism: two derivations differ")

        # Arm 14: --check detects a mutated committed artifact -----------
        out = root / DEFAULT_OUT
        _write(out, render(derive()))
        if run_check(root, out, quiet=True) == 0:
            _ok("--check: a freshly minted artifact verifies")
        else:
            failures.append("--check: fresh artifact did not verify")
        tampered = json.loads(out.read_text())
        tampered["partitions"]["a_pure_rust"]["member_count"] = 999
        out.write_text(json.dumps(tampered, indent=1) + "\n")
        if run_check(root, out, quiet=True) != 0:
            _ok("--check: a tampered committed artifact is refused")
        else:
            failures.append("--check: tampered artifact accepted (fail-open)")

    if failures:
        for f in failures:
            print(f"  FAIL  {f}", file=sys.stderr)
        print(f"VERDICT_SET self-test: {len(failures)} arm(s) RED", file=sys.stderr)
        return 1
    print(f"VERDICT_SET self-test: {len(_PASSED)} arms, all green")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def run_check(root: Path, out_path: Path, quiet: bool = False) -> int:
    if not out_path.is_file():
        if not quiet:
            print(f"VERDICT_SET=fail committed artifact {out_path} is absent", file=sys.stderr)
        return 1
    try:
        previous = json.loads(out_path.read_text())
    except ValueError as exc:
        if not quiet:
            print(f"VERDICT_SET=fail committed artifact is not valid JSON: {exc}", file=sys.stderr)
        return 1
    try:
        fresh = build(root, previous, None, now_utc=None)
    except VerdictSetError as exc:
        if not quiet:
            print(f"VERDICT_SET=fail {exc}", file=sys.stderr)
        return 1
    if render(fresh) == out_path.read_text():
        if not quiet:
            print(f"VERDICT_SET=ok {out_path} matches a fresh derivation")
        return 0
    if not quiet:
        print(
            f"VERDICT_SET=fail {out_path} DIFFERS from a fresh derivation — the verdict-bearing "
            "surface moved (or the artifact was edited by hand). Re-mint with scripts/verdict_set.py.",
            file=sys.stderr,
        )
        _print_delta(previous, fresh)
    return 1


def _print_delta(old: dict, new: dict) -> None:
    for part in ("a_pure_rust", "b_io_bearing", "c_script_surface"):
        o = {m["path"] for m in old.get("partitions", {}).get(part, {}).get("members", [])}
        n = {m["path"] for m in new["partitions"][part]["members"]}
        for p in sorted(n - o):
            print(f"    + {part}: {p}", file=sys.stderr)
        for p in sorted(o - n):
            print(f"    - {part}: {p}", file=sys.stderr)
        if o == n:
            oc = old.get("partitions", {}).get(part, {}).get("member_count")
            nc = new["partitions"][part]["member_count"]
            if oc != nc:
                print(f"    ~ {part}: member_count {oc} -> {nc}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    if "--pinned-inputs" in (sys.argv[1:] if argv is None else argv):
        print(*PINNED_INPUTS, sep="\n")
        return 0
    ap = argparse.ArgumentParser(
        prog="verdict_set.py",
        description="Derive data/verdict_set.json — the Ring R2 verdict-bearing surface (S&L §5).",
    )
    ap.add_argument("--out", default=str(REPO_ROOT / DEFAULT_OUT), help=f"output path (default {DEFAULT_OUT})")
    ap.add_argument("--root", default=str(REPO_ROOT), help="repo root to derive from")
    ap.add_argument("--check", action="store_true", help="derive and fail if the committed file differs")
    ap.add_argument("--describe", action="store_true", help="print the derivation contract and exit")
    ap.add_argument("--self-test", action="store_true", help="synthetic-tree mutation arms")
    ap.add_argument("--rebase-up", metavar="REASON", help="allow the lane (c) line ratchet to rise, dated")
    args = ap.parse_args(argv)

    if args.describe:
        print(__doc__)
        print("RULES")
        for k in sorted(RULES):
            print(f"  {k:10s} {RULES[k]}")
        print("\nEDGE POLICY")
        for k, v in EDGE_POLICY.items():
            print(f"  {k:20s} {v}")
        print(f"\nCLOSURE LIMIT\n  {CLOSURE_LIMIT}")
        return 0
    if args.self_test:
        return self_test()

    root = Path(args.root).resolve()
    out_path = Path(args.out)
    if args.check:
        return run_check(root, out_path)

    previous = None
    if out_path.is_file():
        try:
            previous = json.loads(out_path.read_text())
        except ValueError as exc:
            print(f"VERDICT_SET=fail existing {out_path} is not valid JSON: {exc}", file=sys.stderr)
            return 1
    try:
        doc = build(root, previous, args.rebase_up, now_utc=None)
    except VerdictSetError as exc:
        print(f"VERDICT_SET=fail {exc}", file=sys.stderr)
        return 1
    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp = out_path.with_suffix(out_path.suffix + ".tmp")
    tmp.write_text(render(doc))
    tmp.replace(out_path)
    p = doc["partitions"]
    print(
        f"VERDICT_SET ok a={p['a_pure_rust']['member_count']} "
        f"b={p['b_io_bearing']['member_count']} "
        f"c={p['c_script_surface']['member_count']} "
        f"c_lines={p['c_script_surface']['line_ratchet']['measured_total_lines']} "
        f"-> {out_path}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
