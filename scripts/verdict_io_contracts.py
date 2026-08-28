#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Derive `data/verdict_io_contracts.json` — Ring R2 lane (b)'s IO-boundary
contract model and its assumption ledger.

WHAT THIS IS
------------
`designs/2026-08-22-spine-and-lattice-program.md` §5, Ring R2, lane (b):

    "IO-bearing Rust — decode-pure separated from read-IO where feasible, the
     residual IO boundary CONTRACT-MODELED and LEDGERED (§3.6 pattern)"

and §3.6, the pattern it points at:

    "every unproved thing a chain stands on ... Each entry: statement, probe
     command, date, owning job ... an assumption entering without a ledger row
     is a gate failure. 'Zero axioms is not zero assumptions' is the recorded
     lesson this section operationalizes."

`data/verdict_set.json` measured lane (b): 23 IO-bearing members carrying 211
IO sites. That number is a PARTITION, not a model — it says where the IO is,
not what the verdict path assumes about it. This script does the modeling:

  1. CLASSIFY every one of the 211 sites twice — by EFFECT (what the site
     actually does) and by DEPENDENCE (whether the verdict's correctness
     depends on the IO's CONTENT or only on its SUCCESS). The second axis is
     the cheap one: a success-only boundary is discharged by "the call
     errored or it did not", a content-bearing one needs the bytes pinned.
  2. State, per effect class, the CONTRACT the verdict path assumes.
  3. Cite what CHECKS each contract today, in code, by pattern. A citation
     that stops resolving ABORTS the mint (see `verify_citations`) — an
     evidence pointer that rots is worse than no pointer.
  4. Emit one ledger row per (contract x member) that nothing fully checks,
     each with statement, probe, discharge, date and owning job.

WHAT THE COUNTS ARE NOT
-----------------------
211 is what the IO_TOKENS table in `scripts/verdict_set.py` can SEE. An IO
call reached through a helper, through a dependency's API (`serde_json::
from_reader`, `zstd::decode_all`), or through a macro is not a site. So 211 is
a LOWER bound on lane (b)'s IO surface, and that assumption is itself a ledger
row (`L-DENOM`) rather than a footnote. Likewise the effect classification is
LEXICAL — decided from the matched line, not from the program's semantics —
and that is `L-LEX`.

THE DENOMINATOR IS SHARED BY CONSTRUCTION
-----------------------------------------
This script does not re-implement the site scan. It imports `production_lines`
and `IO_TOKENS` from `scripts/verdict_set.py` and re-runs them over the same
members at the same pinned digests, then REFUSES if its own total disagrees
with the committed `io_site_total`. Two artifacts that count the same thing
differently is exactly the defect a partition is supposed to remove.

FAIL-CLOSED
-----------
The derivation aborts (never silently degrades) when: the source artifact is
absent / malformed / the wrong schema; a lane (b) member file is gone or has
drifted from the digest the source artifact pins; the re-derived site total
disagrees with the committed one; ANY site matches no effect rule; an effect
class has no contract; a cited check or hole no longer resolves in the tree; a
ledger row lacks a probe, a discharge, a date or an owning job; or the ledger
row count grows without an explicit dated `--rebase-up`.

Usage:
  scripts/verdict_io_contracts.py                    # mint the artifact
  scripts/verdict_io_contracts.py --check            # fail if committed differs
  scripts/verdict_io_contracts.py --describe         # the derivation contract
  scripts/verdict_io_contracts.py --sites C-READ-BYTES [--member PATH]
  scripts/verdict_io_contracts.py --self-test        # synthetic-tree arms
  scripts/verdict_io_contracts.py --rebase-up REASON # dated ledger growth
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = "data/verdict_io_contracts.json"
SOURCE_ARTIFACT = "data/verdict_set.json"
SCHEMA = "clean.verdict_io_contracts/v1"
SOURCE_SCHEMA = "clean.verdict_set/v1"
VERDICT_SET_SCRIPT = "scripts/verdict_set.py"


class VerdictIoContractsError(Exception):
    """Fail-closed derivation abort."""


# ---------------------------------------------------------------------------
# The site scan is BORROWED, never re-implemented (shared denominator)
# ---------------------------------------------------------------------------


def load_verdict_set_module(root: Path):
    """Import scripts/verdict_set.py as a module, by path."""
    script = root / VERDICT_SET_SCRIPT
    if not script.is_file():
        raise VerdictIoContractsError(
            f"{VERDICT_SET_SCRIPT} is absent: the site scan (production_lines + IO_TOKENS) "
            "lives there and this script refuses to re-implement it"
        )
    spec = importlib.util.spec_from_file_location("_verdict_set_for_io", script)
    if spec is None or spec.loader is None:
        raise VerdictIoContractsError(f"cannot load {VERDICT_SET_SCRIPT} as a module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    for required in ("production_lines", "IO_TOKENS"):
        if not hasattr(module, required):
            raise VerdictIoContractsError(
                f"{VERDICT_SET_SCRIPT} no longer exports `{required}` — the shared denominator broke"
            )
    return module


# ---------------------------------------------------------------------------
# Axis 1 — EFFECT: what the site actually does
#
# Ordered; FIRST match wins. Every rule is written against the LEXED line
# (comments and string/char literals blanked, #[cfg(test)] mod bodies removed)
# that verdict_set.py's scan produced, so no rule may depend on a literal.
# A site matching no rule is a fail-closed abort, never an "other" bucket.
# ---------------------------------------------------------------------------

EFFECT_RULES: tuple[tuple[str, str, str], ...] = (
    (
        "E-USE",
        r"^\s*(?:pub\s*(?:\([^)]*\)\s*)?)?use\s",
        "declaration-import",
    ),
    (
        "E-TYPE",
        r"#\[from\]\s*std::io::Error"
        r"|source:\s*std::io::Error"
        r"|->\s*std::io::Result"
        r"|:\s*std::io::Error\b"
        r"|:\s*std::io::ErrorKind\b"
        r"|\bmmap:\s*Mmap\b"
        r"|:\s*Mmap\s*[,)]"
        r"|std::process::(?:ExitStatus|Output)\b",
        "declaration-type",
    ),
    ("E-ERRVAL", r"std::io::ErrorKind::|std::io::Error::new", "error-value"),
    ("E-NOIO", r"io::Cursor|\bmap_anon\s*\(", "in-memory-no-io"),
    ("E-ENV", r"\benv::var(?:_os)?\s*\(", "read-env"),
    ("E-PID", r"std::process::id\s*\(", "read-ambient"),
    ("E-PIPE", r"\b(?:stdin|stdout|stderr)\s*\.", "process-stream"),
    ("E-SPAWN", r"\bCommand::new\b|\bStdio::", "spawn-process"),
    ("E-STAT", r"\bfs::metadata\s*\(", "stat-file"),
    ("E-READDIR", r"\bread_dir\s*\(", "read-dir"),
    (
        "E-READ",
        r"\bfs::read\s*\(|\bread_to_string\s*\(|\bFile::open\b|\bMmap::map\s*\(|\bBufReader::new\b",
        "read-file",
    ),
    (
        "E-WRITE",
        r"\bfs::write\s*\(|\bFile::create\b|\bBufWriter::new\b|\bcreate_dir_all\s*\("
        r"|\bremove_file\s*\(|\bremove_dir_all\s*\(|\bfs::copy\s*\(|\bOpenOptions\b",
        "write-file",
    ),
    ("E-NET", r"\bstd::net\b", "network"),
)

EFFECT_RULE_DOC: dict[str, str] = {
    "E-USE": "a `use` item — the module names a type; no syscall is issued here",
    "E-TYPE": "a TYPE position (error-enum field, `#[from]`, return type, closure/fn parameter) — "
    "`std::io::Error`, `Mmap` and `std::process::{ExitStatus,Output}` as types, not operations",
    "E-ERRVAL": "an io::Error VALUE is constructed or inspected (`ErrorKind::…`, `Error::new`) — "
    "error plumbing, no syscall",
    "E-NOIO": "an in-memory buffer wearing an IO name (`io::Cursor`, `MmapMut::map_anon`) — no file",
    "E-ENV": "an environment-variable read (`env::var`/`env::var_os`)",
    "E-PID": "ambient process state (`std::process::id()`)",
    "E-PIPE": "a child process's stdin/stdout/stderr stream is read or written",
    "E-SPAWN": "a child process is configured or spawned (`Command::new`, `Stdio::…`)",
    "E-STAT": "a file's metadata is read without reading its content (`fs::metadata`)",
    "E-READDIR": "a directory is enumerated (`read_dir`)",
    "E-READ": "a file's CONTENT is read (`fs::read`, `read_to_string`, `File::open`, `Mmap::map`, "
    "`BufReader::new`)",
    "E-WRITE": "a file or directory is created, written, appended, copied or removed",
    "E-NET": "a socket type from `std::net`",
}

# ---------------------------------------------------------------------------
# Axis 2 — DEPENDENCE: does the verdict depend on the IO's CONTENT, or only on
# its SUCCESS?  This is the axis that decides what a contract COSTS.
# ---------------------------------------------------------------------------

DEPENDENCE: dict[str, str] = {
    "declaration-import": "verdict-irrelevant",
    "declaration-type": "verdict-irrelevant",
    "error-value": "verdict-irrelevant",
    "in-memory-no-io": "verdict-irrelevant",
    "write-file": "success-only",
    "read-file": "content-bearing",
    "read-dir": "content-bearing",
    "stat-file": "content-bearing",
    "read-env": "content-bearing",
    "read-ambient": "content-bearing",
    "spawn-process": "content-bearing",
    "process-stream": "content-bearing",
    "network": "content-bearing",
}

DEPENDENCE_DOC: dict[str, str] = {
    "verdict-irrelevant": "no syscall is issued at this site, so no verdict can turn on its result. "
    "These sites are IO-bearing only in the token scan; they cost nothing to contract, and their "
    "only residual assumption is that the LEXICAL classification is right (ledger row L-LEX).",
    "success-only": "the verdict depends on whether the call SUCCEEDED, never on what came back — "
    "the bytes were computed in memory before the call. This is the cheap class: the contract is "
    "discharged by 'the error is propagated, and no partial artifact is later read as authoritative', "
    "with no pinning, no digest and no provenance chain.",
    "content-bearing": "the verdict changes with what the IO RETURNED — the bytes, the entry set, the "
    "variable's value, the child's output. This is the expensive class: the contract can only be "
    "discharged by binding the returned value to something the verdict's provenance already pins.",
}

IO_EFFECTS = frozenset(e for e, d in DEPENDENCE.items() if d != "verdict-irrelevant")

# ---------------------------------------------------------------------------
# The contracts.  One per effect class that issues a syscall, plus the residue.
#
# `checks` cite code that DOES enforce part of the contract; `holes` cite code
# that documents or embodies the gap. Both are (path, pattern, note) and both
# are RE-RESOLVED against the tree at mint time — a citation that matches
# nothing aborts the derivation.
# ---------------------------------------------------------------------------

CONTRACTS: tuple[dict, ...] = (
    {
        "id": "C-READ-BYTES",
        "title": "the bytes read are the bytes the verdict was minted over",
        "effects": ("read-file",),
        "statement": "Every byte a verdict path consumes from a file is the byte its provenance was "
        "established over: the path names the file that was digested, the file is not substituted "
        "between the pin and the read, and a short or truncated read is refused rather than decoded.",
        "checks": (
            (
                "crates/clean-mathverse/src/shard.rs",
                r"let actual_hash = blake3::hash\(content\);",
                "the EAGER shard readers (`ShardReader::from_bytes`, `ShardMmapReader::from_mmap`) "
                "recompute a whole-file blake3 and compare it to the footer, so on those two entry "
                "points corruption and truncation are caught",
            ),
        ),
        "holes": (
            (
                "crates/clean-mathverse/src/shard.rs",
                r"fn from_mmap_no_checksum",
                "`open_lazy` / `open_lazy_from_bytes` route through a reader that SKIPS the footer "
                "blake3 by design (demand paging: checking it would fault every page), so on the lazy "
                "path nothing verifies the bytes at all",
            ),
            (
                "crates/clean-mathverse/src/verify/kernel_verified_manifest.rs",
                r"let data = std::fs::read_to_string\(path\)\?;",
                "the KernelVerified manifest is read back as authoritative JSON with no digest, no "
                "signature and no comparison to the run that wrote it",
            ),
        ),
        "why_unproved": "the footer digest travels INSIDE the file it certifies, so it detects "
        "corruption, not substitution; and the twelve members outside clean-mathverse's shard path "
        "read their inputs with no integrity check of any kind.",
        "discharge": "bind every content-bearing read to a digest the verdict's provenance already "
        "pins (the shard footer for shards; an artifact-lineage digest for manifests), and require the "
        "checksummed reader on any path that will MINT a verdict.",
        "owning_job": "R2b-READ",
    },
    {
        "id": "C-READ-SET",
        "title": "the enumerated entry set is the input set the verdict quantifies over",
        "effects": ("read-dir",),
        "statement": "A directory walk returns exactly the input set the verdict quantifies over: no "
        "entry appears or disappears during the walk, no entry is silently dropped for being a symlink, "
        "non-UTF-8 or unreadable, and enumeration order does not change the verdict.",
        "checks": (),
        "holes": (
            (
                "crates/clean-mathverse/src/shard_verify/mod.rs",
                r"if let Ok\(rd\) = fs::read_dir\(dir\)",
                "an unreadable directory is indistinguishable from an EMPTY one here: the `Err` arm is "
                "dropped, so 'nothing to verify' and 'could not look' produce the same verdict",
            ),
        ),
        "why_unproved": "nothing in lane (b) pins the entry set: no manifest lists the files a walk is "
        "expected to find, so a walk that returns a subset produces a verdict over a subset and says so "
        "nowhere.",
        "discharge": "quantify every walk over a committed manifest and refuse on set difference in "
        "BOTH directions (missing and unexpected), rather than over whatever the filesystem returned.",
        "owning_job": "R2b-SET",
    },
    {
        "id": "C-STAT-FRESH",
        "title": "equal metadata implies equal content",
        "effects": ("stat-file",),
        "statement": "When a cache returns a previously parsed module because the file's mtime equals "
        "the recorded mtime, the file's CONTENT equals the content that was parsed.",
        "checks": (),
        "holes": (
            (
                "crates/clean-olean/src/import/mod.rs",
                r"entry\.mtime\.is_some\(\) && entry\.mtime == mtime",
                "the module cache's hit condition IS the assumption: mtime equality is taken as content "
                "equality, and the hit returns an `Arc<ParsedModule>` that later feeds registration",
            ),
        ),
        "why_unproved": "mtime equality does not imply content equality — a same-second rewrite, an "
        "archive restore, a `touch -r`, or a coarse-granularity filesystem all produce equal mtimes over "
        "different bytes. (One direction IS fail-closed: a failed `stat` yields `None`, and the hit "
        "condition requires `is_some()`, so a stat failure misses rather than falsely hits.)",
        "discharge": "key the cache on something that implies content equality — at minimum "
        "`(len, mtime_ns, dev, ino)` from the stat already being made, and a content digest on any path "
        "whose output is used to MINT a verdict rather than to serve a query.",
        "owning_job": "R2b-STAT",
    },
    {
        "id": "C-ENV-NEUTRAL",
        "title": "no environment variable can weaken a verdict",
        "effects": ("read-env",),
        "statement": "The ABSENCE of every environment variable is the safe default, and no value a "
        "caller can set either changes what a verdict depends on or escapes being recorded in that "
        "verdict's provenance.",
        "checks": (),
        "holes": (
            (
                "crates/clean-mathverse/src/coq/universe_releveling.rs",
                r"std::env::var_os\(\"CLEAN_COQ_VAR_RELEVEL\"\)",
                "a BEHAVIOUR-CHANGING variable on an import path: default ON, and `=0` turns the Coq "
                "`Var` universe re-leveling arm off — two runs of the same input under different "
                "environments are two different programs",
            ),
            (
                "crates/clean-mathverse/src/shard.rs",
                r"std::env::var\(MAX_DECOMPRESS_BYTES_ENV\)",
                "a BEHAVIOUR-CHANGING variable: `MATHVERSE_MAX_DECOMPRESS_BYTES` moves the "
                "decompression bound a shard read is refused at",
            ),
        ),
        "why_unproved": "nothing enumerates these reads or pins their dispositions. In particular "
        "`data/env_bypass_census.json` + `scripts/check_env_bypass_census.py` do NOT cover them despite "
        "the name: that census watches the kernel `Environment` bypass surface "
        "(`extend_*_unchecked`, `add_decl_structural`), not `std::env` reads. Reading the name as "
        "coverage is the exact mistake this row exists to prevent.",
        "discharge": "commit a table of every variable name lane (b) reads with a declared disposition "
        "(`diagnostic-only` / `behaviour-changing`), enforce it here so an unlisted name aborts the "
        "mint, and require every behaviour-changing name to appear in the provenance of any verdict "
        "minted under it.",
        "owning_job": "R2b-ENV",
    },
    {
        "id": "C-SPAWN-IDENTITY",
        "title": "the spawned process is the pinned binary",
        "effects": ("spawn-process",),
        "statement": "A spawned program is the pinned binary at the pinned version: the name resolves "
        "to one intended executable rather than the first PATH match, and the executable that actually "
        "ran is the one whose identity the verdict's provenance records.",
        "checks": (
            (
                "crates/clean-mathverse/src/env_fingerprint.rs",
                r"sha256_hex\(&bytes\)",
                "`capture_solver_binary` RECORDS a spawned solver's `--version` output and the sha256 "
                "of its executable — the identity is measured, which is half the contract",
            ),
        ),
        "holes": (
            (
                "crates/clean-mathverse/src/env_fingerprint.rs",
                r"let output = Command::new\(&spec\.path\)",
                "the version spawn and the digest read are two SEPARATE resolutions of `spec.path`, and "
                "the recorded digest is compared to no pin — a fingerprint is provenance, not a gate",
            ),
        ),
        "why_unproved": "17 of the 23 spawn sites pass a BARE NAME resolved through `PATH` "
        "(`tar` x6, `gh` x4, `git` x3, `zstd` x2, `date`, `gzip`), 3 pass a caller-supplied path or "
        "variable, and 3 only configure stdio for a spawn started on another line — see this row's "
        "`spawned_programs` / `program_resolution` tallies, which are derived, not typed. Nothing "
        "resolves a bare name to an absolute path, records which executable answered, or compares it "
        "to anything. This is also where the network enters the surface: `std::net` has ZERO direct "
        "sites in lane (b), but `gh` is a network client spawned from the release/artifact path, so "
        "'no sockets' is not 'no network'.",
        "discharge": "resolve each tool once to an absolute path, fingerprint it through the "
        "`capture_solver_binary` machinery that already exists, and compare the digest to a committed "
        "pin before the first spawn.",
        "owning_job": "R2b-SPAWN",
    },
    {
        "id": "C-SPAWN-FAITHFUL",
        "title": "a child's output is consumed faithfully, and never rounds up to a pass",
        "effects": ("process-stream",),
        "statement": "A child process's verdict-bearing output is consumed faithfully: a non-zero exit, "
        "a killed or timed-out child, a truncated stream, or a short response is an error or an explicit "
        "non-pass — never silently a pass.",
        "checks": (
            (
                "crates/clean-verify/src/external_checker.rs",
                r"if !status\.success\(\)",
                "a non-zero exit becomes `CheckerError::Exit` carrying the code and stderr, not a verdict",
            ),
            (
                "crates/clean-verify/src/external_checker.rs",
                r"return Ok\(vec!\[CheckerVerdict::Timeout; batch\.obligations\.len\(\)\]\)",
                "a child that outruns its deadline is killed and every obligation in the batch becomes "
                "`Timeout` — the timeout path cannot produce a pass",
            ),
            (
                "crates/clean-verify/src/external_checker.rs",
                r"response\.verdicts\.len\(\) != batch\.obligations\.len\(\)",
                "a short response is a protocol error, so verdicts cannot silently be re-indexed onto "
                "the wrong obligations",
            ),
        ),
        "holes": (
            (
                "crates/clean-verify/src/external_checker.rs",
                r"stdout\.read_to_string\(&mut stdout_buf\)\?;",
                "both streams are drained AFTER `child.wait()`, so a child that fills the pipe buffer "
                "blocks on write while the parent blocks on wait — a LIVENESS hazard (hang), not a "
                "soundness one, and worth separating from the rest of this row",
            ),
        ),
        "why_unproved": "the three checks cover how a FAILING child is reported; what they do not cover "
        "is the succeeding one — the checker's `Proved` verdicts are trusted by construction and are "
        "re-checked by nothing, so this contract's soundness rests entirely on whether the external "
        "program is in the TCB.",
        "discharge": "either declare the external checker TCB with a pinned digest (C-SPAWN-IDENTITY) "
        "and say so in the trust register, or require every accepted verdict to carry a certificate the "
        "Clean kernel re-checks — the S&L §0.6 'diverse re-check' posture.",
        "owning_job": "R2b-CHILD",
    },
    {
        "id": "C-AMBIENT-NONCE",
        "title": "ambient process state is a nonce, never a verdict input",
        "effects": ("read-ambient",),
        "statement": "`std::process::id()` is used only for uniqueness, so two runs over the same input "
        "that differ only in pid produce the same verdict.",
        "checks": (),
        "holes": (
            (
                "crates/clean-mathverse/src/attempt_log/mod.rs",
                r"hasher\.update\(&std::process::id\(\)\.to_be_bytes\(\)\);",
                "the pid is hashed INTO an attempt identifier, so the identifier is not reproducible "
                "across runs — benign for a nonce, load-bearing if an identifier is ever compared",
            ),
        ),
        "why_unproved": "the nonce reading is by inspection of two sites; nothing enforces that a third "
        "site cannot let the pid reach a verdict.",
        "discharge": "a determinism probe — mint the same verdict twice in one tree and diff — plus "
        "this enumeration held at exactly two sites by the gate.",
        "owning_job": "R2b-AMBIENT",
    },
    {
        "id": "C-WRITE-COMPLETE",
        "title": "a write lands completely or reports an error (the CHEAP class)",
        "effects": ("write-file",),
        "statement": "Every write either lands completely or reports an error; no partially written "
        "artifact is later read back as authoritative. The write's CONTENT needs no contract at all — "
        "the bytes were computed in memory before the call, so the verdict depends on the call's "
        "SUCCESS and on nothing that came back.",
        "checks": (
            (
                "crates/clean-mathverse/src/attempt_log/mod.rs",
                r"OpenOptions::new\(\)\.write\(true\)\.create_new\(true\)",
                "one record writer refuses to clobber an existing file (`create_new`), so a re-run "
                "cannot silently overwrite the record a previous verdict was minted against",
            ),
        ),
        "holes": (
            (
                "crates/clean-mathverse/src/verify/kernel_verified_manifest.rs",
                r"std::fs::write\(path, self\.to_json\(\)\?\)\?;",
                "`fs::write` is not atomic: a crash or a full disk mid-write leaves a truncated JSON "
                "manifest that `from_file` will later read as authoritative",
            ),
            (
                "crates/clean-mathverse/src/release.rs",
                r"let _ = fs::remove_file\(&index_path\);",
                "the error is DISCARDED, so 'or reports an error' is simply false at this site and the "
                "two others shaped like it",
            ),
        ),
        "why_unproved": "no write in lane (b) is atomic — nothing writes to a temporary and renames, "
        "though `scripts/verdict_set.py` does exactly that two directories away — and several sites "
        "drop the error entirely.",
        "discharge": "tmp-write + rename for the writes whose output is read back as authoritative, and "
        "propagate (or explicitly justify discarding) every write error. This is the cheapest class in "
        "the model and should close first.",
        "owning_job": "R2b-WRITE",
    },
)

# A contract whose site count is ZERO is a MEASURED ABSENCE, not a silence: it
# states the negative so `silence must mean no` cannot be read into the model.
# It gets no ledger row, because nothing is being assumed.
MEASURED_ABSENT: tuple[dict, ...] = (
    {
        "id": "C-NET-DIRECT",
        "title": "no verdict path opens a socket directly",
        "effects": ("network",),
        "statement": "No member of lane (b) constructs a `std::net` socket type.",
        "expected_sites": 0,
        "caveat": "This is NOT 'lane (b) does not reach the network'. `gh` — the GitHub CLI, a network "
        "client — is spawned at four sites in `artifacts.rs` and `release.rs`. Network reachability "
        "lives in C-SPAWN-IDENTITY, not here.",
    },
)

# The residue: token hits at which no syscall is issued. Not a contract — the
# only thing assumed about them is that the LEXICAL rule read them correctly,
# and that assumption is ledger row L-LEX.
RESIDUE_CLASS = {
    "id": "C-NONE",
    "title": "token hits that issue no syscall",
    "effects": ("declaration-import", "declaration-type", "error-value", "in-memory-no-io"),
    "statement": "These sites matched the IO token table but perform no IO: they import a module, name "
    "a type, construct or inspect an `io::Error` value, or wrap an in-memory buffer in an IO-shaped "
    "API. No verdict can turn on their result, so no contract is owed.",
}

# ---------------------------------------------------------------------------
# Meta ledger rows: the two assumptions the MODEL ITSELF stands on. §3.6 is
# explicit that an assumption entering without a row is a gate failure, and
# these two are assumptions of this very artifact.
# ---------------------------------------------------------------------------

META_ROWS: tuple[dict, ...] = (
    {
        "id": "L-LEX",
        "contract": "C-NONE",
        "class": "meta",
        "statement": "The effect classification is LEXICAL: a site's class is decided from the single "
        "matched line, not from the program's semantics. Every site classified declaration-import / "
        "declaration-type / error-value / in-memory-no-io is asserted to issue no syscall on that "
        "evidence alone — a macro expansion, a type alias, or a `Deref` impl could hide an operation "
        "the matched line does not show.",
        "probe": "scripts/verdict_io_contracts.py --sites C-NONE",
        "discharge": "re-derive the classification from MIR/THIR rather than from source lines — the "
        "same whole-crate dump G-SPINE-SET waits on (data/spine_set.PENDING.md).",
        "owning_job": "R2b-LEX",
    },
    {
        "id": "L-DENOM",
        "contract": "*",
        "class": "meta",
        "statement": "The site denominator is the IO_TOKENS table in scripts/verdict_set.py, so it is a "
        "LOWER bound on lane (b)'s IO surface: an IO call reached through an in-crate helper, through a "
        "dependency's API (`serde_json::from_reader`, `zstd::decode_all`, an HTTP client), or through a "
        "macro is not a site. The counts in this artifact are what that table can SEE, not what the "
        "surface does.",
        "probe": "scripts/verdict_io_contracts.py --describe   # prints the borrowed token table",
        "discharge": "derive sites from the call graph instead of from tokens; until then, every added "
        "token lands with a mutation arm proving the scan would have missed it before.",
        "owning_job": "R2b-DENOM",
    },
)

# Reporting-only extraction. These read the RAW line (literals intact) purely
# to NAME what is spawned / read, and feed no classification decision — the
# classification above is lexed, per gate-registry R9.
PROGRAM_LITERAL_RE = re.compile(r"Command::new\(\s*(?:&)?\"([^\"]+)\"")
COMMAND_NEW_RE = re.compile(r"\bCommand::new\b")
ENV_NAME_RE = re.compile(r"env::var(?:_os)?\(\s*\"([A-Za-z_][A-Za-z0-9_]*)\"")
ENV_CONST_RE = re.compile(r"env::var(?:_os)?\(\s*([A-Z][A-Z0-9_]+)\s*\)")
ERROR_DISCARDED_RE = re.compile(r"let\s+_\s*=|if\s+let\s+Ok\(")


def resolve_str_const(raw_text: str, name: str) -> str | None:
    """`const NAME: &str = "VALUE";` in the same file, so a table of variable
    names reads as the names an operator would actually export."""
    m = re.search(
        r"const\s+" + re.escape(name) + r"\s*:\s*&(?:'static\s+)?str\s*=\s*\"([^\"]+)\"", raw_text
    )
    return m.group(1) if m else None


def classify_effect(line: str) -> tuple[str, str] | None:
    for rule_id, pattern, effect in EFFECT_RULES:
        if re.search(pattern, line):
            return rule_id, effect
    return None


# ---------------------------------------------------------------------------
# Source artifact + citation resolution
# ---------------------------------------------------------------------------


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def member_id(rel: str) -> str:
    """`crates/clean-olean/src/import/mod.rs` -> `clean-olean::import::mod`.

    The module PATH, not its basename: three of lane (b)'s members are called
    `mod.rs`, and a ledger whose row ids collide is a ledger that silently
    merges two assumptions into one.
    """
    parts = rel.split("/")
    if len(parts) >= 4 and parts[0] == "crates" and parts[2] == "src":
        crate, tail = parts[1], parts[3:]
    else:
        crate, tail = (parts[0] if parts else "?"), parts[1:]
    tail = list(tail)
    if tail:
        tail[-1] = tail[-1].removesuffix(".rs")
    return "::".join([crate, *tail]) if tail else crate


def load_source_artifact(root: Path) -> tuple[dict, str]:
    path = root / SOURCE_ARTIFACT
    if not path.is_file():
        raise VerdictIoContractsError(
            f"{SOURCE_ARTIFACT} is absent — lane (b)'s member list is the input to this model; "
            "mint it with scripts/verdict_set.py"
        )
    try:
        doc = json.loads(path.read_text())
    except ValueError as exc:
        raise VerdictIoContractsError(f"{SOURCE_ARTIFACT} is not valid JSON: {exc}") from exc
    if not isinstance(doc, dict):
        raise VerdictIoContractsError(f"{SOURCE_ARTIFACT} top level is not an object")
    if doc.get("schema") != SOURCE_SCHEMA:
        raise VerdictIoContractsError(
            f"{SOURCE_ARTIFACT} schema is {doc.get('schema')!r}, want {SOURCE_SCHEMA!r}"
        )
    try:
        lane_b = doc["partitions"]["b_io_bearing"]
        lane_b["members"]
        lane_b["io_site_total"]
    except (KeyError, TypeError) as exc:
        raise VerdictIoContractsError(
            f"{SOURCE_ARTIFACT} has no usable b_io_bearing partition: missing {exc}"
        ) from exc
    return doc, sha256_file(path)


def verify_citations(root: Path, kind: str, cites: tuple) -> list[dict]:
    """Resolve every cited check/hole against the tree. Zero matches aborts."""
    out: list[dict] = []
    for rel, pattern, note in cites:
        path = root / rel
        if not path.is_file():
            raise VerdictIoContractsError(
                f"cited {kind} names {rel}, which is not in the tree — an evidence pointer that "
                "rots is worse than no pointer; re-cite or delete it"
            )
        text = path.read_text(errors="replace")
        lines = [i for i, line in enumerate(text.splitlines(), 1) if re.search(pattern, line)]
        if not lines:
            raise VerdictIoContractsError(
                f"cited {kind} pattern {pattern!r} no longer matches anything in {rel} — the code "
                "moved and this artifact would otherwise keep asserting a check that is gone"
            )
        out.append({"file": rel, "pattern": pattern, "lines": lines, "what": note})
    return out


# ---------------------------------------------------------------------------
# Site derivation
# ---------------------------------------------------------------------------


def derive_sites(root: Path, source: dict, vs) -> list[dict]:
    sites: list[dict] = []
    for member in source["partitions"]["b_io_bearing"]["members"]:
        rel = member["path"]
        path = root / rel
        if not path.is_file():
            raise VerdictIoContractsError(
                f"lane (b) member {rel} is not in the tree — the model cannot be derived over a "
                "member that no longer exists; re-mint scripts/verdict_set.py first"
            )
        digest = sha256_file(path)
        if digest != member["sha256"]:
            raise VerdictIoContractsError(
                f"lane (b) member {rel} has DRIFTED from the digest {SOURCE_ARTIFACT} pins "
                f"(pinned {member['sha256'][:12]}, tree {digest[:12]}) — the contract model must be "
                "derived over the same bytes the partition measured; re-mint scripts/verdict_set.py"
            )
        text = path.read_text(errors="replace")
        raw_lines = text.splitlines()
        for lineno, line in vs.production_lines(text, Path(rel)):
            for pattern, token in vs.IO_TOKENS:
                if not re.search(pattern, line):
                    continue
                hit = classify_effect(line)
                if hit is None:
                    raise VerdictIoContractsError(
                        f"UNCLASSIFIED IO site {rel}:{lineno} token={token} — no effect rule matches "
                        f"`{line.strip()[:100]}`. A site with no class is an unmodelled boundary; add "
                        "a rule (with a self-test arm) rather than letting it fall into an `other` bucket"
                    )
                rule_id, effect = hit
                raw = raw_lines[lineno - 1] if lineno - 1 < len(raw_lines) else ""
                site = {
                    "member": rel,
                    "line": lineno,
                    "token": token,
                    "rule": rule_id,
                    "effect": effect,
                    "dependence": DEPENDENCE[effect],
                    "code": line.strip()[:160],
                }
                if effect == "spawn-process":
                    m = PROGRAM_LITERAL_RE.search(raw)
                    if m:
                        site["program_literal"] = m.group(1)
                        site["program_resolution"] = "PATH lookup of a bare name"
                    elif COMMAND_NEW_RE.search(line):
                        site["program_literal"] = None
                        site["program_resolution"] = "caller-supplied path or variable"
                    else:
                        site["program_literal"] = None
                        site["program_resolution"] = "stdio configuration of a spawn started elsewhere"
                if effect == "read-env":
                    lit = ENV_NAME_RE.search(raw)
                    if lit:
                        site["env_name"] = lit.group(1)
                        site["env_name_via"] = "literal"
                    else:
                        const = ENV_CONST_RE.search(raw)
                        resolved = resolve_str_const(text, const.group(1)) if const else None
                        site["env_name"] = resolved or (const.group(1) if const else None)
                        site["env_name_via"] = (
                            "const in the same file" if resolved else ("const, unresolved" if const else None)
                        )
                if effect in ("write-file", "read-dir", "read-file"):
                    site["error_discarded"] = bool(ERROR_DISCARDED_RE.search(line))
                sites.append(site)
    sites.sort(key=lambda s: (s["member"], s["line"], s["token"]))
    return sites


# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------


def _tally(sites: list[dict], key: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for s in sites:
        out[s[key]] = out.get(s[key], 0) + 1
    return dict(sorted(out.items(), key=lambda kv: (-kv[1], kv[0])))


def build(
    root: Path,
    previous: dict | None,
    rebase_reason: str | None,
    now_utc: str | None,
    contracts: tuple[dict, ...] = CONTRACTS,
) -> dict:
    vs = load_verdict_set_module(root)
    source, source_digest = load_source_artifact(root)
    lane_b = source["partitions"]["b_io_bearing"]
    sites = derive_sites(root, source, vs)

    committed_total = int(lane_b["io_site_total"])
    if len(sites) != committed_total:
        raise VerdictIoContractsError(
            f"DENOMINATOR DRIFT: this model re-derived {len(sites)} IO sites, {SOURCE_ARTIFACT} "
            f"commits {committed_total}. Two artifacts counting the same thing differently is the "
            "defect a partition exists to remove; re-mint scripts/verdict_set.py"
        )

    effect_of_contract: dict[str, str] = {}
    for c in contracts:
        for e in c["effects"]:
            if e in effect_of_contract:
                raise VerdictIoContractsError(
                    f"effect {e} is claimed by two contracts ({effect_of_contract[e]}, {c['id']})"
                )
            effect_of_contract[e] = c["id"]
    for c in MEASURED_ABSENT:
        for e in c["effects"]:
            effect_of_contract.setdefault(e, c["id"])
    for e in RESIDUE_CLASS["effects"]:
        effect_of_contract.setdefault(e, RESIDUE_CLASS["id"])

    for effect in sorted({s["effect"] for s in sites}):
        if effect not in effect_of_contract:
            raise VerdictIoContractsError(
                f"effect class {effect!r} has {sum(1 for s in sites if s['effect'] == effect)} "
                "measured site(s) and NO contract — an unmodelled boundary cannot be committed"
            )

    for c in MEASURED_ABSENT:
        n = sum(1 for s in sites if s["effect"] in c["effects"])
        if n != c["expected_sites"]:
            raise VerdictIoContractsError(
                f"{c['id']} is recorded as a measured ABSENCE ({c['expected_sites']} sites) but "
                f"{n} site(s) were derived — the negative statement is now false and must be "
                "converted into a real contract with a ledger row"
            )

    today = (now_utc or _dt.datetime.now(_dt.UTC).strftime("%Y-%m-%d"))[:10]

    contract_rows: list[dict] = []
    ledger_rows: list[dict] = []
    for c in contracts:
        c_sites = [s for s in sites if s["effect"] in c["effects"]]
        members = sorted({s["member"] for s in c_sites})
        checks = verify_citations(root, "check", c["checks"])
        holes = verify_citations(root, "hole", c["holes"])
        strength = "partial" if checks else "none"
        dependences = sorted({s["dependence"] for s in c_sites})
        row = {
            "id": c["id"],
            "title": c["title"],
            "effects": list(c["effects"]),
            "dependence": dependences[0] if len(dependences) == 1 else dependences,
            "site_count": len(c_sites),
            "member_count": len(members),
            "members": members,
            "statement": c["statement"],
            "check_strength": strength,
            "checked_by": checks,
            "holes": holes,
            "why_unproved": c["why_unproved"],
            "discharge": c["discharge"],
            "owning_job": c["owning_job"],
            "sites_by_member": {m: sum(1 for s in c_sites if s["member"] == m) for m in members},
        }
        if any(s["effect"] == "spawn-process" for s in c_sites):
            progs: dict[str, int] = {}
            resolutions: dict[str, int] = {}
            for s in c_sites:
                key = s.get("program_literal") or f"<{s.get('program_resolution', 'unknown')}>"
                progs[key] = progs.get(key, 0) + 1
                res = s.get("program_resolution", "unknown")
                resolutions[res] = resolutions.get(res, 0) + 1
            row["spawned_programs"] = dict(sorted(progs.items(), key=lambda kv: (-kv[1], kv[0])))
            row["program_resolution"] = dict(
                sorted(resolutions.items(), key=lambda kv: (-kv[1], kv[0]))
            )
        if any(s["effect"] == "read-env" for s in c_sites):
            names: dict[str, int] = {}
            for s in c_sites:
                key = s.get("env_name") or "<unresolved>"
                names[key] = names.get(key, 0) + 1
            row["variables"] = dict(sorted(names.items(), key=lambda kv: (-kv[1], kv[0])))
        discarded = sum(1 for s in c_sites if s.get("error_discarded"))
        if discarded:
            row["sites_discarding_the_error"] = discarded
        contract_rows.append(row)

        if strength == "full" or not c_sites:
            continue
        checked_files = {ch["file"] for ch in checks}
        for member in members:
            msites = [s for s in c_sites if s["member"] == member]
            if not checks:
                checked = "NOTHING in the tree checks this contract"
            elif member in checked_files:
                checked = (
                    f"PARTIAL — {len(checks)} cited check(s) for this contract, at least one inside "
                    "this member; the member's other sites are not covered by it"
                )
            else:
                checked = (
                    f"PARTIAL — {len(checks)} cited check(s) for this contract, NONE of them in this "
                    "member"
                )
            ledger_rows.append(
                {
                    "id": f"L-{c['id'].removeprefix('C-')}/{member_id(member)}",
                    "contract": c["id"],
                    "class": DEPENDENCE[c["effects"][0]],
                    "member": member,
                    "site_count": len(msites),
                    "lines": [s["line"] for s in msites],
                    "statement": f"{member} assumes, without proof, that: {c['statement']}",
                    "checked": checked,
                    "probe": f"scripts/verdict_io_contracts.py --sites {c['id']} --member {member}",
                    "discharge": c["discharge"],
                    "date": today,
                    "owning_job": c["owning_job"],
                }
            )

    for meta in META_ROWS:
        row = dict(meta)
        row["date"] = today
        if meta["id"] == "L-LEX":
            row["site_count"] = sum(1 for s in sites if s["effect"] in RESIDUE_CLASS["effects"])
        else:
            row["site_count"] = len(sites)
        ledger_rows.append(row)

    for row in ledger_rows:
        for field in ("statement", "probe", "discharge", "date", "owning_job"):
            if not row.get(field):
                raise VerdictIoContractsError(
                    f"ledger row {row.get('id')!r} has no {field} — §3.6 requires statement, probe, "
                    "date and owning job on every entry; a row without them is a note, not a ledger row"
                )
    seen: set[str] = set()
    for row in ledger_rows:
        if row["id"] in seen:
            raise VerdictIoContractsError(
                f"DUPLICATE ledger row id {row['id']!r} — two assumptions sharing an id is one "
                "assumption disappearing; the id derivation must distinguish them"
            )
        seen.add(row["id"])

    measured_rows = len(ledger_rows)
    prev_ratchet = (previous or {}).get("ledger", {}).get("row_ratchet")
    rebases = list(prev_ratchet.get("rebases", [])) if prev_ratchet else []
    if prev_ratchet:
        baseline = int(prev_ratchet["baseline_rows"])
        minted_utc = prev_ratchet["minted_utc"]
        if measured_rows > baseline:
            if not rebase_reason:
                raise VerdictIoContractsError(
                    f"ledger row ratchet EXCEEDED: measured {measured_rows} > baseline {baseline} "
                    f"(+{measured_rows - baseline}). The assumption ledger only shrinks; growing it "
                    'needs an explicit dated rebase: re-run with --rebase-up "<why>".'
                )
            rebases.append(
                {"date": today, "from": baseline, "to": measured_rows, "reason": rebase_reason}
            )
            baseline = measured_rows
        else:
            baseline = measured_rows
    else:
        baseline = measured_rows
        minted_utc = now_utc or _dt.datetime.now(_dt.UTC).strftime("%Y-%m-%dT%H:%M:%SZ")
        if rebase_reason:
            raise VerdictIoContractsError(
                "--rebase-up was passed but no committed ledger ratchet exists yet — mint first"
            )

    by_effect = _tally(sites, "effect")
    by_dependence = _tally(sites, "dependence")
    by_member: dict[str, dict] = {}
    for member in sorted({s["member"] for s in sites}):
        msites = [s for s in sites if s["member"] == member]
        io = [s for s in msites if s["effect"] in IO_EFFECTS]
        by_member[member] = {
            "sites": len(msites),
            "issuing_io": len(io),
            "content_bearing": sum(1 for s in msites if s["dependence"] == "content-bearing"),
            "success_only": sum(1 for s in msites if s["dependence"] == "success-only"),
            "verdict_irrelevant": len(msites) - len(io),
            "declaration_only": not io,
        }
    declaration_only = sorted(m for m, v in by_member.items() if v["declaration_only"])

    return {
        "schema": SCHEMA,
        "what_this_is": "Ring R2 lane (b)'s IO-boundary contract model: every measured IO site in "
        "data/verdict_set.json's b_io_bearing partition, classified by EFFECT (what it does) and by "
        "DEPENDENCE (whether the verdict turns on the IO's content or only on its success), each "
        "effect class carrying the contract the verdict path assumes, what checks it today, and — "
        "where nothing does — a §3.6 assumption-ledger row with a probe. The ledger only shrinks. "
        "Nothing here is earned: this artifact models the obligation, it does not discharge it.",
        "derivation": {
            "script": "scripts/verdict_io_contracts.py",
            "source_artifact": SOURCE_ARTIFACT,
            "source_artifact_sha256": source_digest,
            "shared_denominator": "the site scan is IMPORTED from scripts/verdict_set.py "
            "(production_lines + IO_TOKENS) and re-run over the same members at the same pinned "
            "digests; a total that disagrees with the committed io_site_total aborts the mint",
            "axis_1_effect": {
                "what": "what the site actually does, decided by ordered lexical rules over the LEXED "
                "line (comments and literals blanked, #[cfg(test)] mod bodies removed); first match "
                "wins; a site matching no rule aborts the mint",
                "rules": [
                    {"id": rid, "effect": eff, "regex": pat, "means": EFFECT_RULE_DOC[rid]}
                    for rid, pat, eff in EFFECT_RULES
                ],
            },
            "axis_2_dependence": {
                "what": "whether the verdict's correctness depends on the IO's CONTENT or only on its "
                "SUCCESS — the axis that decides what a contract costs",
                "classes": DEPENDENCE_DOC,
                "map": DEPENDENCE,
            },
            "reporting_only_extraction": "spawned program names and environment-variable names are "
            "read from the RAW line (literals intact) to NAME what is spawned or read. They feed no "
            "classification decision — every classification rule above runs on the lexed line, per "
            "gate-registry R9.",
            "fail_closed": [
                "source artifact absent / malformed / wrong schema",
                "a lane (b) member file is absent, or its sha256 has drifted from the pinned one",
                "the re-derived site total disagrees with the committed io_site_total",
                "any site matches no effect rule",
                "an effect class with measured sites has no contract",
                "a measured-absent contract acquires sites",
                "a cited check or hole no longer resolves in the tree",
                "a ledger row lacks statement, probe, discharge, date or owning job",
                "the ledger row count grows without --rebase-up",
            ],
            "regenerate": "scripts/verdict_io_contracts.py     (--check to verify the committed file)",
        },
        "classification": {
            "site_total": len(sites),
            "sites_issuing_io": sum(1 for s in sites if s["effect"] in IO_EFFECTS),
            "sites_issuing_no_io": sum(1 for s in sites if s["effect"] not in IO_EFFECTS),
            "by_effect": by_effect,
            "by_dependence": by_dependence,
            "effect_by_dependence": {
                dep: dict(
                    sorted(
                        (
                            (e, sum(1 for s in sites if s["effect"] == e and s["dependence"] == dep))
                            for e in by_effect
                            if DEPENDENCE[e] == dep
                        ),
                        key=lambda kv: (-kv[1], kv[0]),
                    )
                )
                for dep in ("content-bearing", "success-only", "verdict-irrelevant")
            },
            "unclassified": 0,
            "by_member": by_member,
            "declaration_only_members": {
                "what": "members whose every IO token hit is a declaration / error value / in-memory "
                "buffer: they are IO-BEARING in the token scan and issue no IO at all. This is the "
                "measured half of lane (b)'s 'decode-pure separated from read-IO' obligation that "
                "needs no refactor — the split is already there, it had just never been measured.",
                "count": len(declaration_only),
                "members": declaration_only,
            },
        },
        "contracts": contract_rows,
        "measured_absent": [
            dict(c, measured_sites=sum(1 for s in sites if s["effect"] in c["effects"]))
            for c in MEASURED_ABSENT
        ],
        "residue_class": dict(
            RESIDUE_CLASS,
            effects=list(RESIDUE_CLASS["effects"]),
            site_count=sum(1 for s in sites if s["effect"] in RESIDUE_CLASS["effects"]),
        ),
        "ledger": {
            "what": "the §3.6 assumption ledger for lane (b): one row per (contract x member) that "
            "nothing fully checks, plus the rows this MODEL itself stands on. Each row carries a "
            "statement, a probe command, a discharge condition, a date and an owning job.",
            "pattern": "designs/2026-08-22-spine-and-lattice-program.md §3.6",
            "destination": "data/spine_assumption_ledger.json, when that file exists; until then these "
            "rows live here and scripts/verdict_gate.sh reads them from here",
            "direction": "down",
            "row_count": measured_rows,
            "rows_by_class": {
                cls: sum(1 for r in ledger_rows if r["class"] == cls)
                for cls in sorted({r["class"] for r in ledger_rows})
            },
            "rows_by_contract": {
                cid: sum(1 for r in ledger_rows if r["contract"] == cid)
                for cid in sorted({r["contract"] for r in ledger_rows})
            },
            "row_ratchet": {
                "what": "assumption-ledger rows; may fall freely, may rise only through "
                "scripts/verdict_io_contracts.py --rebase-up '<reason>' (recorded below)",
                "direction": "down",
                "baseline_rows": baseline,
                "measured_rows": measured_rows,
                "minted_utc": minted_utc,
                "rebases": rebases,
            },
            "rows": ledger_rows,
        },
        "recommendations": list(RECOMMENDATIONS),
        "sites": sites,
    }


# ---------------------------------------------------------------------------
# Recommendations — modeling output, NOT changes. Every one names a cost.
# This lane does not own crates/, so nothing below is implemented here.
# ---------------------------------------------------------------------------

RECOMMENDATIONS: tuple[dict, ...] = (
    {
        "id": "REC-SOLVER-PIN",
        "contract": "C-SPAWN-IDENTITY",
        "cheap_because": "the digest is ALREADY COMPUTED on the same code path and thrown at a report",
        "what": "`capture_solver_binary` (crates/clean-mathverse/src/env_fingerprint.rs) already runs "
        "`spec.path --version` and computes `sha256_hex` over the executable's bytes. Nothing compares "
        "that digest to a pin. Add a committed pin table and one equality check before the first "
        "verdict-bearing spawn.",
        "cost": "one committed table + one string comparison per solver per run; ZERO new IO (the read "
        "and the hash already happen). Add an absolute-path resolution to close the TOCTOU between the "
        "version spawn and the digest read.",
        "owner": "crates/clean-mathverse — NOT this lane",
    },
    {
        "id": "REC-SHARD-FOOTER-ON-MINT",
        "contract": "C-READ-BYTES",
        "cheap_because": "the digest exists in the file and the checked reader is already written",
        "what": "`ShardMmapReader::from_mmap` verifies the whole-file blake3 footer; `open_lazy` routes "
        "around it through `from_mmap_no_checksum` for demand paging. Require the checksummed reader "
        "whenever the run will MINT a KernelVerified verdict, and keep the lazy reader for serving.",
        "cost": "one full-file blake3 per shard per MINT run — and a mint run materializes every "
        "constant anyway, so the pages it would fault are pages it faults regardless. No new algorithm, "
        "no new dependency; a mode flag on the open path.",
        "owner": "crates/clean-mathverse — NOT this lane",
    },
    {
        "id": "REC-ENV-TABLE",
        "contract": "C-ENV-NEUTRAL",
        "cheap_because": "the enumeration is already derived here; only the table is missing",
        "what": "Commit the six variable names lane (b) reads with a declared disposition "
        "(diagnostic-only / behaviour-changing) and enforce it in THIS script, so an unlisted name "
        "aborts the mint and a diagnostic-only variable that grows teeth cannot do so silently.",
        "cost": "~40 lines here plus a 6-row table; ~0.3 s per gate run; NO crate change — this one is "
        "inside this lane's ownership and is the cheapest real close in the model.",
        "owner": "this lane (scripts/verdict_io_contracts.py)",
    },
    {
        "id": "REC-TOOL-FINGERPRINT",
        "contract": "C-SPAWN-IDENTITY",
        "cheap_because": "reuses capture_solver_binary, which already exists and is already called",
        "what": "Resolve the six bare-name tools (`gh`, `tar`, `zstd`, `gzip`, `git`, `date`) once to "
        "absolute paths and fingerprint them through the existing solver-binary machinery, so the "
        "provenance of a release artifact names the executables that built it.",
        "cost": "one PATH resolution + one read + one sha256 per tool per run (six tools). Note this is "
        "also where the network enters: `gh` is a network client and `std::net` shows zero sites.",
        "owner": "crates/clean-mathverse — NOT this lane",
    },
    {
        "id": "REC-TMP-RENAME",
        "contract": "C-WRITE-COMPLETE",
        "cheap_because": "the pattern is already written two directories away, in verdict_set.py",
        "what": "The two JSON artifacts that are written and later read back as authoritative — "
        "`kernel_verified_manifest.rs` (`fs::write` then `from_file`) and `release.rs` (`fs::write` "
        "then `read_to_string`) — should write to a temporary and rename, exactly as "
        "`scripts/verdict_set.py` does (`tmp.write_text(...); tmp.replace(out)`).",
        "cost": "two extra lines per site and one rename syscall; removes the torn-artifact hole for "
        "precisely the writes whose output is read back.",
        "owner": "crates/clean-mathverse — NOT this lane",
    },
    {
        "id": "REC-CACHE-KEY",
        "contract": "C-STAT-FRESH",
        "cheap_because": "PARTLY — the cheap variant is free, the sound variant is not",
        "what": "clean-olean's module cache keys on mtime alone. The FREE improvement is to key on "
        "`(len, mtime_ns, dev, ino)` from the `fs::metadata` call already being made, which closes the "
        "same-second rewrite and the archive-restore cases. The SOUND fix — a content digest — is NOT "
        "cheap and should be stated as such: it means reading the file the cache exists to avoid "
        "reading, so it belongs on mint paths only, never on the serve path.",
        "cost": "cheap variant: zero new syscalls, a wider key struct. Sound variant: one full read + "
        "hash per cache probe — quote it honestly rather than calling the whole row cheap.",
        "owner": "crates/clean-olean — NOT this lane",
    },
)


def render(doc: dict) -> str:
    return json.dumps(doc, indent=1) + "\n"


# ---------------------------------------------------------------------------
# self-test: a synthetic tree + mutation arms
# ---------------------------------------------------------------------------


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


SYNTH_MEMBER = """\
use std::fs;
use std::process::Command;

#[derive(Debug)]
pub enum E {
    Io(#[from] std::io::Error),
}

pub fn go(p: &Path) -> Result<Vec<u8>, E> {
    let data = fs::read(p)?;
    fs::write(p, &data)?;
    for entry in fs::read_dir(p)? {
        let _ = entry;
    }
    let _ = Command::new("tar").arg("-xf").status();
    if std::env::var("SYNTH_FLAG").is_ok() {
        return Err(E::Io(std::io::Error::new(std::io::ErrorKind::Other, "x")));
    }
    Ok(data)
}
"""


def _synthetic_tree(base: Path, vs_script: Path) -> Path:
    root = base / "tree"
    _write(root / "scripts" / "verdict_set.py", vs_script.read_text())
    member = "crates/synth/src/lib.rs"
    _write(root / member, SYNTH_MEMBER)
    digest = sha256_file(root / member)
    src = {
        "schema": SOURCE_SCHEMA,
        "partitions": {
            "b_io_bearing": {
                "member_count": 1,
                "io_site_total": 0,  # patched below
                "members": [
                    {
                        "path": member,
                        "crate": "synth",
                        "module": "lib",
                        "sublane": "synthetic",
                        "sha256": digest,
                        "io_token_count": 0,
                    }
                ],
            }
        },
    }
    _write(root / SOURCE_ARTIFACT, json.dumps(src, indent=1))
    return root


def _count_synth_sites(root: Path) -> int:
    vs = load_verdict_set_module(root)
    doc = json.loads((root / SOURCE_ARTIFACT).read_text())
    n = 0
    for member in doc["partitions"]["b_io_bearing"]["members"]:
        text = (root / member["path"]).read_text()
        for lineno, line in vs.production_lines(text, Path(member["path"])):
            for pattern, _token in vs.IO_TOKENS:
                if re.search(pattern, line):
                    n += 1
    return n


SYNTH_CONTRACTS: tuple[dict, ...] = tuple(
    dict(
        c,
        checks=(),
        holes=(),
    )
    for c in CONTRACTS
)


def _ok(arm: str) -> None:
    print(f"  PASS  {arm}")


def _expect_raises(arm: str, fragment: str, fn, failures: list[str]) -> None:
    try:
        fn()
    except VerdictIoContractsError as exc:
        if fragment.lower() in str(exc).lower():
            _ok(arm)
        else:
            failures.append(f"{arm}: raised, but not about {fragment!r}: {exc}")
        return
    failures.append(f"{arm}: DID NOT RAISE (a mutation the derivation should refuse went through)")


def self_test() -> int:
    import tempfile

    failures: list[str] = []
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        root = _synthetic_tree(base, REPO_ROOT / VERDICT_SET_SCRIPT)
        src_path = root / SOURCE_ARTIFACT

        def set_total(n: int) -> None:
            doc = json.loads(src_path.read_text())
            doc["partitions"]["b_io_bearing"]["io_site_total"] = n
            src_path.write_text(json.dumps(doc, indent=1))

        real_total = _count_synth_sites(root)
        set_total(real_total)
        # Captured ONCE, before any arm mutates it: every restore below writes
        # these exact bytes back, so an arm cannot poison the next arm's input.
        pristine_src = src_path.read_text()

        def restore_src() -> None:
            src_path.write_text(pristine_src)

        def derive(previous=None, rebase=None, contracts=SYNTH_CONTRACTS):
            return build(root, previous, rebase, now_utc="2026-08-26T00:00:00Z", contracts=contracts)

        # --- the happy path first: the pipeline is not hardwired to abort -----
        doc = derive()
        cls = doc["classification"]
        if cls["site_total"] == real_total and cls["unclassified"] == 0:
            _ok(f"synthetic tree classifies all {real_total} sites, 0 unclassified")
        else:
            failures.append(f"synthetic classification wrong: {cls['site_total']} vs {real_total}")
        if cls["by_dependence"].get("content-bearing", 0) and cls["by_dependence"].get("success-only", 0):
            _ok("both dependence classes are populated (content-bearing AND success-only)")
        else:
            failures.append(f"dependence tally degenerate: {cls['by_dependence']}")
        if doc["ledger"]["row_count"] > 0 and all(
            r.get("probe") and r.get("date") and r.get("owning_job") for r in doc["ledger"]["rows"]
        ):
            _ok("every ledger row carries a probe, a date and an owning job (§3.6 shape)")
        else:
            failures.append("ledger rows missing §3.6 fields")
        if render(doc) == render(derive()):
            _ok("derivation is deterministic (re-running renders byte-identically)")
        else:
            failures.append("derivation is not deterministic")
        ids = [r["id"] for r in doc["ledger"]["rows"]]
        if len(ids) == len(set(ids)):
            _ok("ledger row ids are unique")
        else:
            failures.append(f"duplicate ledger row ids: {sorted({i for i in ids if ids.count(i) > 1})}")
        # REGRESSION (found 2026-08-26 on the real tree): three lane (b) members
        # are named `mod.rs`, and a basename-derived row id collided two of them
        # into one — an assumption silently disappearing from the ledger.
        if member_id("crates/x/src/a/mod.rs") != member_id("crates/x/src/b/mod.rs"):
            _ok("row ids distinguish two `mod.rs` members in different modules")
        else:
            failures.append("member_id collides on `mod.rs` basenames")

        # --- mutation arms ----------------------------------------------------
        _expect_raises(
            "refusal: an IO site that no effect rule matches",
            "unclassified",
            lambda: _unclassifiable(root, derive),
            failures,
        )

        _expect_raises(
            "refusal: the site total disagrees with the committed denominator",
            "denominator drift",
            lambda: (set_total(real_total + 1), derive())[1],
            failures,
        )
        restore_src()

        member_path = root / "crates/synth/src/lib.rs"
        original = member_path.read_text()
        member_path.write_text(original + "\n// drifted\n")
        _expect_raises(
            "refusal: a lane (b) member drifted from its pinned digest",
            "drifted",
            derive,
            failures,
        )
        member_path.write_text(original)

        member_path.unlink()
        _expect_raises(
            "refusal: a lane (b) member vanished from the tree",
            "not in the tree",
            derive,
            failures,
        )
        member_path.write_text(original)

        doc_bad = json.loads(pristine_src)
        doc_bad["schema"] = "other/v1"
        src_path.write_text(json.dumps(doc_bad, indent=1))
        _expect_raises("refusal: the source artifact has the wrong schema", "schema", derive, failures)
        restore_src()

        src_path.write_text("not json at all")
        _expect_raises("refusal: the source artifact is not JSON", "not valid json", derive, failures)
        restore_src()

        src_path.unlink()
        _expect_raises("refusal: the source artifact is absent", "absent", derive, failures)
        restore_src()

        pruned = tuple(c for c in SYNTH_CONTRACTS if c["id"] != "C-READ-BYTES")
        _expect_raises(
            "refusal: an effect class with measured sites has no contract",
            "no contract",
            lambda: derive(contracts=pruned),
            failures,
        )

        no_probe = tuple(
            dict(c, discharge="") if c["id"] == "C-READ-BYTES" else c for c in SYNTH_CONTRACTS
        )
        _expect_raises(
            "refusal: a ledger row without a discharge condition",
            "§3.6",
            lambda: derive(contracts=no_probe),
            failures,
        )

        broken_cite = tuple(
            dict(c, checks=(("crates/synth/src/lib.rs", r"THIS_PATTERN_MATCHES_NOTHING", "n/a"),))
            if c["id"] == "C-READ-BYTES"
            else c
            for c in SYNTH_CONTRACTS
        )
        _expect_raises(
            "refusal: a cited check no longer resolves in the tree",
            "no longer matches",
            lambda: derive(contracts=broken_cite),
            failures,
        )

        missing_cite = tuple(
            dict(c, checks=(("crates/synth/src/gone.rs", r"x", "n/a"),))
            if c["id"] == "C-READ-BYTES"
            else c
            for c in SYNTH_CONTRACTS
        )
        _expect_raises(
            "refusal: a cited check names a file that is not in the tree",
            "not in the tree",
            lambda: derive(contracts=missing_cite),
            failures,
        )

        dup = SYNTH_CONTRACTS + (dict(SYNTH_CONTRACTS[0], id="C-DUPE"),)
        _expect_raises(
            "refusal: two contracts claim the same effect class",
            "claimed by two contracts",
            lambda: derive(contracts=dup),
            failures,
        )

        # a measured-absent contract that acquires a site
        net_member = root / "crates/synth/src/net.rs"
        _write(net_member, "pub fn f() { let _x: Option<std::net::TcpStream> = None; }\n")
        srcdoc = json.loads(pristine_src)
        srcdoc["partitions"]["b_io_bearing"]["members"].append(
            {
                "path": "crates/synth/src/net.rs",
                "crate": "synth",
                "module": "net",
                "sublane": "synthetic",
                "sha256": sha256_file(net_member),
                "io_token_count": 1,
            }
        )
        srcdoc["partitions"]["b_io_bearing"]["io_site_total"] = real_total + 1
        src_path.write_text(json.dumps(srcdoc, indent=1))
        _expect_raises(
            "refusal: a MEASURED-ABSENT contract acquires a site (silence stops meaning no)",
            "measured absence",
            derive,
            failures,
        )
        net_member.unlink()
        restore_src()

        # --- the ratchet ------------------------------------------------------
        # The ledger is per-(contract x member), so a SECOND member grows it.
        prev = derive()
        _write(root / "crates/synth/src/second.rs", SYNTH_MEMBER)
        srcdoc = json.loads(pristine_src)
        srcdoc["partitions"]["b_io_bearing"]["members"].append(
            {
                "path": "crates/synth/src/second.rs",
                "crate": "synth",
                "module": "second",
                "sublane": "synthetic",
                "sha256": sha256_file(root / "crates/synth/src/second.rs"),
                "io_token_count": real_total,
            }
        )
        srcdoc["partitions"]["b_io_bearing"]["io_site_total"] = real_total * 2
        widened_src = json.dumps(srcdoc, indent=1)
        src_path.write_text(widened_src)
        _expect_raises(
            "refusal: the ledger grows without --rebase-up",
            "ratchet exceeded",
            lambda: derive(previous=prev),
            failures,
        )
        grown = derive(previous=prev, rebase="measured widening, self-test")
        rat = grown["ledger"]["row_ratchet"]
        if rat["rebases"] and rat["rebases"][-1]["reason"] == "measured widening, self-test":
            _ok("--rebase-up records a dated row and moves the baseline")
        else:
            failures.append(f"rebase row missing: {rat}")
        if grown["ledger"]["row_count"] > prev["ledger"]["row_count"]:
            _ok("the ledger is per-(contract x member): a new member adds rows")
        else:
            failures.append("ledger did not grow with a new member")

        # now take the second member away again: the baseline must FOLLOW it down
        restore_src()
        shrunk_doc = derive(previous=grown)
        srat = shrunk_doc["ledger"]["row_ratchet"]
        if (
            srat["baseline_rows"] == shrunk_doc["ledger"]["row_count"]
            and srat["baseline_rows"] < rat["baseline_rows"]
        ):
            _ok("the ratchet tightens silently when the ledger shrinks")
        else:
            failures.append(f"ratchet did not tighten: {srat} after {rat}")

    if failures:
        print("\nVERDICT_IO_CONTRACTS self-test: RED", file=sys.stderr)
        for f in failures:
            print(f"  FAIL  {f}", file=sys.stderr)
        return 1
    print("VERDICT_IO_CONTRACTS self-test: all arms green")
    return 0


def _unclassifiable(root: Path, derive) -> None:
    """Plant an IO token on a line no effect rule can classify."""
    member = root / "crates/synth/src/lib.rs"
    original = member.read_text()
    src_path = root / SOURCE_ARTIFACT
    doc = json.loads(src_path.read_text())
    try:
        member.write_text(original + "\npub fn hidden() { let _alias = std::fs; }\n")
        doc["partitions"]["b_io_bearing"]["members"][0]["sha256"] = sha256_file(member)
        doc["partitions"]["b_io_bearing"]["io_site_total"] += 1
        src_path.write_text(json.dumps(doc, indent=1))
        derive()
    finally:
        member.write_text(original)
        doc = json.loads(src_path.read_text())
        doc["partitions"]["b_io_bearing"]["members"][0]["sha256"] = sha256_file(member)
        doc["partitions"]["b_io_bearing"]["io_site_total"] -= 1
        src_path.write_text(json.dumps(doc, indent=1))


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def run_check(root: Path, out_path: Path) -> int:
    if not out_path.is_file():
        print(f"VERDICT_IO_CONTRACTS=fail committed artifact {out_path} is absent", file=sys.stderr)
        return 1
    try:
        previous = json.loads(out_path.read_text())
    except ValueError as exc:
        print(f"VERDICT_IO_CONTRACTS=fail committed artifact is not valid JSON: {exc}", file=sys.stderr)
        return 1
    try:
        fresh = build(root, previous, None, now_utc=None)
    except VerdictIoContractsError as exc:
        print(f"VERDICT_IO_CONTRACTS=fail {exc}", file=sys.stderr)
        return 1
    if render(fresh) == out_path.read_text():
        print(f"VERDICT_IO_CONTRACTS=ok {out_path} matches a fresh derivation")
        return 0
    print(
        f"VERDICT_IO_CONTRACTS=fail {out_path} DIFFERS from a fresh derivation — the IO surface "
        "moved (or the artifact was edited by hand). Re-mint: scripts/verdict_io_contracts.py",
        file=sys.stderr,
    )
    old_rows = {r["id"] for r in previous.get("ledger", {}).get("rows", [])}
    new_rows = {r["id"] for r in fresh["ledger"]["rows"]}
    for r in sorted(new_rows - old_rows):
        print(f"    + ledger row {r}", file=sys.stderr)
    for r in sorted(old_rows - new_rows):
        print(f"    - ledger row {r}", file=sys.stderr)
    return 1


def print_sites(root: Path, contract_id: str, member: str | None) -> int:
    try:
        doc = build(root, None, None, now_utc=None)
    except VerdictIoContractsError as exc:
        print(f"VERDICT_IO_CONTRACTS=fail {exc}", file=sys.stderr)
        return 1
    known = {c["id"] for c in doc["contracts"]}
    known |= {c["id"] for c in doc["measured_absent"]} | {doc["residue_class"]["id"]}
    if contract_id not in known:
        print(f"unknown contract {contract_id!r}; known: {', '.join(sorted(known))}", file=sys.stderr)
        return 2
    effects = None
    for group in (doc["contracts"], doc["measured_absent"], [doc["residue_class"]]):
        for c in group:
            if c["id"] == contract_id:
                effects = set(c["effects"])
    sites = [s for s in doc["sites"] if s["effect"] in (effects or set())]
    if member:
        sites = [s for s in sites if s["member"] == member]
    print(f"{contract_id}: {len(sites)} site(s)" + (f" in {member}" if member else ""))
    for s in sites:
        extra = ""
        if s.get("program_literal"):
            extra = f"  program={s['program_literal']} ({s['program_resolution']})"
        elif s.get("env_name"):
            extra = f"  var={s['env_name']}"
        print(f"  {s['member']}:{s['line']:<6} {s['effect']:<20} {s['rule']:<9} {s['code'][:80]}{extra}")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="verdict_io_contracts.py",
        description="Derive data/verdict_io_contracts.json — Ring R2 lane (b)'s IO contract model.",
    )
    ap.add_argument("--out", default=str(REPO_ROOT / DEFAULT_OUT), help=f"output (default {DEFAULT_OUT})")
    ap.add_argument("--root", default=str(REPO_ROOT), help="repo root to derive from")
    ap.add_argument("--check", action="store_true", help="derive and fail if the committed file differs")
    ap.add_argument("--describe", action="store_true", help="print the derivation contract and exit")
    ap.add_argument("--self-test", action="store_true", help="synthetic-tree mutation arms")
    ap.add_argument("--sites", metavar="CONTRACT_ID", help="print the sites a contract covers (the probe)")
    ap.add_argument("--member", metavar="PATH", help="with --sites: restrict to one member")
    ap.add_argument("--rebase-up", metavar="REASON", help="allow the ledger row ratchet to rise, dated")
    args = ap.parse_args(argv)

    root = Path(args.root).resolve()

    if args.describe:
        print(__doc__)
        print("EFFECT RULES (ordered, first match wins)")
        for rid, pat, eff in EFFECT_RULES:
            print(f"  {rid:10s} -> {eff:20s} {EFFECT_RULE_DOC[rid]}")
            print(f"  {'':10s}    regex: {pat}")
        print("\nDEPENDENCE")
        for cls, doc in DEPENDENCE_DOC.items():
            print(f"  {cls}\n    {doc}")
        print("\nBORROWED TOKEN TABLE (the denominator, from scripts/verdict_set.py)")
        try:
            vs = load_verdict_set_module(root)
            for pat, label in vs.IO_TOKENS:
                print(f"  {label:22s} {pat}")
        except VerdictIoContractsError as exc:
            print(f"  <unavailable: {exc}>")
        return 0
    if args.self_test:
        return self_test()

    out_path = Path(args.out)
    if args.sites:
        return print_sites(root, args.sites, args.member)
    if args.check:
        return run_check(root, out_path)

    previous = None
    if out_path.is_file():
        try:
            previous = json.loads(out_path.read_text())
        except ValueError as exc:
            print(f"VERDICT_IO_CONTRACTS=fail existing {out_path} is not valid JSON: {exc}", file=sys.stderr)
            return 1
    try:
        doc = build(root, previous, args.rebase_up, now_utc=None)
    except VerdictIoContractsError as exc:
        print(f"VERDICT_IO_CONTRACTS=fail {exc}", file=sys.stderr)
        return 1
    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp = out_path.with_suffix(out_path.suffix + ".tmp")
    tmp.write_text(render(doc))
    tmp.replace(out_path)
    cls = doc["classification"]
    print(
        f"VERDICT_IO_CONTRACTS ok sites={cls['site_total']} "
        f"io={cls['sites_issuing_io']} no-io={cls['sites_issuing_no_io']} "
        f"content={cls['by_dependence'].get('content-bearing', 0)} "
        f"success-only={cls['by_dependence'].get('success-only', 0)} "
        f"contracts={len(doc['contracts'])} ledger={doc['ledger']['row_count']} -> {out_path}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
