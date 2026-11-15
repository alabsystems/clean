#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""A tactic family's sealed LEAN_VERDICTS.json: its row grammar, rule and checks.

Each family carries pinned Lean's verdict on every declared row in a sidecar
beside its fixtures, minted OFFLINE by mint_lean_verdicts.py (the only code
that runs Lean) and keyed to each fixture's sha256. This module owns what that
file means, and runs no process at all:

  * the row grammar the fixtures and the sidecar share (`DECL_RE`, the span a
    row owns, the declared names of a MANIFEST entry, a row's kind);
  * the verdict rule `classify` and the unknown-tactic token a row's stored
    message points at (`unknown_tactics`);
  * the content `seal`, and `verdict_problems` / `load_checked`, which refuse a
    sidecar that is missing, malformed, unsealed, from another Lean world,
    minted over other fixture bytes, or whose stored verdict, class or
    unknown tactics do not RE-DERIVE from the Lean messages and axioms stored
    beside them.

WHAT THE STATIC CHECKS CANNOT SEE. The seal is a plain sha256 over canonical
JSON: it catches an edit that forgot it, never a forger, who can recompute it.
A hand edit that rewrites a row's verdict, class, messages and axioms together
and reseals re-derives cleanly, and only `mint_lean_verdicts.py --check` (which
asks pinned Lean again; the FULL-mode `tactic-lean-verdicts` leg) can see it.

A row is `accept` only with no error and no "declaration uses `sorry`" warning
in its span AND its own `#print axioms` line free of `sorryAx` (both signals
are needed: `grind +distrib` errors with clean axioms, and a theorem that
merely USES a failed one has `sorryAx` and no message). Classes go by
precedence, not position: Lean prints "unknown tactic" AFTER the "unsolved
goals" it causes, which starts earlier.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

SCHEMA = "tactic-family-lean-verdicts-v1"
RULE = "tactic-family-lean-verdict-v1"
VERDICTS_FILE = "LEAN_VERDICTS.json"
METHOD = {
    "lean_args": ["--json"],
    "suffix": "#print axioms <row> per declared row",
    "cross_check": "per-row split: import Init + preceding helpers + row",
}
# The build each oracle world is minted with, by `lean --githash`. A world with
# no entry here refuses every sidecar until its build is named: an oracle flip
# makes every LEAN_VERDICTS.json refuse until it is re-minted, on purpose.
ORACLE_GITHASHES = {"v4.30.0-rc2": "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"}
# Phase 2 respells the class-73 canaries; until then a canary Lean rejects is
# reported, not refused.
CANARIES_MUST_ACCEPT = False
UNSEALED = ("minted_at_utc", "seal")
MESSAGE_CAP = 600
SORRY_WARNINGS = ("declaration uses `sorry`", "declaration uses 'sorry'")
CLASSES = (None, "unknown-tactic", "parse-error", "unknown-identifier", "elab-error",
           "sorry-warning", "depends-on-sorry", "not-declared")
REJECT_CLASSES = CLASSES[1:]
# MANIFEST.json's reviewed list of in-world rows Clean accepts and pinned Lean
# rejects that `--update-baseline` may record although the baseline did not
# (family_two_way.unrecorded_false_accepts): {row name: written reason}.
EXEMPTIONS_KEY = "two_way_record_exemptions"
HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent

# The row grammar (moved here from family_gate.py, which re-exports it): a row
# is a `theorem`/`def`/`lemma` at column 0, optionally after one attribute.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]+\]\s*)?(?:theorem|def|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)
# A `/-- -/` docstring ending right before a row belongs to that row's span.
DOC_BEFORE = re.compile(r"/--(?:(?!-/).)*-/\s*$", re.S)
TACTIC_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'?!]*")
_TACTIC_CHAR = re.compile(r"[A-Za-z0-9_'?!]")


def mint_command(family: str) -> str:
    # Backticked: a path in prose is a name, not an invocation (R3).
    return f"`scripts/tactic_parity/mint_lean_verdicts.py --family {family}`"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def span_starts(text: str) -> list[tuple[str, int]]:
    """(row name, offset) per DECL_RE row, each pulled back over a docstring
    that ends right before it."""
    out = []
    for m in DECL_RE.finditer(text):
        s = m.start()
        d = DOC_BEFORE.search(text, 0, s)
        if d and d.end() == s:
            s = d.start()
        out.append((m.group(1), s))
    return out


def span_lines(text: str) -> dict[str, int]:
    """The 1-based line each row's span starts on (what `line_rel` counts from)."""
    return {name: text.count("\n", 0, s) + 1 for name, s in span_starts(text)}


def tactic_at(line: str, col: int) -> str | None:
    """The tactic token at a Lean message column. Lean's `unknown tactic`
    points ONE PAST the token's first character (measured on v4.30.0-rc2:
    `by ring` errs at the `i`), so walk back to the token's start."""
    i = max(0, min(col, len(line)))
    while i > 0 and _TACTIC_CHAR.match(line[i - 1]):
        i -= 1
    m = TACTIC_TOKEN.match(line, i)
    return m.group(0) if m else None


def unknown_tactics(messages: list[dict], lines: list[str], span_line: int) -> list[str] | None:
    """The sorted tokens a row's stored `unknown tactic` errors point at, or
    None when one points at no tactic token (the reading is then unusable)."""
    found = set()
    for m in messages:
        if m.get("severity") != "error" or not str(m.get("data", "")).startswith("unknown tactic"):
            continue
        at = span_line + int(m.get("line_rel") or 0) - 1
        tok = tactic_at(lines[at - 1], int(m.get("col") or 0)) if 1 <= at <= len(lines) else None
        if tok is None:
            return None
        found.add(tok)
    return sorted(found)


def oracle_world(root: Path = REPO_ROOT) -> tuple[str | None, str | None, list[str]]:
    """(world id, toolchain, problems): the one `oracle` row of lean_worlds.tsv,
    which must name the toolchain `./lean-toolchain` pins."""
    tsv = root / "crates" / "clean-olean" / "lean_worlds.tsv"
    try:
        rows = [ln.split("\t") for ln in tsv.read_text(encoding="utf-8").splitlines()
                if ln.strip() and not ln.startswith("#")]
        pin = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    except OSError as exc:
        return None, None, [f"cannot read the oracle world: {exc}"]
    oracles = [r for r in rows if len(r) >= 3 and r[1] == "oracle"]
    if len(oracles) != 1:
        return None, None, [f"{tsv.name} names {len(oracles)} oracle rows, not exactly one"]
    world, toolchain = oracles[0][0], oracles[0][2]
    if toolchain != pin:
        return world, toolchain, [f"{tsv.name}'s oracle toolchain {toolchain!r} is not "
                                  f"./lean-toolchain's {pin!r}"]
    return world, toolchain, []


def negative_names(entry: dict) -> list[str]:
    return [n["name"] for n in entry.get("negatives", [])]


def control_names(entry: dict) -> list[str]:
    return [c["name"] for c in entry.get("controls", [])]


def declared_names(entry: dict) -> list[str]:
    """Every declaration a manifest file entry owns: canary, helpers, probes,
    negatives, controls. Only `probes` are the pinned family denominator."""
    return [entry["canary"], *entry.get("helpers", []), *entry["probes"],
            *negative_names(entry), *control_names(entry)]


def row_kind(entry: dict, name: str) -> str | None:
    if name == entry["canary"]:
        return "canary"
    for kind, names in (("helper", entry.get("helpers", [])), ("probe", entry["probes"]),
                        ("negative", negative_names(entry)), ("control", control_names(entry))):
        if name in names:
            return kind
    return None


def exemptions(manifest: dict) -> dict:
    ex = manifest.get(EXEMPTIONS_KEY, {})
    return ex if isinstance(ex, dict) else {}


def classify(messages: list[dict], axioms: list[str] | None) -> tuple[str, str | None]:
    """(verdict, class) of one row from the messages in its span and its own
    `#print axioms` reading (None: the constant was never declared)."""
    errors = [m.get("data", "") for m in messages if m.get("severity") == "error"]
    if errors:
        if any(d.startswith("unknown tactic") for d in errors):
            return "reject", "unknown-tactic"
        if any(d.startswith(("unexpected ", "expected ")) for d in errors):
            return "reject", "parse-error"
        if any(d.startswith(("Unknown identifier", "Unknown constant",
                             "unknown identifier", "unknown constant")) for d in errors):
            return "reject", "unknown-identifier"
        return "reject", "elab-error"
    if any(m.get("severity") == "warning" and any(s in m.get("data", "") for s in SORRY_WARNINGS)
           for m in messages):
        return "reject", "sorry-warning"
    if axioms is None:
        return "reject", "not-declared"
    if "sorryAx" in axioms:
        return "reject", "depends-on-sorry"
    return "accept", None


def _sealed_view(doc: dict) -> dict:
    view = {k: v for k, v in doc.items() if k not in UNSEALED}
    if isinstance(view.get("lean_world"), dict):
        view["lean_world"] = {k: v for k, v in view["lean_world"].items() if k != "version_line"}
    return view


def seal(doc: dict) -> str:
    """sha256 of canonical JSON over every field but the unsealed ones."""
    text = json.dumps(_sealed_view(doc), sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return sha256_bytes(text.encode("utf-8"))


def load_verdicts(fam_dir: Path) -> dict | None:
    try:
        doc = json.loads((fam_dir / VERDICTS_FILE).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return doc if isinstance(doc, dict) else None


def load_checked(family: str, manifest: dict, fam_dir: Path,
                 root: Path = REPO_ROOT) -> tuple[dict | None, list[str], list[str]]:
    """(doc, problems, notes): ONE read of the sidecar, validated. The caller
    crosses with this very doc, never a second read (the file can move under a
    long measured run)."""
    rel = f"{family}/{VERDICTS_FILE}"
    try:
        doc = json.loads((fam_dir / VERDICTS_FILE).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None, [f"{rel} is missing -- mint it with {mint_command(family)}"], []
    except (OSError, ValueError) as exc:
        return None, [f"{rel} is unreadable or malformed ({exc})"], []
    problems, notes = doc_problems(doc, family, manifest, fam_dir, root)
    return (doc if not problems else None), problems, notes


def verdict_problems(family: str, manifest: dict, fam_dir: Path,
                     root: Path = REPO_ROOT) -> tuple[list[str], list[str]]:
    """(problems, notes) for the family's sidecar against the live fixtures."""
    return load_checked(family, manifest, fam_dir, root)[1:]


def manifest_problems(manifest: dict) -> list[str]:
    """The two-way fields of a MANIFEST: negatives and the record exemptions."""
    problems = []
    declared = {n for e in manifest.get("files", []) for n in declared_names(e)}
    for entry in manifest.get("files", []):
        for neg in entry.get("negatives", []):
            if neg.get("lean_class") not in REJECT_CLASSES:
                problems.append(f"{entry['file']}: negative {neg.get('name')} names lean_class "
                                f"{neg.get('lean_class')!r}, not one of {list(REJECT_CLASSES)}")
            if not isinstance(neg.get("lean_contains"), str) or not neg["lean_contains"].strip():
                problems.append(f"{entry['file']}: negative {neg.get('name')} has an empty "
                                f"lean_contains, which every message contains")
    ex = manifest.get(EXEMPTIONS_KEY, {})
    if not isinstance(ex, dict):
        return problems + [f"MANIFEST.json {EXEMPTIONS_KEY} must be an object {{row: reason}}"]
    for name, why in sorted(ex.items()):
        if name not in declared:
            problems.append(f"MANIFEST.json {EXEMPTIONS_KEY} names {name}, which is no declared row")
        if not isinstance(why, str) or not why.strip():
            problems.append(f"MANIFEST.json {EXEMPTIONS_KEY} gives {name} no written reason")
    return problems


def _row_problems(fname: str, name: str, r: dict, lines: list[str] | None,
                  starts: dict[str, int]) -> tuple[list[str], bool]:
    """(problems, printed an error or was never declared) for one minted row."""
    msgs, ax = r.get("messages"), r.get("axioms")
    if not isinstance(msgs, list) or not all(isinstance(m, dict) for m in msgs) or not (
            ax is None or isinstance(ax, list)):
        return [f"{fname}: {name} has malformed messages or axioms"], False
    problems = []
    derived = classify(msgs, ax)
    if (r.get("verdict"), r.get("class")) != derived:
        problems.append(f"{fname}: {name} is recorded {r.get('verdict')}/{r.get('class')} but "
                        f"does not re-derive from its stored messages and axioms, which "
                        f"give {derived[0]}/{derived[1]}")
    if r.get("split_verdict") != r.get("verdict"):
        problems.append(f"{fname}: {name}'s split reading {r.get('split_verdict')!r} is not "
                        f"its whole-file verdict {r.get('verdict')!r}")
    if lines is not None and name in starts:
        toks = unknown_tactics(msgs, lines, starts[name])
        if toks is None or r.get("unknown_tactics") != toks:
            problems.append(f"{fname}: {name} records unknown_tactics {r.get('unknown_tactics')!r}, "
                            f"but its stored `unknown tactic` errors point at {toks!r} in the fixture")
    return problems, ax is None or any(m.get("severity") == "error" for m in msgs)


def doc_problems(doc, family: str, manifest: dict, fam_dir: Path,
                 root: Path = REPO_ROOT) -> tuple[list[str], list[str]]:
    rel = f"{family}/{VERDICTS_FILE}"
    if not isinstance(doc, dict) or doc.get("schema_version") != SCHEMA:
        got = doc.get("schema_version") if isinstance(doc, dict) else type(doc).__name__
        return [f"{rel} has schema {got!r}, not {SCHEMA!r}"], []
    problems = manifest_problems(manifest)
    if doc.get("family") != family:
        problems.append(f"{rel} is minted for family {doc.get('family')!r}, not {family!r}")
    if doc.get("seal") != seal(doc):
        problems.append(f"{rel}: content seal broken -- the file was edited after it was minted "
                        f"and not resealed; re-mint it with {mint_command(family)}, never by hand")
    world, toolchain, wp = oracle_world(root)
    problems += [f"{rel}: {p}" for p in wp]
    lw = doc.get("lean_world") if isinstance(doc.get("lean_world"), dict) else {}
    if (lw.get("id"), lw.get("toolchain"), lw.get("githash")) != (
            world, toolchain, ORACLE_GITHASHES.get(world or "")):
        problems.append(f"{rel}: minted under Lean world {lw.get('id')!r} ({lw.get('toolchain')!r}, "
                        f"build {str(lw.get('githash'))[:12]}), not the oracle world {world!r} "
                        f"({toolchain!r}); re-mint with {mint_command(family)}")
    if doc.get("rule") != RULE:
        problems.append(f"{rel}: rule {doc.get('rule')!r} is not {RULE!r}")
    files = doc.get("files") if isinstance(doc.get("files"), dict) else {}
    listed = {e["file"]: e for e in manifest.get("files", [])}
    if set(files) != set(listed):
        problems.append(f"{rel}: minted files {sorted(files)} are not the manifest's {sorted(listed)}")
    canary_rejects: list[str] = []
    for fname, entry in listed.items():
        rec = files.get(fname)
        if not isinstance(rec, dict):
            continue
        try:
            data = (fam_dir / fname).read_bytes()
        except OSError:
            continue  # static_check reports the missing fixture
        live, lines, starts = sha256_bytes(data), None, {}
        if rec.get("fixture_sha256") != live:
            problems.append(f"{fname}: edited without a re-mint (minted over "
                            f"{str(rec.get('fixture_sha256'))[:12]}, the file is now {live[:12]}); "
                            f"run {mint_command(family)}")
        else:
            text = data.decode("utf-8", errors="replace")
            lines, starts = text.splitlines(), span_lines(text)
        rows = rec.get("rows") if isinstance(rec.get("rows"), dict) else {}
        names = declared_names(entry)
        if set(rows) != set(names):
            problems.append(f"{fname}: minted rows differ from the manifest's "
                            f"(missing={sorted(set(names) - set(rows))}, "
                            f"unlisted={sorted(set(rows) - set(names))})")
        any_error = False
        for name in names:
            r = rows.get(name)
            if not isinstance(r, dict):
                continue
            row_problems, errored = _row_problems(fname, name, r, lines, starts)
            problems += row_problems
            any_error = any_error or errored
            kind = row_kind(entry, name)
            if kind in ("helper", "control") and r.get("verdict") != "accept":
                problems.append(f"{fname}: {kind} {name} is not accepted by pinned Lean "
                                f"({r.get('class')}); a {kind} must be")
            if kind == "canary" and r.get("verdict") != "accept":
                canary_rejects.append(name)
        if rec.get("lean_exit") != (1 if any_error else 0):
            problems.append(f"{fname}: lean_exit {rec.get('lean_exit')!r} is inconsistent with its "
                            f"rows' messages (errors printed: {any_error})")
        controls = set(control_names(entry))
        for neg in entry.get("negatives", []):
            r = rows.get(neg["name"])
            if not isinstance(r, dict):
                continue
            if r.get("verdict") != "reject":
                problems.append(f"{fname}: negative {neg['name']} is ACCEPTED by pinned Lean; a "
                                f"negative must be a row Lean rejects")
            elif r.get("class") != neg.get("lean_class") or not any(
                    str(neg.get("lean_contains") or "\0") in str(m.get("data")) for m in r["messages"]):
                problems.append(f"{fname}: negative {neg['name']} is rejected for a different reason "
                                f"({r.get('class')}) than its manifest entry names "
                                f"({neg.get('lean_class')}, containing {neg.get('lean_contains')!r})")
            ctl = rows.get(neg.get("control"))
            if neg.get("control") not in controls or not isinstance(ctl, dict) \
                    or ctl.get("verdict") != "accept":
                problems.append(f"{fname}: negative {neg['name']}'s control {neg.get('control')!r} is "
                                f"missing or not accepted by pinned Lean")
    notes: list[str] = []
    if canary_rejects:
        msg = (f"{len(canary_rejects)} canar{'y' if len(canary_rejects) == 1 else 'ies'} minted "
               f"reject by pinned Lean ({', '.join(sorted(canary_rejects))}; frontend ledger class 73)")
        if CANARIES_MUST_ACCEPT:
            problems.append(msg)
        else:
            notes.append(msg + " -- report-only until phase 2 respells them")
    return problems, notes
