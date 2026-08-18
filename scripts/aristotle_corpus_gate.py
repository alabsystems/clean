#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Fail-closed re-check gate for the Aristotle whnf model-guide corpus.

Until this script existed, **nothing in the repository re-checked the corpus**
(``grep -rln aristotle-whnf-model-guides`` over ``*.sh|*.rs|*.toml|*.py|*.js``
returned zero hits), and the manual per-round landing gate — 0 errors, 0 sorry,
byte-identical statements, axiom closure ``⊆ {propext, Classical.choice,
Quot.sound}`` — was structurally blind to two failure modes that both occurred:

* **Vacuity.** ``def decLEq (l1 l2 : Level) : Decidable (LEq l1 l2) := by
  classical; exact Classical.propDecidable (LEq l1 l2)`` passes every check in
  the manual gate and carries zero algorithmic content. Found live in
  ``level-eq-decidable`` (headlined as "unconditional decidability") and
  ``let-delta-whnf-conversion``.
* **Undischarged hypotheses.** The axiom-closure check sees *axioms*, not
  *hypotheses*. ``decWH`` sat as an unproved parameter in all ten dependent
  conversion capstones while the handoff advertised "exactly one undischarged
  fact". 0 axioms != 0 assumptions.

The gate therefore checks five things, and ratchets each so drift must be
consciously accepted (``--update``, ratchet staged in the same commit):

1. **Elaboration** under the pinned toolchain — 0 errors, 0 sorry-warnings.
   The corpus is toolchain-brittle: under the elan default (4.32.x) some rungs
   produce real elaboration errors; they are clean only under v4.30.0-rc2.
2. **Comment-stripped soundness scan** — no ``sorry`` / ``admit`` / ``axiom``
   declaration / ``native_decide`` / ``unsafe`` / ``partial def`` / ``opaque``
   in code. (A naive grep yields 67 false positives from guide prose; this
   strips nested ``/- -/`` and ``--`` first.)
3. **Vacuity** — classical-shortcut inhabitants of ``Decidable``. Known debt is
   registered per rung and may only decrease; any new site fails the gate.
4. **Hypothesis ledger** — every undischarged binder (``sn``, ``cr``, ``decWH``,
   whnf oracles, ...) recorded per rung. A rung gaining an unregistered
   hypothesis fails. This is what makes "modulo N facts" auditable.
5. **Composition byte-identity** — the corpus discharges ``cr`` across files by
   textual identity of the ``inductive Step`` / ``def Confl`` blocks between
   sibling rungs, re-verified by hand each round with no machine gate. One
   divergent edit silently breaks the discharge; this hashes the blocks.

Usage::

    python3 scripts/aristotle_corpus_gate.py              # --check (default)
    python3 scripts/aristotle_corpus_gate.py --fast       # skip elaboration
    python3 scripts/aristotle_corpus_gate.py --update     # rewrite the ratchet
    python3 scripts/aristotle_corpus_gate.py --jobs 8
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CORPUS_DIR = REPO_ROOT / "proofs" / "aristotle-whnf-model-guides"
RATCHET_PATH = REPO_ROOT / "data" / "aristotle_corpus_ratchet.json"
RATCHET_REL = "data/aristotle_corpus_ratchet.json"

# The corpus elaborates ONLY under this pin. Do not "modernise" it without
# re-running the full sweep: under 4.32.x several dependent rungs fail with real
# simp-normalisation type mismatches.
TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"

# Forbidden in code (not in comments). `axiom` is matched line-initially so that
# `#print axioms` and prose do not trip it.
BANNED_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom_decl": re.compile(r"^\s*axiom\s+\w", re.M),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "unsafe": re.compile(r"^\s*unsafe\s", re.M),
    "partial_def": re.compile(r"^\s*partial\s+def\s", re.M),
    "opaque": re.compile(r"^\s*opaque\s+\w", re.M),
}

# Classical shortcuts that inhabit `Decidable` (or otherwise erase algorithmic
# content) while passing every axiom-closure check.
VACUITY_PATTERNS = {
    "Classical.propDecidable": re.compile(r"\bClassical\.propDecidable\b"),
    "Classical.dec": re.compile(r"\bClassical\.dec(?:Eq|Rel|Pred)?\b"),
    "classical_decide": re.compile(r"\bclassical\b[\s\S]{0,80}?\bexact\s+decide\b"),
}

# Binder types that denote an undischarged assumption rather than ordinary data.
HYPOTHESIS_TYPE_HINTS = re.compile(
    r"\b(?:SN|Acc|Confl|Decidable|PiInj|Conv|RTC\s+Step|HasType)\b"
)

# Blocks whose byte-identity carries the cross-file composition discharge.
COMPOSITION_BLOCKS = ("inductive Step", "def Confl", "inductive Tm", "inductive HasType")

# The load-bearing assumptions: binders that carry a rung's conclusion rather
# than a local lemma's. Tracked by name with an explicit discharge status so the
# headline "everything modulo X" claim is machine-derived instead of prose.
#
# `cr` is genuinely discharged: a byte-identical sibling rung proves
# `confluence : Confl` with no hypotheses (checked by the composition gate
# below). `sn` and `decWH` are not discharged anywhere in the corpus — and `sn`
# is worse than open, it is FALSE for the modelled λ* (`Type : Type` is
# Girard-inconsistent; 41 corpus files carry the note), which makes every
# completeness/decidability theorem depending on it vacuous rather than merely
# conditional. See HANDOFF_CORRECTION_2026-07-24.md.
#
# ONE STATUS PER NAME IS NOT ENOUGH, and pretending otherwise misreports the
# corpus in BOTH directions. `sn` is false-under-`Type : Type` for the dependent
# rungs, but the SIMPLY TYPED ones are a different calculus where it is true AND
# PROVED. `PER_RUNG_DISCHARGE` records those exceptions so a rung that really has
# been discharged stops being counted as open. It is reporting only: it never
# changes a pass/fail verdict, and a name absent from it keeps its global status
# for every rung.
GLOBAL_ASSUMPTIONS = {
    "sn": "UNDISCHARGED_AND_FALSE_UNDER_TYPE_IN_TYPE",
    "decWH": "UNDISCHARGED",
    "whnf_conv": "UNDISCHARGED_ORACLE",
    "whnf_steps": "UNDISCHARGED_ORACLE",
    "whnf_whnf": "UNDISCHARGED_ORACLE",
    "whnf_reduces": "UNDISCHARGED_ORACLE",
    "whnf_pi": "UNDISCHARGED_ORACLE",
    "pinj": "UNDISCHARGED",
    "cr": "DISCHARGED_BY_BYTE_IDENTICAL_SIBLING",
    # Found 2026-08-17, when `prop_defs` taught the scanner to see binders whose
    # type is a bare rung-local `Prop`. All four were invisible before: nothing
    # in `HYPOTHESIS_TYPE_HINTS` matches `WfEnv E`, `EnvAcyclic E`, `WCR` or
    # `KComplete`, so a whole assumption could hide behind one capitalised name.
    "wf": "UNDISCHARGED_SIDE_CONDITION",
    "ac": "UNDISCHARGED_SIDE_CONDITION",
    "wcr": "BY_DESIGN_STATEMENT_PREMISE",
    "hcomp": "UNDISCHARGED",
}

# assumption name -> {rung: the discharge, in one line}. An entry here is a claim
# that THIS rung's occurrence is proved, and it must name where.
# A rung whose central relation turns out to be TRIVIAL. Nothing else in this gate
# can see this: the relation is a `def`/`inductive`, not an axiom; the file has no
# vacuity pattern, no sorry, and elaborates clean. But a theorem quantified over a
# degenerate relation says nothing, so the corpus must not report such a rung as
# healthy. Each entry names the MACHINE-CHECKED witness that proves the collapse.
DEGENERATE_RELATIONS = {
    "proof-irrelevance-r3":
        "Conv is the TOTAL relation — `conv_total (Γ) (x y) : Conv Γ x y` is proved in "
        "the rung itself, so `Conv Γ x y` holds for EVERY context and EVERY pair of "
        "terms. Witness: `conv_srt_one_two : Conv [] (.srt 1) (.srt 2)`. Cause: the "
        "TYPED `irrel` rule feeding the UNTYPED `appCong`/`beta` congruences, which "
        "lifts one typed identification to arbitrary untyped terms. CONSEQUENCE: "
        "`preservation_irrel` is quantified over a trivial conversion, so its subject-"
        "reduction claim carries no content, and `pinj` is discharged only because "
        "everything is. A type-indexed conversion `Γ ⊢ a ≡ b : T` is the standard repair "
        "— DONE in `proof-irrelevance-r4`, which PROVES non-degeneracy "
        "(conv_presupposition, not_conv_total) plus step-by-step regression against this "
        "exact collapse (not_conv_any_of_proof, not_conv_total_srt0_cons). r3 is KEPT, "
        "degenerate, as the machine-checked record of the defect.",
}

# An assumption can be open in two very different ways: nobody has tried, or the
# cheap routes are PROVED not to work. Recording the second kind keeps the census
# from flattening a measured wall into the same "UNDISCHARGED" as an untouched
# row. Reporting only — like PER_RUNG_DISCHARGE, it never moves a verdict, and an
# obstruction is NOT a discharge.
OBSTRUCTIONS = {
    ("pinj", "proof-irrelevance-r4"):
        "OPEN, but the frontier has MOVED TWICE. Dead routes (machine-checked): "
        "(1) confluence — `PiInjObstruction.conv_not_bconv`, with `irrel` Conv is not "
        "contained in untyped β-conversion even between Π-types; (2) a closed-term PER "
        "model — `model_pi_codomain_blind`, `Π (srt 0). B` gets ONE code for every B. "
        "The named missing ingredient, REFLECTION, is now BUILT: `KRel.lean` is a "
        "Kripke logical relation carrying syntactic ConvTy evidence, with escape, "
        "reflection of neutrals, Π-shape transfer and PROVED non-degeneracy "
        "(`not_kty_srt0_srt1`, `not_kty_srt0_pi`). `KFund.pi_injective : KComplete → "
        "PiInj` is machine-checked, so PiInj is now reduced to ONE named hypothesis: "
        "`KComplete`, the fundamental theorem of that relation. Separately, the "
        "SORT-CONFUSION ROUTE TO A COUNTEREXAMPLE IS CLOSED UNCONDITIONALLY — "
        "`SNCMain.no_sort_is_prop` proves no context (junk included) makes a sort a "
        "proposition, so `irrel` can never fire at the top of a type conversion "
        "anywhere. Remaining wall: `KComplete`'s Π case needs the fundamental theorem "
        "relative to a PARALLEL substitution; `SNCSub.lean` now supplies that calculus.",
}

PER_RUNG_DISCHARGE = {
    "pinj": {
        "proof-irrelevance-r3":
            "proof-irrelevance-r3.pi_injective — PROVED, but BY DEGENERACY: it is "
            "`⟨conv_total .., conv_total ..⟩`. See DEGENERATE_RELATIONS; this is not a "
            "healthy discharge and must not be read as one",
    },
    "decWH": {
        "whnf-conversion":
            "whnf-conversion.decWH_discharged — decWHConvOfSN from `sn` and `cr` alone, "
            "axiom closure [propext]; typechecks AS the decWH parameter of decConv_whnf "
            "and instConvDecidable_whnf with no coercion",
    },
    "sn": {
        "whnf-conversion":
            "stlc-sn.sn_of_typed_open (open-context SN); (Tm, Step, HasType, SN) "
            "byte-identical to stlc-sn, so the proof transfers by the same route as `cr`",
    },
}

DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|inductive|structure|class|example)\b"
)


def strip_comments(src: str) -> str:
    """Remove nested ``/- -/`` blocks and ``--`` line comments.

    Lean block comments nest, so a regex is wrong here; the corpus embeds its
    house prompt in a leading block comment containing the literal words
    "fill every sorry", which is exactly the false positive this avoids.
    """
    out: list[str] = []
    i, depth, n = 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "".join(out)


def extract_block(code: str, header: str) -> str | None:
    """Return the source of the top-level declaration beginning with ``header``."""
    lines = code.splitlines()
    for idx, line in enumerate(lines):
        if line.startswith(header):
            body = [line]
            for nxt in lines[idx + 1 :]:
                if nxt and not nxt[0].isspace() and DECL_START.match(nxt):
                    break
                body.append(nxt)
            return "\n".join(body).rstrip()
    return None


def declaration_headers(code: str) -> list[str]:
    """Yield the *signature* text of each top-level declaration.

    Binders introduced inside a proof body (``intro h``, ``fun ih =>``) are not
    assumptions of the statement, so scanning whole files would drown the real
    hypotheses in ``h``/``h1``/``ih`` noise. A declaration's signature runs from
    its header to the ``:=``/``where`` that opens the body.
    """
    headers: list[str] = []
    lines = code.splitlines()
    idx = 0
    while idx < len(lines):
        if DECL_START.match(lines[idx]):
            body: list[str] = []
            for line in lines[idx:]:
                if body and line and not line[0].isspace() and DECL_START.match(line):
                    break
                body.append(line)
                idx += 1
                if ":=" in line or re.search(r"\bwhere\b", line):
                    break
            else:
                pass
            headers.append("\n".join(body).split(":=")[0])
            continue
        idx += 1
    return headers


def prop_defs(code: str) -> set[str]:
    """Names a rung defines as a bare `Prop` — e.g. `def PiInj : Prop := ...`.

    These are the sneakiest hypothesis types, because a binder `(hcomp : KComplete)`
    carries no judgement name for `HYPOTHESIS_TYPE_HINTS` to match: the whole
    assumption hides behind one capitalised identifier. `PiInj` was only caught
    because it had been hard-coded into the hint list by hand; the next such
    definition would have been invisible. Collecting them per rung generalises
    that special case.
    """
    return set(
        re.findall(
            r"^\s*(?:private\s+|protected\s+)?(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)"
            r"\s*(?:\{[^}]*\}|\([^)]*\)|\s)*:\s*Prop\b",
            code,
            re.M,
        )
    )


def hypotheses_of(code: str, prop_names: frozenset[str] = frozenset()) -> list[str]:
    """Binder names in declaration *signatures* whose type denotes an assumption.

    Deliberately over-collects rather than under-collects: this is a ratchet, so
    a false positive costs one line of accepted drift while a false negative is
    exactly the ``decWH`` failure this gate exists to prevent.
    """
    found: set[str] = set()
    for header in declaration_headers(code):
        for match in re.finditer(
            r"[({]\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^)}]{0,400})[)}]", header
        ):
            name, ty = match.group(1), match.group(2)
            if (
                HYPOTHESIS_TYPE_HINTS.search(ty)
                or ty.lstrip().startswith("∀")
                or any(re.search(rf"\b{re.escape(p)}\b", ty) for p in prop_names)
            ):
                found.add(name)
    return sorted(found)


def elaborate(path: Path) -> tuple[bool, int, int, str]:
    """Elaborate one file under the pinned toolchain. Returns (ok, errors, sorries, detail)."""
    try:
        proc = subprocess.run(
            ["elan", "run", TOOLCHAIN, "lean", path.name],
            cwd=path.parent,
            capture_output=True,
            text=True,
            timeout=1800,
        )
    except FileNotFoundError:
        return False, -1, -1, "elan not installed"
    except subprocess.TimeoutExpired:
        return False, -1, -1, "timeout after 1800s"
    output = proc.stdout + proc.stderr
    errors = len(re.findall(r"^\S+\.lean:\d+:\d+: error", output, re.M))
    # Lean 4.30 emits BACKTICKS: "declaration uses `sorry`". Matching only the
    # straight-quote spelling made this detector silently dead — and `lean` exits
    # 0 on a sorry warning, so nothing else in this branch would have caught it.
    # Match either spelling, and never rely on the exit code alone for sorries.
    sorries = len(re.findall(r"declaration uses [`']sorry[`']", output))
    ok = proc.returncode == 0 and errors == 0 and sorries == 0
    detail = ""
    if not ok:
        first = [ln for ln in output.splitlines() if ": error" in ln][:2]
        detail = f"rc={proc.returncode} " + " | ".join(first)
    return ok, errors, sorries, detail


def scan(path: Path, prop_names: frozenset[str] = frozenset()) -> dict:
    """Static audit of one solution file (no Lean required)."""
    src = path.read_text(encoding="utf-8", errors="replace")
    code = strip_comments(src)
    banned = {k: len(p.findall(code)) for k, p in BANNED_PATTERNS.items()}
    vacuity = {k: len(p.findall(code)) for k, p in VACUITY_PATTERNS.items()}
    blocks = {}
    for header in COMPOSITION_BLOCKS:
        block = extract_block(code, header)
        if block is not None:
            blocks[header] = hashlib.sha256(block.encode()).hexdigest()[:16]
    return {
        "lines": src.count("\n") + 1,
        "theorems": len(re.findall(r"^\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\b", code, re.M)),
        "banned": {k: v for k, v in banned.items() if v},
        "vacuity": {k: v for k, v in vacuity.items() if v},
        "hypotheses": hypotheses_of(code, prop_names),
        "blocks": blocks,
    }


def solution_files() -> list[Path]:
    return sorted(CORPUS_DIR.glob("*/solution/**/*.lean"))


def rung_name(path: Path) -> str:
    return path.relative_to(CORPUS_DIR).parts[0]


def order_rung_files(paths: list[Path]) -> tuple[list[Path], str]:
    """Topologically order one rung's files by their INTRA-RUNG imports.

    A rung became multi-file with `proof-irrelevance-r4`, whose model/obstruction
    development spans eight modules. Import order matters twice over: `lean` must
    see a dependency's `.olean` before the importer, and — more importantly — the
    per-file scan below must run over EVERY file, not just the last one.
    """
    by_stem = {p.stem: p for p in paths}
    if len(by_stem) != len(paths):
        # Keying by stem is what `lean` itself does for imports, so a collision is
        # not merely ambiguous here — it would drop a file from the ordering, which
        # is the exact silent-coverage bug this function exists to end.
        seen: set[str] = set()
        dupes = sorted({p.stem for p in paths if p.stem in seen or seen.add(p.stem)})
        return paths, f"duplicate module stem(s) in one rung: {dupes}"
    deps: dict[str, set[str]] = {}
    for stem, path in by_stem.items():
        src = path.read_text(encoding="utf-8", errors="replace")
        found = set(re.findall(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)", src, re.M))
        deps[stem] = {d for d in found if d in by_stem and d != stem}

    ordered: list[Path] = []
    done: set[str] = set()

    def visit(stem: str, stack: tuple[str, ...]) -> str:
        if stem in done:
            return ""
        if stem in stack:
            return f"import cycle: {' -> '.join(stack + (stem,))}"
        for dep in sorted(deps[stem]):
            err = visit(dep, stack + (stem,))
            if err:
                return err
        done.add(stem)
        ordered.append(by_stem[stem])
        return ""

    for stem in sorted(by_stem):
        err = visit(stem, ())
        if err:
            return paths, err
    return ordered, ""


def elaborate_rung(paths: list[Path]) -> tuple[bool, int, int, str]:
    """Elaborate every file of one rung, sharing an `.olean` build directory.

    Single-file rungs keep the exact original invocation, so the 79 rungs that
    predate multi-file support are not perturbed.
    """
    if len(paths) == 1:
        return elaborate(paths[0])

    ordered, cycle = order_rung_files(paths)
    if cycle:
        return False, -1, -1, cycle

    errors = sorries = 0
    details: list[str] = []
    with tempfile.TemporaryDirectory(prefix="corpus-gate-") as build:
        env = dict(os.environ, LEAN_PATH=build)
        for path in ordered:
            try:
                proc = subprocess.run(
                    ["elan", "run", TOOLCHAIN, "lean",
                     "-o", str(Path(build) / f"{path.stem}.olean"), path.name],
                    cwd=path.parent, capture_output=True, text=True, timeout=1800, env=env,
                )
            except FileNotFoundError:
                return False, -1, -1, "elan not installed"
            except subprocess.TimeoutExpired:
                return False, -1, -1, f"timeout after 1800s on {path.name}"
            output = proc.stdout + proc.stderr
            errors += len(re.findall(r"^\S+\.lean:\d+:\d+: error", output, re.M))
            sorries += len(re.findall(r"declaration uses [`']sorry[`']", output))
            if proc.returncode != 0:
                first = [ln for ln in output.splitlines() if ": error" in ln][:2]
                details.append(f"{path.name}: rc={proc.returncode} " + " | ".join(first))
                # A failed dependency makes every later file's result meaningless.
                break
    ok = not details and errors == 0 and sorries == 0
    return ok, errors, sorries, " ;; ".join(details)


def merge_rung_entries(entries: list[dict]) -> dict:
    """Fold one rung's per-file scans into a single entry.

    Assignment (`rungs[name] = entry`) silently dropped every file but the last
    for a multi-file rung — banned constructs, vacuity sites and undischarged
    hypotheses in the other files would have been invisible to the ratchet while
    the gate still reported green.
    """
    merged: dict = {
        "lines": sum(e["lines"] for e in entries),
        "theorems": sum(e["theorems"] for e in entries),
        "banned": {},
        "vacuity": {},
        "hypotheses": sorted({h for e in entries for h in e["hypotheses"]}),
        "blocks": {},
        "file": entries[0]["file"],
        "files": [e["file"] for e in entries],
    }
    conflicts: list[str] = []
    for entry in entries:
        for key, count in entry["banned"].items():
            merged["banned"][key] = merged["banned"].get(key, 0) + count
        for key, count in entry["vacuity"].items():
            merged["vacuity"][key] = merged["vacuity"].get(key, 0) + count
        for header, digest in entry["blocks"].items():
            if merged["blocks"].setdefault(header, digest) != digest:
                conflicts.append(header)
    if conflicts:
        merged["block_conflicts"] = sorted(set(conflicts))
    return merged


def build_report(paths: list[Path], run_elab: bool, jobs: int) -> dict:
    by_rung: dict[str, list[Path]] = {}
    for path in paths:
        by_rung.setdefault(rung_name(path), []).append(path)

    rungs: dict[str, dict] = {}
    for name, rung_paths in by_rung.items():
        # A rung's `def X : Prop` may be declared in one file and used as a
        # hypothesis in another, so collect them across the whole rung first.
        prop_names = frozenset().union(
            *(
                prop_defs(strip_comments(p.read_text(encoding="utf-8", errors="replace")))
                for p in rung_paths
            )
        )
        entries = []
        for path in rung_paths:
            entry = scan(path, prop_names)
            entry["file"] = str(path.relative_to(REPO_ROOT))
            entries.append(entry)
        rungs[name] = merge_rung_entries(entries)

    if run_elab:
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
            futures = {pool.submit(elaborate_rung, p): n for n, p in by_rung.items()}
            for done, fut in enumerate(concurrent.futures.as_completed(futures), 1):
                name = futures[fut]
                ok, errors, sorries, detail = fut.result()
                entry = rungs[name]
                entry["elaborates"] = ok
                entry["elab_errors"] = errors
                entry["elab_sorries"] = sorries
                if detail:
                    entry["elab_detail"] = detail
                status = "ok" if ok else "FAIL"
                span = f" ({len(by_rung[name])} files)" if len(by_rung[name]) > 1 else ""
                print(f"  [{done:3d}/{len(by_rung)}] {status:4s} {name}{span}", file=sys.stderr)

    composition: dict[str, dict[str, list[str]]] = {}
    for name, entry in rungs.items():
        family = re.sub(r"-(?:sr|cr|progress|whnf-conversion|conversion)$", "", name)
        for header, digest in entry["blocks"].items():
            composition.setdefault(family, {}).setdefault(f"{header}::{digest}", []).append(name)

    assumptions = {
        name: {
            "status": status,
            "rungs": sorted(n for n, e in rungs.items() if name in e["hypotheses"]),
        }
        for name, status in GLOBAL_ASSUMPTIONS.items()
        if any(name in e["hypotheses"] for e in rungs.values())
    }

    return {
        "toolchain": TOOLCHAIN,
        "rung_count": len(rungs),
        "total_lines": sum(e["lines"] for e in rungs.values()),
        "total_theorems": sum(e["theorems"] for e in rungs.values()),
        "vacuity_debt": sum(sum(e["vacuity"].values()) for e in rungs.values()),
        "undischarged_assumption_count": sum(
            1 for a in assumptions.values() if not a["status"].startswith("DISCHARGED")
        ),
        "global_assumptions": assumptions,
        "hypothesis_names": sorted({h for e in rungs.values() for h in e["hypotheses"]}),
        "rungs": rungs,
        "composition_families": composition,
    }


def check(report: dict, ratchet: dict, run_elab: bool) -> list[str]:
    failures: list[str] = []

    for name, entry in sorted(report["rungs"].items()):
        if entry["banned"]:
            failures.append(f"{name}: BANNED CONSTRUCT in code: {entry['banned']}")
        if entry.get("block_conflicts"):
            failures.append(
                f"{name}: files of one rung disagree on composition block(s) "
                f"{entry['block_conflicts']}. A rung defines its calculus once; two "
                "spellings inside one rung break the cross-rung byte-identity discharge."
            )
        if run_elab and not entry.get("elaborates", True):
            failures.append(
                f"{name}: does not elaborate under {TOOLCHAIN} "
                f"({entry.get('elab_errors')} errors, {entry.get('elab_sorries')} sorries)"
                f" {entry.get('elab_detail', '')}"
            )

    old_rungs = ratchet.get("rungs", {})

    # Vacuity may only decrease, and no rung may acquire a new site.
    if report["vacuity_debt"] > ratchet.get("vacuity_debt", 0):
        failures.append(
            f"VACUITY RATCHET: classical-shortcut sites rose "
            f"{ratchet.get('vacuity_debt', 0)} -> {report['vacuity_debt']}. "
            "A `Classical.propDecidable` proof of a `Decidable` target has zero "
            "algorithmic content; prove the decision procedure instead."
        )
    for name, entry in sorted(report["rungs"].items()):
        was = sum(old_rungs.get(name, {}).get("vacuity", {}).values())
        now = sum(entry["vacuity"].values())
        if now > was:
            failures.append(f"{name}: new vacuity site(s) {sorted(entry['vacuity'])} ({was} -> {now})")

    # Hypotheses: a rung may not silently acquire a new undischarged assumption.
    for name, entry in sorted(report["rungs"].items()):
        known = set(old_rungs.get(name, {}).get("hypotheses", []))
        if name not in old_rungs:
            continue
        gained = sorted(set(entry["hypotheses"]) - known)
        if gained:
            failures.append(
                f"{name}: NEW UNDISCHARGED HYPOTHES(ES) {gained}. "
                "Axiom closure cannot see these; register them via --update only "
                "if the rung's claim is restated to expose them."
            )

    # Composition: sibling rungs sharing a family must agree byte-for-byte on the
    # calculus blocks, else the cross-file `cr` discharge is broken.
    for family, groups in sorted(report["composition_families"].items()):
        by_header: dict[str, list[tuple[str, list[str]]]] = {}
        for key, members in groups.items():
            header, digest = key.split("::")
            by_header.setdefault(header, []).append((digest, members))
        for header, variants in sorted(by_header.items()):
            all_members = sorted({m for _, ms in variants for m in ms})
            if len(variants) > 1 and len(all_members) > 1:
                detail = "; ".join(f"{d}={sorted(ms)}" for d, ms in variants)
                failures.append(
                    f"COMPOSITION DRIFT in family '{family}' for `{header}`: {detail}. "
                    "The cross-file confluence discharge relies on these being identical."
                )

    if report["rung_count"] < ratchet.get("rung_count", 0):
        failures.append(
            f"rung count fell {ratchet.get('rung_count')} -> {report['rung_count']} "
            "(a landed rung disappeared)"
        )

    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--update", action="store_true", help="rewrite the ratchet from the current tree")
    parser.add_argument("--fast", action="store_true", help="skip Lean elaboration (static checks only)")
    parser.add_argument("--jobs", type=int, default=4, help="parallel elaboration jobs")
    args = parser.parse_args()

    paths = solution_files()
    if not paths:
        print(f"error: no solution files under {CORPUS_DIR}", file=sys.stderr)
        return 1

    run_elab = not args.fast
    if run_elab:
        print(f"elaborating {len(paths)} solution files under {TOOLCHAIN} ...", file=sys.stderr)
    report = build_report(paths, run_elab, args.jobs)

    if args.update:
        RATCHET_PATH.parent.mkdir(parents=True, exist_ok=True)
        payload = dict(report)
        payload["_notes"] = (
            "Fail-closed ratchet for the Aristotle model-guide corpus. Regenerate with "
            "`python3 scripts/aristotle_corpus_gate.py --update` and stage this file in the "
            "same commit as the corpus change. vacuity_debt must only decrease."
        )
        RATCHET_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote {RATCHET_REL}: {report['rung_count']} rungs, "
              f"{report['total_lines']} lines, {report['total_theorems']} theorems, "
              f"vacuity_debt={report['vacuity_debt']}")
        return 0

    if not RATCHET_PATH.exists():
        print(f"error: {RATCHET_REL} missing; run --update to establish the baseline", file=sys.stderr)
        return 1
    ratchet = json.loads(RATCHET_PATH.read_text(encoding="utf-8"))

    failures = check(report, ratchet, run_elab)

    print(f"corpus: {report['rung_count']} rungs, {report['total_lines']} lines, "
          f"{report['total_theorems']} theorems")
    print(f"vacuity debt: {report['vacuity_debt']} (ratchet {ratchet.get('vacuity_debt', 0)})")
    print(f"\nload-bearing assumptions ({report['undischarged_assumption_count']} undischarged):")
    for name, info in sorted(report["global_assumptions"].items()):
        done = sorted(set(PER_RUNG_DISCHARGE.get(name, {})) & set(info["rungs"]))
        extra = f"  [{len(done)} discharged: {', '.join(done)}]" if done else ""
        walled = sorted(r for (n, r) in OBSTRUCTIONS if n == name and r in info["rungs"])
        if walled:
            extra += f"  [obstruction proved: {', '.join(walled)}]"
        print(f"  {name:14s} {info['status']:38s} {len(info['rungs'])} rungs{extra}")
    if DEGENERATE_RELATIONS:
        print(f"\nDEGENERATE RELATIONS ({len(DEGENERATE_RELATIONS)}) — a theorem over one of "
              f"these says NOTHING:")
        for rung, why in sorted(DEGENERATE_RELATIONS.items()):
            print(f"  {rung}: {why[:96]}…")
    live = {k: v for k, v in OBSTRUCTIONS.items() if k[1] in report["rungs"]}
    if live:
        print(f"\nPROVED OBSTRUCTIONS ({len(live)}) — open, but the cheap routes are ruled out "
              f"(an obstruction is NOT a discharge):")
        for (name, rung), why in sorted(live.items()):
            print(f"  {name} @ {rung}: {why[:96]}…")
    if run_elab:
        bad = [n for n, e in report["rungs"].items() if not e.get("elaborates", True)]
        print(f"elaboration: {report['rung_count'] - len(bad)}/{report['rung_count']} clean")

    if failures:
        print(f"\nFAILED ({len(failures)}):", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        print(
            f"\nIf a change is intended, re-run with --update and stage {RATCHET_REL} "
            "in the same commit.",
            file=sys.stderr,
        )
        return 1

    print("\nOK — corpus gate passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
