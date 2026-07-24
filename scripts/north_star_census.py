#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Authoritative, reproducible census of the north-star metric.

North star = novel theorems conjectured, proven on Clean's own substrate,
kernel-verified, and graduated into Mathverse with a full attestation. The
count had no single source of truth (the roadmap said 13, a run report said 0,
memory said ~60) because the graduation tree under data/graduation/ accumulated
overlapping, replica, and empty-baseline artifacts. This script scans every
*.graduation.json, deduplicates by canonical statement_hash, segments by what
is actually defensible, and prints ONE reconciled set of numbers.

A theorem is "graduated" iff its record has, all four:
  kernel.verdict == "kernel_verified"
  axiom_closure.foundational_only == true   (zero domain axioms)
  novelty.verdict == "new"
  accepted == true
"Defensible" additionally requires the artifact's corpus_pin to be the real
released corpus (default mathverse-v1.2.0) — novelty against an empty/local
baseline is meaningless and is reported separately.

Pure-stdlib; reads only checked-in JSON. Run: python3 scripts/north_star_census.py
"""
from __future__ import annotations

import glob
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
GRADUATION_DIR = REPO_ROOT / "data" / "graduation"
REAL_CORPUS = "mathverse-v1.2.0"

# Namespaces that are standard-library / foundational re-formalizations — "novel"
# only in the weak statement-hash-absence sense, NOT new mathematics. Kept honest
# and explicit so the headline cannot quietly inflate on arithmetic lemmas.
REFORMALIZATION_PREFIXES = {"Int", "Rat", "Fin", "Nat", "if_pos", "if_neg"}


def is_graduated(t: dict) -> bool:
    return (
        t.get("kernel", {}).get("verdict") == "kernel_verified"
        and t.get("axiom_closure", {}).get("foundational_only") is True
        and t.get("novelty", {}).get("verdict") == "new"
        and t.get("accepted") is True
    )


def main() -> int:
    files = sorted(glob.glob(str(GRADUATION_DIR / "**" / "*.graduation.json"), recursive=True))
    if not files:
        print(f"no graduation artifacts under {GRADUATION_DIR}", file=sys.stderr)
        return 1

    real: dict[str, str] = {}   # statement_hash -> name (real-corpus-pinned graduated)
    empty: dict[str, str] = {}  # statement_hash -> name (empty/local-baseline graduated)
    by_dir: dict[str, set] = defaultdict(set)
    per_file = []

    for f in files:
        try:
            d = json.loads(Path(f).read_text())
        except (OSError, json.JSONDecodeError) as exc:
            print(f"FAIL: cannot read {f}: {exc}", file=sys.stderr)
            return 1
        pin = d.get("corpus_pin", {}).get("mathverse_release", "?")
        is_real = pin == REAL_CORPUS
        grad = [t for t in d.get("theorems", []) if is_graduated(t)]
        rel = f[len(str(REPO_ROOT)) + 1 :]
        top_dir = Path(rel).relative_to("data/graduation").parts[0]
        for t in grad:
            sh = t["statement_hash"]
            (real if is_real else empty)[sh] = t["name"]
            if is_real:
                by_dir[top_dir].add(sh)
        per_file.append((rel, pin if is_real else f"NOT-REAL ({pin[:24]})", len(d.get("theorems", [])), len(grad)))

    research = {sh: n for sh, n in real.items() if n.split(".")[0] not in REFORMALIZATION_PREFIXES}
    reform = {sh: n for sh, n in real.items() if n.split(".")[0] in REFORMALIZATION_PREFIXES}

    print("=" * 78)
    print("NORTH-STAR CENSUS  (data/graduation/, dedup by statement_hash)")
    print("=" * 78)
    print(f"\nAUTHORITATIVE corpus-pinned ({REAL_CORPUS}) distinct graduated : {len(real)}")
    print(f"  of which NN-verification research theorems (NNVerify/Crownproof…): {len(research)}")
    print(f"  of which standard-library re-formalizations (Int/Rat/Fin/Nat/…) : {len(reform)}")
    print(f"\nEMPTY/local-baseline graduated (novelty NOT vs real corpus)      : {len(empty)}")
    print(f"  (of those, also re-graduated against the real corpus)          : {len(set(empty) & set(real))}")

    print("\n--- real-corpus distinct, by namespace ---")
    for k, v in Counter(n.split(".")[0] for n in real.values()).most_common():
        tag = "  [re-formalization]" if k in REFORMALIZATION_PREFIXES else ""
        print(f"  {k:14} {v:4}{tag}")

    print("\n--- real-corpus distinct, by source dir ---")
    for d, hs in sorted(by_dir.items()):
        print(f"  {d:28} {len(hs):4}")

    print("\n--- per-artifact (theorems / graduated) ---")
    for rel, pin, tot, g in per_file:
        print(f"  {rel[14:]:62} {tot:4}/{g:<4} {pin}")

    print("\nHEADLINE GUIDANCE: report the corpus-pinned distinct count")
    print(f"  ({len(real)}) WITH the research/re-formalization split ({len(research)}/{len(reform)}).")
    print("  The historical '0 -> 13' was the qcore crown-proofs first movement only.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
