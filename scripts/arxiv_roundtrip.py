#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""
Mathverse Engine roundtrip validation (Layer 3 of Semantic Alignment Engine).

Takes formalized JSON files and back-translates Lean→NL via LLM,
then computes similarity with the original LaTeX statement.

Usage:
    python3 scripts/arxiv_roundtrip.py [formalized_dir] [--limit N]
"""

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


# ---------------------------------------------------------------------------
# Similarity scoring
# ---------------------------------------------------------------------------

def normalize_math_text(text: str) -> str:
    """Normalize math text for comparison."""
    text = text.lower()
    # Remove LaTeX commands
    text = re.sub(r'\\[a-zA-Z]+\{([^}]*)\}', r'\1', text)
    text = re.sub(r'\\[a-zA-Z]+', '', text)
    # Remove $ delimiters
    text = text.replace('$', '')
    # Normalize whitespace
    text = re.sub(r'\s+', ' ', text).strip()
    return text


def extract_key_concepts(text: str) -> set:
    """Extract key mathematical concepts from text."""
    normalized = normalize_math_text(text)
    # Split into words, keep only meaningful ones
    words = set(normalized.split())
    # Remove common stopwords
    stopwords = {'the', 'a', 'an', 'is', 'are', 'was', 'were', 'be', 'been',
                 'being', 'have', 'has', 'had', 'do', 'does', 'did', 'will',
                 'would', 'could', 'should', 'may', 'might', 'must', 'shall',
                 'can', 'that', 'this', 'these', 'those', 'it', 'its',
                 'of', 'in', 'on', 'at', 'to', 'for', 'with', 'by', 'from',
                 'and', 'or', 'but', 'if', 'then', 'than', 'so', 'as',
                 'we', 'let', 'where', 'such', 'there', 'every', 'all',
                 'any', 'some', 'no', 'not', 'each'}
    return words - stopwords


def concept_overlap_score(original: str, roundtrip: str) -> float:
    """Compute concept overlap score between original and roundtrip."""
    orig_concepts = extract_key_concepts(original)
    rt_concepts = extract_key_concepts(roundtrip)

    if not orig_concepts or not rt_concepts:
        return 0.0

    overlap = orig_concepts & rt_concepts
    # Jaccard similarity
    union = orig_concepts | rt_concepts
    return len(overlap) / len(union) if union else 0.0


def structural_similarity(original_latex: str, roundtrip_nl: str) -> float:
    """Compute structural similarity between original LaTeX and roundtrip NL.

    Checks for preservation of:
    - Quantifier structure (∀, ∃)
    - Key math objects (groups, rings, etc.)
    - Logical connectives (implies, iff, and, or)
    """
    score = 0.0
    checks = 0

    # Quantifier preservation
    orig_lower = original_latex.lower()
    rt_lower = roundtrip_nl.lower()

    for concept_pair in [
        # (original marker, roundtrip markers)
        (r'\forall', ['for all', 'for every', 'for each', '∀', 'forall']),
        (r'\exists', ['there exists', 'there is', '∃', 'exists']),
        ('implies', ['implies', 'then', '→', 'if...then']),
        ('iff', ['if and only if', 'iff', '↔']),
        ('injective', ['injective', 'one-to-one', '1-1']),
        ('surjective', ['surjective', 'onto']),
        ('continuous', ['continuous']),
        ('compact', ['compact']),
        ('prime', ['prime']),
        ('finite', ['finite']),
        ('infinite', ['infinite']),
    ]:
        orig_marker, rt_markers = concept_pair
        checks += 1
        orig_has = orig_marker in orig_lower
        rt_has = any(m in rt_lower for m in rt_markers)
        if orig_has == rt_has:
            score += 1.0

    return score / max(1, checks)


def combined_similarity(original_latex: str, roundtrip_nl: str) -> float:
    """Combined similarity metric."""
    concept = concept_overlap_score(original_latex, roundtrip_nl)
    structural = structural_similarity(original_latex, roundtrip_nl)
    # Weighted average: concepts 0.6, structure 0.4
    return 0.6 * concept + 0.4 * structural


# ---------------------------------------------------------------------------
# LLM roundtrip
# ---------------------------------------------------------------------------

def back_translate(lean_code: str) -> str:
    """Back-translate Lean code to natural language via LLM."""
    prompt = f"""Describe the following Lean 4 code in plain mathematical English.
Focus on what the statement says mathematically, not the Lean syntax.
Be concise (1-3 sentences). Do NOT include any Lean code in your response.

```lean
{lean_code}
```

Mathematical description:"""

    prompt_path = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
            f.write(prompt)
            prompt_path = f.name

        result = subprocess.run(
            f'cat "{prompt_path}" | AI Model -p -',
            shell=True,
            capture_output=True, text=True, timeout=60,
        )
        if prompt_path and os.path.exists(prompt_path):
            os.unlink(prompt_path)

        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip()

    except (FileNotFoundError, subprocess.TimeoutExpired):
        if prompt_path and os.path.exists(prompt_path):
            os.unlink(prompt_path)

    return ""


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

def validate_paper(json_path: str, verbose: bool = False) -> dict:
    """Run roundtrip validation on one formalized paper."""
    with open(json_path) as f:
        data = json.load(f)

    paper_id = data.get("paper_id", "?")
    results = []
    total = 0
    high_sim = 0  # similarity >= 0.5
    validated = 0

    for kind in ("definitions", "theorems"):
        for item in data.get(kind, []):
            if not item.get("success") or not item.get("best_clean"):
                continue

            total += 1
            lean_code = item["best_clean"]
            original = item.get("original_latex", "")

            # Back-translate
            roundtrip_nl = back_translate(lean_code)
            if not roundtrip_nl:
                results.append({
                    "label": item.get("label", "?"),
                    "kind": item.get("kind", kind.rstrip("s")),
                    "roundtrip_nl": "",
                    "similarity": 0.0,
                    "status": "llm_failed",
                })
                continue

            validated += 1
            sim = combined_similarity(original, roundtrip_nl)
            if sim >= 0.5:
                high_sim += 1

            result = {
                "label": item.get("label", "?"),
                "kind": item.get("kind", kind.rstrip("s")),
                "roundtrip_nl": roundtrip_nl,
                "similarity": round(sim, 3),
                "status": "pass" if sim >= 0.5 else "low_similarity",
            }
            results.append(result)

            if verbose:
                status = "PASS" if sim >= 0.5 else "LOW "
                print(f"    {status} {result['label']:30s} sim={sim:.3f}")
                if sim < 0.5:
                    print(f"         Original: {original[:80]}...")
                    print(f"         Roundtrip: {roundtrip_nl[:80]}...")

    return {
        "paper_id": paper_id,
        "total_checked": total,
        "validated": validated,
        "high_similarity": high_sim,
        "results": results,
    }


def run_roundtrip(formalized_dir: str, limit: int = 0, verbose: bool = False):
    """Run roundtrip validation on all formalized papers."""
    json_files = sorted(Path(formalized_dir).glob("*.json"))
    json_files = [f for f in json_files if not f.name.startswith("_")]

    if limit:
        json_files = json_files[:limit]

    print("=" * 70)
    print("MATHVERSE ENGINE — ROUNDTRIP VALIDATION (Layer 3)")
    print("=" * 70)
    print(f"  Input:      {formalized_dir}")
    print(f"  Papers:     {len(json_files)}")
    print()

    all_results = []
    total_checked = 0
    total_high = 0
    total_validated = 0

    for json_path in json_files:
        paper = validate_paper(str(json_path), verbose=verbose)
        all_results.append(paper)
        total_checked += paper["total_checked"]
        total_high += paper["high_similarity"]
        total_validated += paper["validated"]

        if paper["total_checked"] > 0:
            rate = paper["high_similarity"] / paper["total_checked"] * 100
            print(f"  {json_path.stem:25s} {paper['high_similarity']}/{paper['total_checked']} "
                  f"({rate:.0f}%) semantic match")

    print()
    print("=" * 70)
    print("ROUNDTRIP VALIDATION SUMMARY")
    print("=" * 70)
    rate = total_high / max(1, total_checked) * 100
    print(f"  Statements checked:      {total_checked}")
    print(f"  LLM back-translated:     {total_validated}")
    print(f"  High similarity (≥0.5):  {total_high} ({rate:.1f}%)")
    print()

    # Save results
    summary = {
        "total_checked": total_checked,
        "total_validated": total_validated,
        "high_similarity": total_high,
        "similarity_rate": total_high / max(1, total_checked),
        "papers": all_results,
    }

    out_path = os.path.join(formalized_dir, "_roundtrip.json")
    with open(out_path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"  Results saved to: {out_path}")


def main():
    formalized_dir = "data/arxiv/formalized"
    limit = 0
    verbose = False

    skip_next = False
    for i, arg in enumerate(sys.argv[1:]):
        if skip_next:
            skip_next = False
            continue
        if arg == "--verbose" or arg == "-v":
            verbose = True
        elif arg == "--limit" and i + 2 < len(sys.argv):
            limit = int(sys.argv[i + 2])
            skip_next = True
        elif not arg.startswith("-"):
            formalized_dir = arg

    run_roundtrip(formalized_dir, limit=limit, verbose=verbose)


if __name__ == "__main__":
    main()
