#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""
Analyze Mathverse Engine formalization pilot results.
Reads JSON output from arxiv_formalize.py and produces statistics.
"""

import json
import os
import sys
from pathlib import Path


def analyze_paper(data: dict) -> dict:
    """Analyze one paper's formalization results."""
    results = {
        "paper_id": data["paper_id"],
        "title": data["title"],
        "def_total": data["def_total"],
        "def_formalized": data["def_formalized"],
        "thm_total": data["thm_total"],
        "thm_formalized": data["thm_formalized"],
        "total": data["def_total"] + data["thm_total"],
        "formalized": data["def_formalized"] + data["thm_formalized"],
        "error_types": {},
        "lean_code_lengths": [],
    }

    for item in data.get("definitions", []) + data.get("theorems", []):
        for attempt in item.get("attempts", []):
            code = attempt.get("clean_code", "")
            if item.get("success"):
                results["lean_code_lengths"].append(len(code))
            else:
                err = attempt.get("error_message", "unknown")
                # Categorize errors
                if "placeholder" in err or "LLM failed" in err:
                    cat = "llm_failure"
                elif "no Lean declaration" in err:
                    cat = "wrong_structure"
                elif "empty" in err or "sorry-only" in err:
                    cat = "empty_output"
                elif "type checker" in err:
                    cat = "type_check_fail"
                else:
                    cat = "other"
                results["error_types"][cat] = results["error_types"].get(cat, 0) + 1

    return results


def print_report(papers: list):
    """Print aggregate analysis report."""
    total_defs = sum(p["def_total"] for p in papers)
    total_thms = sum(p["thm_total"] for p in papers)
    formalized_defs = sum(p["def_formalized"] for p in papers)
    formalized_thms = sum(p["thm_formalized"] for p in papers)
    total = total_defs + total_thms
    formalized = formalized_defs + formalized_thms

    all_errors = {}
    all_lengths = []
    for p in papers:
        for k, v in p["error_types"].items():
            all_errors[k] = all_errors.get(k, 0) + v
        all_lengths.extend(p["lean_code_lengths"])

    print("=" * 70)
    print("MATHVERSE ENGINE FORMALIZATION PILOT — ANALYSIS REPORT")
    print("=" * 70)
    print()
    print(f"  Papers analyzed:         {len(papers)}")
    print(f"  Papers with statements:  {sum(1 for p in papers if p['total'] > 0)}")
    print()
    print(f"  Definitions:             {formalized_defs}/{total_defs} "
          f"({formalized_defs/max(1,total_defs)*100:.1f}%)")
    print(f"  Theorems:                {formalized_thms}/{total_thms} "
          f"({formalized_thms/max(1,total_thms)*100:.1f}%)")
    print(f"  Total formalized:        {formalized}/{total} "
          f"({formalized/max(1,total)*100:.1f}%)")
    print()

    if all_lengths:
        avg_len = sum(all_lengths) / len(all_lengths)
        max_len = max(all_lengths)
        min_len = min(all_lengths)
        print(f"  Lean code stats:")
        print(f"    Avg length:            {avg_len:.0f} chars")
        print(f"    Min/Max:               {min_len}/{max_len} chars")
    print()

    if all_errors:
        print(f"  Error breakdown:")
        for cat, count in sorted(all_errors.items(), key=lambda x: -x[1]):
            print(f"    {cat:25s} {count}")
    print()

    print("  Per-paper results:")
    for p in papers:
        if p["total"] > 0:
            rate = p["formalized"] / p["total"] * 100
            print(f"    {p['paper_id']:20s} "
                  f"{p['formalized']}/{p['total']} ({rate:.0f}%) "
                  f"— {p['title'][:50]}")

    print()
    print("=" * 70)

    # Return summary dict
    return {
        "papers": len(papers),
        "total_statements": total,
        "formalized": formalized,
        "success_rate": formalized / max(1, total),
        "definitions": {"total": total_defs, "formalized": formalized_defs},
        "theorems": {"total": total_thms, "formalized": formalized_thms},
        "error_breakdown": all_errors,
        "avg_lean_length": sum(all_lengths) / max(1, len(all_lengths)),
    }


def main():
    formalized_dir = sys.argv[1] if len(sys.argv) > 1 else "data/arxiv/formalized"
    json_files = sorted(Path(formalized_dir).glob("*.json"))
    json_files = [f for f in json_files if not f.name.startswith("_")]

    papers = []
    for f in json_files:
        with open(f) as fh:
            data = json.load(fh)
        if "paper_id" in data:
            papers.append(analyze_paper(data))

    if not papers:
        print("No formalization results found.")
        sys.exit(1)

    summary = print_report(papers)

    # Save summary
    summary_path = os.path.join(formalized_dir, "_analysis.json")
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"  Summary saved to: {summary_path}")


if __name__ == "__main__":
    main()
