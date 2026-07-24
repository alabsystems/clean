# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Compare benchmark baseline vs candidate and report regressions.

Usage:
    python3 scripts/bench_compare.py BASELINE CANDIDATE OUTPUT [THRESHOLD]

Arguments:
    BASELINE    Path to baseline JSON
    CANDIDATE   Path to candidate JSON
    OUTPUT      Path to write regression report JSON
    THRESHOLD   Regression threshold percentage (default: 10)

Exit codes:
    0  No regressions detected
    1  Regressions found (>threshold% slower)
    2  Missing input files
"""

import json
import logging
import sys

log = logging.getLogger("bench_compare")


def classify_benchmarks(base_benchmarks, cand_benchmarks, threshold):
    """Classify benchmark changes into regressions, improvements, unchanged."""
    regressions = []
    improvements = []
    unchanged = []
    new_benchmarks = []

    for key, cand_val in sorted(cand_benchmarks.items()):
        cand_ns = cand_val["ns_per_iter"]
        if key not in base_benchmarks:
            new_benchmarks.append({"name": key, "ns_per_iter": cand_ns})
            continue

        base_ns = base_benchmarks[key]["ns_per_iter"]
        if base_ns == 0:
            continue

        pct_change = ((cand_ns - base_ns) / base_ns) * 100
        entry = {
            "name": key,
            "baseline_ns": base_ns,
            "candidate_ns": cand_ns,
            "change_pct": round(pct_change, 2),
        }

        if pct_change > threshold:
            regressions.append(entry)
        elif pct_change < -threshold:
            improvements.append(entry)
        else:
            unchanged.append(entry)

    return regressions, improvements, unchanged, new_benchmarks


def log_report(report):
    """Log human-readable regression report."""
    threshold = report["threshold_pct"]
    regressions = report["regressions"]

    log.info(
        "Comparison: %s -> %s", report["baseline_commit"], report["candidate_commit"]
    )
    log.info(
        "Regressions (>%d%% slower): %d", threshold, report["summary"]["regressions"]
    )
    log.info(
        "Improvements (>%d%% faster): %d", threshold, report["summary"]["improvements"]
    )
    log.info("Unchanged: %d", report["summary"]["unchanged"])
    log.info("New benchmarks: %d", report["summary"]["new"])

    if regressions:
        log.warning("REGRESSIONS:")
        for r in regressions:
            log.warning(
                "  %s: %dns -> %dns (+%s%%)",
                r["name"],
                r["baseline_ns"],
                r["candidate_ns"],
                r["change_pct"],
            )


def main():
    logging.basicConfig(
        level=logging.INFO,
        format="[bench] %(message)s",
    )

    if len(sys.argv) < 4:
        log.error("Usage: bench_compare.py BASELINE CANDIDATE OUTPUT [THRESHOLD]")
        sys.exit(2)

    baseline_path = sys.argv[1]
    candidate_path = sys.argv[2]
    output_path = sys.argv[3]
    threshold = int(sys.argv[4]) if len(sys.argv) > 4 else 10

    with open(baseline_path) as f:
        baseline = json.load(f)
    with open(candidate_path) as f:
        candidate = json.load(f)

    regressions, improvements, unchanged, new_benchmarks = classify_benchmarks(
        baseline.get("benchmarks", {}),
        candidate.get("benchmarks", {}),
        threshold,
    )

    report = {
        "baseline_commit": baseline.get("git_commit", "unknown"),
        "candidate_commit": candidate.get("git_commit", "unknown"),
        "baseline_cargo_build_jobs": baseline.get("cargo_build_jobs", "unknown"),
        "candidate_cargo_build_jobs": candidate.get("cargo_build_jobs", "unknown"),
        "baseline_cargo_command": baseline.get("cargo_command", "unknown"),
        "candidate_cargo_command": candidate.get("cargo_command", "unknown"),
        "threshold_pct": threshold,
        "summary": {
            "regressions": len(regressions),
            "improvements": len(improvements),
            "unchanged": len(unchanged),
            "new": len(new_benchmarks),
        },
        "regressions": regressions,
        "improvements": improvements,
        "new_benchmarks": new_benchmarks,
    }

    with open(output_path, "w") as f:
        json.dump(report, f, indent=2, sort_keys=True)

    log_report(report)
    sys.exit(1 if regressions else 0)


if __name__ == "__main__":
    main()
