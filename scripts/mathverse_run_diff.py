#!/usr/bin/env python3
"""Diff two `clean mathverse stamp-verified` runs — the paragon improvement loop.

Each import pass should *measurably* improve. This compares two runs and reports
exactly what changed: which constants newly verify, which regressed, and how the
per-cause failure histograms moved — so a re-import after a kernel-completeness fix
shows its delta and points at the next gap.

Inputs are either:
  * a stamp-verified `--manifest` JSON (has `kernel_verified_names`), or
  * a stamp-verified `--json` summary (has the count histograms), or
  * a run's out-dir (we look for `manifest.json` / `*.json` inside).

Usage:
    mathverse_run_diff.py OLD NEW [--names] [--json]

Exit status is always 0; this is a reporting tool, not a gate.
"""
import json
import sys
import os
from pathlib import Path


def _load(path):
    """Return a dict from a manifest/summary JSON, tolerant of run dirs."""
    p = Path(path)
    if p.is_dir():
        for cand in ("kv_manifest.json", "manifest.json"):
            if (p / cand).exists():
                p = p / cand
                break
        else:
            js = sorted(p.glob("*.json"))
            if not js:
                sys.exit(f"no JSON found under {path}")
            p = js[0]
    text = p.read_text(errors="ignore")
    # tolerate a trailing/leading log line: grab the largest {...} span
    s, e = text.find("{"), text.rfind("}")
    if s < 0 or e < 0:
        sys.exit(f"no JSON object in {p}")
    return json.loads(text[s : e + 1])


def _verified_names(d):
    for k in ("kernel_verified_names", "verified_names"):
        v = d.get(k)
        if isinstance(v, list):
            return set(v)
    return None


def _hist(d, key):
    h = d.get(key)
    return h if isinstance(h, dict) else {}


def main(argv):
    args = [a for a in argv if not a.startswith("--")]
    flags = {a for a in argv if a.startswith("--")}
    if len(args) != 2:
        sys.exit("usage: mathverse_run_diff.py OLD NEW [--names] [--json]")
    old, new = _load(args[0]), _load(args[1])

    def cnt(d, k):
        return d.get(k, 0) or 0

    report = {
        "kernel_verified": {"old": cnt(old, "kernel_verified"), "new": cnt(new, "kernel_verified")},
        "total": {"old": cnt(old, "total"), "new": cnt(new, "total")},
        "axiom_fallback": {"old": cnt(old, "axiom_fallback"), "new": cnt(new, "axiom_fallback")},
        "failed": {"old": cnt(old, "failed"), "new": cnt(new, "failed")},
    }
    report["kernel_verified"]["delta"] = report["kernel_verified"]["new"] - report["kernel_verified"]["old"]

    # per-cause histogram deltas
    cause_deltas = {}
    for hk in ("axiom_fallback_by_class", "failed_by_class"):
        oh, nh = _hist(old, hk), _hist(new, hk)
        keys = sorted(set(oh) | set(nh))
        cause_deltas[hk] = {
            k: {"old": oh.get(k, 0), "new": nh.get(k, 0), "delta": nh.get(k, 0) - oh.get(k, 0)}
            for k in keys
            if (nh.get(k, 0) - oh.get(k, 0)) != 0
        }
    report["cause_deltas"] = cause_deltas

    # name-level diff (only if both runs carry verified-name lists)
    on, nn = _verified_names(old), _verified_names(new)
    newly = regressed = None
    if on is not None and nn is not None:
        newly = sorted(nn - on)
        regressed = sorted(on - nn)
        report["newly_verified_count"] = len(newly)
        report["regressed_count"] = len(regressed)

    if "--json" in flags:
        print(json.dumps(report, indent=2))
        return 0

    kv = report["kernel_verified"]
    pct = lambda d: (100 * d["kernel_verified"] / d["total"]) if d.get("total") else 0.0
    print("=== mathverse run diff ===")
    print(f"kernel_verified: {kv['old']} -> {kv['new']}  (delta {kv['delta']:+d})")
    print(f"  rate: {pct(old):.1f}% -> {pct(new):.1f}%   total {report['total']['old']} -> {report['total']['new']}")
    print(f"  axiom_fallback: {report['axiom_fallback']['old']} -> {report['axiom_fallback']['new']}")
    print(f"  failed: {report['failed']['old']} -> {report['failed']['new']}")
    for hk, deltas in cause_deltas.items():
        if deltas:
            print(f"  {hk} (changed causes):")
            for k, v in sorted(deltas.items(), key=lambda kv: kv[1]["delta"]):
                print(f"    {k}: {v['old']} -> {v['new']}  ({v['delta']:+d})")
    if newly is not None:
        print(f"newly verified: {len(newly)}   regressed: {len(regressed)}")
        if "--names" in flags:
            for n in newly[:200]:
                print(f"  + {n}")
            for n in regressed[:200]:
                print(f"  - {n}")
            if len(newly) > 200 or len(regressed) > 200:
                print(f"  ... ({len(newly)} new / {len(regressed)} regressed total; showing first 200 each)")
    else:
        print("(no verified-name lists in both inputs — pass --manifest runs for name-level diff)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
