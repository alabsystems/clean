#!/usr/bin/env python3
"""Diff two `clean mathverse stamp-verified` runs — the paragon improvement loop.

Each import pass should *measurably* improve. This compares two runs and reports
exactly what changed: which constants newly verify, which regressed, and how the
per-cause failure histograms moved — so a re-import after a kernel-completeness fix
shows its delta and points at the next gap.

Inputs are either:
  * a stamp-verified `--manifest` JSON (a schema-2 `kernel-verified.json`), or
  * a stamp-verified `--json` summary (has the count histograms), or
  * a run's out-dir (we look for `manifest.json` / `*.json` inside).

Both kinds are read through scripts/acceptance_manifest.py (P6 reader R12): a
schema-1 or identity-less manifest, a pre-P6 summary and any reference-tier
record are refused, and two manifests are compared only when they name the
same checker (theory, entry, discipline, imports and the settings that change
which names are accepted; the build may differ). Every count is development
tier: the legacy checker's acceptances, never a label.

Usage:
    mathverse_run_diff.py OLD NEW [--names] [--json]

Exit status 0 for a report, 1 for a refused input; this is a reporting tool,
not a gate.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from acceptance_manifest import Refused, checker_key, validate_manifest, validate_summary  # noqa: E402


def _load(path):
    """Return a normalized, validated record from a manifest/summary JSON."""
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
    data = json.loads(text[s : e + 1])
    try:
        if "schema_version" in data:
            d = validate_manifest(data)
            return {"accepted": d["accepted"], "total": d["total_constants"],
                    "axiom_fallback": d["axiom_fallback"], "failed": d["failed"],
                    "names": set(d["accepted_names"]), "identity": d["identity"]}
        d = validate_summary(data)
        return {"accepted": d["accepted"], "total": d["total"],
                "axiom_fallback": d.get("axiom_fallback", 0), "failed": d.get("failed", 0),
                "axiom_fallback_by_class": d.get("axiom_fallback_by_class"),
                "failed_by_class": d.get("failed_by_class"), "names": None, "identity": None}
    except Refused as error:
        print(f"mathverse_run_diff: refused {p}: {error}", file=sys.stderr)
        sys.exit(1)


def _hist(d, key):
    h = d.get(key)
    return h if isinstance(h, dict) else {}


def main(argv):
    args = [a for a in argv if not a.startswith("--")]
    flags = {a for a in argv if a.startswith("--")}
    if len(args) != 2:
        sys.exit("usage: mathverse_run_diff.py OLD NEW [--names] [--json]")
    old, new = _load(args[0]), _load(args[1])
    if old["identity"] is not None and new["identity"] is not None:
        if checker_key(old["identity"]) != checker_key(new["identity"]):
            print("mathverse_run_diff: refused: the two manifests name different checkers "
                  "(theory, entry, discipline, imports or accepting settings); their name sets "
                  "are not comparable", file=sys.stderr)
            return 1

    def cnt(d, k):
        return d.get(k, 0) or 0

    report = {
        "tier": "development",
        "accepted": {"old": cnt(old, "accepted"), "new": cnt(new, "accepted")},
        "total": {"old": cnt(old, "total"), "new": cnt(new, "total")},
        "axiom_fallback": {"old": cnt(old, "axiom_fallback"), "new": cnt(new, "axiom_fallback")},
        "failed": {"old": cnt(old, "failed"), "new": cnt(new, "failed")},
    }
    report["accepted"]["delta"] = report["accepted"]["new"] - report["accepted"]["old"]

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
    on, nn = old["names"], new["names"]
    newly = regressed = None
    if on is not None and nn is not None:
        newly = sorted(nn - on)
        regressed = sorted(on - nn)
        report["newly_accepted_count"] = len(newly)
        report["regressed_count"] = len(regressed)

    if "--json" in flags:
        print(json.dumps(report, indent=2))
        return 0

    kv = report["accepted"]
    pct = lambda d: (100 * d["accepted"] / d["total"]) if d.get("total") else 0.0
    print("=== mathverse run diff (development tier: legacy-checker acceptances, no label) ===")
    print(f"accepted: {kv['old']} -> {kv['new']}  (delta {kv['delta']:+d})")
    print(f"  rate: {pct(old):.1f}% -> {pct(new):.1f}%   total {report['total']['old']} -> {report['total']['new']}")
    print(f"  axiom_fallback: {report['axiom_fallback']['old']} -> {report['axiom_fallback']['new']}")
    print(f"  failed: {report['failed']['old']} -> {report['failed']['new']}")
    for hk, deltas in cause_deltas.items():
        if deltas:
            print(f"  {hk} (changed causes):")
            for k, v in sorted(deltas.items(), key=lambda kv: kv[1]["delta"]):
                print(f"    {k}: {v['old']} -> {v['new']}  ({v['delta']:+d})")
    if newly is not None:
        print(f"newly accepted: {len(newly)}   regressed: {len(regressed)}")
        if "--names" in flags:
            for n in newly[:200]:
                print(f"  + {n}")
            for n in regressed[:200]:
                print(f"  - {n}")
            if len(newly) > 200 or len(regressed) > 200:
                print(f"  ... ({len(newly)} new / {len(regressed)} regressed total; showing first 200 each)")
    else:
        print("(no accepted-name lists in both inputs — pass --manifest runs for name-level diff)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
