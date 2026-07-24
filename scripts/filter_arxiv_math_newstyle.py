#!/usr/bin/env python3
"""Build the new-style (post-2007, NNNN.NNNNN) arXiv math PDF URL list.

Category lives only in the metadata for new-style ids, so we:
  1. stream the metadata (JSON-lines), collecting ids whose category set
     intersects math (math.*, math-ph),
  2. filter the bucket manifest's arxiv/arxiv/pdf/*.pdf entries to those ids,
     keeping the latest version per paper,
  3. emit HTTPS object URLs.

Usage: filter_arxiv_math_newstyle.py <metadata.json> <manifest.txt> <out-urls.txt>
"""
import json
import re
import sys

GS = "gs://arxiv-dataset/arxiv/arxiv/pdf/"
HTTPS = "https://storage.googleapis.com/arxiv-dataset/arxiv/arxiv/pdf/"
VER = re.compile(r"^(.*?)v(\d+)\.pdf$")


def cat_list(rec) -> list:
    """`categories` may be a list (metadata-v5) or a space-separated string."""
    c = rec.get("categories")
    if isinstance(c, list):
        return c
    if isinstance(c, str):
        return c.split()
    return []


def is_math(cats: list) -> bool:
    for c in cats:
        if c.startswith("math.") or c == "math-ph" or c == "math":
            return True
    return False


def main() -> int:
    meta, manifest, out = sys.argv[1], sys.argv[2], sys.argv[3]

    math_ids = set()
    bad = 0
    with open(meta, encoding="utf-8", errors="replace") as f:
        for line in f:
            line = line.strip().rstrip(",")
            if not line or line in "[]":
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                bad += 1
                continue
            cats = cat_list(rec)
            if cats and is_math(cats):
                rid = (rec.get("id") or "").strip()
                if rid and "/" not in rid:  # new-style only; old handled by path
                    math_ids.add(rid)
    print(f"[filter] math new-style ids in metadata: {len(math_ids)} (json-parse misses: {bad})")

    best = {}  # base path (no version) -> (version, full gs path)
    scanned = matched = 0
    with open(manifest, encoding="utf-8", errors="replace") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.startswith(GS) or not line.endswith(".pdf"):
                continue
            scanned += 1
            fname = line[len(GS):]              # e.g. 0704/0704.0001v2.pdf
            base = fname.split("/", 1)[1] if "/" in fname else fname
            m = VER.match(base)
            paper_id = m.group(1) if m else base[:-4]
            ver = int(m.group(2)) if m else 0
            if paper_id not in math_ids:
                continue
            matched += 1
            key = line[: line.rfind("v")] if m else line[:-4]
            if key not in best or ver > best[key][0]:
                best[key] = (ver, line)
    print(f"[filter] new-style pdf files scanned: {scanned}; math matches: {matched}; unique papers: {len(best)}")

    urls = sorted(p.replace(GS, HTTPS) for (_, p) in best.values())
    with open(out, "w", encoding="utf-8") as f:
        f.write("\n".join(urls) + "\n")
    print(f"[filter] wrote {len(urls)} urls -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
