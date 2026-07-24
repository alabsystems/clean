#!/usr/bin/env python3
"""Harvest current arXiv math metadata for free via OAI-PMH.

Fills the 2020-snapshot -> present gap: the free Google mirror's PDFs stop at
2020-11, but arXiv's OAI-PMH endpoint serves complete, current metadata at no
cost. This gives the exact worklist of math paper IDs (and categories) from a
given date forward; PDFs for those IDs can then be fetched via S3 (paid bulk)
or politely per-paper later.

Saves raw OAI XML pages under <out-dir>/page_NNNNN.xml and is resumable: it
records the last resumptionToken in <out-dir>/.token so a re-run continues.

Usage: harvest_arxiv_oai.py <out-dir> [from-date YYYY-MM-DD] [set]
"""
import os
import sys
import time
import urllib.parse
import urllib.request

BASE = "https://export.arxiv.org/oai2"
UA = "clean-mathverse-harvester/1.0 (research; contact: repo owner)"


def fetch(url: str, tries: int = 8) -> str:
    for attempt in range(tries):
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                return r.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            if e.code == 503:
                wait = int(e.headers.get("Retry-After", "20"))
                print(f"  503; sleeping {wait}s (Retry-After)")
                time.sleep(wait)
                continue
            raise
        except Exception as e:  # transient network
            wait = 10 * (attempt + 1)
            print(f"  err {e}; retry in {wait}s")
            time.sleep(wait)
    raise SystemExit("too many failures")


def extract_token(xml: str):
    i = xml.find("<resumptionToken")
    if i < 0:
        return None
    j = xml.find(">", i)
    k = xml.find("</resumptionToken>", j)
    if j < 0 or k < 0:
        return None
    tok = xml[j + 1:k].strip()
    return tok or None


def main() -> int:
    out = sys.argv[1] if len(sys.argv) > 1 else "data/corpora/arxiv/metadata_current"
    frm = sys.argv[2] if len(sys.argv) > 2 else "2020-11-01"
    setspec = sys.argv[3] if len(sys.argv) > 3 else "math"
    os.makedirs(out, exist_ok=True)
    tokfile = os.path.join(out, ".token")

    token = None
    if os.path.exists(tokfile):
        token = open(tokfile).read().strip() or None
        print(f"resuming from saved token: {token[:40]}...")

    page = len([f for f in os.listdir(out) if f.startswith("page_")])
    records = 0
    while True:
        if token:
            url = f"{BASE}?verb=ListRecords&resumptionToken={urllib.parse.quote(token)}"
        else:
            url = (f"{BASE}?verb=ListRecords&metadataPrefix=arXiv"
                   f"&set={urllib.parse.quote(setspec)}&from={frm}")
        xml = fetch(url)
        page += 1
        path = os.path.join(out, f"page_{page:05d}.xml")
        open(path, "w", encoding="utf-8").write(xml)
        records += xml.count("<record>")
        token = extract_token(xml)
        open(tokfile, "w").write(token or "")
        print(f"page {page}: ~{records} records cumulative; token={'yes' if token else 'DONE'}")
        if not token:
            break
        time.sleep(3)  # be polite
    print(f"harvest complete: {page} pages, ~{records} records -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
