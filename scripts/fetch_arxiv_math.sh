#!/usr/bin/env bash
# Fetch arXiv PDFs from the public (free, anonymous) Google Cloud mirror
# gs://arxiv-dataset, given a newline-delimited list of HTTPS object URLs.
#
# Usage: fetch_arxiv_math.sh <url-list> <out-dir> [parallelism]
#
# - Resumable: skips any target that already exists and is non-empty.
# - Mirrors the bucket layout under <out-dir> (archive/pdf/yymm/idvN.pdf),
#   so a local path maps back to its arXiv id.
# - Free egress: the arxiv-dataset bucket is a Google Cloud Public Dataset.
#   NOTE: it is a ~2020 snapshot; post-2020 papers must be sourced separately.
set -euo pipefail

URLS="${1:?usage: fetch_arxiv_math.sh <url-list> <out-dir> [parallelism]}"
OUTDIR="${2:?usage: fetch_arxiv_math.sh <url-list> <out-dir> [parallelism]}"
PAR="${3:-16}"
PREFIX="https://storage.googleapis.com/arxiv-dataset/arxiv/"

mkdir -p "$OUTDIR"
total=$(grep -c . "$URLS" || true)
echo "[fetch] $total urls -> $OUTDIR (parallelism=$PAR)"

export OUTDIR PREFIX
fetch_one() {
  url="$1"
  rel="${url#"$PREFIX"}"
  out="$OUTDIR/$rel"
  [ -s "$out" ] && return 0
  mkdir -p "$(dirname "$out")"
  if curl -fsSL --retry 4 --retry-delay 2 --max-time 300 -o "$out.part" "$url"; then
    mv -f "$out.part" "$out"
  else
    rm -f "$out.part"
    echo "FAIL $url" >&2
  fi
}
export -f fetch_one

# shellcheck disable=SC2002
cat "$URLS" | xargs -P "$PAR" -I {} bash -c 'fetch_one "$@"' _ {}

got=$(find "$OUTDIR" -name '*.pdf' -type f | wc -l | tr -d ' ')
echo "[fetch] done. local pdf count: $got"
