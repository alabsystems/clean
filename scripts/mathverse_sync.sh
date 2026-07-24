#!/usr/bin/env bash
# Sync locally-computed Metamath kernel-verified shards to the CENTRAL mathverse
# store (GitHub Releases on this repo). The shards themselves are gitignored
# (released as assets, per CLAUDE.md), so this is how they reach the central store.
#
# Local store : data/mathverse-shards/*.mathverse   (persistent, gitignored)
# Central store: GitHub Release `mathverse-metamath-cleankernel-<VERSION>`
#
# Usage: scripts/mathverse_sync.sh <VERSION> "<title>" "<notes>"
#   e.g. scripts/mathverse_sync.sh v1.8 "5,200 kernel-verified" "+segmented full-corpus run"
set -euo pipefail

VERSION="${1:?usage: mathverse_sync.sh <VERSION> <title> [notes]}"
TITLE="${2:-Mathverse — Metamath Clean-kernel-verified ${VERSION}}"
NOTES="${3:-Kernel-verified Metamath theorems (set.mm) as .mathverse shards. Trust: KernelVerified, AxiomProfile AXIOMATIZED (rests on Metamath \$a axioms).}"

STORE="data/mathverse-shards"
TAG="mathverse-metamath-cleankernel-${VERSION}"

cd "$(git rev-parse --show-toplevel)"
shopt -s nullglob
shards=("$STORE"/*.mathverse)
if [ ${#shards[@]} -eq 0 ]; then
  echo "no shards in $STORE — nothing to sync"; exit 1
fi
# include the .json sidecars if present
assets=()
for s in "${shards[@]}"; do
  assets+=("$s")
  [ -f "$s.json" ] && assets+=("$s.json")
done

total=$(du -ch "${shards[@]}" | tail -1 | awk '{print $1}')
echo "syncing ${#shards[@]} shard(s) ($total) → central store as release $TAG"

if gh release view "$TAG" >/dev/null 2>&1; then
  gh release upload "$TAG" "${assets[@]}" --clobber
  echo "updated existing release $TAG"
else
  gh release create "$TAG" "${assets[@]}" --title "$TITLE" --notes "$NOTES"
  echo "created release $TAG"
fi
