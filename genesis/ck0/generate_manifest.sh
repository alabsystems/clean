#!/usr/bin/env bash
# Historical entry point: refuse before Git, compiler, build or archive writes.
set -euo pipefail
printf '%s\n' 'Q6 REFUSED: historical genesis generation is retired; MANIFEST.txt remains an archive.' \
  'Use just ck0-lineage for bounded evidence consistency; full Q6 remains partial.' >&2
exit 1
