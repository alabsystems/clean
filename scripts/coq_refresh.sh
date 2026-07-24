#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# One-command Coq corpus refresh: staleness-aware re-dump → import → 0-regression
# gate → (optional) baseline promotion. The repeatable entrypoint for keeping the
# Mathverse Coq lane current.
#
#   scripts/coq_refresh.sh [--redump] [--promote] [--timeout=SECS] [--out=DIR]
#
#   --redump    Re-dump every module whose sidecar (.meta.json) records skipped
#               declarations, plus any module named in a manifest's
#               modules_failed — one dumper invocation per module (the dumper is
#               self-healing: poison-name recovery, poison-value type-only
#               salvage, plain-Require fallback). Without --redump the existing
#               corpus is imported as-is.
#   --promote   Pass --promote-on-green to the import gate: on a fully green
#               gate (0 regressions in every baselined library) the fresh
#               kernel-verified manifests + shards replace the promoted
#               baselines under data/corpora/coq-mathverse/. Red gates promote
#               nothing and exit nonzero.
#   --timeout   Per-declaration sertop answer timeout for --redump (default 300;
#               giant Hierarchy-Builder terms need more than the dumper's 60s
#               default).
#   --out       Import output dir (default: a fresh mktemp -d).
#
# Libraries: stdlib (host sertop via build_coq_serapi_dumps.sh) and mathcomp
# (Linux-container sertop via build_mathcomp_dumps.sh). Gate + promotion run
# through `mathverse_shard coq-import --gate-baseline [--promote-on-green]`, so
# the 0-regression comparison logic lives in ONE audited place (the binary),
# not in shell.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEXP_ROOT="${REPO_ROOT}/data/corpora/coq-sexp"
BASELINE_DIR="${REPO_ROOT}/data/corpora/coq-mathverse"
SHARD_BIN="${REPO_ROOT}/target/release/mathverse_shard"

REDUMP=0
PROMOTE=0
TIMEOUT=300
OUT_DIR=""
for arg in "$@"; do
  case "$arg" in
    --redump) REDUMP=1 ;;
    --promote) PROMOTE=1 ;;
    --timeout=*) TIMEOUT="${arg#--timeout=}" ;;
    --out=*) OUT_DIR="${arg#--out=}" ;;
    *) echo "unknown arg: $arg" >&2; exit 2 ;;
  esac
done
[[ -n "$OUT_DIR" ]] || OUT_DIR="$(mktemp -d /tmp/coq-refresh.XXXXXX)"

[[ -x "$SHARD_BIN" ]] || {
  echo "[coq-refresh] building mathverse_shard (release)..." >&2
  (cd "$REPO_ROOT" && cargo build --release -p clean-mathverse --bin mathverse_shard)
}

# Modules needing a re-dump: any with recorded skips, or listed in a manifest's
# modules_failed. Emits "<library> <module>" lines.
stale_modules() {
  python3 - "$SEXP_ROOT" <<'PY'
import json, glob, os, sys
root = sys.argv[1]
for lib in sorted(os.listdir(root)):
    libdir = os.path.join(root, lib)
    if not os.path.isdir(libdir):
        continue
    for f in sorted(glob.glob(os.path.join(libdir, "*.meta.json"))):
        m = json.load(open(f))
        if m.get("counts", {}).get("skipped"):
            print(lib, m["module"])
    man = os.path.join(libdir, "manifest.json")
    if os.path.exists(man):
        mf = json.load(open(man))
        for e in mf.get("modules_failed", []) or []:
            name = e[0] if isinstance(e, (list, tuple)) else (e.get("module") if isinstance(e, dict) else e)
            if name:
                print(lib, name)
PY
}

if [[ "$REDUMP" == 1 ]]; then
  echo "[coq-refresh] scanning for stale modules (recorded skips / failed)..."
  # Sort -u to dedup manifest+meta overlap; one dumper run per module (the
  # docker-backed wrapper eats stdin, hence </dev/null).
  stale_modules | sort -u | while IFS=' ' read -r lib mod; do
    case "$lib" in
      stdlib)
        "${REPO_ROOT}/scripts/build_coq_serapi_dumps.sh" --force "--module=${mod}" </dev/null ;;
      mathcomp)
        "${REPO_ROOT}/scripts/build_mathcomp_dumps.sh" --force "--timeout=${TIMEOUT}" "--module=${mod}" </dev/null ;;
      *)
        echo "[coq-refresh] no dump script for library '$lib' — skipping ${mod}" >&2 ;;
    esac
  done
fi

echo "[coq-refresh] import + gate (out: ${OUT_DIR})"
GATE_ARGS=("--sexp-root=${SEXP_ROOT}" "--out=${OUT_DIR}" "--json=${OUT_DIR}/report.json"
  "--gate-baseline=${BASELINE_DIR}")
[[ "$PROMOTE" == 1 ]] && GATE_ARGS+=("--promote-on-green")
"$SHARD_BIN" coq-import "${GATE_ARGS[@]}"
