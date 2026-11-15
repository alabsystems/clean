#!/usr/bin/env bash
# Offline / vendored-source build wrapper for clean (paragon axis 1).
#
# Runs targo against the opt-in vendored-sources config
# (.cargo/config.offline.toml) with --offline, so the whole workspace builds
# from the local vendor/ tree with ZERO network access after cache-backed
# source authentication. Canonical registry archives and first-party Git
# sources must already be cached. This is the OPT-IN counterpart to the default
# (online, crates.io) build: the offline stanza is deliberately kept OUT of
# .cargo/config.toml so it never forces vendored resolution on normal builds.
#
# Usage:
#   scripts/build_offline.sh                      # -> targo --unverified build --offline ...
#   scripts/build_offline.sh check -p clean-kernel
#   scripts/build_offline.sh test  --lib -p clean-parser
#
# If the first argument is a targo subcommand (check/build/test/...), it is
# used as-is; otherwise `build` is assumed and all args are passed through.
#
# PREREQUISITE: the vendor/ tree must exist. It is GITIGNORED (released as an
# artifact, not committed). Internal AY/NY/ty repositories must remain subrepos
# and are rejected by the preflight below. Stage it third-party-only with
# `python3 scripts/gen_vendor_manifest.py --stage-third-party vendor`, or fetch
# + extract a compatible released archive (scripts/package_vendor.sh verify;
# see docs/SUPPLY_CHAIN_VENDORING.md). Never regenerate it with raw
# `cargo vendor`, which copies first-party Git sources.

set -euo pipefail

# Resolve repo root from this script's location so cargo's config discovery and
# the relative `directory = "vendor"` in the offline config both anchor there.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

OFFLINE_CONFIG=".cargo/config.offline.toml"

if [[ ! -d vendor ]]; then
  echo "error: vendor/ tree not found at ${REPO_ROOT}/vendor" >&2
  echo "       stage it: python3 scripts/gen_vendor_manifest.py --stage-third-party vendor" >&2
  echo "       or fetch the compatible vendor-sources-v*.tar.zst artifact" >&2
  echo "       (see scripts/package_vendor.sh and docs/SUPPLY_CHAIN_VENDORING.md)." >&2
  exit 1
fi

# Fail before Cargo if this tree contains an internal repository or does not
# exactly match the committed external-source manifest and current Cargo.lock.
# This prevents an ambient/raw `cargo vendor` run from turning AY or NY into a
# vendored dependency.
bash scripts/package_vendor.sh authenticate vendor
VENDOR_PREFLIGHT_TMP="$(mktemp)"
trap 'rm -f "${VENDOR_PREFLIGHT_TMP:-}"' EXIT
python3 scripts/gen_vendor_manifest.py vendor "${VENDOR_PREFLIGHT_TMP}"
python3 - data/vendor_manifest.json "${VENDOR_PREFLIGHT_TMP}" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    expected = json.load(handle)
with open(sys.argv[2], encoding="utf-8") as handle:
    actual = json.load(handle)

for field in ("cargo_lock_sha256", "summary", "crates"):
    if expected.get(field) != actual.get(field):
        print(
            f"error: vendor provenance field {field!r} is stale or mismatched; "
            "refresh only through a third-party-only staging flow",
            file=sys.stderr,
        )
        raise SystemExit(1)
PY

# Finish preflight cleanup before exec replaces the shell and its EXIT trap.
rm -f -- "${VENDOR_PREFLIGHT_TMP}"
trap - EXIT

# Default to `build` when no cargo subcommand is given.
SUBCMD="build"
if [[ $# -gt 0 ]]; then
  case "$1" in
    -*) : ;;            # first arg is a flag -> keep default `build`
    *) SUBCMD="$1"; shift ;;
  esac
fi

# The driver is targo (owner directive 2026-09-28); compilation verbs take its
# unverified lane, the rest (metadata, tree, ...) take none.
LANE=()
case "${SUBCMD}" in
  build|check|test|run|bench|doc|install|rustc|fix) LANE=(--unverified) ;;
esac

echo "+ targo ${LANE[*]-} ${SUBCMD} --config ${OFFLINE_CONFIG} --offline $*" >&2
exec targo ${LANE[@]+"${LANE[@]}"} "${SUBCMD}" --config "${OFFLINE_CONFIG}" --offline "$@"
