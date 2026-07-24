#!/usr/bin/env bash
# Offline / vendored-source build wrapper for clean (paragon axis 1).
#
# Runs cargo against the opt-in vendored-sources config
# (.cargo/config.offline.toml) with --offline, so the whole workspace builds
# from the local vendor/ tree with ZERO network access — reproducible from
# vendored source alone. This is the OPT-IN counterpart to the default
# (online, crates.io) build: the offline stanza is deliberately kept OUT of
# .cargo/config.toml so it never forces vendored resolution on normal builds.
#
# Usage:
#   scripts/build_offline.sh                      # -> cargo build --offline ...
#   scripts/build_offline.sh check -p clean-kernel
#   scripts/build_offline.sh test  --lib -p clean-parser
#
# If the first argument is a cargo subcommand (check/build/test/...), it is
# used as-is; otherwise `build` is assumed and all args are passed through.
#
# PREREQUISITE: the vendor/ tree must exist. It is GITIGNORED (released as an
# artifact, not committed). Populate it with:
#   cargo vendor --versioned-dirs vendor/
# or fetch + extract the released archive (scripts/package_vendor.sh get/verify;
# see docs/SUPPLY_CHAIN_VENDORING.md).

set -euo pipefail

# Resolve repo root from this script's location so cargo's config discovery and
# the relative `directory = "vendor"` in the offline config both anchor there.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

OFFLINE_CONFIG=".cargo/config.offline.toml"

if [[ ! -d vendor ]]; then
  echo "error: vendor/ tree not found at ${REPO_ROOT}/vendor" >&2
  echo "       generate it with:  cargo vendor --versioned-dirs vendor/" >&2
  echo "       or fetch the released vendor-sources-v*.tar.zst artifact" >&2
  echo "       (see scripts/package_vendor.sh and docs/SUPPLY_CHAIN_VENDORING.md)." >&2
  exit 1
fi

# Default to `build` when no cargo subcommand is given.
SUBCMD="build"
if [[ $# -gt 0 ]]; then
  case "$1" in
    -*) : ;;            # first arg is a flag -> keep default `build`
    *) SUBCMD="$1"; shift ;;
  esac
fi

echo "+ cargo ${SUBCMD} --config ${OFFLINE_CONFIG} --offline $*" >&2
exec cargo "${SUBCMD}" --config "${OFFLINE_CONFIG}" --offline "$@"
