#!/usr/bin/env bash
#
# Provision the `leanprover-community/repl` binary used by mathbot's
# persistent-stateful Lean REPL backend (charter §B1.1). Clones the
# upstream repo at a Lean toolchain matching the workspace, runs
# `lake build`, and prints the absolute path to the produced `repl`
# binary on success.
#
# Usage:
#   scripts/provision-lean-repl.sh [TARGET_DIR]
#
# Default TARGET_DIR is `~/.cache/mathbot/lean-repl`. The script is
# idempotent: re-running against an existing checkout pulls and
# rebuilds.
#
# Then set:
#
#   export MATHBOT_LEAN_REPL_BIN="$(scripts/provision-lean-repl.sh)"
#
# in your shell init to enable the persistent backend.

set -euo pipefail

REPO_URL="https://github.com/leanprover-community/repl.git"
TARGET_DIR="${1:-${HOME}/.cache/mathbot/lean-repl}"

# Read the workspace's lean-toolchain to bound which branch of the
# upstream repl can match. The repl repo's master tracks the latest
# Lean release; older bumps live on `bump_to_vX.Y.Z` branches. If our
# workspace pins an older toolchain, the caller can override BRANCH=
# in the environment.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
WS_TOOLCHAIN_FILE="${WORKSPACE_ROOT}/lean-toolchain"
if [[ -f "${WS_TOOLCHAIN_FILE}" ]]; then
  WS_TOOLCHAIN="$(cat "${WS_TOOLCHAIN_FILE}")"
  echo "[provision-lean-repl] workspace lean-toolchain: ${WS_TOOLCHAIN}" >&2
fi

BRANCH="${BRANCH:-master}"
mkdir -p "$(dirname "${TARGET_DIR}")"

if [[ -d "${TARGET_DIR}/.git" ]]; then
  echo "[provision-lean-repl] updating existing checkout at ${TARGET_DIR}" >&2
  (cd "${TARGET_DIR}" && git fetch origin "${BRANCH}" && git checkout "${BRANCH}" && git reset --hard "origin/${BRANCH}")
else
  echo "[provision-lean-repl] cloning ${REPO_URL} (${BRANCH}) into ${TARGET_DIR}" >&2
  git clone --depth 1 --branch "${BRANCH}" "${REPO_URL}" "${TARGET_DIR}"
fi

echo "[provision-lean-repl] building repl (this can take 1-3 minutes on first run)" >&2
(cd "${TARGET_DIR}" && lake build)

REPL_BIN="${TARGET_DIR}/.lake/build/bin/repl"
if [[ ! -x "${REPL_BIN}" ]]; then
  echo "[provision-lean-repl] ERROR: repl binary not produced at ${REPL_BIN}" >&2
  exit 1
fi

# Print on stdout so `export MATHBOT_LEAN_REPL_BIN=$(...)` works.
echo "${REPL_BIN}"
