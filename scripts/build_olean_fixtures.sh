#!/usr/bin/env bash
# Build the .olean test fixtures consumed by `clean-olean` integration tests.
#
# The .lean sources live under tests/fixtures/olean/<version>/custom/ and are
# checked in, but the matching .olean binaries are regenerable artifacts. This
# script compiles them with the appropriate Lean toolchain and copies the small
# subset of stdlib oleans the test suite needs.
#
# Usage: scripts/build_olean_fixtures.sh
#
# Requirements:
#   - elan installed
#   - Internet access for `elan toolchain install` on first run
#
# Toolchains used (must match the version assertions in the test files):
#   - lean-4.13.0 — produces .olean format v1 (custom/* + stdlib/*)
#   - lean-4.26.0 — produces .olean format v2 (custom/StringCompat.olean)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURES_ROOT="${REPO_ROOT}/tests/fixtures/olean"

LEAN_4_13="leanprover/lean4:v4.13.0"
LEAN_4_26="leanprover/lean4:v4.26.0"

if ! command -v elan >/dev/null 2>&1; then
  echo "error: elan is required (install from https://lean-lang.org)." >&2
  exit 1
fi

echo "==> Ensuring required Lean toolchains are installed"
ensure_toolchain() {
  local tc="$1"
  if elan toolchain list 2>/dev/null | grep -Fqx "${tc}"; then
    echo "    - ${tc} already installed"
  else
    elan toolchain install "${tc}"
  fi
}
ensure_toolchain "${LEAN_4_13}"
ensure_toolchain "${LEAN_4_26}"

# -----------------------------------------------------------------------------
# v4.13.0 custom fixtures
# -----------------------------------------------------------------------------
V413_CUSTOM="${FIXTURES_ROOT}/v4.13.0/custom"
echo "==> Building v4.13.0 custom fixtures in ${V413_CUSTOM}"
pushd "${V413_CUSTOM}" >/dev/null
for src in Minimal.lean Inductive.lean Structure.lean; do
  out="${src%.lean}.olean"
  echo "    - ${src} -> ${out}"
  elan run "${LEAN_4_13}" lean "${src}" -o "${out}"
done
popd >/dev/null

# -----------------------------------------------------------------------------
# v4.13.0 stdlib fixtures
# -----------------------------------------------------------------------------
# The tests reference:
#   stdlib/Init.olean         — the Lean 4.13.0 root Init module (copied)
#   stdlib/Init/Char.olean    — re-export of Init.Data.Char (compiled stub)
#   stdlib/Init/Option.olean  — re-export of Init.Data.Option (compiled stub)
#
# We can't copy Init/Data/Char.olean directly because the embedded constants
# would still report `Init.Data.Char` paths; the integration tests only care
# about the file's imports list, so a thin re-export module is enough.

LEAN_4_13_LIB="$(elan run "${LEAN_4_13}" lean --print-libdir)"
V413_STDLIB="${FIXTURES_ROOT}/v4.13.0/stdlib"
echo "==> Building v4.13.0 stdlib fixtures in ${V413_STDLIB}"
mkdir -p "${V413_STDLIB}/Init"

echo "    - copying Init.olean from ${LEAN_4_13_LIB}"
cp "${LEAN_4_13_LIB}/Init.olean" "${V413_STDLIB}/Init.olean"

build_stub() {
  local module_path="$1"   # e.g. Init/Char
  local import_target="$2" # e.g. Init.Data.Char
  local out_dir
  out_dir="${V413_STDLIB}/$(dirname "${module_path}")"
  local out_olean="${V413_STDLIB}/${module_path}.olean"
  mkdir -p "${out_dir}"
  local tmp
  tmp="$(mktemp -d)"
  trap 'rm -rf "${tmp}"' RETURN
  local stub_src="${tmp}/$(basename "${module_path}").lean"
  printf 'import %s\n' "${import_target}" >"${stub_src}"
  echo "    - ${module_path}.olean (re-exports ${import_target})"
  ( cd "${tmp}" && elan run "${LEAN_4_13}" lean "$(basename "${stub_src}")" -o "${out_olean}" )
}

build_stub "Init/Char" "Init.Data.Char"
build_stub "Init/Option" "Init.Data.Option"

# -----------------------------------------------------------------------------
# v4.26.0 custom fixtures
# -----------------------------------------------------------------------------
V426_CUSTOM="${FIXTURES_ROOT}/v4.26.0/custom"
echo "==> Building v4.26.0 custom fixtures in ${V426_CUSTOM}"
pushd "${V426_CUSTOM}" >/dev/null
for src in StringCompat.lean; do
  out="${src%.lean}.olean"
  echo "    - ${src} -> ${out}"
  elan run "${LEAN_4_26}" lean "${src}" -o "${out}"
done
popd >/dev/null

echo
echo "Done. Built fixtures:"
find "${FIXTURES_ROOT}" -name '*.olean' -print | sort
