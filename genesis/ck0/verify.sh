#!/usr/bin/env bash
#
# Verify a ck0 genesis seed: prove the source tree matches the checksum-pinned
# MANIFEST.txt, then rebuild and run the kernel suite with the pinned command.
# This is the reproducibility gate for the trust root — exit 0 means "this exact
# source reproduces, and the kernel it builds passes its own validation suite."
#
# Usage:  genesis/ck0/verify.sh            (from inside the repo or a seed extract)
#
set -euo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

MAN="genesis/ck0/MANIFEST.txt"
[ -f "$MAN" ] || { echo "FATAL: $MAN not found (run from the repo root or a seed extract)"; exit 2; }

if command -v sha256sum >/dev/null 2>&1; then
  SHA_C() { sha256sum -c -; }
else
  SHA_C() { shasum -a 256 -c -; }
fi

echo "== ck0 genesis verification =="
echo "manifest commit : $(awk -F'= ' '/^git_commit/{print $2}' "$MAN")"
echo "manifest rustc  : $(awk -F'= ' '/^rustc /{print $2}' "$MAN")"

# 1) Checksum integrity: every pinned source file must match, byte for byte.
echo "-- [1/3] checksum integrity --"
awk '/^# --- checksums/{p=1;next} p' "$MAN" | SHA_C
echo "   checksums OK"

# 2) Toolchain note (source is pinned regardless; the binary is only bit-identical
#    under the same rustc — we warn, never fail, on a toolchain mismatch).
want_rustc="$(awk -F'= ' '/^rustc /{print $2}' "$MAN")"
have_rustc="$(rustc --version)"
if [ "$want_rustc" != "$have_rustc" ]; then
  echo "-- [2/3] toolchain: WARN — rustc differs"
  echo "     manifest: $want_rustc"
  echo "     here    : $have_rustc"
  echo "     (source is pinned; the rebuilt binary may not be bit-identical)"
else
  echo "-- [2/3] toolchain: matches ($have_rustc)"
fi

# 3) Rebuild + run the kernel's own validation suite with the pinned command.
echo "-- [3/3] rebuild + kernel suite (cargo test --locked -p clean-ck0) --"
cargo test --locked -p clean-ck0

echo
echo "== REPRODUCED: pinned source checksums match AND the kernel suite passes =="
