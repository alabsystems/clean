#!/usr/bin/env bash
#
# Generate the ck0 genesis manifest — the durable, checksum-pinned seed of the
# trust root. Records: a sha256 over every build-input source file of the
# clean-ck0 kernel crate, the exact toolchain, the build/verify command, and a
# pointer to the honestly-named irreducible trust floor (TRUST_FLOOR.md).
#
# Determinism: the file list is `LC_ALL=C sort`ed; the manifest is reproducible
# from a fixed source tree. Run from anywhere inside the repo.
#
# Usage:  genesis/ck0/generate_manifest.sh
#
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

OUT="genesis/ck0/MANIFEST.txt"

# Portable sha256 (Linux: sha256sum; macOS: shasum -a 256). Both emit
# "<hex>  <path>", which `verify.sh` feeds back to the same tool with -c.
if command -v sha256sum >/dev/null 2>&1; then
  SHA() { sha256sum "$@"; }
else
  SHA() { shasum -a 256 "$@"; }
fi

# Build-input set: the trusted kernel source, its validation suite, the crate
# manifest, the dependency lockfile, and the workspace manifest (workspace deps
# the kernel resolves through). Sorted for determinism.
FILES="$( {
  find crates/clean-ck0/src crates/clean-ck0/tests -name '*.rs' -type f
  echo crates/clean-ck0/Cargo.toml
  echo Cargo.lock
  echo Cargo.toml
} | LC_ALL=C sort )"

{
  echo "# ck0 GENESIS MANIFEST — durable checksum-pinned seed of the trust root"
  echo "#"
  echo "# Verify (reproduce):  genesis/ck0/verify.sh"
  echo "#   -> recomputes every checksum below, then rebuilds + runs the kernel"
  echo "#      suite with the pinned build command. Exit 0 == reproduced."
  echo "# Trust floor (the irreducible, honestly-named base): genesis/ck0/TRUST_FLOOR.md"
  echo "#"
  echo "kernel        = clean-ck0"
  echo "scope         = M0-M3 (terms, def_eq, inductives, mutual+nested recursors, positivity/elim gates)"
  echo "git_commit    = $(git rev-parse HEAD)"
  echo "git_branch    = $(git rev-parse --abbrev-ref HEAD)"
  echo "rustc         = $(rustc --version)"
  echo "cargo         = $(cargo --version)"
  echo "host          = $(rustc -vV | awk '/host:/{print $2}')"
  echo "build_cmd     = cargo test --locked -p clean-ck0"
  echo "deps          = num-bigint, num-traits, thiserror (see TRUST_FLOOR.md)"
  echo "source_files  = $(printf '%s\n' "$FILES" | wc -l | tr -d ' ')"
  echo "kernel_src_loc= $(find crates/clean-ck0/src -name '*.rs' | xargs wc -l | tail -1 | awk '{print $1}')"
  echo "# --- checksums (sha256) ---"
  while IFS= read -r f; do SHA "$f"; done <<< "$FILES"
} > "$OUT"

echo "wrote $OUT ($(printf '%s\n' "$FILES" | wc -l | tr -d ' ') files pinned)"
