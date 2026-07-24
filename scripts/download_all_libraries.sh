#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Download all major formal math libraries from the internet.
# Creates /tmp/mathverse-data/raw/ with symlinks to downloaded datasets.
# Then runs mathverse_convert to import all 14 systems.

set -euo pipefail

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

DATA_DIR="${1:-/tmp/mathverse-data}"
RAW_DIR="$DATA_DIR/raw"
mkdir -p "$RAW_DIR"

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  MATHVERSE LIBRARY — DOWNLOAD ALL FORMAL MATH LIBRARIES        ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

clone_if_missing() {
    local url="$1"
    local dest="$2"
    if [ -d "$dest" ]; then
        echo "  [SKIP] $dest already exists"
    else
        echo "  [CLONE] $url -> $dest"
        git clone --depth 1 "$url" "$dest" 2>&1 | tail -1
    fi
}

echo "=== Downloading 14 formal math libraries ==="
echo ""

# 1. Metamath (set.mm — largest Metamath database)
echo "--- Metamath ---"
clone_if_missing "https://github.com/metamath/set.mm" "/tmp/metamath-set.mm"

# 2. Mathlib4 (largest Lean 4 math library)
echo "--- Mathlib4 ---"
clone_if_missing "https://github.com/leanprover-community/mathlib4" "/tmp/mathlib4"

# 3. Isabelle AFP (Archive of Formal Proofs)
echo "--- Isabelle AFP ---"
clone_if_missing "https://github.com/isabelle-prover/mirror-afp-2024" "/tmp/isabelle-afp"

# 4. HOL Light
echo "--- HOL Light ---"
clone_if_missing "https://github.com/jrh13/hol-light" "/tmp/hol-light"

# 5. HOL4
echo "--- HOL4 ---"
clone_if_missing "https://github.com/HOL-Theorem-Prover/HOL" "/tmp/hol4"

# 6. Mizar MML (via mizar-rs — verified Mizar implementation with MML support)
echo "--- Mizar MML ---"
clone_if_missing "https://github.com/digama0/mizar-rs" "/tmp/mizar-rs"

# 7. UniMath (Coq/Rocq — univalent mathematics)
echo "--- UniMath ---"
clone_if_missing "https://github.com/UniMath/UniMath" "/tmp/unimath"

# 8. OpenTheory
echo "--- OpenTheory ---"
clone_if_missing "https://github.com/gilith/opentheory" "/tmp/opentheory"

# 9. Agda stdlib
echo "--- Agda stdlib ---"
clone_if_missing "https://github.com/agda/agda-stdlib" "/tmp/agda-stdlib"

# 10. Idris2
echo "--- Idris2 ---"
clone_if_missing "https://github.com/idris-lang/Idris2" "/tmp/idris2"

# 11. F*
echo "--- F* ---"
clone_if_missing "https://github.com/FStarLang/FStar" "/tmp/fstar"

# 12. Dafny
echo "--- Dafny ---"
clone_if_missing "https://github.com/dafny-lang/dafny" "/tmp/dafny"

# 13. Why3
echo "--- Why3 ---"
clone_if_missing "https://github.com/AdaCore/why3" "/tmp/why3"

# 14. ACL2
echo "--- ACL2 ---"
clone_if_missing "https://github.com/acl2/acl2" "/tmp/acl2"

# 15. Lean 3 (mathlib3 — frozen since 2023-07-16, text-based structured import; no Lean 3 toolchain required)
echo "--- Lean 3 (mathlib3) ---"
clone_if_missing "https://github.com/leanprover-community/mathlib" "/tmp/mathlib3"

echo ""
echo "=== Setting up raw data symlinks ==="

# Create symlinks
ln -sf /tmp/metamath-set.mm "$RAW_DIR/metamath"
ln -sf /tmp/opentheory/data "$RAW_DIR/opentheory"
ln -sf /tmp/hol-light "$RAW_DIR/hol-light"
ln -sf /tmp/hol4 "$RAW_DIR/hol4"
ln -sf /tmp/isabelle-afp/thys "$RAW_DIR/isabelle-afp"
ln -sf /tmp/mizar-rs "$RAW_DIR/mizar-contents"
ln -sf /tmp/unimath "$RAW_DIR/coq"
ln -sf /tmp/mathlib4 "$RAW_DIR/mathlib4"
ln -sf /tmp/agda-stdlib "$RAW_DIR/agda-stdlib"
ln -sf /tmp/idris2 "$RAW_DIR/idris2"
ln -sf /tmp/fstar "$RAW_DIR/fstar"
ln -sf /tmp/dafny "$RAW_DIR/dafny"
ln -sf /tmp/why3 "$RAW_DIR/why3"
ln -sf /tmp/acl2 "$RAW_DIR/acl2"
ln -sf /tmp/mathlib3 "$RAW_DIR/lean3"

# Copy .mm files to raw root (Metamath converter looks for them there)
cp -f /tmp/metamath-set.mm/set.mm "$RAW_DIR/set.mm"
cp -f /tmp/metamath-set.mm/iset.mm "$RAW_DIR/iset.mm"
cp -f /tmp/metamath-set.mm/hol.mm "$RAW_DIR/hol.mm"
cp -f /tmp/metamath-set.mm/ql.mm "$RAW_DIR/ql.mm"
cp -f /tmp/metamath-set.mm/nf.mm "$RAW_DIR/nf.mm"

echo ""
echo "=== Running mathverse_convert ==="

SCRIPT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
BINARY="$SCRIPT_DIR/target/release/mathverse_convert"

if [ ! -f "$BINARY" ]; then
    echo "Building mathverse_convert..."
    cargo build --locked -p clean-mathverse --bin mathverse_convert --release --message-format=short -j "$CARGO_BUILD_JOBS"
fi

"$BINARY" all "$DATA_DIR"
