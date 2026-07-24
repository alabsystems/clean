#!/usr/bin/env bash
#
# Mathverse — All-Math Acquisition (priority-ordered)
#
# IMPORTANT (read the manifest "What downloading actually buys"):
#   - Statement-only import has ~0 marginal value until the .olean loader fix +
#     C1 (kernel re-check at scale) land. Mathverse already holds ~5.77M
#     statements at ~0 stored KernelVerified.
#   - This script downloads in value-per-effort order toward KERNEL-VERIFIED
#     depth. Heavy corpora are gated behind THROUGHPUT_BOX=1.
#
# Usage:
#   bash download.sh              # run-here tier only (small, dev-box safe)
#   THROUGHPUT_BOX=1 bash download.sh   # also pull the heavy corpora
#   ARXIV=1 THROUGHPUT_BOX=1 bash download.sh   # also arXiv bulk (TBs, $$$)

set -euo pipefail

# Repo root is the parent of scripts/ (this file lives in scripts/).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DATA="${MATHVERSE_DATA:-$ROOT/data/corpora}"
RAW="${MATHVERSE_RAW:-$ROOT/data/raw}"
mkdir -p "$DATA" "$RAW"

THROUGHPUT_BOX="${THROUGHPUT_BOX:-0}"
ARXIV="${ARXIV:-0}"

note()  { printf '\n=== %s ===\n' "$*"; }
have()  { command -v "$1" >/dev/null 2>&1; }

# Skip-if-present guard for git corpora.
clone_into() { # <dest-subdir> <url> [extra git args...]
  local sys="$1"; shift
  local url="$1"; shift
  local dest="$DATA/$sys"
  if [ -d "$dest/.git" ] || [ -e "$dest" ] && [ -n "$(ls -A "$dest" 2>/dev/null || true)" ]; then
    echo "SKIP  $sys (already present at $dest)"
    return 0
  fi
  mkdir -p "$(dirname "$dest")"
  echo "CLONE $sys <- $url"
  git clone "$@" "$url" "$dest"
}

dl_http() { # <dest-file> <url>  (size/license echoed by caller)
  local dest="$1"; local url="$2"
  if [ -f "$dest" ]; then echo "SKIP  $(basename "$dest") (present)"; return 0; fi
  mkdir -p "$(dirname "$dest")"
  echo "FETCH $url -> $dest"
  if have curl; then curl -fL --retry 3 -o "$dest" "$url"
  elif have wget; then wget -O "$dest" "$url"
  else echo "ERROR: need curl or wget" >&2; return 1; fi
}

############################################################
# TIER A — RUN HERE (dev-box safe). Depth proof-of-pipeline.
############################################################

note "TIER A: depth proof-of-pipeline (run-here, small)"

# --- Metamath set.mm + sisters (CC0 / Public Domain; ~64 MB working tree) ---
# set.mm is the ONLY in-family corpus with a working in-repo RPN verifier.
echo "LICENSE: Metamath set.mm = CC0 1.0 / Public Domain"
echo "SIZE:    ~64 MB working tree (set.mm ~48 MB, iset/nf/ql/hol smaller)"
if [ -f "$DATA/metamath/set.mm" ]; then
  echo "SKIP  metamath/set.mm (already present, $(wc -c < "$DATA/metamath/set.mm") bytes)"
else
  clone_into metamath https://github.com/metamath/set.mm --depth 1
fi

# --- OpenTheory stdlib (MIT; tens of MB). WIRED: mathverse_convert opentheory ---
echo "LICENSE: OpenTheory tooling/stdlib = MIT"
echo "SIZE:    ~tens of MB (.art articles)"
clone_into ../raw/opentheory https://github.com/gilith/opentheory --depth 1 \
  || clone_into opentheory https://github.com/gilith/opentheory --depth 1

# --- Stacks Project (GFDL; ~tens of MB). Cleanest text source (tag=boundary) ---
echo "LICENSE: Stacks Project = GFDL"
echo "SIZE:    ~tens of MB LaTeX (21,436 tags)"
if [ -d "$DATA/stacks-project" ] && [ -n "$(ls -A "$DATA/stacks-project" 2>/dev/null || true)" ]; then
  echo "SKIP  stacks-project (already present)"
else
  clone_into stacks-project https://github.com/stacks/stacks-project.git --depth 1
fi

# --- Competition benchmarks (MIT/Apache-2.0; small). Formal halves -> kernel ---
echo "LICENSE: miniF2F MIT(Metamath)/Apache-2.0(Lean); PutnamBench Apache-2.0/MIT"
echo "SIZE:    <50 MB combined"
clone_into bench/minif2f https://github.com/openai/miniF2F --depth 1
clone_into bench/putnambench https://github.com/trishullab/PutnamBench --depth 1

############################################################
# TIER A2 — Small CIC sources (KernelVerified-eligible)
# Cheap to host; depth blocked on coq/vo proof-term replay.
############################################################

note "TIER A2: small Coq/Rocq CIC corpora (KernelVerified-eligible)"
echo "LICENSE: stdlib LGPL-2.1 | MathComp CeCILL-B | CoRN GPL-2.0 | math-classes MIT"
echo "SIZE:    ~120 MB + ~60 MB + ~80 MB + ~25 MB"
clone_into coq/stdlib       https://github.com/rocq-prover/stdlib --depth 1
clone_into coq/math-comp    https://github.com/math-comp/math-comp --depth 1
clone_into coq/corn         https://github.com/coq-community/corn --depth 1
clone_into coq/math-classes https://github.com/coq-community/math-classes --depth 1

############################################################
# THROUGHPUT BOX ONLY — heavy corpora. NOT for the dev box.
############################################################

if [ "$THROUGHPUT_BOX" = "1" ]; then

  note "TIER B: Lean .olean depth payload (THROUGHPUT BOX; needs loader fix to be useful)"
  echo "LICENSE: Apache-2.0 (Lean4, Batteries, Mathlib4, PFR, ...)"
  echo "SIZE:    Mathlib4 cache ~5-8 GB"
  echo "NOTE:    Use 'lake exe cache get' — NEVER rebuild from scratch."
  clone_into lean/batteries https://github.com/leanprover-community/batteries --depth 1
  clone_into lean/mathlib4   https://github.com/leanprover-community/mathlib4 --depth 1
  clone_into lean/pfr        https://github.com/teorth/pfr --depth 1
  clone_into lean/flt-regular https://github.com/leanprover-community/flt-regular --depth 1
  clone_into lean/carleson   https://github.com/fpvandoorn/carleson --depth 1
  clone_into lean/equational_theories https://github.com/teorth/equational_theories --depth 1
  if have lake; then
    ( cd "$DATA/lean/mathlib4" && lake exe cache get ) || echo "WARN: lake cache get failed (pin toolchain)"
  else
    echo "WARN: 'lake' not found — clone holds source only; oleans require lake."
  fi

  note "TIER B2: dependent-type sources (signatures -> Autoformalize-only / VC-cert)"
  echo "LICENSE: Agda MIT | F* Apache-2.0 | Idris2 BSD-3 | Dafny MIT | cubical MIT"
  clone_into dtt/agda-stdlib https://github.com/agda/agda-stdlib --depth 1
  clone_into dtt/fstar       https://github.com/FStarLang/FStar --depth 1
  clone_into dtt/idris2      https://github.com/idris-lang/Idris2 --depth 1
  clone_into dtt/dafny       https://github.com/dafny-lang/dafny --depth 1
  clone_into dtt/cubical     https://github.com/agda/cubical --depth 1
  # HACL*: sparse-checkout .fst only (real count 991 .fst; full tree counts gen'd C)
  if [ ! -d "$DATA/dtt/hacl-star/.git" ]; then
    echo "CLONE hacl-star (blobless, sparse .fst)"
    git clone --filter=blob:none --no-checkout https://github.com/hacl-star/hacl-star "$DATA/dtt/hacl-star"
    ( cd "$DATA/dtt/hacl-star" && git sparse-checkout init --cone && git sparse-checkout set '*.fst' '*.fsti' && git checkout ) || true
  else
    echo "SKIP  hacl-star (present)"
  fi

  note "TIER C: large foreign-logic breadth (CertificateReplayed/AxiomDependent)"
  echo "LICENSE: AFP per-entry BSD/LGPL | Mizar CC-BY-SA 4.0 | ACL2 BSD-3 | HOL* BSD"
  echo "SIZE:    AFP ~1.5 GB; Mizar/ACL2/HOL hundreds of MB each"
  dl_http "$RAW/afp/afp-current.tar.gz" "https://www.isa-afp.org/release/afp-current.tar.gz"
  clone_into hol/hol-light https://github.com/jrh13/hol-light --depth 1
  clone_into hol/hol4      https://github.com/HOL-Theorem-Prover/HOL --depth 1
  clone_into mizar/MML     https://github.com/MizarSystem/MML --depth 1
  clone_into acl2/acl2     https://github.com/acl2/acl2 --depth 1
  clone_into pvs/pvslib    https://github.com/nasa/pvslib --depth 1

  note "TIER C2: cross-system / SMT / TPTP (smtlib & tptp importers exist but UNWIRED)"
  echo "LICENSE: SMT-LIB CC-BY-4.0 | TPTP free-for-research | Dedukti CeCILL-B"
  echo "SIZE:    SMT-LIB ~4.8 GB; TPTP hundreds of MB"
  dl_http "$RAW/smtlib/non-incremental-2024.tar" \
    "https://zenodo.org/records/11061097/files/non-incremental.tar" \
    || echo "WARN: fetch the per-logic archives from https://zenodo.org/records/11061097 manually"
  dl_http "$RAW/tptp/TPTP-v9.1.0.tgz" "https://www.tptp.org/TPTP/Distribution/TPTP-v9.1.0.tgz"
  clone_into typetheory/dedukti  https://github.com/Deducteam/Dedukti --depth 1
  clone_into typetheory/lambdapi https://github.com/Deducteam/lambdapi --depth 1
  clone_into typetheory/logipedia https://github.com/Deducteam/Logipedia --depth 1

  note "TIER D: autoformalize-only text (blocked on missing LlmClient)"
  echo "LICENSE: ProofWiki CC-BY-SA 3.0 | NaturalProofs mixed (CC-BY-SA/GFDL/NC/MIT)"
  dl_http "$RAW/proofwiki/latest.xml.gz" "https://proofwiki.org/xmldump/latest.xml.gz"
  dl_http "$RAW/naturalproofs/naturalproofs.zip" \
    "https://zenodo.org/records/4902289/files/naturalproofs.zip" \
    || echo "WARN: confirm NaturalProofs asset name on Zenodo 4902289"

else
  note "SKIPPED heavy tiers (set THROUGHPUT_BOX=1 to enable: Lean cache, AFP, Mizar, ACL2, SMT-LIB, TPTP, text)"
fi

############################################################
# ARXIV — requester-pays S3 (TBs, billed egress). Opt-in only.
############################################################

if [ "$ARXIV" = "1" ] && [ "$THROUGHPUT_BOX" = "1" ]; then
  note "TIER D-arXiv: bulk LaTeX (REQUESTER-PAYS S3; ~2.9 TB src; ~\$0.09/GB egress)"
  echo "LICENSE: per-paper (MOSTLY RESTRICTED) — filter to CC-BY/CC0 before any redistribution"
  if have aws; then
    mkdir -p "$RAW/arxiv"
    aws s3 cp --request-payer requester s3://arxiv/src/arXiv_src_manifest.xml \
      "$RAW/arxiv/arXiv_src_manifest.xml" --region us-east-1
    echo "Manifest fetched. Filter to math.* via OAI-PMH, then:"
    echo "  aws s3 cp --request-payer requester s3://arxiv/src/<chunk>.tar $RAW/arxiv/ --region us-east-1"
  else
    echo "ERROR: aws CLI required for arXiv bulk. Install awscli and configure credentials." >&2
  fi
else
  note "SKIPPED arXiv bulk (set ARXIV=1 THROUGHPUT_BOX=1; costs real money)"
fi

note "DONE. Reminder: downloading buys ~0 KernelVerified until the .olean loader fix + C1 land."
echo "Next concrete actions: (1) fix .olean loader, (2) close C1 re-check, (3) stamp set.mm + scale OpenTheory."
