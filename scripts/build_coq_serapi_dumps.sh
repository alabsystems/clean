#!/usr/bin/env bash
# Build importer-form SerAPI .sexp dumps of the Coq 8.20 stdlib (COQ-0).
#
# Drives crates/clean-mathverse/src/bin/mathverse_coq_dump (sertop subprocess
# per worker) to write per-module dumps + sidecars + a manifest under
# data/corpora/coq-sexp/stdlib/ in the exact forms consumed by
# coq::alpha::CoqImporter::import_sexp:
#   (CoqConstant "<qualified>" <type> <value>)
#   (CoqAxiom    "<qualified>" <type>)
#   (CoqInductive "<qualified>" <block> <arity> (NumParams k) (Ctor ...)...)
#
# Idempotent: modules with an existing .sexp + .meta.json pair are skipped
# unless --force is given. The binary writes manifest.json (toolchain
# versions + aggregate counts) itself.
#
# Usage: scripts/build_coq_serapi_dumps.sh [--force] [--jobs=N] [--module=M ...]
#   (extra --module=M args restrict the run; default is the full stdlib)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SWITCH_ROOT="${HOME}/.opam/mathverse-serapi"
SERTOP="${SWITCH_ROOT}/bin/sertop"
OUT_DIR="${REPO_ROOT}/data/corpora/coq-sexp/stdlib"

if [[ ! -x "${SERTOP}" ]]; then
  cat >&2 <<'EOF'
error: sertop not found at ~/.opam/mathverse-serapi/bin/sertop

The isolated Coq 8.20 + SerAPI opam switch is required (it never touches the
system Rocq). Install it with (see data/MATHVERSE_COQ_DEPTH.md):

  opam switch create mathverse-serapi ocaml-base-compiler.4.14.2
  opam repo add coq-released https://coq.inria.fr/opam/released --switch=mathverse-serapi
  opam install coq.8.20.0 coq-serapi --switch=mathverse-serapi
EOF
  exit 1
fi

FORCE=""
JOBS=""
MODULE_ARGS=()
for arg in "$@"; do
  case "${arg}" in
    --force) FORCE="--force" ;;
    --jobs=*) JOBS="${arg#--jobs=}" ;;
    --module=*) MODULE_ARGS+=("${arg}") ;;
    *)
      echo "error: unknown argument: ${arg}" >&2
      exit 1
      ;;
  esac
done

if [[ -z "${JOBS}" ]]; then
  if command -v nproc >/dev/null 2>&1; then
    CORES="$(nproc)"
  else
    CORES="$(sysctl -n hw.ncpu 2>/dev/null || echo 2)"
  fi
  JOBS=$(( CORES / 2 ))
  [[ "${JOBS}" -lt 1 ]] && JOBS=1
fi

echo "[build_coq_serapi_dumps] toolchain: $("${SERTOP}" --version)"
echo "[build_coq_serapi_dumps] out: ${OUT_DIR} (jobs=${JOBS})"

cargo build --locked --release -p clean-mathverse --bin mathverse_coq_dump \
  --manifest-path "${REPO_ROOT}/Cargo.toml"

SELECT=(--stdlib)
if [[ ${#MODULE_ARGS[@]} -gt 0 ]]; then
  SELECT=("${MODULE_ARGS[@]}")
fi

"${REPO_ROOT}/target/release/mathverse_coq_dump" \
  --sertop="${SERTOP}" \
  --out="${OUT_DIR}" \
  --jobs="${JOBS}" \
  --validate \
  ${FORCE:+"${FORCE}"} \
  "${SELECT[@]}"

echo "[build_coq_serapi_dumps] done: $(ls "${OUT_DIR}"/*.sexp 2>/dev/null | wc -l | tr -d ' ') module dumps"
