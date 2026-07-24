#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# Build importer-form SerAPI .sexp dumps of the MathComp library (D6b).
#
# MathComp's toolchain lives in a Linux container (macOS/arm64 cannot build
# coq-elpi/elpi — see docker/coq-linux-runner/README.md). The HOST dump
# driver (mathverse_coq_dump) drives the container's sertop through
# scripts/coq_linux_sertop.sh and writes per-module dumps + sidecars + a
# manifest under data/corpora/coq-sexp/mathcomp/ in the exact forms consumed
# by coq::alpha::CoqImporter::import_sexp — same conventions as
# scripts/build_coq_serapi_dumps.sh (idempotent: fresh .sexp + .meta.json
# pairs are skipped unless --force; the binary writes manifest.json itself).
#
# Extra provenance: container-toolchain.json records the container image id /
# digest, docker server platform, and the exact opam package solution.
#
# Usage: scripts/build_mathcomp_dumps.sh [--force] [--jobs=N] [--timeout=SECS]
#          [--only=PREFIX ...] [--module=M ...]
#   --only=mathcomp.ssreflect. restricts to modules with that logical prefix;
#   --module=M adds an explicit module (bypasses container enumeration);
#   default is every compiled mathcomp module found in the container.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WRAPPER="${REPO_ROOT}/scripts/coq_linux_sertop.sh"
OUT_DIR="${REPO_ROOT}/data/corpora/coq-sexp/mathcomp"
DUMP_BIN="${REPO_ROOT}/target/release/mathverse_coq_dump"
CONTAINER="${MATHVERSE_COQ_CONTAINER:-mathverse-coq-linux}"
IMAGE="${MATHVERSE_COQ_IMAGE:-mathverse-coq-linux:mc1.19.0-coq8.20.0}"
export MATHVERSE_COQ_CONTAINER="${CONTAINER}" MATHVERSE_COQ_IMAGE="${IMAGE}"

FORCE=""
JOBS=""
TIMEOUT="300"
ONLY_PREFIXES=()
MODULE_ARGS=()
for arg in "$@"; do
  case "${arg}" in
    --force) FORCE="--force" ;;
    --jobs=*) JOBS="${arg#--jobs=}" ;;
    --timeout=*) TIMEOUT="${arg#--timeout=}" ;;
    --only=*) ONLY_PREFIXES+=("${arg#--only=}") ;;
    --module=*) MODULE_ARGS+=("${arg#--module=}") ;;
    *)
      echo "error: unknown argument: ${arg}" >&2
      exit 1
      ;;
  esac
done

if ! docker image inspect "${IMAGE}" >/dev/null 2>&1; then
  cat >&2 <<EOF
error: container image ${IMAGE} not found

Build the Linux Coq+MathComp toolchain first (30-60 min):

  docker build -t ${IMAGE} ${REPO_ROOT}/docker/coq-linux-runner

See docker/coq-linux-runner/README.md for fallback pin paths.
EOF
  exit 1
fi

# Starts the container if needed AND proves the wrapper round-trip: the
# version string must come back from the CONTAINER toolchain over the same
# stdout pipe the dump protocol uses.
TOOLCHAIN_VERSION="$("${WRAPPER}" --version)"
if [[ -z "${TOOLCHAIN_VERSION}" ]]; then
  echo "error: wrapper round-trip failed (empty sertop --version)" >&2
  exit 1
fi
echo "[build_mathcomp_dumps] container toolchain: ${TOOLCHAIN_VERSION}"

if [[ -z "${JOBS}" ]]; then
  # Workers all land inside the one container: size by ITS cpu budget.
  NCPU="$(docker info --format '{{.NCPU}}' 2>/dev/null || echo 2)"
  JOBS=$(( NCPU / 2 ))
  [[ "${JOBS}" -lt 1 ]] && JOBS=1
fi

mkdir -p "${OUT_DIR}"
MODULES_FILE="${OUT_DIR}/modules.txt"

# Enumerate compiled MathComp modules INSIDE the container:
#   <lib>/coq/user-contrib/mathcomp/<subdirs>/<stem>.vo
#     -> logical path mathcomp.<subdirs>.<stem>
{
  echo "# MathComp modules enumerated from container ${IMAGE}"
  echo "# ($(date -u +%Y-%m-%dT%H:%M:%SZ); regenerate with scripts/build_mathcomp_dumps.sh)"
  if [[ ${#MODULE_ARGS[@]} -gt 0 ]]; then
    printf '%s\n' "${MODULE_ARGS[@]}"
  else
    docker exec "${CONTAINER}" sh -lc \
      'find "$(opam var lib)/coq/user-contrib/mathcomp" -name "*.vo" | sort' \
      | sed -e 's#.*/user-contrib/##' -e 's#\.vo$##' -e 's#/#.#g'
  fi
} > "${MODULES_FILE}"

if [[ ${#ONLY_PREFIXES[@]} -gt 0 ]]; then
  FILTERED="${MODULES_FILE}.filtered"
  {
    head -2 "${MODULES_FILE}"
    for p in "${ONLY_PREFIXES[@]}"; do
      grep -v '^#' "${MODULES_FILE}" | grep "^${p}" || true
    done
  } > "${FILTERED}"
  mv "${FILTERED}" "${MODULES_FILE}"
fi

N_MODULES="$(grep -cv '^#' "${MODULES_FILE}" || true)"
if [[ "${N_MODULES}" -eq 0 ]]; then
  echo "error: no modules selected (check --only= prefixes against ${MODULES_FILE})" >&2
  exit 1
fi
echo "[build_mathcomp_dumps] ${N_MODULES} modules -> ${OUT_DIR} (jobs=${JOBS}, timeout=${TIMEOUT}s)"

# Provenance sidecar: image digest + platform + exact opam solution. The
# dump manifest.json (written by the binary) records coq/serapi versions as
# reported over the wrapper; this records WHERE they ran.
IMAGE_ID="$(docker image inspect -f '{{.Id}}' "${IMAGE}")"
IMAGE_DIGESTS="$(docker image inspect -f '{{join .RepoDigests ","}}' "${IMAGE}")"
PLATFORM="$(docker version --format '{{.Server.Os}}/{{.Server.Arch}} (server {{.Server.Version}})')"
MATHCOMP_VARIANT="$(docker image inspect -f '{{index .Config.Labels "org.mathverse.mathcomp-variant"}}' "${IMAGE}")"
OPAM_PKGS="$(docker exec "${CONTAINER}" sh -lc \
  "grep -E '^(ocaml|coq|coq-serapi|coq-mathcomp-[a-z]+|elpi|coq-elpi|coq-hierarchy-builder) ' /home/opam/opam-installed.txt \
   | awk '{printf \"%s.%s \", \$1, \$2}'")"
cat > "${OUT_DIR}/container-toolchain.json" <<EOF
{
  "image": "${IMAGE}",
  "image_id": "${IMAGE_ID}",
  "repo_digests": "${IMAGE_DIGESTS}",
  "platform": "${PLATFORM}",
  "mathcomp_variant": "${MATHCOMP_VARIANT}",
  "sertop_version": "${TOOLCHAIN_VERSION}",
  "opam_packages": "${OPAM_PKGS% }",
  "wrapper": "scripts/coq_linux_sertop.sh",
  "generated": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF

# Host driver (only rebuild when missing: the shared cargo lock is contended).
if [[ ! -x "${DUMP_BIN}" ]]; then
  cargo build --locked --release -p clean-mathverse --bin mathverse_coq_dump \
    --manifest-path "${REPO_ROOT}/Cargo.toml"
fi

"${DUMP_BIN}" \
  --sertop="${WRAPPER}" \
  --out="${OUT_DIR}" \
  --modules-file="${MODULES_FILE}" \
  --jobs="${JOBS}" \
  --timeout="${TIMEOUT}" \
  --validate \
  ${FORCE:+"${FORCE}"}

# Sweep sertop stragglers left by timeout kills (see wrapper caveat).
docker exec "${CONTAINER}" sh -c 'pkill -f sertop || true' >/dev/null 2>&1 || true

echo "[build_mathcomp_dumps] done: $(ls "${OUT_DIR}"/*.sexp 2>/dev/null | wc -l | tr -d ' ') module dumps in ${OUT_DIR}"
