#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# sertop-projfix shim: run the LINUX container's PATCHED sertop from the host.
#
# Identical to scripts/coq_linux_sertop.sh except it execs
# /usr/local/bin/sertop-projfix instead of /usr/local/bin/sertop. The projfix
# binary is a coq-serapi 8.20.0+0.20.0 build with the serlib Projection.Repr
# memory-layout fix (docker/coq-linux-runner/serlib-projfix.patch): the stock
# sertop SEGFAULTS serializing any term with a primitive projection (Proj)
# node -- its Pierce Obj.magic mirror of Names.Projection.Repr.t is the stale
# pre-8.18 5-field layout, so it reads field 4 out of bounds of the real
# 4-field record and dereferences garbage as a string. The fix makes the
# ~1200 Proj-bearing MathComp constants dump with real values instead of
# type-only stand-ins.
#
# Usage (re-dump a module into a corpus COPY, never the shared corpus):
#   target/release/mathverse_coq_dump \
#     --sertop=scripts/coq_linux_sertop_projfix.sh \
#     --out=<copy>/mathcomp --modules-file=<mods> --force --validate

set -euo pipefail

CONTAINER="${MATHVERSE_COQ_CONTAINER:-mathverse-coq-linux}"
IMAGE="${MATHVERSE_COQ_IMAGE:-mathverse-coq-linux:mc1.19.0-coq8.20.0}"

running() {
  [[ "$(docker inspect -f '{{.State.Running}}' "${CONTAINER}" 2>/dev/null)" == "true" ]]
}

ensure_running() {
  running && return 0
  local state
  state="$(docker inspect -f '{{.State.Running}}' "${CONTAINER}" 2>/dev/null || echo absent)"
  if [[ "${state}" == "false" ]]; then
    docker start "${CONTAINER}" >/dev/null 2>&1 || true
  else
    if ! docker image inspect "${IMAGE}" >/dev/null 2>&1; then
      echo "coq_linux_sertop_projfix: image ${IMAGE} not built" >&2
      return 1
    fi
    docker run -d --name "${CONTAINER}" "${IMAGE}" >/dev/null 2>&1 || true
  fi
  local i
  for i in $(seq 1 60); do
    running && return 0
    sleep 0.5
  done
  echo "coq_linux_sertop_projfix: container ${CONTAINER} failed to start from ${IMAGE}" >&2
  return 1
}

ensure_running
exec docker exec -i "${CONTAINER}" /usr/local/bin/sertop-projfix "$@"
