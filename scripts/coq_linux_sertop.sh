#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# sertop shim: run the LINUX container's sertop from the macOS host (D6b).
#
# MathComp needs coq-elpi/elpi, which is unbuildable on macOS/arm64, so the
# MathComp toolchain lives in the mathverse-coq-linux Docker image (see
# docker/coq-linux-runner/). The host dump driver (mathverse_coq_dump) spawns
# its sertop by path with piped stdio, so pointing --sertop= at THIS script
# transparently drives the container toolchain with zero Rust changes:
#
#   target/release/mathverse_coq_dump --sertop=scripts/coq_linux_sertop.sh ...
#
# Behavior:
#   - Starts the container from $MATHVERSE_COQ_IMAGE if it is not running
#     (named $MATHVERSE_COQ_CONTAINER; concurrent invocations may race to
#     start it — all racers poll until one wins).
#   - exec's `docker exec -i <container> /usr/local/bin/sertop "$@"`, so
#     stdin/stdout ARE the sertop pipe protocol. All shim diagnostics go to
#     stderr; stdout stays protocol-clean.
#   - `--version` passes straight through (the dump driver probes it).
#
# Caveat: the driver kills this shim (SIGKILL) on answer timeout. The docker
# exec client dies immediately; the in-container sertop then sees EOF on its
# stdin stream and exits. A brief straggler between kill and EOF-teardown is
# possible; scripts/build_mathcomp_dumps.sh sweeps leftovers after each run.

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
      echo "coq_linux_sertop: image ${IMAGE} not built — run:" >&2
      echo "  docker build -t ${IMAGE} docker/coq-linux-runner" >&2
      return 1
    fi
    # May lose a race with a sibling worker creating the same name: fine,
    # the poll below waits for whoever won.
    docker run -d --name "${CONTAINER}" "${IMAGE}" >/dev/null 2>&1 || true
  fi
  local i
  for i in $(seq 1 60); do
    running && return 0
    sleep 0.5
  done
  echo "coq_linux_sertop: container ${CONTAINER} failed to start from ${IMAGE}" >&2
  return 1
}

ensure_running
exec docker exec -i "${CONTAINER}" /usr/local/bin/sertop "$@"
