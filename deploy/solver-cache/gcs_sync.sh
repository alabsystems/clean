#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# "Convert once, share": upload the local solver-cache Core to GCS so every
# Cloud Run instance mounts the same bytes. This is a one-way mirror of the
# local Core directory to gs://CORE_BUCKET/core.
#
# YOU run this with YOUR gcloud auth. It moves data only — it does not verify or
# re-label anything. A cached result is PROVENANCE: the telemetry is a hint and
# the `<digest>.scache` proof blobs are re-checkable by the consumer's kernel,
# never trusted by this transport. This script ships the bytes unchanged.
#
# Usage:
#   CORE_DIR=/path/to/local/core ./gcs_sync.sh
#   ./gcs_sync.sh /path/to/local/core          # positional override
#
# The local Core is the solver-cache producer artifact layout — the SAME dirs
# the producer + `clean solver` CLI + the service read via $CLEAN_SOLVER_*:
#   telemetry/attempts.jsonl   <- REQUIRED: the solver-attempt-record-v1 stream
#   cache/<digest>.scache      <- (optional) re-checkable proof blobs
#   solver.vcidx               <- (optional) pre-built VCIDX01 index (µs /lookup)
#
# Build the Core locally first with the Phase-0/1 producer + the index builder:
#   CLEAN_SOLVER_TELEMETRY_DIR=./core/telemetry CLEAN_SOLVER_CACHE_DIR=./core/cache \
#     <run the swarm / graduation so attempts + proofs accrue>
#   clean solver index-build --out ./core/solver.vcidx   # see cmd_solver.rs
#
# The uploaded layout mirrors the service mount:
#   gs://CORE_BUCKET/core/telemetry/attempts.jsonl
#   gs://CORE_BUCKET/core/cache/<digest>.scache
#   gs://CORE_BUCKET/core/solver.vcidx

set -euo pipefail

# --- PLACEHOLDERS (override via env) ---------------------------------------
PROJECT_ID="${PROJECT_ID:-your-gcp-project}"
CORE_BUCKET="${CORE_BUCKET:-solver-cache-core-${PROJECT_ID}}"
CORE_DIR="${1:-${CORE_DIR:-./core}}"
GCS_PREFIX="${GCS_PREFIX:-core}"   # uploads to gs://CORE_BUCKET/core

DEST="gs://${CORE_BUCKET}/${GCS_PREFIX}"

echo "==> Syncing local solver-cache Core to GCS"
echo "    local   ${CORE_DIR}"
echo "    dest    ${DEST}"
echo "    project ${PROJECT_ID}"
echo

# --- preflight: the local Core must be a loadable producer layout ------------
if [[ ! -d "${CORE_DIR}" ]]; then
  echo "ERROR: CORE_DIR '${CORE_DIR}' is not a directory." >&2
  echo "       Build it first (Phase-0 telemetry + Phase-1 index-build)." >&2
  exit 1
fi
# The service reads the telemetry stream from $CLEAN_SOLVER_TELEMETRY_DIR. At
# minimum the Core must carry a telemetry/attempts.jsonl (the read endpoints
# aggregate it). The cache/ blobs + solver.vcidx are optional accelerators.
TELEMETRY="${CORE_DIR}/telemetry/attempts.jsonl"
if [[ ! -f "${TELEMETRY}" && ! -f "${CORE_DIR}/attempts.jsonl" ]]; then
  echo "ERROR: no telemetry stream found in Core dir '${CORE_DIR}'." >&2
  echo "       Expected ${CORE_DIR}/telemetry/attempts.jsonl (or" >&2
  echo "       ${CORE_DIR}/attempts.jsonl). The service aggregates this stream;" >&2
  echo "       refusing to upload a Core the service cannot read." >&2
  exit 1
fi
scache_count="$(find "${CORE_DIR}" -name '*.scache' | wc -l | tr -d ' ')"
vcidx_note=""
[[ -f "${CORE_DIR}/solver.vcidx" ]] && vcidx_note=" + solver.vcidx"
echo "    found   attempts.jsonl + ${scache_count} proof blob(s)${vcidx_note}"
echo

echo "==> [1/2] Ensuring bucket gs://${CORE_BUCKET} exists"
if ! gcloud storage buckets describe "gs://${CORE_BUCKET}" --project "${PROJECT_ID}" >/dev/null 2>&1; then
  echo "    bucket not found — create it explicitly before re-running, e.g.:"
  echo "      gcloud storage buckets create gs://${CORE_BUCKET} \\"
  echo "        --project ${PROJECT_ID} --location US --uniform-bucket-level-access"
  echo "    (not auto-created here — bucket naming/location is YOUR decision)"
  exit 1
fi

echo "==> [2/2] rsync (parallel, delete extraneous) -> ${DEST}"
# -r: recursive. --delete-unmatched-destination-objects: delete remote files not
# present locally so the mirror stays exact across Core rebuilds.
gcloud storage rsync -r --delete-unmatched-destination-objects \
  "${CORE_DIR}" "${DEST}"

echo
echo "==> Core mirrored. The Cloud Run service mounts gs://${CORE_BUCKET}/${GCS_PREFIX}"
echo "    at /core (read-only by default). Re-run this script after every Core"
echo "    rebuild. Trust note: this ships PROVENANCE — the consumer re-checks any"
echo "    proof blob through the kernel; the transport asserts nothing."
