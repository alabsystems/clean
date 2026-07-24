#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# "Convert once, share": upload the local verified Core to GCS so every Cloud
# Run instance mounts the same bytes. This is a one-way mirror of the local
# Core directory (manifest + base/ + delta/ shards + optional
# baseline.mvix) to gs://CORE_BUCKET/core.
#
# YOU run this with YOUR gcloud auth. It moves data only — it does not verify
# or re-label anything. The trust labels are whatever the Core already carries.
# (The v1.3.0 Core now includes the cleankernel shard's KernelVerified depth;
# this script ships those stored labels unchanged — it never relabels.)
#
# Usage:
#   CORE_DIR=/path/to/local/core ./gcs_sync.sh
#   ./gcs_sync.sh /path/to/local/core          # positional override
#
# The local Core must be a LibraryLoader layout (what `mathverse_serve` loads):
#   mathverse-manifest.json  <- REQUIRED (LibraryLoader reads THIS name; it also
#                               accepts an in-place manifest.json if present)
#   base/*.mathverse         <- the shards
#   delta/*.mathverse        <- (optional) delta shards
#   baseline.mvix            <- (optional) novelty baseline index
#
# NOTE on manifest filename: a downloaded `mathverse-library-v*.tar.zst` release
# ships `mathverse-manifest.json` at the archive ROOT (the parent of the
# `mathverse-library/` Core dir). The LibraryLoader the service uses now reads
# `mathverse-manifest.json` directly from the Core dir (falling back to it when
# no in-place `manifest.json` exists) — no rename needed. This script copies the
# release-root `mathverse-manifest.json` INTO the Core dir if it is missing.

set -euo pipefail

# --- PLACEHOLDERS (override via env) ---------------------------------------
PROJECT_ID="${PROJECT_ID:-your-gcp-project}"
CORE_BUCKET="${CORE_BUCKET:-mathverse-core-${PROJECT_ID}}"
CORE_DIR="${1:-${CORE_DIR:-./core}}"
GCS_PREFIX="${GCS_PREFIX:-core}"   # uploads to gs://CORE_BUCKET/core

DEST="gs://${CORE_BUCKET}/${GCS_PREFIX}"

echo "==> Syncing local Core to GCS"
echo "    local   ${CORE_DIR}"
echo "    dest    ${DEST}"
echo "    project ${PROJECT_ID}"
echo

# --- preflight: the local Core must be a loadable LibraryLoader layout ------
if [[ ! -d "${CORE_DIR}" ]]; then
  echo "ERROR: CORE_DIR '${CORE_DIR}' is not a directory." >&2
  echo "       Build it first (clean mathverse download / mathverse_convert)." >&2
  exit 1
fi
# The LibraryLoader reads `mathverse-manifest.json` from the Core dir (and still
# accepts an in-place `manifest.json` if one is present). A downloaded release
# ships `mathverse-manifest.json` at the archive ROOT — i.e. the PARENT of the
# `mathverse-library/` Core dir — so place it into the Core dir if it's absent.
RELEASE_MANIFEST="mathverse-manifest.json"
if [[ ! -f "${CORE_DIR}/${RELEASE_MANIFEST}" && ! -f "${CORE_DIR}/manifest.json" ]]; then
  PARENT_MANIFEST="$(dirname "${CORE_DIR}")/${RELEASE_MANIFEST}"
  if [[ -f "${PARENT_MANIFEST}" ]]; then
    echo "    no manifest in Core dir — copying release manifest from parent:" >&2
    echo "      ${PARENT_MANIFEST} -> ${CORE_DIR}/${RELEASE_MANIFEST}" >&2
    cp "${PARENT_MANIFEST}" "${CORE_DIR}/${RELEASE_MANIFEST}"
  fi
fi
if [[ ! -f "${CORE_DIR}/${RELEASE_MANIFEST}" && ! -f "${CORE_DIR}/manifest.json" ]]; then
  echo "ERROR: no manifest found in Core dir '${CORE_DIR}'." >&2
  echo "       The service's LibraryLoader reads ${RELEASE_MANIFEST} (or an" >&2
  echo "       in-place manifest.json) at the Core root. A release ships" >&2
  echo "       ${RELEASE_MANIFEST} at the archive root (the parent of the" >&2
  echo "       mathverse-library/ Core dir); this script copies it in" >&2
  echo "       automatically, but neither location had it. Refusing to upload" >&2
  echo "       a Core the service cannot load." >&2
  exit 1
fi
shard_count="$(find "${CORE_DIR}" -name '*.mathverse' | wc -l | tr -d ' ')"
if [[ "${shard_count}" -eq 0 ]]; then
  echo "ERROR: no *.mathverse shards under '${CORE_DIR}'." >&2
  exit 1
fi
manifest_name="$( [[ -f "${CORE_DIR}/manifest.json" ]] && echo 'manifest.json' || echo "${RELEASE_MANIFEST}" )"
echo "    found   ${manifest_name} + ${shard_count} shard(s)$( [[ -f "${CORE_DIR}/baseline.mvix" ]] && echo ' + baseline.mvix' )"
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
# -m: parallel. rsync -r: recursive. -d: delete remote files not present
# locally so the mirror stays exact across Core rebuilds.
gcloud storage rsync -r --delete-unmatched-destination-objects \
  "${CORE_DIR}" "${DEST}"

echo
echo "==> Core mirrored. The Cloud Run service mounts gs://${CORE_BUCKET}/${GCS_PREFIX}"
echo "    at /core (read-only). Re-run this script after every Core rebuild."
