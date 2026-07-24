#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Build + push the solver_serve image to Artifact Registry, then deploy it to
# Cloud Run with the gcsfuse-mounted solver-cache Core.
#
# YOU run this — it uses YOUR gcloud auth + GCP project. Nothing here mints or
# alters a trust verdict; this ships the Phase-2 DISTRIBUTION front-end. A cached
# result is PROVENANCE, never a verdict; ingest (off by default) mints nothing.
# Fill the PLACEHOLDERS below (or pass them as env vars).
#
# Prereqs (one-time, see README.md):
#   - gcloud auth login   &&   gcloud config set project PROJECT_ID
#   - gcloud services enable run.googleapis.com artifactregistry.googleapis.com \
#       storage.googleapis.com
#   - an Artifact Registry docker repo (see AR_REPO below; create cmd in README)
#   - the runtime service account + roles/storage.objectViewer on the Core bucket
#   - the Core uploaded to gs://CORE_BUCKET/core  (run gcs_sync.sh first)

set -euo pipefail

# --- PLACEHOLDERS (override via env) ---------------------------------------
PROJECT_ID="${PROJECT_ID:-your-gcp-project}"
REGION="${REGION:-us-central1}"
AR_REPO="${AR_REPO:-solver-cache}"                   # Artifact Registry repo name
SERVICE="${SERVICE:-solver-serve}"                   # Cloud Run service name
CORE_BUCKET="${CORE_BUCKET:-solver-cache-core-${PROJECT_ID}}"
RUNTIME_SA="${RUNTIME_SA:-solver-serve@${PROJECT_ID}.iam.gserviceaccount.com}"
TAG="${TAG:-$(git rev-parse --short HEAD 2>/dev/null || date +%Y%m%d%H%M%S)}"
MEMORY="${MEMORY:-1Gi}"
CPU="${CPU:-1}"
MIN_INSTANCES="${MIN_INSTANCES:-0}"
MAX_INSTANCES="${MAX_INSTANCES:-4}"
CONCURRENCY="${CONCURRENCY:-8}"
BUDGET_MS="${BUDGET_MS:-5000}"
# Set INGEST=1 to enable POST /ingest. This REQUIRES a writable Core mount, so it
# also drops the read-only flag on the volume below. Ingest still mints nothing.
INGEST="${INGEST:-0}"

IMAGE="${REGION}-docker.pkg.dev/${PROJECT_ID}/${AR_REPO}/${SERVICE}:${TAG}"

# Repo root = two levels up from this script (deploy/solver-cache/).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

echo "==> Deploying ${SERVICE} to Cloud Run"
echo "    project        ${PROJECT_ID}"
echo "    region         ${REGION}"
echo "    image          ${IMAGE}"
echo "    core bucket    gs://${CORE_BUCKET}/core (mounted at /core)"
echo "    runtime SA     ${RUNTIME_SA}"
echo "    scale          ${MIN_INSTANCES}..${MAX_INSTANCES}  concurrency=${CONCURRENCY}"
echo "    resources      mem=${MEMORY} cpu=${CPU}  budget_ms=${BUDGET_MS}"
echo "    ingest         $( [[ "${INGEST}" != "0" ]] && echo 'ENABLED (writable mount)' || echo 'disabled (read-only)' )"
echo

# Env vars passed to the container. The Core layout under /core matches gcs_sync.sh.
ENV_VARS="CLEAN_SOLVER_TELEMETRY_DIR=/core/telemetry"
ENV_VARS="${ENV_VARS},CLEAN_SOLVER_CACHE_DIR=/core/cache"
ENV_VARS="${ENV_VARS},CLEAN_SOLVER_INDEX=/core/solver.vcidx"
ENV_VARS="${ENV_VARS},CLEAN_SOLVER_BUDGET_MS=${BUDGET_MS}"
ENV_VARS="${ENV_VARS},RUST_MIN_STACK=67108864"
if [[ "${INGEST}" != "0" ]]; then
  ENV_VARS="${ENV_VARS},CLEAN_SOLVER_INGEST=1"
  VOLUME_FLAGS=(--add-volume "name=core-bucket,type=cloud-storage,bucket=${CORE_BUCKET}" \
                --add-volume-mount "volume=core-bucket,mount-path=/core")
else
  VOLUME_FLAGS=(--add-volume "name=core-bucket,type=cloud-storage,bucket=${CORE_BUCKET},readonly=true" \
                --add-volume-mount "volume=core-bucket,mount-path=/core")
fi

echo "==> [1/4] Configuring docker auth for Artifact Registry"
gcloud auth configure-docker "${REGION}-docker.pkg.dev" --quiet

echo "==> [2/4] Building image (build context = repo root)"
# Cloud Run runs linux/amd64; build for it explicitly (the Dockerfile pins the
# x86-64 baseline). On an Apple-silicon host docker buildx cross-builds.
docker build \
  --platform linux/amd64 \
  -f "${SCRIPT_DIR}/Dockerfile" \
  -t "${IMAGE}" \
  "${REPO_ROOT}"

echo "==> [3/4] Pushing image to Artifact Registry"
docker push "${IMAGE}"

echo "==> [4/4] Deploying to Cloud Run (gcsfuse volume mount of the Core)"
gcloud run deploy "${SERVICE}" \
  --project "${PROJECT_ID}" \
  --region "${REGION}" \
  --image "${IMAGE}" \
  --platform managed \
  --execution-environment gen2 \
  --service-account "${RUNTIME_SA}" \
  --memory "${MEMORY}" \
  --cpu "${CPU}" \
  --min-instances "${MIN_INSTANCES}" \
  --max-instances "${MAX_INSTANCES}" \
  --concurrency "${CONCURRENCY}" \
  --timeout 300 \
  --port 8080 \
  --set-env-vars "${ENV_VARS}" \
  "${VOLUME_FLAGS[@]}" \
  --allow-unauthenticated

echo
echo "==> Deployed. Service URL:"
URL="$(gcloud run services describe "${SERVICE}" --project "${PROJECT_ID}" \
  --region "${REGION}" --format='value(status.url)')"
echo "    ${URL}"
echo
echo "Smoke-test it:"
echo "    curl -fsS ${URL}/healthz                 # -> ok"
echo "    curl -fsS ${URL}/stats | head -c 400; echo"
echo "    curl -fsS ${URL}/vbs-gap                 # the Phase-3 gate (VBS-SBS gap)"
echo
echo "NOTE: --allow-unauthenticated makes this a PUBLIC read-only query endpoint."
echo "Drop that flag for an internal-only deploy. A cached result is PROVENANCE,"
echo "not a verdict — every response says so (trust_note + soundness_model)."
