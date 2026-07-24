#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Build + push the mathverse_serve image to Artifact Registry, then deploy it
# to Cloud Run with the gcsfuse-mounted verified Core.
#
# YOU run this — it uses YOUR gcloud auth + GCP project. Nothing here mints or
# alters a trust verdict; this ships the read-only Phase-1 distribution
# front-end. Fill the PLACEHOLDERS below (or pass them as env vars).
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
AR_REPO="${AR_REPO:-mathverse}"                      # Artifact Registry repo name
SERVICE="${SERVICE:-mathverse-serve}"                # Cloud Run service name
CORE_BUCKET="${CORE_BUCKET:-mathverse-core-${PROJECT_ID}}"
RUNTIME_SA="${RUNTIME_SA:-mathverse-serve@${PROJECT_ID}.iam.gserviceaccount.com}"
TAG="${TAG:-$(git rev-parse --short HEAD 2>/dev/null || date +%Y%m%d%H%M%S)}"
MEMORY="${MEMORY:-2Gi}"
CPU="${CPU:-1}"
MIN_INSTANCES="${MIN_INSTANCES:-0}"
MAX_INSTANCES="${MAX_INSTANCES:-4}"
CONCURRENCY="${CONCURRENCY:-8}"

IMAGE="${REGION}-docker.pkg.dev/${PROJECT_ID}/${AR_REPO}/${SERVICE}:${TAG}"

# Repo root = two levels up from this script (deploy/cloud-run/).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

echo "==> Deploying ${SERVICE} to Cloud Run"
echo "    project        ${PROJECT_ID}"
echo "    region         ${REGION}"
echo "    image          ${IMAGE}"
echo "    core bucket     gs://${CORE_BUCKET}/core (mounted read-only at /core)"
echo "    runtime SA     ${RUNTIME_SA}"
echo "    scale          ${MIN_INSTANCES}..${MAX_INSTANCES}  concurrency=${CONCURRENCY}"
echo "    resources      mem=${MEMORY} cpu=${CPU}"
echo

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
  --set-env-vars "MATHVERSE_CORE_DIR=/core,RUST_MIN_STACK=67108864" \
  --add-volume "name=core-bucket,type=cloud-storage,bucket=${CORE_BUCKET},readonly=true" \
  --add-volume-mount "volume=core-bucket,mount-path=/core" \
  --allow-unauthenticated

echo
echo "==> Deployed. Service URL:"
URL="$(gcloud run services describe "${SERVICE}" --project "${PROJECT_ID}" \
  --region "${REGION}" --format='value(status.url)')"
echo "    ${URL}"
echo
echo "Smoke-test it:"
echo "    curl -fsS ${URL}/healthz   # -> ok"
echo "    curl -fsS ${URL}/stats | head -c 400; echo"
echo
echo "NOTE: --allow-unauthenticated makes this a PUBLIC read-only browse/search/"
echo "download endpoint (Phase 1). Drop that flag for an internal-only deploy."
echo "OPTIONAL: to 302-redirect downloads to GCS instead of streaming bytes,"
echo "add MATHVERSE_DOWNLOAD_BASE=https://storage.googleapis.com/${CORE_BUCKET}/core"
echo "to --set-env-vars and make the core/ prefix public-readable."
