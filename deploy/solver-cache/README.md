<!--
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0
-->

# Solver-results cache on Cloud Run — Deployment Runbook (Phase 2)

This deploys **`solver_serve`**, the solver-results-cache distribution + ingest
front-end, to Google Cloud Run. It queries and (optionally) ingests the
solver-attempt telemetry + content-addressed proof cache over plain HTTP/1.1. It
is the software-verification analogue of `mathverse_serve` (which serves verified
MATH): `solver_serve` serves **solved obligations**.

> **Trust posture — read this first.** The service is a *distribution front-end,
> NOT a trust authority* (design §10.3). A cached solving result is
> **PROVENANCE, never a verdict**:
>
> - A **proof-bearing** result ships a re-checkable proof term; the consumer
>   MUST re-run it through the kernel (`recheck_and_classify`). The solver stays
>   out of the TCB. The obligation digest is a soundness **bucket**; the kernel
>   is the **arbiter**.
> - A **raw** unsat/timeout/unknown verdict is **telemetry / a hint**, never a
>   verification.
> - `POST /ingest` **NEVER mints a `verified` badge** — every ingest response
>   carries `verified: false`. A submitted proof is stored *untrusted* (it must
>   only *decode* to a well-formed kernel term so the store holds no garbage);
>   the consumer's kernel re-check is the arbiter.
>
> Every substantive response restates this via `trust_note` + `soundness_model`,
> mirroring `mathverse_serve`.

> **You run the `gcloud` commands.** This directory provides everything with
> explicit placeholders; it assumes nothing about your GCP project or auth. No
> credentials are bundled and nothing here was deployed for you.

---

## What's in this directory

| File | Purpose |
|---|---|
| `Dockerfile` | Multi-stage build: release-compile `solver_serve` (in `clean-auto`), slim non-root Debian runtime. Build context is the **repo root**. |
| `service.yaml` | Declarative Cloud Run (Knative) Service manifest with placeholders. gcsfuse-mounts the Core read-only at `/core`. |
| `deploy.sh` | Build + push image to Artifact Registry, then `gcloud run deploy`. `INGEST=1` enables a writable ingest deployment. |
| `gcs_sync.sh` | `gcloud storage rsync` the local Core up to `gs://BUCKET/core` ("convert once, share"). Fail-closed on a missing telemetry stream. |
| `README.md` | This runbook. |

The repo root's `.dockerignore` (shared with `deploy/cloud-run/`) already excludes
`target/`, `.git/`, and local Core artifacts (`*.scache`, `*.vcidx`, `core/`) from
the Docker build context.

---

## The Core layout (`$CLEAN_SOLVER_*`)

The service reads the SAME producer artifacts the Phase-0/1 producer + the
`clean solver` CLI write, via these env vars (the Dockerfile + `service.yaml`
default them under `/core`):

| Env var | Mount path | Content |
|---|---|---|
| `CLEAN_SOLVER_TELEMETRY_DIR` | `/core/telemetry` | `attempts.jsonl` — the `solver-attempt-record-v1` stream (REQUIRED). |
| `CLEAN_SOLVER_CACHE_DIR` | `/core/cache` | `<obligation_digest-hex>.scache` re-checkable proof blobs (optional). |
| `CLEAN_SOLVER_INDEX` | `/core/solver.vcidx` | a pre-built `VCIDX01` index for µs `/lookup` (optional). |
| `CLEAN_SOLVER_BUDGET_MS` | — | PAR-2 timeout budget the reports assume (default 5000). |
| `CLEAN_SOLVER_INGEST` | — | set non-empty to enable `POST /ingest` (off by default). |

---

## Placeholders you must fill

Set these as environment variables (the scripts read them) or edit the defaults
in `deploy.sh` / `gcs_sync.sh` / `service.yaml`:

| Placeholder | Meaning | Example |
|---|---|---|
| `PROJECT_ID` | Your GCP project id | `my-clean-proj` |
| `REGION` | Cloud Run region | `us-central1` |
| `AR_REPO` | Artifact Registry docker repo name | `solver-cache` |
| `SERVICE` | Cloud Run service name | `solver-serve` |
| `CORE_BUCKET` | GCS bucket holding the Core | `solver-cache-core-my-clean-proj` |
| `RUNTIME_SA` | Runtime service account email | `solver-serve@PROJECT_ID.iam.gserviceaccount.com` |
| `TAG` | Image tag (defaults to git short SHA) | `2026-06-28` |

In `service.yaml` the literal tokens `PROJECT_ID`, `REGION`, `IMAGE`,
`CORE_BUCKET` must be replaced before `gcloud run services replace`. (If you use
`deploy.sh`, it passes these as flags and you do **not** need to edit
`service.yaml` — the YAML is the GitOps/review equivalent.)

---

## One-time GCP setup (you run these)

```bash
gcloud auth login
gcloud config set project PROJECT_ID

# APIs
gcloud services enable \
  run.googleapis.com \
  artifactregistry.googleapis.com \
  storage.googleapis.com

# Artifact Registry docker repo
gcloud artifacts repositories create solver-cache \
  --repository-format=docker --location=REGION \
  --description="Solver-results-cache Cloud Run images"

# GCS bucket for the Core (your choice of name + location)
gcloud storage buckets create gs://CORE_BUCKET \
  --location US --uniform-bucket-level-access

# Runtime service account + read access to the Core bucket
gcloud iam service-accounts create solver-serve \
  --display-name="solver_serve Cloud Run runtime"
gcloud storage buckets add-iam-policy-binding gs://CORE_BUCKET \
  --member="serviceAccount:solver-serve@PROJECT_ID.iam.gserviceaccount.com" \
  --role="roles/storage.objectViewer"
```

---

## Ordered deployment steps

### (a) Build the solver-cache Core locally

The Core is the Phase-0/1 producer output. Point the producer (the swarm /
graduation run, or any solving campaign) at a telemetry + cache dir, then build
the index:

```bash
mkdir -p ./core/telemetry ./core/cache
CLEAN_SOLVER_TELEMETRY_DIR=./core/telemetry \
CLEAN_SOLVER_CACHE_DIR=./core/cache \
  <run the solving campaign so attempts.jsonl + <digest>.scache accrue>

# Build the VCIDX01 index for µs /lookup (see clean-cli cmd_solver.rs):
clean solver index-build --out ./core/solver.vcidx
```

Sanity-check locally before uploading:

```bash
CLEAN_SOLVER_TELEMETRY_DIR=./core/telemetry \
CLEAN_SOLVER_CACHE_DIR=./core/cache \
CLEAN_SOLVER_INDEX=./core/solver.vcidx PORT=8080 \
  cargo run --locked --release -p clean-auto --bin solver_serve
# in another shell:
curl -fsS localhost:8080/healthz   # -> ok
curl -fsS localhost:8080/stats | head -c 400; echo
```

### (b) Sync the Core up to GCS ("convert once, share")

```bash
PROJECT_ID=... CORE_BUCKET=... \
  ./deploy/solver-cache/gcs_sync.sh ./core
# mirrors ./core -> gs://CORE_BUCKET/core (parallel rsync, deletes stale objects)
```

### (c) + (d) Build, push, and deploy

```bash
PROJECT_ID=... REGION=... CORE_BUCKET=... \
  ./deploy/solver-cache/deploy.sh
```

`deploy.sh` builds `linux/amd64`, pushes to Artifact Registry, and runs
`gcloud run deploy` with the gcsfuse volume mounting `gs://CORE_BUCKET/core` at
`/core` (read-only). It prints the live URL when done.

> **Declarative alternative.** Edit the placeholders in `service.yaml`, then:
> ```bash
> gcloud run services replace deploy/solver-cache/service.yaml --region REGION
> ```

### (e) Smoke-test the live URL

```bash
URL=$(gcloud run services describe solver-serve \
  --region REGION --format='value(status.url)')

curl -fsS "$URL/healthz"                              # -> ok
curl -fsS "$URL/stats"                  | jq .         # aggregate report + trust note
curl -fsS "$URL/weak?by=theory&top=10"  | jq .        # worst-class regression worklist
curl -fsS "$URL/vbs-gap"                | jq .         # the Phase-3 gate (VBS-SBS gap)
curl -fsS "$URL/lookup/blake3:aaaa...." | jq .        # per-obligation provenance + re-check note
curl -fsS "$URL/export-dataset?limit=5" | jq .        # bounded NN dataset rows
curl -fsS "$URL/"                       | jq .         # banner + endpoint list + posture
```

`/stats` carries the `soundness_model` block and `trust_note` ("not a trust
authority"); `/lookup` reports `re_checkable` + `verdict_kind`. If those are
missing, you are not looking at this service.

---

## Enabling ingest (`POST /ingest`)

Ingest is **off by default** (a read-only distribution front-end). To accept
submitted records (+ optional re-checkable proof blobs), you need a **writable**
Core mount and the ingest flag:

```bash
INGEST=1 PROJECT_ID=... REGION=... CORE_BUCKET=... \
  ./deploy/solver-cache/deploy.sh
```

`deploy.sh` then drops the volume's `readonly` flag and sets
`CLEAN_SOLVER_INGEST=1`. Ingest still **mints nothing**: it validates the
envelope (schema, full `blake3:<64hex>` digest, that a proof accompanies only a
`Proved` result, and that the blob *decodes* to a well-formed kernel term —
fail-closed, nothing appended on a reject), appends the record to
`attempts.jsonl`, stores the proof blob *untrusted*, and returns `202` with
`verified: false`. The consumer's kernel re-check is the arbiter.

```bash
curl -fsS -X POST "$URL/ingest" -H 'content-type: application/json' \
  -d '{"record":{...solver-attempt-record-v1...},"proof_term_hex":"<bincode(Expr) hex>"}'
# -> 202 {"accepted":true,"verified":false,"re_checkable":true,...}
```

> **Production note.** A public writable ingest endpoint accepts unbounded
> provenance from anyone. For a shared deployment, prefer the offline
> convert-once factory (design §10.1) — ingest CI/swarm runs once, replay-validate
> the `[PROVED]` blobs against a clean kernel checkout, then publish a read-only
> Core — and keep `/ingest` behind an internal-only (no `--allow-unauthenticated`)
> revision.

---

## How the Core reaches the container

The service reads the `$CLEAN_SOLVER_*` dirs under `/core`. We mount the GCS
bucket there via the **gcsfuse CSI driver** (`run.googleapis.com` Gen2):

- **gcsfuse mount (chosen):** zero startup-sync code, fast cold start (no copy at
  boot), read-only mount matches the read-only default posture. Browse/query
  endpoints read the telemetry stream + small `VCIDX01` header; `/export-dataset`
  streams bounded rows.
- **download-on-start (alternative):** `gsutil rsync gs://BUCKET/core /core` in a
  startup wrapper. Local-disk speed afterward, slow cold start. Not used here.

---

## Resource / scaling notes

- **Memory 1Gi** is a safe Phase-2 ceiling (the `VCIDX01` header + in-memory
  aggregation arenas are small). Raise if `/stats` reports OOM on a much larger
  telemetry corpus.
- **Concurrency 8, single-threaded service.** The binary runs a current-thread
  tokio runtime and serves requests sequentially; each request is a cheap
  in-memory aggregate or an append. Cloud Run scales **out by instance count**
  (`maxScale: 4`), not in by threads.
- **`minScale: 0`** scales to zero (cheapest, cold starts on first hit). Set
  `--min-instances 1` for a warm demo endpoint.
- **`--allow-unauthenticated`** makes this a public endpoint. Drop it for an
  internal-only deploy (then callers need an identity token) — strongly advised
  if ingest is enabled.

---

## Teardown

```bash
gcloud run services delete solver-serve --region REGION
# the Core bucket + image persist until you delete them explicitly:
# gcloud storage rm -r gs://CORE_BUCKET/core
# gcloud artifacts docker images delete IMAGE
```
