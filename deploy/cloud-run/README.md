<!--
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0
-->

# Mathverse on Cloud Run — Deployment Runbook (Phase 1)

This deploys **`mathverse_serve`**, the read-only Mathverse distribution
front-end, to Google Cloud Run. It browses, searches, and streams the verified
Mathverse Core over plain HTTP/1.1.

> **Trust posture — read this first.** The service is a *distribution
> front-end, NOT a trust authority*. Every payload surfaces the **stored
> import/source trust label** plus the per-declaration `expr_canonical_digest`
> so a consumer can re-verify independently (de Bruijn). It never mints,
> upgrades, or alters a verdict. **`KernelVerified` is the only independently
> re-verifiable tier**; all others are source/import self-attested.
>
> **Phase 1 is read-only** public browse / search / download. Proof
> **submission / minting is Phase 2** and is intentionally absent here.

> **You run the `gcloud` commands.** This directory provides everything with
> explicit placeholders; it assumes nothing about your GCP project or auth. No
> credentials are bundled and nothing here was deployed for you.

---

## What's in this directory

| File | Purpose |
|---|---|
| `Dockerfile` | Multi-stage build: release-compile `mathverse_serve`, slim non-root Debian runtime. Build context is the **repo root**. |
| `service.yaml` | Declarative Cloud Run (Knative) Service manifest with placeholders. gcsfuse-mounts the Core read-only at `/core`. |
| `deploy.sh` | Build + push image to Artifact Registry, then `gcloud run deploy`. |
| `gcs_sync.sh` | `gcloud storage rsync` the local Core up to `gs://BUCKET/core` ("convert once, share"). Fail-closed on a missing manifest; copies the release-root `mathverse-manifest.json` into the Core dir if absent. |
| `README.md` | This runbook. |

The repo root also gets a `.dockerignore` (created alongside these files) so the
Docker build context excludes `target/`, `.git/`, and any local Core.

---

## Placeholders you must fill

Set these as environment variables (the scripts read them) or edit the
defaults in `deploy.sh` / `gcs_sync.sh` / `service.yaml`:

| Placeholder | Meaning | Example |
|---|---|---|
| `PROJECT_ID` | Your GCP project id | `my-mathverse-proj` |
| `REGION` | Cloud Run region | `us-central1` |
| `AR_REPO` | Artifact Registry docker repo name | `mathverse` |
| `SERVICE` | Cloud Run service name | `mathverse-serve` |
| `CORE_BUCKET` | GCS bucket holding the Core | `mathverse-core-my-mathverse-proj` |
| `RUNTIME_SA` | Runtime service account email | `mathverse-serve@PROJECT_ID.iam.gserviceaccount.com` |
| `TAG` | Image tag (defaults to git short SHA) | `2026-06-24` |

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
gcloud artifacts repositories create mathverse \
  --repository-format=docker --location=REGION \
  --description="Mathverse Cloud Run images"

# GCS bucket for the Core (your choice of name + location)
gcloud storage buckets create gs://CORE_BUCKET \
  --location US --uniform-bucket-level-access

# Runtime service account + read access to the Core bucket
gcloud iam service-accounts create mathverse-serve \
  --display-name="Mathverse Cloud Run runtime"
gcloud storage buckets add-iam-policy-binding gs://CORE_BUCKET \
  --member="serviceAccount:mathverse-serve@PROJECT_ID.iam.gserviceaccount.com" \
  --role="roles/storage.objectViewer"
```

---

## Ordered deployment steps

### (a) Build the verified Core locally

Two paths. Either produces a **LibraryLoader layout** (`mathverse-manifest.json`
+ `base/` shards [+ `delta/`, + `baseline.mvix`]) — that is exactly what the
service loads from `$MATHVERSE_CORE_DIR`.

> **What's in the v1.3.0 Core.** Breadth across 15 shards plus the
> **cleankernel shard's KernelVerified depth**: 3,767 Metamath theorems whose
> stored trust label is `KernelVerified` (re-checked by the Clean kernel during
> the campaign). `/stats` therefore reports
> `by_trust_level.KernelVerified = 3767` and
> `independently_reverifiable.count = 3767`. The service re-serves those
> **stored** labels with the de-Bruijn re-verify note; it never relabels.

**Path 1 — download the published release (fast):**

```bash
# Downloads mathverse-library-v1.3.0.tar.zst and extracts it.
clean mathverse download --version 1.3.0 --out ./core
# (or use the equivalent release.rs `download_release` entry point)
```

> **Manifest filename.** A release archive ships `mathverse-manifest.json` at
> the archive **root** — i.e. the parent of the `mathverse-library/` Core dir.
> The service's `LibraryLoader` reads `mathverse-manifest.json` directly from
> the Core dir (falling back to it when no in-place `manifest.json` exists), so
> **no rename is needed**. If your extracted Core dir is missing it,
> `gcs_sync.sh` copies the release-root `mathverse-manifest.json` into the Core
> dir automatically and refuses to upload a Core with no manifest at all — so
> you catch a broken layout before it reaches Cloud Run.

**Path 2 — build from raw upstream sources (canonical, slow):**

```bash
cargo run -p clean-mathverse --release --bin mathverse_convert -- all ./core
```

This writes the manifest directly (no rename needed).

Sanity-check locally before uploading:

```bash
MATHVERSE_CORE_DIR=./core PORT=8080 \
  cargo run -p clean-mathverse --release --bin mathverse_serve
# in another shell:
curl -fsS localhost:8080/healthz   # -> ok
curl -fsS localhost:8080/stats | head -c 400; echo
```

### (b) Sync the Core up to GCS ("convert once, share")

```bash
PROJECT_ID=... CORE_BUCKET=... \
  ./deploy/cloud-run/gcs_sync.sh ./core
# mirrors ./core -> gs://CORE_BUCKET/core (parallel rsync, deletes stale objects)
```

### (c) + (d) Build, push, and deploy

```bash
PROJECT_ID=... REGION=... CORE_BUCKET=... \
  ./deploy/cloud-run/deploy.sh
```

`deploy.sh` builds `linux/amd64`, pushes to Artifact Registry, and runs
`gcloud run deploy` with the gcsfuse volume mounting `gs://CORE_BUCKET/core` at
`/core` (read-only). It prints the live URL when done.

> **Declarative alternative.** Edit the placeholders in `service.yaml`, then:
> ```bash
> gcloud run services replace deploy/cloud-run/service.yaml --region REGION
> ```

### (e) Smoke-test the live URL

```bash
URL=$(gcloud run services describe mathverse-serve \
  --region REGION --format='value(status.url)')

curl -fsS "$URL/healthz"                       # -> ok
curl -fsS "$URL/stats"          | jq .          # totals + honest trust ladder
curl -fsS "$URL/search?q=add&limit=5" | jq .    # name search
curl -fsS "$URL/theorem/SOME.Name"    | jq .    # one declaration (digest, axioms)
curl -fsS "$URL/shards"         | jq .          # shard inventory + sizes
curl -fsSL "$URL/download/SOME_SHARD" -o out.mathverse   # stream a shard
curl -fsS "$URL/"               | jq .          # banner + endpoint list + posture
```

`/stats` should report `independently_reverifiable.tier = "KernelVerified"` with
`independently_reverifiable.count = 3767` (the cleankernel depth, also visible as
`by_trust_level.KernelVerified`) and carry the `trust_note`. If those are
missing, you are not looking at this service. A sanity HIT:

```bash
curl -fsS "$URL/search?q=mm.idALT&limit=20" | jq '.results[]
  | select(.shard=="metamath_cleankernel")
  | {name, trust_level, shard, expr_canonical_digest}'
# -> mm.idALT, trust_level "KernelVerified", shard "metamath_cleankernel"
```

---

## How the Core reaches the container

The service reads `$MATHVERSE_CORE_DIR` (default `/core`). We mount the GCS
bucket there via the **gcsfuse CSI driver** (`run.googleapis.com` Gen2). This is
the simpler of the two options:

- **gcsfuse mount (chosen):** zero startup-sync code, fast cold start (no
  multi-GB copy at boot), read-only mount matches the read-only service. First
  touch of each shard is a network read; for browse/search/`/stats` that's just
  the manifest + small headers, and `/download` streams the bytes the client
  asked for anyway.
- **download-on-start (alternative):** `gsutil rsync gs://BUCKET/core /core` in a
  startup wrapper. Local-disk speed afterward, but a slow cold start and a large
  ephemeral disk. Rejected for Phase 1; documented in `service.yaml`.

**Optional download redirect.** Set `MATHVERSE_DOWNLOAD_BASE` (e.g.
`https://storage.googleapis.com/CORE_BUCKET/core`) to make `/download/{shard}`
return a `302` to GCS instead of streaming through the service. Requires the
`core/` prefix to be readable at that URL. Leave unset to stream from the mount.

---

## Resource / scaling notes

- **Memory 2Gi** is a safe Phase-1 ceiling for the v1.3.0 Core (headers + arenas
  in memory). Raise if you see OOM restarts on a larger Core.
- **Concurrency 8, single-threaded service.** The loaded library is `!Sync`
  (thread-local BM25 index), so the binary serves requests sequentially on one
  thread. Cloud Run scales **out by instance count** (`maxScale: 4`), not in by
  threads.
- **`minScale: 0`** scales to zero (cheapest, cold starts on first hit). Set
  `--min-instances 1` for a warm demo endpoint.
- **`--allow-unauthenticated`** makes this a public read-only endpoint. Drop it
  for an internal-only deploy (then callers need an identity token).

---

## Teardown

```bash
gcloud run services delete mathverse-serve --region REGION
# the Core bucket + image persist until you delete them explicitly:
# gcloud storage rm -r gs://CORE_BUCKET/core
# gcloud artifacts docker images delete IMAGE
```
