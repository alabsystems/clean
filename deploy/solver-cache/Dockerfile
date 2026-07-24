# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Multi-stage build for the solver-results-cache Cloud Run distribution +
# ingest front-end (`solver_serve`, Phase 2).
#
# Stage 1 compiles the release binary against the workspace. Stage 2 is a slim
# Debian runtime that carries ONLY the binary + a minimal runtime and runs as a
# non-root user. The solver-cache Core (telemetry `attempts.jsonl` + the
# `<digest>.scache` proof blobs + the `*.vcidx` index) is deliberately NOT baked
# into the image — it lives in GCS and is mounted (gcsfuse) or synced at runtime
# into $CLEAN_SOLVER_TELEMETRY_DIR / $CLEAN_SOLVER_CACHE_DIR. Keeping the Core
# out of the image keeps the image small and "convert once, share" honest: one
# Core in a bucket feeds every revision.
#
# TRUST POSTURE (see ../../designs/2026-06-24-solver-results-cache-service.md
# §10.3): this service is a DISTRIBUTION FRONT-END, NOT a trust authority. A
# cached result is PROVENANCE — a proof-bearing hit ships a re-checkable proof
# term the consumer re-runs through the kernel; a raw verdict is telemetry. The
# image ships no key and mints no `verified` badge.
#
# Build context MUST be the repo root (the workspace), not deploy/solver-cache/:
#   docker build -f deploy/solver-cache/Dockerfile -t IMAGE .

# ---------------------------------------------------------------------------
# Stage 1 — builder
# ---------------------------------------------------------------------------
# Pin to the toolchain the repo builds with locally (rustc 1.95). Bump in
# lockstep with the workspace toolchain.
FROM rust:1.95-bookworm AS builder

WORKDIR /build

# The env init chain needs a 64MB stack (see .cargo/config.toml / #1455); set it
# so any build.rs / proc step that recurses inherits the same floor as local
# builds.
ENV RUST_MIN_STACK=67108864 \
    CARGO_TERM_COLOR=never \
    # Portable Linux/x86_64 baseline: do NOT inherit target-cpu=native from a
    # build host. Cloud Run runs generic x86-64. (.cargo/config.toml already
    # pins this for cfg(linux,x86_64), but be explicit for the image.)
    RUSTFLAGS="-C target-cpu=x86-64"

# Copy the whole workspace. The repo-root .dockerignore keeps target/, .git/,
# and any local Core out of the context so the layer stays lean.
COPY . .

# Build ONLY the serve binary, in release, with the repo's --locked posture.
# --locked is the repo standard (Cargo.lock is tracked) and makes the build
# reproducible. The binary lives in clean-auto (the solver-cache lives there).
RUN cargo build --locked --release -p clean-auto --bin solver_serve \
    && strip target/release/solver_serve

# ---------------------------------------------------------------------------
# Stage 2 — runtime
# ---------------------------------------------------------------------------
# debian:bookworm-slim (not distroless) so the same image can OPTIONALLY shell
# out to `gsutil rsync` on startup if you choose the download-on-start path
# instead of a gcsfuse CSI volume. If you commit to the gcsfuse-volume path,
# you can swap this for gcr.io/distroless/cc-debian12 and drop the apt layer.
FROM debian:bookworm-slim AS runtime

# ca-certificates: TLS to GCS for any startup sync. tini: correct PID-1 signal
# handling under Cloud Run.
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates tini \
    && rm -rf /var/lib/apt/lists/*

# Non-root runtime user (Cloud Run does not require root; least privilege).
RUN groupadd --system --gid 10001 solver \
    && useradd --system --uid 10001 --gid solver --home /home/solver \
       --create-home solver

COPY --from=builder /build/target/release/solver_serve /usr/local/bin/solver_serve

# Mount points for the solver-cache Core. With a gcsfuse CSI volume the bucket
# is mounted here at runtime (see service.yaml); with download-on-start it is
# rsynced here. Created empty and owned by the runtime user.
#   /core/telemetry  -> $CLEAN_SOLVER_TELEMETRY_DIR (attempts.jsonl)
#   /core/cache      -> $CLEAN_SOLVER_CACHE_DIR      (<digest>.scache blobs)
#   /core/solver.vcidx -> $CLEAN_SOLVER_INDEX        (pre-built µs lookup index)
RUN mkdir -p /core && chown -R solver:solver /core
ENV CLEAN_SOLVER_TELEMETRY_DIR=/core/telemetry \
    CLEAN_SOLVER_CACHE_DIR=/core/cache \
    CLEAN_SOLVER_INDEX=/core/solver.vcidx \
    CLEAN_SOLVER_BUDGET_MS=5000 \
    RUST_MIN_STACK=67108864 \
    PORT=8080
# NOTE: ingest is OFF by default (read-only distribution). Set
# CLEAN_SOLVER_INGEST=1 in service.yaml/deploy.sh to enable POST /ingest on a
# WRITABLE Core mount. Ingest still mints nothing — it appends provenance.

USER solver

# Cloud Run sends traffic to $PORT (default 8080); the service binds 0.0.0.0:$PORT.
EXPOSE 8080

# tini reaps zombies and forwards SIGTERM (Cloud Run's shutdown signal) cleanly.
ENTRYPOINT ["/usr/bin/tini", "--"]
CMD ["/usr/local/bin/solver_serve"]
