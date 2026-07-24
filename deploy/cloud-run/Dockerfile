# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Multi-stage build for the Mathverse Cloud Run distribution front-end
# (`mathverse_serve`, Phase 1: read-only browse / search / download).
#
# Stage 1 compiles the release binary against the workspace. Stage 2 is a slim
# Debian runtime that carries ONLY the binary + the gcsfuse/gsutil-free runtime
# deps and runs as a non-root user. The multi-GB verified Core is deliberately
# NOT baked into the image — it lives in GCS and is mounted (gcsfuse) or synced
# at runtime into $MATHVERSE_CORE_DIR. Keeping the Core out of the image keeps
# the image small, the build fast, and "convert once, share" honest: one Core
# in a bucket feeds every revision.
#
# Build context MUST be the repo root (the workspace), not deploy/cloud-run/:
#   docker build -f deploy/cloud-run/Dockerfile -t IMAGE .

# ---------------------------------------------------------------------------
# Stage 1 — builder
# ---------------------------------------------------------------------------
# Pin to the toolchain the repo builds with locally (rustc 1.95). Bump in
# lockstep with the workspace toolchain.
FROM rust:1.95-bookworm AS builder

WORKDIR /build

# The env init chain needs a 64MB stack (see .cargo/config.toml / #1455); the
# build itself is fine on the default stack, but set it so any build.rs / proc
# step that recurses inherits the same floor as local builds.
ENV RUST_MIN_STACK=67108864 \
    CARGO_TERM_COLOR=never \
    # Portable Linux/x86_64 baseline: do NOT inherit target-cpu=native from a
    # build host. Cloud Run runs generic x86-64. (.cargo/config.toml already
    # pins this for cfg(linux,x86_64), but be explicit for the image.)
    RUSTFLAGS="-C target-cpu=x86-64"

# Copy the whole workspace. A .dockerignore at the repo root keeps target/,
# .git/, and any local Core out of the context so the layer stays lean.
COPY . .

# Build ONLY the serve binary, in release, with the repo's --locked posture.
# --locked is the repo standard (Cargo.lock is tracked); it also makes the
# build reproducible. If the daemon has network egress the registry deps are
# fetched normally; for a hermetic build, vendor first (see README runbook).
RUN cargo build --locked --release -p clean-mathverse --bin mathverse_serve \
    && strip target/release/mathverse_serve

# ---------------------------------------------------------------------------
# Stage 2 — runtime
# ---------------------------------------------------------------------------
# debian:bookworm-slim (not distroless) so the same image can OPTIONALLY shell
# out to `gsutil rsync` on startup if you choose the download-on-start path
# instead of a gcsfuse CSI volume. If you commit to the gcsfuse-volume path,
# you can swap this for gcr.io/distroless/cc-debian12 and drop the apt layer.
FROM debian:bookworm-slim AS runtime

# ca-certificates: TLS to GCS if the binary ever redirects to signed URLs and
# for any startup sync. tini: correct PID-1 signal handling under Cloud Run.
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates tini \
    && rm -rf /var/lib/apt/lists/*

# Non-root runtime user (Cloud Run does not require root; least privilege).
RUN groupadd --system --gid 10001 mathverse \
    && useradd --system --uid 10001 --gid mathverse --home /home/mathverse \
       --create-home mathverse

COPY --from=builder /build/target/release/mathverse_serve /usr/local/bin/mathverse_serve

# Mount point for the Core. With a gcsfuse CSI volume the bucket is mounted
# here at runtime (see service.yaml); with download-on-start it is rsynced here.
# Created empty and owned by the runtime user.
RUN mkdir -p /core && chown mathverse:mathverse /core
ENV MATHVERSE_CORE_DIR=/core \
    PORT=8080

USER mathverse

# Cloud Run sends traffic to $PORT (default 8080); the service binds 0.0.0.0:$PORT.
EXPOSE 8080

# tini reaps zombies and forwards SIGTERM (Cloud Run's shutdown signal) cleanly.
ENTRYPOINT ["/usr/bin/tini", "--"]
CMD ["/usr/local/bin/mathverse_serve"]
