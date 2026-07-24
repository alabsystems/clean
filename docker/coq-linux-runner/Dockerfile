# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# mathverse-coq-linux: Linux (aarch64) Coq 8.20 + SerAPI + MathComp toolchain.
#
# Why this exists: MathComp 2.x needs coq-elpi/elpi, which is unbuildable on
# macOS/arm64 (ocamlopt Mach-O fixup-out-of-range with elpi 2.x; cmxs
# packaging failure with elpi 1.18.2). A Linux container sidesteps the Mach-O
# toolchain entirely. The HOST dump driver (mathverse_coq_dump) drives the
# container's sertop through scripts/coq_linux_sertop.sh (docker exec -i),
# so no Rust changes are needed.
#
# Build (long — 30-60 min; opam compiles Coq from source):
#   docker build -t mathverse-coq-linux:mc2.2.0-coq8.20.0 docker/coq-linux-runner
#
# The elpi lane MUST be pinned: an unconstrained solve picks rocq-elpi 3.x /
# rocq-hierarchy-builder 1.10.x (Rocq 9.x-era transition packages), whose
# build breaks under Coq 8.20 (elpi_plugin.cmxs never produced). Verified
# 2026-07-05 on linux/arm64. Defaults below are the known-good 8.20 lane.
#
# Fallback pin paths if the default fails — see README.md in this directory:
#   (a) --build-arg EXTRA_PINS="elpi.1.18.2 coq-elpi.2.2.3 coq-hierarchy-builder.1.7.1"
#   (b) --build-arg MATHCOMP_PKGS="coq-mathcomp-ssreflect.1.19.0 coq-mathcomp-algebra.1.19.0 coq-mathcomp-fingroup.1.19.0 coq-mathcomp-solvable.1.19.0 coq-mathcomp-field.1.19.0 coq-mathcomp-character.1.19.0" EXTRA_PINS=""
#       (MathComp 1.x line: no elpi / hierarchy-builder; coq >= 8.16 & < 8.21~.
#        This FULL 1.19.0 set is the mathverse production dump lane, matching
#        the live mathverse-coq-linux:mc1.19.0-coq8.20.0 container after the
#        2026-07-10 solvable/field/character extension.)
#
# Versions are pinned exactly; the full solved package set is recorded at
# /home/opam/opam-installed.txt inside the image (surfaced into the dump
# manifest by scripts/build_mathcomp_dumps.sh).

FROM ocaml/opam:debian-12-ocaml-4.14

# Exact pins (match the host mathverse-serapi switch: coq 8.20.0,
# coq-serapi 8.20.0+0.20.0, ocaml 4.14).
ARG COQ_PKG=coq.8.20.0
ARG SERAPI_PKG=coq-serapi.8.20.0+0.20.0
ARG MATHCOMP_PKGS="coq-mathcomp-ssreflect.2.2.0 coq-mathcomp-algebra.2.2.0"
# Extra exact pins installed in the same solver call as MATHCOMP_PKGS.
# Default = the Coq-8.20-native elpi lane: coq-elpi 2.3.0 targets exactly
# coq >= 8.20+rc1 & < 8.21~ (elpi 2.0.3..2.0.x); hierarchy-builder 1.8.0
# accepts coq-elpi >= 2.0 & < 2.4; mathcomp 2.2.0 needs HB >= 1.5.0.
ARG EXTRA_PINS="coq-elpi.2.3.0 coq-hierarchy-builder.1.8.0"

USER root
RUN apt-get update \
    && apt-get install -y --no-install-recommends libgmp-dev pkg-config m4 \
    && rm -rf /var/lib/apt/lists/*
USER opam

# Fresh package index + the Coq opam repository.
RUN opam repo add coq-released https://coq.inria.fr/opam/released \
    && opam update

# Separate layers so a MathComp-layer failure keeps the (expensive) Coq and
# SerAPI layers cached for fallback rebuilds.
RUN opam install -y ${COQ_PKG}
RUN opam install -y ${SERAPI_PKG}
RUN opam install -y ${MATHCOMP_PKGS} ${EXTRA_PINS}

# Stable entry points independent of the opam switch name, plus a record of
# the exact solved package set.
RUN sudo ln -s "$(opam var bin)/sertop" /usr/local/bin/sertop \
    && sudo ln -s "$(opam var bin)/sercomp" /usr/local/bin/sercomp \
    && sudo ln -s "$(opam var bin)/coqc" /usr/local/bin/coqc \
    && opam list --installed > /home/opam/opam-installed.txt \
    && echo "COQLIB=$(opam var lib)/coq" > /home/opam/coq-paths.env

ARG MATHCOMP_VARIANT=mathcomp-2.2.0-hb1.8.0-coqelpi2.3.0
LABEL org.mathverse.role="coq-linux-runner" \
      org.mathverse.coq="8.20.0" \
      org.mathverse.serapi="8.20.0+0.20.0" \
      org.mathverse.mathcomp-variant="${MATHCOMP_VARIANT}"

# Idle by default: scripts/coq_linux_sertop.sh starts the container detached
# and drives sertop via `docker exec -i`.
CMD ["sleep", "infinity"]
