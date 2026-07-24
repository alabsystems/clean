# coq-linux-runner — Linux Coq 8.20 + SerAPI + MathComp toolchain

Docker image that carries the **MathComp** Coq toolchain for the Mathverse
Coq import pipeline (campaign work package D6b).

## Why a container

MathComp 2.x requires `coq-elpi`, whose OCaml dependency `elpi` is
**unbuildable on macOS/arm64**:

- elpi 2.x: `ocamlopt` Mach-O fixup-out-of-range (large-function relocation
  overflow in the Mach-O backend);
- elpi 1.18.2: `.cmxs` packaging failure.

(Logs in `~/.opam/log/` on the affected host.) The bug is **Mach-O-specific**:
on linux/arm64 inside this container, elpi 2.0.x compiles cleanly in under a
minute.

The host dump driver (`mathverse_coq_dump`) spawns sertop as a subprocess by
path and speaks pipes, so `scripts/coq_linux_sertop.sh` (a `docker exec -i`
shim) lets the unmodified **host** binary drive the **container** toolchain.

## Contents (exact pins)

| Package | Version | Why |
|---|---|---|
| base image | `ocaml/opam:debian-12-ocaml-4.14` (linux/arm64) | matches host switch's ocaml 4.14 |
| `coq` | `8.20.0` | same as host `mathverse-serapi` switch |
| `coq-serapi` | `8.20.0+0.20.0` | same as host — identical dump sexp forms |
| `coq-mathcomp-ssreflect` | `2.2.0` | coq >= 8.17 & < 8.21~ |
| `coq-mathcomp-algebra` | `2.2.0` | pulls `coq-mathcomp-fingroup.2.2.0` |
| `coq-elpi` | `2.3.0` (pinned) | targets exactly coq >= 8.20+rc1 & < 8.21~ |
| `coq-hierarchy-builder` | `1.8.0` (pinned) | accepts coq-elpi >= 2.0 & < 2.4; mathcomp needs >= 1.5.0 |
| `elpi` | solver-picked in 2.0.3..2.0.x (coq-elpi 2.3.0's bound) | compiles fine on linux/arm64 |

The full solved opam package set is recorded inside the image at
`/home/opam/opam-installed.txt`; `scripts/build_mathcomp_dumps.sh` copies the
relevant lines into `data/corpora/coq-sexp/mathcomp/container-toolchain.json`
together with the image id/digest and docker platform.

Stable entry points (symlinked, independent of the opam switch name):
`/usr/local/bin/{sertop,sercomp,coqc}`.

## Pin-path record (2026-07-05, linux/arm64, colima docker 29.2.1)

1. **FAILED — unpinned solve**: `opam install coq-mathcomp-ssreflect.2.2.0
   coq-mathcomp-algebra.2.2.0` selects `elpi.3.4.2` + `rocq-elpi.3.2.0` +
   `rocq-hierarchy-builder.1.10.1` (Rocq 9.x-era transition packages).
   `rocq-elpi.3.2.0` fails under Coq 8.20: `dune build` never produces
   `elpi_plugin.cmxs` (`System error: ... elpi_plugin.cmxs: No such file or
   directory`). Note `elpi.3.4.2` itself compiled cleanly — the macOS Mach-O
   wall does not exist on Linux.
2. **FAILED — pinned 8.20 lane**: `coq-elpi.2.3.0` + `coq-hierarchy-builder.1.8.0`
   (with `elpi.2.0.7`) hits the SAME `elpi_plugin.cmxs`-never-produced dune
   packaging failure during the `coq-elpi` build — so the cmxs defect is a
   coq-elpi 2.x packaging bug, not a platform wall (macOS failed identically).
3. **SUCCEEDED — MathComp 1.19.0 lane (shipped default, elpi-free)**:
   `coq-mathcomp-ssreflect.1.19.0` + `coq-mathcomp-algebra.1.19.0` with
   `EXTRA_PINS=""` — the pre-hierarchy-builder MathComp line needs no
   elpi at all. Image: `mathverse-coq-linux:mc1.19.0-coq8.20.0`. Wrapper
   round-trip proven (host pipe → docker exec sertop → elaborated Qed
   proof term back). MathComp 2.x needs a fixed coq-elpi packaging or a
   different distribution channel (e.g. Docker Hub `mathcomp/mathcomp`
   images) — record whichever lands first.

## Build

```bash
docker build --build-arg MATHCOMP_PKGS="coq-mathcomp-ssreflect.1.19.0 coq-mathcomp-algebra.1.19.0" \
             --build-arg EXTRA_PINS="" \
             -t mathverse-coq-linux:mc1.19.0-coq8.20.0 docker/coq-linux-runner
```

30–60 min cold (opam compiles Coq from source; ~90 s for Coq itself on a
fast arm64 VM, MathComp algebra dominates). Layers are ordered so a MathComp
failure keeps the Coq/SerAPI layers cached.

Fallback pin paths (only if the default breaks on your platform):

```bash
# (a) elpi 1.18 lane
docker build --build-arg EXTRA_PINS="elpi.1.18.2 coq-elpi.2.2.3 coq-hierarchy-builder.1.7.1" ...
# (b) MathComp 1.x line (no elpi / hierarchy-builder at all)
docker build --build-arg MATHCOMP_PKGS="coq-mathcomp-ssreflect.1.19.0 coq-mathcomp-algebra.1.19.0" \
             --build-arg EXTRA_PINS="" ...
```

## Run / use

Never run the container by hand for dumps — use the harness:

```bash
scripts/build_mathcomp_dumps.sh --only=mathcomp.ssreflect.   # ssreflect core
scripts/build_mathcomp_dumps.sh                              # everything installed
```

It starts the container (`mathverse-coq-linux`, idling on `sleep infinity`),
proves the wrapper round-trip, enumerates compiled `mathcomp.*` modules from
the container's `user-contrib`, and drives the host `mathverse_coq_dump`
with `--sertop=scripts/coq_linux_sertop.sh --validate`.

Manual probe through the shim (pipe-only + timeout, as always with sertop):

```bash
printf '(Add () "Require Import mathcomp.ssreflect.ssrnat.")\n(Exec 2)\n(Query () (TypeOf "mathcomp.ssreflect.ssrnat.half"))\n' \
  | timeout 120 scripts/coq_linux_sertop.sh --printer=sertop
```

Container lifecycle: `docker rm -f mathverse-coq-linux` to reclaim; the shim
recreates it on demand. Killed shim clients (driver timeouts) can leave a
sertop briefly running inside the container until its stdin EOFs;
`build_mathcomp_dumps.sh` sweeps stragglers after each run.

## Trust note

Dumps produced through this container are **import/source provenance**, same
as the host stdlib dumps: SerAPI-elaborated kernel terms from opam-released
MathComp sources. They are not Clean-kernel verification by themselves; the
import + kernel lanes downstream decide `KernelVerified` honestly.
