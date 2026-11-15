#!/usr/bin/env bash
# Re-project the FIVE-BODY derived module `ir_lzd` from the sidecar dump.
#
# This is the command that produced
# `crates/clean-verify/src/spec/core_spec/generated/ir_lzd.*`. It lived only in a
# shell history until 2026-09-10, which meant the artifacts could be READ but not
# RE-DERIVED — so a reader could not tell a derivation from a transcription.
#
# The five bodies: the target, the kernel's own `LevelArc::deref`, and the three
# foreign callees the trust-side callee sidecar supplies (`as_deref`, `expect`,
# `Arc::deref`). `--merge` brings the sidecar artifact's functions in behind the
# crate module's; `--join` retargets the crate module's two calls from their
# bodyless DECLARATIONS to the merged bodies.
set -euo pipefail

# Defaults resolve inside THIS repo. They were absolute paths into
# `$HOME/clean/target/...` until 2026-09-15, which no checkout but one
# could satisfy: on any other box both defaults named files that cannot exist,
# so the script failed on a missing dump rather than saying the default was
# never applicable. Same location on the box it was written for.
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

DUMP="${CRYSTAL_LZD_DUMP:-$REPO_ROOT/target/crystal-lane/dump-sidecar-O3}"
OUT="${1:-crates/clean-verify/src/spec/core_spec/generated}"
BIN="${CRYSTAL_A2_BIN:-$REPO_ROOT/target/crystal-lane/tgt-a2proj/debug/a2project}"

AS_DEREF='core::option::Option::<alloc::sync::Arc<clean_kernel::level::Level>>::as_deref::<__trust_args@70cdfda50ac8f275dc812a3df6e87a17>'
EXPECT='core::option::Option::<&clean_kernel::level::Level>::expect::<__trust_args@a8727e115d13c4cf156f1ed67b0f185a>'
ARC_DEREF='<alloc::sync::Arc<clean_kernel::level::Level> as core::ops::deref::Deref>::deref::<__trust_args@ded6b36b6bb6d04d44fb2792b0a95cf6>'

exec "$BIN" \
  "$DUMP/clean_kernel.trust-ir.bin" \
  'level::Level::is_zero' \
  "$OUT" \
  ir_lzd \
  --with '<level::LevelArc as std::ops::Deref>::deref' \
  --with "$AS_DEREF" \
  --with "$EXPECT" \
  --with "$ARC_DEREF" \
  --merge "$DUMP/callees/clean_kernel.callees.trust-ir.bin" \
  --join  "$DUMP/callees/clean_kernel.callees.manifest.json" \
  --usize-bits 64
