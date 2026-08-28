#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Trusted-kernel lint ratchet (exhaustive-audit #6).
#
# The workspace deliberately sets dead_code / unused_* = "allow"
# ([workspace.lints.rust] in Cargo.toml; justified in
# docs/JUSTIFIED_EXCEPTIONS.md) because the experimental CLI/factory crates
# emit too much such noise while subsystems are wired up. That rationale does
# NOT apply to the TRUSTED CORE (clean-kernel, #![forbid(unsafe_code)]), where
# dead code / unused imports are genuine TCB hygiene debt — and the
# workspace allow makes that debt INVISIBLE in normal builds + the clippy gate.
#
# This ratchet re-surfaces it WITHOUT flipping the workspace policy (which would
# promote ~51 warnings to errors under the `-D warnings` clippy gate) and
# WITHOUT polluting normal build output: it force-warns the five allowed lints
# over clean-kernel --lib ONLY, counts the crate's own warnings, and enforces
# flat-or-down against data/kernel_lint_ratchet.json.
#
#   scripts/kernel_lint_ratchet.sh            # FAIL if the count grew
#   scripts/kernel_lint_ratchet.sh --update   # rewrite baseline (ratchet-down)
#
# Wired into scripts/local_gate.sh (full mode). clean-kernel does not depend on
# the AY solver graph, so this check is self-contained and does not compile it.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

DATA_FILE="data/kernel_lint_ratchet.json"
LINTS=(dead_code unused_imports unused_variables unused_mut unused_qualifications)

UPDATE=0
[[ "${1:-}" == "--update" ]] && UPDATE=1

flags=()
for l in "${LINTS[@]}"; do flags+=(--force-warn "$l"); done

# A BARE `RUSTFLAGS=` OVERRIDE DROPS THE TRUST VERIFIER OPT-OUT. Cargo does not
# merge RUSTFLAGS with `[target.<triple>].rustflags` -- the env var REPLACES it --
# and since the 2026-08-18 flip to `channel = "trust"` that stanza is where
# `-Ztrust-verify=off` lives. `.cargo/config.toml` says so in its own words:
# "a bare RUSTFLAGS override REPLACES the target stanza above entirely -- include
# the opt-out when overriding". This script did not, so the fail-closed verifier
# ran on the whole dependency graph and `cargo check` died inside third-party
# `shlex` on proof obligations, never reaching clean-kernel at all (measured
# 2026-08-27 on aarch64-unknown-linux-gnu: exit 101, `could not compile shlex
# (lib) due to 40 previous errors`). Probed rather than hardcoded, because the
# Docker cross lane deliberately runs a stock upstream toolchain that rejects the
# nightly-only -Z flag on every unit.
opt_out=()
if rustc -Z help 2>/dev/null | grep -q 'trust-verify=' ; then
  opt_out+=("-Ztrust-verify=off")
fi

# Cargo only emits warnings on actual COMPILATION (a cache hit prints nothing),
# so force a fresh recompile of just clean-kernel before counting. `clean -p`
# touches only this crate's artifacts; its deps stay cached.
cargo clean -p clean-kernel >/dev/null 2>&1 || true

# FAIL CLOSED ON A COMPILE THAT DID NOT COMPLETE. This used to read
# `... 2>&1 || true)` and then count warning lines, which means EVERY way of not
# compiling -- a verifier refusal, a compiler ICE, an OOM kill, a missing
# toolchain -- produced zero matching lines and was scored as `count=0`, i.e. as
# the best result this ratchet can report. Measured 2026-08-27: the gate printed
# `IMPROVED 70 -> 0 -- run scripts/kernel_lint_ratchet.sh --update to lock it in`
# and exited 0 while `cargo check` was exiting 101 and clean-kernel was never
# compiled. A shrink-only ratchet whose failure mode is "perfect score" is worse
# than no ratchet, and `--update` would have written that fabricated 0 into the
# baseline permanently.
check_rc=0
out=$(RUSTFLAGS="${flags[*]} ${opt_out[*]}" cargo check -p clean-kernel --lib \
        --message-format=short 2>&1) || check_rc=$?
if [[ $check_rc -ne 0 ]]; then
  printf '%s\n' "$out" | tail -25 >&2
  echo "kernel lint ratchet: FAIL — the force-warn check of clean-kernel did not COMPLETE (cargo exit $check_rc)." >&2
  echo "  A compile that does not finish emits no warnings, so counting them would score 0 and read as an IMPROVEMENT." >&2
  echo "  Known cause on this tree (measured 2026-08-27, aarch64-unknown-linux-gnu): --force-warn unused_qualifications" >&2
  echo "  ICEs the pinned toolchain -- rustc_errors/src/diagnostic.rs: \`Span crates/clean-kernel/src/expr/kind.rs:147:24" >&2
  echo "  must not be empty and have no suggestion\` -- on the serde-attributed \`Const(Name, ... LevelVec)\` variant." >&2
  echo "  Isolated per lint: dead_code 65 warnings exit 0; unused_imports/unused_variables/unused_mut 0 warnings exit 0;" >&2
  echo "  unused_qualifications exit 101. That is a COMPILER defect, not kernel lint debt -- do NOT --update past it." >&2
  exit 1
fi

# Count clean-kernel's OWN warnings (exclude dependency crates).
count=$(printf '%s\n' "$out" | grep -Ec "^crates/clean-kernel/src/.*: warning:" || true)
count=${count:-0}

if [[ $UPDATE -eq 1 ]]; then
  python3 - "$DATA_FILE" "$count" "${LINTS[*]}" <<'PY'
import json, sys, subprocess
data_file, count, lints = sys.argv[1], int(sys.argv[2]), sys.argv[3].split()
doc = {
    "note": "Trusted-kernel (clean-kernel --lib) count of dead_code/unused_* warnings that the "
            "workspace [lints] allow hides. Flat-or-down ratchet (audit #6); enforced by "
            "scripts/kernel_lint_ratchet.sh, wired into scripts/local_gate.sh full mode. "
            "Lower it by removing dead imports / unused vars / redundant `mut` in clean-kernel.",
    "lints_forced": lints,
    "kernel_warnings": count,
    "generated_by": "scripts/kernel_lint_ratchet.sh --update",
}
with open(data_file, "w") as f:
    f.write(json.dumps(doc, indent=2) + "\n")
print(f"kernel lint ratchet: baseline written to {data_file} (kernel_warnings={count})")
PY
  exit 0
fi

baseline=$(python3 -c "import json;print(json.load(open('$DATA_FILE'))['kernel_warnings'])")
if [[ "$count" -gt "$baseline" ]]; then
  echo "KERNEL LINT RATCHET: FAIL — clean-kernel dead_code/unused warnings grew ${baseline} -> ${count}." >&2
  echo "  Remove the new dead import / unused var / redundant \`mut\` in clean-kernel, or (if intentional)" >&2
  echo "  prefix with _ / #[allow] with a reason. Do NOT raise the baseline to mask new rot." >&2
  exit 1
elif [[ "$count" -lt "$baseline" ]]; then
  echo "kernel lint ratchet: IMPROVED ${baseline} -> ${count} — run scripts/kernel_lint_ratchet.sh --update to lock it in."
else
  echo "kernel lint ratchet: PASS (clean-kernel hidden warnings = ${count}, flat against baseline)."
fi
