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

# Cargo only emits warnings on actual COMPILATION (a cache hit prints nothing),
# so force a fresh recompile of just clean-kernel before counting. `clean -p`
# touches only this crate's artifacts; its deps stay cached. `|| true` guards
# keep `set -e` from killing the run when grep finds zero warnings (the goal).
cargo clean -p clean-kernel >/dev/null 2>&1 || true
out=$(RUSTFLAGS="${flags[*]}" cargo check -p clean-kernel --lib --message-format=short 2>&1 || true)
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
