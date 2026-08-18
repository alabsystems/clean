#!/usr/bin/env bash
# G-AUTO — executable fail-closed automation-family tactic gate.
# See docs/plans/TACTICS_TO_100_2026-07-29.md §7 and scripts/tactic_parity/TEETH.md.
#
# Drives the PREBUILT release binary (target/release/clean, override CLEAN_BIN)
# over tests/fixtures/tactic_families/g_auto/*.lean under real `import Init`.
# Never invokes cargo in any form.
#
# Exit codes: 0 measured, 1 gate FAILED (fail-closed), 2 SKIPPED (no prebuilt
# binary). Writes a dated verdict artifact under reports/tactic-families/.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
exec python3 scripts/tactic_parity/family_gate.py --family g_auto "$@"
