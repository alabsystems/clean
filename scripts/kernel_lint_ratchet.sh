#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Trusted-kernel lint ratchet (exhaustive-audit #6).
#
# MECHANISM (corrected audit r5 M1, wf_ca0a3923 — the previous header said
# the workspace sets these lints to "allow"; Cargo.toml [workspace.lints.rust]
# has said `warn` for all five since f6d5952f6, 2026-07-24, BEFORE the
# baseline mint, and docs/JUSTIFIED_EXCEPTIONS.md documents warn): what hides
# the debt is 522 SOURCE-LEVEL (unconditional; audit r6 recount) `#[allow(dead_code)]` attributes inside
# crates/clean-kernel/src itself. A workspace/attribute `allow` beats `warn`,
# so normal builds and the `-D warnings` clippy gate see none of it — which is
# why the same morning's workspace clippy passes while this ratchet counts 65.
# `--force-warn` PIERCES source-level allows; plain warn does not. A SECOND
# mechanism exists at expansion level (audit r6): a warning SITE can land
# after a mint (e.g. the unused_qualifications site at expr/kind.rs:147,
# 8ae06db5c, 2026-08-25 -- after the 2026-08-14 combined-70 mint). Every
# baseline component is now a direct per-lint measurement (2026-09-23), and
# the down-only --update rule below keeps any future dead zone from being
# cashed in silently. Dead code
# in the TRUSTED CORE (clean-kernel, #![forbid(unsafe_code)]) is genuine TCB
# hygiene debt, so this ratchet force-warns the five lints over clean-kernel
# --lib ONLY, counts the crate's own warnings, and enforces flat-or-down
# against data/kernel_lint_ratchet.json — without touching the attributes and
# without polluting normal build output.
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

# All five lints are forced on every run. Until 2026-09-23 this spot held a
# PINNED-TOOLCHAIN DEFECT CARVE-OUT that dropped unused_qualifications whenever
# the active compiler was trustc 10f221fbe (2026-08-08), which ICEd emitting that
# lint on a serde-derive-expanded path ("Span ... must not be empty and have no
# suggestion"). Trust 263fe47fd4 fixed the defect at its root (an EMPTY removal
# span is no longer suggested; regression test
# tests/ui/lint/unused-qualifications-empty-removal-span.rs); the installed
# toolchain the `channel = "trust"` pin resolves to (trustc 321aaeda7,
# 2026-09-17) carries the fix, and 10f221fbe is no toolchain this repo pins any
# more, so the carve-out, its --update refusal and its canned ICE note are
# retired. On a pre-fix compiler built WITHOUT debug assertions (e.g. c4e667ca5)
# the same defect does not crash: it reports false empty-span
# unused_qualifications warnings, which this ratchet counts and FAILS on --
# update the toolchain, never the baseline.
# The history lives in git (`git log -p -- scripts/kernel_lint_ratchet.sh`).

UPDATE=0
[[ "${1:-}" == "--update" ]] && UPDATE=1

flags=()
for l in "${LINTS[@]}"; do flags+=(--force-warn "$l"); done

# The force-warn flags go to clean-kernel ALONE through `targo --unverified
# rustc -p clean-kernel --lib -- <flags>` (owner directive 2026-09-28: the
# driver is targo). Until then this assigned RUSTFLAGS, which replaced the
# config's target stanza and so had to re-add the `-Ztrust-verify=off` opt-out
# it probed for (and twice lost to a flaky probe); the unverified lane applies
# that opt-out itself and `rustc -- <flags>` touches no dependency, so neither
# the RUSTFLAGS assignment nor the probe is needed.
# That history: `git show 7330fa6ce:scripts/kernel_lint_ratchet.sh`.

# Cargo only emits warnings on actual COMPILATION (a cache hit prints nothing),
# so force a fresh recompile of just clean-kernel before counting. `clean -p`
# touches only this crate's artifacts; its deps stay cached.
targo clean -p clean-kernel >/dev/null 2>&1 || true

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
out=$(targo --unverified rustc -p clean-kernel --lib --message-format=short \
        -- "${flags[@]}" 2>&1) || check_rc=$?
if [[ $check_rc -ne 0 ]]; then
  printf '%s\n' "$out" | tail -25 >&2
  echo "kernel lint ratchet: FAIL — the force-warn check of clean-kernel did not COMPLETE (targo exit $check_rc)." >&2
  echo "  A compile that does not finish emits no warnings, so counting them would score 0 and read as an IMPROVEMENT." >&2
  exit 1
fi

# Count clean-kernel's OWN warnings (exclude dependency crates).
count=$(printf '%s\n' "$out" | grep -Ec "^crates/clean-kernel/src/.*: warning:" || true)
count=${count:-0}

# Audit r3 M2 (workflow wf_e15af3e7): the baseline records a per-lint split and
# the effective baseline is the SUM over the lints actually forced this run, so
# the comparison is like-for-like over exactly those lints. (It was introduced
# for the retired 10f221fbe carve-out, which forced FOUR lints against a FIVE-
# lint baseline -- a masked-regression dead zone the width of the skipped
# lint's share; the split also keeps --update's per-lint cross-check honest.)
# Effective baseline, shared by the check path and --update's down-only rule
# (one reader, not two -- audit r3 proved a mirrored reader drifts). Prints -1
# on any incomparable or non-integer shape (audit r4/r5), which callers treat
# as "no honest baseline".
effective_baseline() {
  python3 - "$DATA_FILE" "$1" <<'PY'
import json, sys
doc = json.load(open(sys.argv[1]))
active = sys.argv[2].split()
by = doc.get("kernel_warnings_by_lint")
def ok_int(v):
    return isinstance(v, int) and not isinstance(v, bool)
if by is not None and set(active) <= set(by) and all(ok_int(by[l]) for l in active):
    print(sum(by[l] for l in active))
elif active == doc.get("lints_forced") and ok_int(doc.get("kernel_warnings")):
    print(doc["kernel_warnings"])
else:
    print(-1)
PY
}

if [[ $UPDATE -eq 1 ]]; then
  old_eff=$(effective_baseline "${LINTS[*]}")
  if [[ "$old_eff" -ge 0 && "$count" -gt "$old_eff" && "${CLEAN_LINT_RATCHET_ALLOW_INCREASE:-0}" != "1" ]]; then
    echo "kernel lint ratchet: --update REFUSES to raise the baseline ${old_eff} -> ${count}." >&2
    echo "  A ratchet only goes down; an increase means new debt landed (or a masked-regression" >&2
    echo "  dead zone is being cashed in -- audit r6). If the increase is intended and accounted," >&2
    echo "  re-run with CLEAN_LINT_RATCHET_ALLOW_INCREASE=1 and say why in the commit." >&2
    exit 1
  fi
  by_lint="{"
  first=1
  for l in "${LINTS[@]}"; do
    lo=$(targo --unverified rustc -p clean-kernel --lib --message-format=short \
           -- --force-warn "$l" 2>&1) || {
      echo "kernel lint ratchet: --update per-lint pass for $l did not COMPLETE; refusing." >&2
      exit 1
    }
    lc=$(printf '%s\n' "$lo" | grep -Ec "^crates/clean-kernel/src/.*: warning:" || true)
    [[ $first -eq 1 ]] || by_lint+=", "
    by_lint+="\"$l\": ${lc:-0}"
    first=0
    targo clean -p clean-kernel >/dev/null 2>&1 || true
  done
  by_lint+="}"
  python3 - "$DATA_FILE" "$count" "${LINTS[*]}" "$by_lint" <<'PY'
import json, sys
data_file, count, lints = sys.argv[1], int(sys.argv[2]), sys.argv[3].split()
by_lint = json.loads(sys.argv[4])
# audit r4 minor 5: the combined pass and the per-lint isolation passes are
# two measurements of the same thing; a divergent pair is refused at write
# time because the reader prefers by_lint and would never see the disagreement
if sum(by_lint.values()) != count:
    raise SystemExit(
        f"kernel lint ratchet --update: per-lint sum {sum(by_lint.values())} != "
        f"combined count {count} -- the two passes disagree; refusing to write a "
        f"self-inconsistent baseline")
doc = {
    "note": "Trusted-kernel (clean-kernel --lib) count of dead_code/unused_* warnings hidden by "
            "source-level #[allow] attributes in clean-kernel itself (the workspace [lints] set "
            "these five to warn; --force-warn pierces the attributes — audit r5 M1). "
            "Flat-or-down ratchet (audit #6); enforced by "
            "scripts/kernel_lint_ratchet.sh, wired into scripts/local_gate.sh full mode. "
            "Lower it by removing dead imports / unused vars / redundant `mut` in clean-kernel.",
    "lints_forced": lints,
    "kernel_warnings": count,
    "kernel_warnings_by_lint": by_lint,
    "generated_by": "scripts/kernel_lint_ratchet.sh --update",
}
with open(data_file, "w") as f:
    f.write(json.dumps(doc, indent=2) + "\n")
print(f"kernel lint ratchet: baseline written to {data_file} (kernel_warnings={count})")
PY
  exit 0
fi

baseline=$(effective_baseline "${LINTS[*]}")
if [[ "$baseline" -lt 0 ]]; then
  echo "KERNEL LINT RATCHET: FAIL — the active lint set differs from the baseline's and the" >&2
  echo "  baseline has no per-lint split to compare like-for-like. Re-record it" >&2
  echo "  (scripts/kernel_lint_ratchet.sh --update)." >&2
  exit 1
fi
if [[ "$count" -gt "$baseline" ]]; then
  echo "KERNEL LINT RATCHET: FAIL — clean-kernel dead_code/unused warnings grew ${baseline} -> ${count}." >&2
  echo "  Remove the new dead import / unused var / redundant \`mut\` in clean-kernel, or (if intentional)" >&2
  echo "  prefix with _ / #[allow] with a reason. Do NOT raise the baseline to mask new rot." >&2
  exit 1
elif [[ "$count" -lt "$baseline" ]]; then
  echo "kernel lint ratchet: IMPROVED ${baseline} -> ${count} — run scripts/kernel_lint_ratchet.sh --update to lock it in."
else
  echo "kernel lint ratchet: PASS (clean-kernel hidden warnings = ${count}, flat against baseline over: ${LINTS[*]})."
fi
