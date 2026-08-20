#!/usr/bin/env bash
# Local enforcement gate (roadmap A1, revised 2026-06-10: GitHub CI deleted by
# owner decision — enforcement is local and fail-closed).
#
# Run before pushing main:  scripts/local_gate.sh [--fast]
# Install as a pre-push hook: ln -sf ../../scripts/local_gate.sh .git/hooks/pre-push
#
# Gates (each fail-closed):
#   1. Soundness certificate (C1-C5+C4') + golden TCB pin + false-axiom guards
#   1b. axiom_audit.json ↔ soundness_tcb.json (cert C2 golden) consistency —
#      fail-closed; binds the first-class domain-axiom metric to the live cert
#   2. CLI feature coverage (descriptor registry ↔ clap paths ↔ referenced files)
#   3. Ratchets: unchecked-decl + axiom audit surfaced from the cert golden pins;
#      extend_constants_* bulk-bypass ratchet (fail-closed); path-to-3 TCB ratchet
#      (domain-axiom count monotonic-down toward the 3-axiom goal, fail-closed);
#      prelude/.olean collision ratchet (prelude names that DISCARD Lean's
#      declaration at import, monotonic-down, fail-closed)
#   3b. Trust-core evidence staleness tripwire: recomputes the cmd_replacement
#      module-tree digest + cmd_replacement.rs sha and fails when the checked-in
#      launch-evidence artifacts pin different digests (prints
#      TRUSTCORE_STALENESS=fresh|stale|skipped:<reason>)
#   3c. Crystal revalidation scope: binds the crystal chain revalidation records
#      to the clean-kernel SOURCE tree they were measured at, and fails when a
#      CHAINED body's own source file has moved past it (whole-crate
#      renumbering is ledgered, not failed)
#   3d. Crystal enum tag pin: the chained kernel enums' declaration order and
#      discriminants, re-derived from source and cross-checked against the
#      reflected tag defs and the recorded trust-ir artifacts. A reorder is
#      invisible to every other gate and silently makes a registered crystal
#      module a theorem about a body that is no longer shipped
#      (data/crystal_enum_tag_pin.json)
#   4. Paragon quality ratchet (shrink-only: file-size, unwrap/expect,
#      bare-pub, dead-code suppressions — data/paragon_ratchet.json)
#   4b. Lint coverage: no tracked crate outside [workspace] members, no gate
#      site that dropped --workspace/--all-targets (scripts/check_lint_coverage.py)
#   5. (full mode) workspace LINT (`cargo clippy --locked --workspace
#      --all-targets -- -D warnings`; the former bare `cargo check` obeyed
#      default-members and saw 8 of 27 crates) + NON-VACUOUS KernelVerified gate (re-stamps a
#      pinned OOM-safe slice → KV ratchet + elision subset, scripts/kv_ratchet_gate.sh)
#      + full clean-kernel --lib suite + trusted-kernel lint ratchet (dead_code/
#      unused the workspace allow hides)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

FAST=0
[[ "${1:-}" == "--fast" ]] && FAST=1
fail() { echo "LOCAL GATE: FAIL — $1" >&2; exit 1; }

echo "== local gate: cross-repo dependency boundary =="
python3 scripts/check_workspace_dependency_boundary.py \
  || fail "Clean must consume shared verification vocabulary through trust-ir-contract, never the Trust workspace"

# Lint-coverage invariant (~0.1s, metadata only — safe in the --fast path). The
# lint gate below is only worth its runtime if it still SELECTS everything: a
# tracked crate outside [workspace] members is linted by no command at all, and
# a gate site that drops --workspace/--all-targets re-opens the blind spot where
# non-default members' test targets are never compiled.
echo "== local gate: lint coverage (every tracked crate, every target) =="
python3 scripts/check_lint_coverage.py \
  || fail "lint coverage — a tracked crate escaped [workspace] members, or a gate site dropped --workspace/--all-targets (scripts/check_lint_coverage.py)"

echo "== local gate: first-party Rust contains no ignored tests or doctests =="
if ignore_hits="$(
  git grep --line-number --extended-regexp \
    '(^[[:space:]]*#[[:space:]]*!?[[:space:]]*\[[[:space:]]*(ignore([[:space:]]*=|[[:space:]]*\])|cfg_attr\([^]]*,[[:space:]]*ignore([[:space:]]*=|[[:space:]]*[,)])))|(^[[:space:]]*(///|//!|\*)[[:space:]]*```([^`,[:space:]]+,)?ignore([,[:space:]]|$))' \
    -- '*.rs' ':(exclude)vendor/**' ':(exclude)third_party/**' \
      ':(exclude)reference/**'
)"; then
  printf '%s\n' "$ignore_hits" >&2
  fail "ignored first-party tests/doctests are forbidden; make bounded tests active or move qualification/measurement code to an explicit Rust tool"
else
  ignore_scan_status=$?
  [[ $ignore_scan_status -eq 1 ]] \
    || fail "the first-party #[ignore] scanner failed with status $ignore_scan_status"
fi

echo "== local gate: soundness certificate =="
cargo test -p clean-kernel --lib --locked --features math-overlays -q \
  -- test_soundness_certificate golden_matches_live_axioms tests_false_axiom_prevention soundness_nested_arg \
  || fail "soundness certificate / golden TCB / regression suites"

echo "== local gate: axiom-audit <-> cert consistency =="
cargo test -p clean-kernel --test verify_axiom_audit_integration --locked -q \
  -- axiom_audit_tcb_mirror_matches_soundness_tcb_golden \
  || fail "axiom_audit.json drifted from data/soundness_tcb.json (cert C2 golden) — sync the soundness_tcb_mirror block"

echo "== local gate: feature coverage =="
cargo test --locked -p clean-cli --test feature_coverage -q \
  || fail "CLI feature coverage"

echo "== local gate: ratchet surfaces =="
python3 - <<'EOF' || exit 1
import json, sys
r = json.load(open('data/unchecked_decl_ratchet.json'))
tcb = json.load(open('data/soundness_tcb.json'))
audit = json.load(open('data/axiom_audit.json'))
mirror = audit.get('soundness_tcb_mirror', {})
print(f"  unchecked-decl call sites: structural={r.get('structural_call_sites', r.get('add_decl_structural', 'n/a'))} "
      f"unchecked={r.get('unchecked_call_sites', r.get('add_decl_unchecked', 'n/a'))}")
print(f"  TCB axioms: {tcb.get('axiom_count', 'n/a')} "
      f"(foundational={tcb.get('foundational_count', 'n/a')}, "
      f"domain={tcb.get('admitted_domain_count', 0) + tcb.get('other_admitted_count', 0)})")
print(f"  axiom_audit.json mirror: domain_axiom_count={mirror.get('domain_axiom_count', 'MISSING')} "
      f"(asserted == cert by step 1b)")
EOF

echo "== local gate: extend_constants bypass ratchet =="
python3 scripts/check_extend_constants_ratchet.py \
  || fail "extend_constants_* bypass ratchet — a new unaccounted bulk-import bypass; add a // SOUNDNESS: comment + a data/unchecked_decl_ratchet.json entry"

echo "== local gate: trust-verdict emitter discipline (Pillar 1) =="
python3 scripts/check_trust_verdict_emitters.py \
  || fail "trust-verdict emitter discipline — a new unclassified KernelVerified green in clean-kernel, a mislabeled kernel-rechecked entry, an un-justified asserts-own-authority emitter, or a raised own-authority ratchet; classify it in data/trust_verdict_emitters.json (Pillar-1 gate)"

echo "== local gate: path-to-3 TCB ratchet =="
python3 scripts/tcb_target_ratchet.py \
  || fail "path-to-3 TCB ratchet — a domain axiom was added (moving away from the 3-axiom goal) or the foundational set drifted; see data/tcb_target_ratchet.json"

echo "== local gate: prelude/.olean collision ratchet =="
python3 scripts/check_prelude_collision_ratchet.py \
  || fail "prelude/.olean collision ratchet — a prelude name now shadows (and discards) a differently-typed Lean declaration at import, so tactics see a statement the user never wrote; see data/prelude_collision_census.json"

echo "== local gate: prelude instance-priority ratchet =="
python3 scripts/check_prelude_instance_priority_ratchet.py \
  || fail "prelude instance-priority ratchet — a hand-registered instance carries a priority the shipped .olean contradicts (or the measured denominator shrank), so synthInstance reaches a different candidate first and elaborated terms change shape; see data/prelude_instance_priority_census.json"

echo "== local gate: silent-tactic ratchet =="
python3 scripts/check_silent_tactic_ratchet.py \
  || fail "silent-tactic ratchet — a tactic now fails with NO diagnostic naming it, so the declaration degrades to an unattributable synthetic sorry and every UnknownTactic-keyed coverage script under-reports the gap; see data/silent_tactic_census.json"

echo "== local gate: tactic family gates (G-AUTO, G-SIMP) =="
# Executable family gates (docs/plans/TACTICS_TO_100_2026-07-29.md §7; teeth
# record: scripts/tactic_parity/TEETH.md). Fixture/manifest integrity (probe
# denominators pinned at 131/127, import-Init headers, no unlisted fixtures)
# is enforced fail-closed on EVERY run — it needs no binary. The MEASURED
# gates drive the prebuilt release binary over real `import Init` fixtures
# (~2 min per fixture file, 13 files) and therefore run in full mode only;
# they NEVER invoke cargo. Exit 2 = "no prebuilt binary": non-fatal by
# design, with the SKIPPED verdict line printed by the gate itself.
# Fail-closed (any other nonzero exit is a hard failure) when the binary
# exists.
python3 scripts/tactic_parity/family_gate.py --family g_auto --static \
  || fail "G-AUTO fixture/manifest integrity (tests/fixtures/tactic_families/g_auto)"
python3 scripts/tactic_parity/family_gate.py --family g_simp --static \
  || fail "G-SIMP fixture/manifest integrity (tests/fixtures/tactic_families/g_simp)"
if [[ $FAST -eq 1 ]]; then
  echo "  G-AUTO=SKIPPED reason=fast-mode (measured gate runs in full mode, or directly: scripts/tactic_parity/g_auto.sh)"
  echo "  G-SIMP=SKIPPED reason=fast-mode (measured gate runs in full mode, or directly: scripts/tactic_parity/g_simp.sh)"
else
  for fam_gate in g_auto g_simp; do
    if scripts/tactic_parity/${fam_gate}.sh; then
      :
    else
      fam_rc=$?
      if [[ $fam_rc -eq 2 ]]; then
        : # SKIPPED verdict line already printed by the gate (no prebuilt binary)
      else
        fail "tactic family gate ${fam_gate} — fail-closed measurement failure (scripts/tactic_parity/${fam_gate}.sh exit ${fam_rc}; see reports/tactic-families/${fam_gate}-latest.json and scripts/tactic_parity/TEETH.md)"
      fi
    fi
  done
fi

# Trust-core evidence staleness tripwire. The three trust-core launch-evidence
# artifacts pin the gate logic that minted them (cmd_replacement.rs sha +, for
# kernel-soundness/deny-sorry, the sha256_repo_module_tree digest of every
# non-test .rs under crates/clean-cli/src/cmd_replacement/), so ANY edit there
# silently stales all three — the in-binary validators reject them at read time
# but nothing at push time said so. The script recomputes the IDENTICAL digests
# (byte-identity proven against the Rust-minted pin at 93670bb91) and fails
# loudly on any mismatch. Prints TRUSTCORE_STALENESS=fresh|stale|skipped:<reason>.
echo "== local gate: trust-core evidence staleness tripwire =="
python3 scripts/check_trustcore_evidence_staleness.py \
  || fail "trust-core evidence staleness — a cmd_replacement/ gate-logic edit outdated the pinned digests in reports/{kernel-soundness,deny-sorry,axiom-audit}-launch-evidence.json; regenerate with a HEAD-built clean binary (clean replacement trust-core-evidence --kernel-soundness / --deny-sorry, clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json) and commit the refreshed artifacts in the SAME change as the gate edit"

# Crystal revalidation SCOPE. Every link-2a gate compares a spec module to a
# COMMITTED FIXTURE; the only thing that ever compared a fixture to a live
# trustc dump is scripts/crystal_fixture_freshness.py, whose answer is a dated
# record (data/crystal_chain_revalidation_*.json). Nothing bound those records
# to the clean-kernel source they were measured at, so nothing could say whether
# they still describe HEAD -- and at 891b7d153 they did not: three files had
# moved in crates/clean-kernel/src/env/ with every crystal gate green.
#
# Fails on CONTENT scope only -- a chained body's own defining source file
# moving. Whole-crate functy.N/enum.N/struct.N/@func.N renumbering, which moves
# on any crate item with zero instructions changed, is printed as a ledgered
# revalidation DEBT and does not fail: a gate that reddens on renumbering is a
# gate that gets switched off, taking the content case with it. ~0.24 s.
echo "== local gate: crystal revalidation scope (chained-body source drift) =="
python3 scripts/crystal_freshness_scope.py \
  || fail "crystal revalidation scope — either a chained body's own clean-kernel source moved since the newest data/crystal_chain_revalidation_*.json (the spec module may no longer transcribe the emitted body; re-derive with scripts/crystal_fixture_freshness.py against a fresh dump and commit a new record) or the def_path->source mapping went stale (scripts/crystal_freshness_scope.py)"

# Crystal ENUM TAG PIN. Four of the eleven chained bodies are matches over a
# kernel enum, and the emitted trust-ir names no variants -- it switches on the
# NUMERIC DISCRIMINANT, which Clean's side of the proof encodes too
# (clean_mode_tag, source_system_tag, expr_path_step_tag, level_kind_tag).
# The Reference guarantees the VALUES given a declaration order; nothing
# guaranteed the ORDER. Reordering two variants changes no behaviour of the Rust
# program and fails no other gate, while moving Cubical off 2 and leaving the
# registered module, the fixture and the lineage digest byte-identical. ~0.05 s.
echo "== local gate: crystal enum tag pin =="
python3 scripts/check_enum_tag_pin.py \
  || fail "crystal enum tag pin — a chained enum's declaration order, discriminants, serde-index coherence, reflected tag def or recorded switch arms moved, so a registered crystal module now proves something about a body that is no longer shipped; see data/crystal_enum_tag_pin.json"

echo "== local gate: paragon quality ratchet =="
scripts/paragon_ratchet.sh || fail "paragon quality ratchet (see data/paragon_ratchet.json)"

echo "== local gate: portable Isabelle/Trust operations =="
python3 scripts/test_isabelle_ops_portability.py \
  || fail "Isabelle/Trust operations portability regression"

echo "== local gate: Aristotle model-guide corpus (static) =="
python3 scripts/aristotle_corpus_gate.py --fast \
  || fail "Aristotle corpus gate — a banned construct in code, a new vacuous Classical.propDecidable inhabitant of a Decidable target, a rung that gained an undischarged hypothesis, or composition byte-identity drift (which silently breaks the cross-file confluence discharge); see data/aristotle_corpus_ratchet.json. Elaboration is checked separately by 'just corpus-gate-full'."

if [[ $FAST -eq 0 ]]; then
  # Workspace lint. This step used to be `cargo check --locked -q` under a
  # "workspace check" label, which was a misnomer: bare `cargo check` obeys
  # `default-members` (8 of 27 crates), so it compiled neither clean-autoform /
  # clean-ck0 / clean-reflect nor ANY test target of the 19 non-default members
  # — including crates/clean-verify/tests, where the crystal work lands.
  # `--workspace --all-targets` under clippy strictly subsumes what it did:
  # 27/27 crates, 521/521 targets, with the [workspace.lints.clippy] deny level
  # applied. Measured 2026-08-12 on an 18-core box: 233 s from an empty target
  # dir, 172 s on top of a warm default-members clippy. Default features only —
  # feature-gated code still needs its own `-p <crate> --features` run.
  echo "== local gate: workspace lint (27/27 crates, all targets) =="
  cargo clippy --locked --workspace --all-targets -q -- -D warnings \
    || fail "workspace clippy (--workspace --all-targets) — a warning or error outside the default-members inner loop"

  # Dependency trust-boundary gate (paragon axis 1: "every dependency verified,
  # continuously gated"). Runs the cargo-deny policy in deny.toml over the whole
  # resolved dep graph: advisories (RustSec DB), licenses (SPDX allow-list),
  # bans (rustls-only: no openssl/native-tls), sources (registry locked to
  # crates.io, git locked to carcara plus immutable first-party AY). FULL-mode
  # only — it resolves the entire graph against the advisory DB, too slow for
  # the <30s --fast pre-push path. The historical state in
  # data/dep_boundary_state.json is explicitly stale after AY's Git migration
  # until this gate is rerun. SKIPs green with a notice if cargo-deny is not
  # installed, so a contributor without the tool is not blocked (install:
  # cargo install cargo-deny --locked). cargo-deny reads the committed
  # Cargo.lock, including AY's immutable Git sources.
  echo "== local gate: dependency trust boundary (cargo-deny) =="
  if command -v cargo-deny >/dev/null 2>&1; then
    cargo deny check \
      || fail "dependency trust boundary (cargo deny check — advisory/license/ban/source violation; see deny.toml + data/dep_boundary_state.json)"
  else
    echo "  SKIP: cargo-deny not installed (install: cargo install cargo-deny --locked)"
  fi

  # Per-crate supply-chain AUDIT tracker (cargo-vet — paragon axis 1: "every
  # third-party dependency VERIFIED"). Complements the cargo-deny GATE above:
  # deny checks advisories/licenses/bans/sources; vet adds per-crate human/imported
  # audit attestation (supply-chain/config.toml + audits.toml + imports.lock against
  # the trusted Mozilla/Google/Bytecode-Alliance/Embark/ISRG/Zcash registries).
  # SOFT/INFORMATIONAL by design — the historical graph exited 0 because the
  # remaining unaudited crates were carried as exemptions. The recorded state is
  # explicitly stale after AY's Git migration and must be refreshed. This remains
  # a MONOTONIC coverage tracker (audited fraction only rises / exemptions only
  # shrink), NOT a fail-closed gate that blocks every push. It prints the
  # audited-vs-exempted counts as a tracked metric. State: data/dep_audit_state.json.
  # SKIPs green with a notice if cargo-vet is absent (install: cargo install
  # cargo-vet --locked). cargo-vet reads the committed resolved graph.
  echo "== local gate: dependency supply-chain audit (cargo-vet, soft tracker) =="
  if command -v cargo-vet >/dev/null 2>&1; then
    if vet_out="$(cargo vet 2>&1)"; then
      vet_line="$(printf '%s\n' "$vet_out" | grep -i 'Vetting Succeeded' || true)"
      echo "  ${vet_line:-$(printf '%s' "$vet_out" | tail -1)}"
      echo "  (informational tracker — monotonic: audited fraction only rises; see data/dep_audit_state.json)"
    else
      # Non-zero vet means a crate is neither audited nor exempted (a NEW unvetted
      # dependency slipped in). Surface it loudly but do NOT fail the gate — this is
      # the warn-mode contract. Refresh the baseline: `cargo vet` then re-run.
      echo "  WARN: cargo vet reported unvetted dependencies (a new dep is neither audited nor exempted)."
      echo "        Refresh the baseline and update data/dep_audit_state.json. NOT failing the gate (soft tracker)."
      printf '%s\n' "$vet_out" | tail -8 | sed 's/^/        /'
    fi
  else
    echo "  SKIP: cargo-vet not installed (install: cargo install cargo-vet --locked)"
  fi

  # KernelVerified gate (NON-VACUOUS): re-stamps the pinned, OOM-safe, deterministic
  # slice (data/kv_ratchet_slice.txt) on every run and enforces BOTH the KV ratchet
  # (kernel_verified must not drop below data/mathlib_kv_ratchet.json's baseline;
  # heuristic_kernel_verified must be 0) AND the elision subset gate (KV(opaque) ⊆
  # KV(opaque-and-theorem)). Re-measuring a real slice is what makes these guards
  # bite — a static committed summary or a 0 baseline would catch nothing. SKIPs
  # green inside the script when the clean binary or the Mathlib checkout is absent.
  # Full-mode only: re-stamping the slice costs ~75s, so the --fast pre-push hook
  # skips it (same contract as the elision gate it replaces + the full kernel suite).
  echo "== local gate: KernelVerified gate (re-stamps pinned slice) =="
  KV_GATE_VERDICT_FILE="$(mktemp "${TMPDIR:-/tmp}/kv_verdict.XXXXXX")"
  export KV_GATE_VERDICT_FILE
  scripts/kv_ratchet_gate.sh \
    || fail "KernelVerified gate — re-stamping the pinned slice dropped a KernelVerified verdict (ratchet regression or elision subset breach); see data/mathlib_kv_ratchet.json + data/kv_ratchet_slice.txt"
  KV_VERDICT="$(cat "$KV_GATE_VERDICT_FILE" 2>/dev/null || echo 'KV_GATE=unknown')"
  rm -f "$KV_GATE_VERDICT_FILE"; unset KV_GATE_VERDICT_FILE

  # CLEAN_LAZY_CLOSURE no-weaker invariance gate. Now ALWAYS-ON: seeded by the
  # committed Minimal.olean fixture, it runs the truly-independent eager-vs-lazy
  # parity unit tests (clean-olean convert_expr vs the lazy mmap source) so a v3
  # shard-format encoder divergence is caught without a Mathlib checkout. The
  # corpus-scale binary leg still activates when KV_GATE_* are set.
  echo "== local gate: CLEAN_LAZY_CLOSURE no-weaker invariance gate =="
  KVINV_GATE_VERDICT_FILE="$(mktemp "${TMPDIR:-/tmp}/kvinv_verdict.XXXXXX")"
  export KVINV_GATE_VERDICT_FILE
  scripts/kv_invariance_gate.sh \
    || fail "kv invariance gate — lazy closure loading is not no-weaker than eager (an independent-parity unit test or the corpus leg failed)"
  KVINV_VERDICT="$(cat "$KVINV_GATE_VERDICT_FILE" 2>/dev/null || echo 'KVINV_GATE=unknown')"
  rm -f "$KVINV_GATE_VERDICT_FILE"; unset KVINV_GATE_VERDICT_FILE

  # Full clean-kernel lib suite (slow, ~30min). The soundness step above runs only
  # a name-filtered SUBSET; the full suite catches the rest — e.g. the env::tests
  # add_inductive duplicate-detection regression that sat red for days
  # (2026-06-13..15, fixed in 97e465e3) precisely because no gate ran the whole
  # suite. Full-mode only; the pre-push hook (`--fast`) deliberately skips it.
  echo "== local gate: full clean-kernel --lib suite (slow) =="
  cargo test -p clean-kernel --lib --locked --features math-overlays -q \
    || fail "clean-kernel --lib suite (full)"

  # Trusted-kernel lint ratchet (audit #6): re-surfaces the dead_code/unused
  # debt the workspace [lints] allow hides in clean-kernel. Last because it
  # `cargo clean -p clean-kernel` (force-warn needs a fresh compile), which
  # would otherwise invalidate the suite's artifacts above. Full-mode only.
  echo "== local gate: trusted-kernel lint ratchet =="
  scripts/kernel_lint_ratchet.sh \
    || fail "kernel lint ratchet (clean-kernel dead_code/unused grew — see data/kernel_lint_ratchet.json)"
fi

# Trust-verify SOUNDNESS ratchet (conditional): if a local Trust stage1 can be
# discovered portably, assert the verifier still leaves the genuinely-false
# canary obligations unproved (no false-proves). An explicitly configured but
# invalid/ambiguous toolchain fails closed; a machine with no Trust checkout
# retains the historical conditional skip. Fast (canaries only); the heavy
# coverage re-verify runs separately: scripts/trust_verify_ratchet.sh --coverage.
if stage1_bin="$(bash scripts/trust_verify_ratchet.sh --locate-stage1)"; then
  echo "  using Trust stage1: $stage1_bin"
  echo "== local gate: trust-verify soundness ratchet =="
  bash scripts/trust_verify_ratchet.sh --soundness \
    || fail "trust-verify soundness ratchet — a genuinely-false canary obligation was PROVED (verifier unsoundness; data/trust_verify_ratchet.json)"
else
  locate_rc=$?
  if [[ "$locate_rc" -eq 2 ]]; then
    echo "== local gate: trust-verify soundness ratchet (SKIP: no local Trust stage1) =="
  else
    fail "Trust stage1 discovery is invalid or ambiguous; set TRUST_STAGE1_BIN explicitly"
  fi
fi

# Trust-ir CODEGEN ratchet (opt-in): compile clean-kernel with trustc and the
# codegen FLIP on, and assert the measured lowering/splicing/flip counts have
# not regressed. This is a DIFFERENT mechanism from the soundness ratchet above
# (`-Ztrust-verify`, the Level-0 verifier); it exercises the crystal's path,
# THIR -> trust-ir -> derived-MIR differential -> codegen flip.
#
# OPT-IN because it is a non-incremental release compile of clean-kernel under a
# compiler that lives outside this repo (~4 min), and because at 1.28% of `fn`
# bodies flipping there is no case for putting it on every local run yet. It is
# additive: nothing here relaxes an existing gate.
#
# The COMPILE stays opt-in, and that is a decision with a reason, not inertia:
# it is a non-incremental release compile of clean-kernel under a compiler that
# lives OUTSIDE this repo and moves on its own schedule. Making it mandatory
# would block every clean-side push on trust-side drift — which is not
# hypothetical, because `lowered`/`spliced` are red at HEAD today by established
# COMPILER DRIFT (reports/trust-ir-ratchet-verdict-2026-08-13.md) with the
# re-baseline deliberately left to the owner.
#
# What is NOT opt-in any more is the SIGNAL. The 2026-08-13 loss of 38 `agreed`
# verdicts went unnoticed for two days because nothing anywhere printed how long
# it had been since anyone measured. The staleness surface below costs no
# compiler and ~0.1 s, and it puts that number in front of a human on EVERY gate
# run, opted in or not.
echo "== local gate: trust-ir axis comparator (no compiler; ~0.1s) =="
python3 scripts/trust_ir_axes.py selftest \
  || fail "trust-ir axis comparator selftest — the ratchet's own comparator is broken (scripts/trust_ir_axes.py)"
TRUST_IR_AXES_VERDICT="$(
  python3 - <<'PY'
import datetime, json, subprocess, sys
try:
    doc = json.load(open("data/trust_ir_build_baseline.json"))
except (OSError, ValueError) as exc:
    print(f"trust-ir axes: NO BASELINE ({exc})")
    sys.exit(0)
gated = subprocess.run([sys.executable, "scripts/trust_ir_axes.py", "table"],
                       capture_output=True, text=True).stdout.strip().splitlines()[-1]
stamp = doc.get("updated_utc_date", "?")
try:
    # UTC on both sides: the baseline stamp is UTC, and comparing it to a LOCAL
    # date reads "-1d old" for a baseline written minutes ago west of Greenwich.
    today = datetime.datetime.now(datetime.timezone.utc).date()
    age = max(0, (today - datetime.date.fromisoformat(stamp)).days)
except ValueError:
    age = None
label = "STALE" if (age is None or age > 7) else "fresh"
print(f"trust-ir axes: baseline {stamp} ({'?' if age is None else age}d old) — {label}; {gated}")
PY
)"
echo "  ${TRUST_IR_AXES_VERDICT}"
case "$TRUST_IR_AXES_VERDICT" in
  *STALE*) echo "  ^ nobody has re-measured the trust-ir coverage axes in over a week."
           echo "    Run: CLEAN_TRUST_IR_BUILD=1 scripts/local_gate.sh   (or scripts/trust_ir_build.sh)" ;;
esac

if [[ "${CLEAN_TRUST_IR_BUILD:-0}" == "1" ]]; then
  echo "== local gate: trust-ir codegen ratchet =="
  # `set -e` is on, so capture the status without letting a non-zero exit abort
  # the gate before it can distinguish SKIP (2) from FAIL.
  tib_rc=0
  bash scripts/trust_ir_build.sh || tib_rc=$?
  case "$tib_rc" in
    0) ;;
    2) echo "  SKIP: no local Trust stage1 toolchain" ;;
    *) fail "trust-ir codegen ratchet (data/trust_ir_build_baseline.json)" ;;
  esac
else
  echo "== local gate: trust-ir codegen ratchet (SKIP: set CLEAN_TRUST_IR_BUILD=1) =="
fi

# What the KV gates actually DID, not merely that they exited 0. Both have
# skip-green paths that fire routinely (absent corpus, low free RAM), so "the
# local gate is green" does NOT by itself mean the KernelVerified claim was
# re-measured. Surfacing the verdict here means nobody has to reconstruct which
# of the six paths a run took by re-reading stdout.
if [[ -n "${KV_VERDICT:-}${KVINV_VERDICT:-}" ]]; then
  echo "== local gate: KV measurement verdicts =="
  [[ -n "${KV_VERDICT:-}" ]]    && echo "  ${KV_VERDICT}"
  [[ -n "${KVINV_VERDICT:-}" ]] && echo "  ${KVINV_VERDICT}"
  case "${KV_VERDICT:-}" in
    KV_GATE=measured) ;;
    *) echo "  NOTE: the KernelVerified slice was NOT re-measured on this run."
       echo "        A green gate here is the ABSENCE of a measurement, not a passing one."
       echo "        Re-run with KV_GATE_REQUIRE_MEASURED=1 to make that a hard failure." ;;
  esac
fi

echo "LOCAL GATE: PASS"
