# TEETH — recorded perturbations for the tactic family gates

Per docs/plans/TACTICS_TO_100_2026-07-29.md §7.3: **a gate with no recorded
perturbation-failure is not a gate.** This file names one specific mutation per
gate and the observation that must follow. The mutations are DESCRIBED here and
are to be DEMONSTRATED by the central verifier (this repo forbids gate authors
from running cargo; the demonstration requires a rebuild).

Both gates read per-declaration verdicts from `clean check --json`
(success_count / trust_failures / kernel_failures / proof_state_feedback) and
fail closed on: fixture/manifest drift, a probe count differing from the pinned
family denominator, any silently skipped declaration (decl_count mismatch), any
verdict that cannot be attributed to a declaration, a failing environment
canary (stub/builtin-prelude fallback), a **disarmed** environment canary (one
that the builtin prelude can also prove, and which therefore could not have
failed), a failing `required` row, zero passing probes, and any regression
against the recorded baseline
(`data/tactic_family_baselines/<family>.json`).

## Demonstration procedure (both gates)

1. At HEAD, with a freshly built release binary: `scripts/tactic_parity/<fam>.sh`
   must print `<GATE>=measured …` (exit 0).
2. Record the ratchet: `scripts/tactic_parity/<fam>.sh --update-baseline` and
   commit `data/tactic_family_baselines/<fam>.json` (the update refuses to drop
   passing rows — ratchets only go down).
3. Apply the named mutation below, rebuild the release binary, re-run the gate.
   The gate must print `<GATE>=failed reason=…baseline regression…` naming the
   flipped rows, and exit 1.
4. Revert the mutation. Step 2's baseline is the permanent teeth record; update
   this file with the observed flip count and artifact paths once demonstrated.

## G-AUTO — named mutation: revert RC-A in `norm_num.rs`

**Mutation.** In `crates/clean-elab/src/tactic/norm_num.rs`, revert the RC-A
decide-routing import

```rust
use super::decide::eval_decide as decide;
```

back to the pre-fix

```rust
use super::smt::decide;
```

(the line carries a do-not-revert comment; this mutation is exactly the defect
fixed by commit `bf3a92a10`, plan §4 RC-A).

**Must observe.** ≥3 `g_auto` rows flip pass→fail, with the norm_num rows on
true ground goals — designated rows `p_auto_norm_num_01` ((2:Nat) ≤ 3),
`p_auto_norm_num_05` (¬(3 = 4)), `p_auto_norm_num_06` ((0:Nat) < 1) — failing
via `SmtFailed { tactic: "decide", detail: "found no proof: the negated goal is
satisfiable in the solver's abstraction …" }` (the pre-2026-09-28 text of the same
failure was "found counterexample — goal is not valid", an unvalidated claim), while the `p_auto_decide_*` controls on the identical goals keep
passing (the in-file control pattern from the plan's live reproduction,
`scratchpad/rc2_control.lean`, which measured 3 pass/3 fail before the fix and
6/0 after). With the baseline recorded, the gate exits 1 on the regression;
once the designated rows are promoted to `required` in the manifest (after the
first green run), the gate fails on this mutation even without a baseline.

**Status.** Described; not yet demonstrated at HEAD (requires a rebuild — the
central verifier runs the procedure above). The "before" direction is already
recorded in the plan: §4 RC-A's live differential and the brick-progress table
(3 pass/3 fail → 6 pass/0 fail at `6cae2dac3`).

## G-SIMP — named mutation: restore the hardcoded `u_simp` level

**Mutation.** In `crates/clean-elab/src/tactic/simp/expr.rs`, in the
`lemma_levels` construction (the RC-E.1 fix site — the long two-convention
comment block), replace the per-parameter resolution

```rust
.map(|param| resolve_lemma_level(&metas, param))
```

with the pre-fix hardcoded level

```rust
.map(|_| metas.instantiate_level(&Level::param(Name::from_string("u_simp"))))
```

(this is exactly the defect fixed by RC-E part 1, commit `7936e3c17`).

**Must observe.** ≥3 of the universe-polymorphic `simp only` rows
`p_simp_only_16` … `p_simp_only_25` (List lemmas: `reverse_reverse`,
`length_reverse`, `append_nil`, …) flip pass→fail as `NoProgress` — the RC-E
measured delta was 1/10 → 7/10 on exactly this probe class — while the
monomorphic rows `p_simp_only_01..15` are unaffected (the in-file control that
isolated RC-E). With the baseline recorded, the gate exits 1 on the regression.

**Status.** Described; not yet demonstrated at HEAD (requires a rebuild — the
central verifier runs the procedure above). The "before" direction is recorded
in the plan's brick-progress table (RC-E part 1: polymorphic `simp only`
1/10 → 7/10 on one binary, A/B under `import Init`).

## Meta-teeth already executable without a rebuild

These perturbations fail the gate TODAY with no Rust mutation, and demonstrate
the fail-closed integrity properties:

- Delete (or add) one probe from any fixture without touching MANIFEST.json →
  `…=failed reason=fixture-manifest-integrity` (declaration mismatch, and the
  denominator check refuses a probe count ≠ 131/127).
- Replace a fixture's `import Init` header with a blank line →
  `…=failed reason=fixture-manifest-integrity` (builtin-prelude fixtures are
  rejected by the gate script itself).
- Point `CLEAN_BIN` at a binary whose import path cannot resolve the Init
  `.olean`s → the per-file term-mode canary fails and the gate exits 1.
- Round the `diverged` verdict off in ANY direction → `scripts/test_family_gate.py`
  goes RED in milliseconds. **DEMONSTRATED 2026-08-28** at `9051c9aaa`, three
  arms, each reverted immediately after:

  | mutation | observed |
  | --- | --- |
  | `classify_file_verdicts` stops reading the report's `diverged` list (the pre-fix reading) | 2 RED — three declarations claimed passing against the binary's `success_count=2` |
  | `diverged` rounded UP to `pass` | 1 RED — `test_diverged_is_neither_pass_nor_fail` |
  | the `--decl-budget=` flag dropped from the argv | 1 RED — `test_the_budget_is_actually_passed_to_the_binary` |

  The load-bearing check is arithmetic, not prose: the names left over after
  removing the failed and the diverged must number EXACTLY the binary's own
  `success_count`. Rounding `diverged` up to `pass` is the one direction that
  would mint a green a declaration never earned, and that count is what makes
  it impossible to do quietly. This tooth is why the budget could be turned on
  at all — see `DECL_BUDGET` in `family_gate.py` for why a runaway declaration
  used to cost its whole file's report, and
  `docs/issues/2026-08-28-simp-diverges-bridging-nat-successor-spellings.md` for the
  declaration that was doing it.
- Rewrite any canary to something the builtin prelude can also prove →
  `…=failed reason=canary-disarmed`. The canary's discriminating power is
  **measured, not assumed**: every measured run (and `--canary-check` on its
  own, ~5 s) re-runs each canary against `--prelude builtin` and requires it to
  be REFUTED there.

  This tooth exists because the property was silently lost for four days and
  nothing noticed. The canary was chosen on 2026-08-10 as
  `List.reverse_reverse`, genuinely absent from the builtin prelude at the
  time; commit `3df6e4aad` (2026-08-23) registered a kernel-proved
  `List.reverse_reverse` **into** that prelude, after which all 13 canaries in
  both families passed on `--prelude builtin` and could no longer detect the
  fallback they exist to detect. Measured 2026-08-27 at `9f604ef85`:
  `clean check --prelude builtin` proved the old canary in 0.3 s with
  `peak_decl_ticks=111`. A canary is only ever run in the environment it is
  supposed to be distinguishing FROM the other one, so the loss is invisible
  unless the other environment is measured too — which is now what the gate
  does.

## Two-way — pinned Lean's verdict on every row (item 17, phase 1, 2026-10-27)

Every declared row (probes, required, helpers, canaries; negatives and controls
once phase 2 adds them) carries pinned Lean's verdict in the sealed
`LEAN_VERDICTS.json` beside its fixture, minted only by
`scripts/tactic_parity/mint_lean_verdicts.py --family <F>` (the pinned
v4.30.0-rc2 `lean` by absolute path, 120 s / 2 GiB caps, whole-file `lean
--json` plus one `#print axioms` per row, cross-checked by a per-row split
run). Three modules hold the rules and run nothing: `lean_verdicts.py` (the
sidecar: seal, world, digests, the row grammar and the re-derivation),
`family_two_way.py` (the cross, the ratchet, `--strict`, `--check-artifact`)
and `clean_report.py` (parsing `clean check --json`). Minted 2026-10-27 and
re-minted after the review round with no verdict, class, axiom or message
changed: g_auto 139 rows, 53 accept / 86 reject (78 unknown-tactic,
8 elab-error); g_simp 137 rows, 112 accept / 25 reject (15 unknown-tactic,
10 elab-error). The elab-error rejects are the 13 canaries (`Function expected`,
frontend ledger class 73: report-only until phase 2 respells them),
`p_auto_grind_10`, `p_simp_local_09` and `p_simp_push_cast_01/03/05`.

**In world.** A probe is outside the `import Init` world only when every
tactic pinned Lean calls unknown is in `family_two_way.MATHLIB_TACTICS`
(`aesop`, `cc`, `field_simp`, `gcongr`, `linarith`, `nlinarith`, `norm_num`,
`positivity`, `ring`, `tauto`). The tokens are recorded per row at mint
(`unknown_tactics`) and `--static` re-derives them from each stored message's
position in the fixture's bytes, so a respelled token is refused. 92 of the 111
rejected rows are out of world; `p_auto_search_10` (`library_search`, renamed
`exact?` in Lean v4.3.0) is a verdict on Clean like any other row. Keyed on the
class alone, as first landed, a typo or a Clean-only tactic name was exempt.

**Recording.** The NEW-FALSE-ACCEPT ratchet sees only rows a baseline records,
so `--update-baseline` refuses any in-world row Clean accepts and pinned Lean
rejects that the baseline does not already record as a pass (a renamed row, a
new negative, a deleted baseline), unless `MANIFEST.json`'s
`two_way_record_exemptions` names it with a written reason.

**`--check-artifact`** re-crosses every row of every minted file: a minted file
the artifact never measured, or one whose bytes moved since, is UNKNOWN and
exits 3 (never `artifact-ok`; a hard failure under `--strict`), and a dropped,
duplicated or unlisted row is refused. At most one of `--static`,
`--canary-check`, `--check-artifact`; `--strict` and `--update-baseline` are
refused where they would be ignored. A measured run crosses the one sidecar
`main` validated; it is never re-read.

**What the seal is.** A plain sha256 over canonical JSON: it catches an edit
that forgot to reseal (A4), and the re-derivation catches a verdict that no
longer follows from its own stored messages (A3, A8). A forger who rewrites a
row's messages, axioms and verdict consistently and recomputes the seal passes
`--static`; only `mint_lean_verdicts.py --check` (the FULL-mode
`tactic-lean-verdicts` leg, which asks pinned Lean again) refuses that. No
in-repo stamp would help: whoever can reseal can restamp. That leg skips only
on exit 2 with the minter's own `MINT_LEAN_VERDICTS=skipped:no-usable-lean`
line; argparse's and Python's own exit 2 are hard fails.

Recorded as `arms.family_gate` in `data/gate_demonstrations.json`, for
`scripts/check_gate_registry.py --demonstrate family_gate` to replay. Every arm
is binary-free and Lean-free. Replayed by hand on 2026-10-27 in a scratch copy,
through the runner's own `_apply`: 13/13 green unmutated and red mutated. The
registry's `--demonstrate` / `--repin` did not run: every demonstration command
goes through `heavy_gate`, and the gate was held by an exclusive job with a
14-deep queue all session, so `family_gate` still records `demonstrated: null`
until the landing runs them.

| Arm | Perturbation | Red with |
|---|---|---|
| A1 | `p_auto_decide_08 : (2 : Nat) < 5` → `< 6` in `g_auto/decide.lean`, no re-mint | `--static`: `decide.lean: edited without a re-mint` |
| A2 | a comment-only edit in `g_auto/decide.lean` (the digest pins no normalisation) | the same |
| A3 | `p_auto_grind_10`'s Lean verdict hand-flipped to `accept` | `--static`: `… is recorded accept/elab-error but does not re-derive …` |
| A4 | one stored Lean message of `p_auto_grind_10` edited (the verdict still re-derives) | `--static`: `content seal broken` |
| A5 | the sidecar's `lean_world.id` set to `v4.33.1` | `--static`: `not the oracle world` |
| A8 | `p_auto_search_10`'s recorded unknown tactic respelled `aesop` | `--static`: `records unknown_tactics ['aesop']` |
| S1 | `--strict`'s rule neutered in `family_two_way.py` | `test_strict_fails_on_a_false_acceptance` |
| S2 | the NEW-FALSE-ACCEPT comparison neutered | `test_run_family_seeded_acceptance_names_new_false_accept` |
| S3 | the `sorryAx` condition in `lean_verdicts.classify` dropped | `test_classify_sorry_axiom_alone_rejects` |
| S4 | the in-world rule keyed on the class again, not the allowlist | `test_only_a_mathlib_tactic_probe_is_out_of_world` |
| S5 | `--update-baseline`'s unrecorded-false-acceptance refusal dropped | `test_an_unrecorded_in_world_false_acceptance_is_not_recorded` |
| S6 | `--check-artifact` exits 0 on a stale file | `test_a_stale_file_is_unknown_not_red_and_not_green` |
| S7 | `--check-artifact` stops requiring every minted file | `test_a_minted_file_the_artifact_never_measured_is_unknown` |

The S-arms' test files (`scripts/test_family_two_way.py`,
`scripts/test_family_gate_two_way.py`) are among `--pinned-inputs`, so editing
one re-stales the demonstration (R7).

S2 is item 17's phase-1 seeded acceptance through the measured code path:
`run_family` with `clean` stubbed passes a negative the v2 baseline recorded
`fail`, pinned Lean rejects it, and the run exits 1 naming
`NEW-FALSE-ACCEPT neg_t`; `--update-baseline` refuses it even with
`CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION=1`. An out-of-world probe is exempt from
the ratchet (pinned by `test_ratchet_unknown_tactic_probe_is_exempt`); a
negative never is.

There is no unmutated `--strict` arm: off by default, it is red on the real
families while the false-acceptance count is nonzero. The committed
`reports/tactic-families/*-latest.json` are v1 (2026-09-15) and carry no
two-way totals; `--check-artifact` refuses them as `artifact-not-v2` until
phase 2 re-measures with `target/release/clean`. Phase 2 adds the arms that
need the binary or the phase-2 MANIFEST rows: A6 (a negative rejected for a
different reason), A7 (a control pointed at a negative), and B1 (the seeded
acceptance on a real dated v2 artifact).

`scripts/test_lean_oracle_diff.sh` pins the oracle column of
`scripts/lean_oracle_diff.sh`: `LEAN=/nonexistent` used to read `0`
(ACCEPTED), because `lean_verdict` grepped for an error line and a missing
binary prints none. It now reads `2` and the script exits 2.
