# U2 stage 3 — obligations PENDING on this box (honest ledger)

Date: 2026-08-25 • Lane: U2 stage 3 (the level-mint registry — retiring
identity-by-string for universe levels at the ElabCtx↔ProofState bridge)
Plan: `docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage 3.

> **The three DEFERRALS this stage recorded (plan delta 3c) were executed
> 2026-08-26.** The p21 explicitness channel landed on its own at `d7da82cef`;
> the other two — a total `is_rigid_level_param` (a measured failure WAS
> exhibited) and retiring the legacy `level_constraints` map (verified dead,
> removed) — are recorded in
> `docs/analysis/u2-stage3-deferrals-2026-08-26.md`,
> with their own pending ledger at
> [`data/u2_stage3_deferrals.PENDING.md`](u2_stage3_deferrals.PENDING.md).
> **The items below are stage 3's OWN obligations and are still outstanding.**

## Measured root cause (EXHIBITED on this box, builtin prelude)

Stage 1a seeded the tactic `ProofState`'s universe counter with a `u64`
SNAPSHOT of the enclosing `ElabCtx`'s (`seed_universe_world`). That closes
the aliasing across a whole `by` block but not WITHIN one: both authorities
then start at the same value `N`, and a single tactic STEP mints on both —
its term arguments through the ElabCtx (`elab_app` mints one level per
declared level param of every polymorphic head constant, reached from
`elaborate_exact_term` / `elaborate_refine_term` / a `have`'s term) and its
lemma instances on the ProofState (`mk_const`,
`resolve_env_rewrite_equation`). Level identity IS the `u_N` string, so the
first mid-block mint on each side named the same level twice.

Three measurements, all on this box:

1. **Unit exhibit.** Replaying the bridge-entry sequence verbatim and then
   minting once on each side returned the SAME `Name`, with the same
   `lean4_hash` (`u_2` on both).
2. **End-to-end exhibit.** `CLEAN_U2_MINT_TRACE=1` over eight builtin-prelude
   tactic scripts (a `.{u}`-polymorphic `pid`/`pid_eq` pair): SEVEN
   double-minted `u_3`, and in each of the seven the two authorities held
   DIFFERENT values for that one name at the bridge exit —
   `elabctx=S(0) proofstate=u` (×5), `elabctx=S(0) proofstate=v`, and
   `elabctx=u_3 proofstate=S(0)` (the ElabCtx's still ABSTRACT, awaiting
   generalization at declaration close, against a concrete tactic-side
   solution — the silent-monomorphization direction). The bridge exit's
   `ps.metas.instantiate_levels(&proof)` runs immediately after that point
   and realizes the ProofState's value into every occurrence of the name.
3. **A second, ElabCtx-free face.** `create_sub_proof_state`
   (`have h : T := by …`, `conv`) COPIED the counter as well, so a
   sub-proof-state and its parent minted aliasing names into one spliced
   proof term; and the second bridge entry
   (`wf_recursion::decreasing::try_tactic_on_goal`) had no counter copy-back
   at all, so after a decreasing-goal tactic run the ElabCtx could re-mint
   names that block had already used.

**What did NOT happen at HEAD: no verdict flipped.** All eight scripts
elaborate and kernel-check both before and after. The reason is an
accident of eager realization — every ElabCtx→ProofState handoff calls
`instantiate_levels` on what it hands over, so an ElabCtx level that is
already SOLVED is substituted away before it can be conflated. What survives
a handoff is an UNSOLVED ElabCtx-minted level (`instantiate_levels` passes
those through unchanged: `adopt_residual_elab_metas`, `elaborate_refine_term`
pending-goal types), and no builtin-prelude script was found in which such an
occurrence both survives into the assembled proof and meets a same-named
tactic-side solve. Soundness posture is unchanged either way: a wrong
realization is caught by `verify_tactic_proof` and the mandatory decl-close
kernel re-check, so the exposure is a spurious LOUD reject / wrong
monomorphization, never an unsound accept.

The fix does not rely on that accident: `crate::level_mint::LevelMint` is one
monotone counter shared by handle across both bridge entries, across
`ProofState::clone`, and across `create_sub_proof_state`, so two mints can no
longer produce the same id — hence never the same name.

## This box (8 GB, no Mathlib corpus, no clean-verify spec binaries) cannot run

1. **The 5-file Mathlib source-elab gate re-measurement.** Command, on the
   corpus box, per the armed ratchet's own recorded invocation:

   ```
   scripts/source_elab_gate.sh --jobs 3 --update
   ```

   Stage 3 makes NO per-declaration claim: it is a correctness/identity
   brick, not a capability flip, and no verdict changed on this box. The
   obligation is therefore a NO-REGRESSION one — the armed ratchet's success
   floor (154/77/13/8/58 on `Logic/Basic`, `Logic/Function/Basic`,
   `Data/Subtype`, `Logic/Unique`, `Order/Basic`) may not drop, and the
   `sort/universe mismatch` class may not grow. Any declaration that LEAVES
   the class is a bonus to be recorded, not a promise made here. Stage 1's
   and stage 2's per-declaration claims (`data/u2_stage1.PENDING.md`,
   `data/u2_stage2.PENDING.md`) are still outstanding and unaffected.

2. **The A/B wall-time profile on the corpus box** (stage-1 perf discipline,
   inherited unchanged). Stage 3's per-mint work is one relaxed
   `AtomicU64::fetch_add` in place of a plain `u64` increment, plus one
   `Arc` clone per bridge entry / proof-state clone; the removed
   `max(self, ps)` copy-back cancels part of that. No walk, no allocation in
   the mint path, no new cache. A regression is not expected, but per the
   plan a wall-time regression on the 5-file gate is a BLOCKER even with all
   verdicts green. Method: concurrent BEFORE/AFTER release binaries, as in
   `docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md`.

3. **E1/kernel-obligation suite legs**: clean-verify spec test binaries are
   the 8.8 GB class and are banned on this box; those rows stay UNKNOWN here
   by policy — the pinned runner on the suite box owns them.

4. **`scripts/u2_battery.sh` green-through-the-gate at the final split**: the
   gate's provenance check requires its fixture inputs TRACKED and CLEAN, so
   with `p45_bridge_mint_registry.lean` uncommitted it refuses by design. Run
   it once after commit (it re-mints `reports/u2-battery.json` with the
   derived 37 pass / 8 fail split and the shipped binary's sha). Until then
   the equivalent assertion was executed manually with the same binary (p45:
   7 passed, 0 failed), and the committed-input battery (36 pass /
   8 fail-pinned, p41–p44 included) is GREEN through the unmodified gate on
   the stage-3 binary. That committed-input mint is byte-identical to the
   HEAD one apart from `commit` and `clean_binary_sha256` — every fixture
   hash and the whole split are unchanged.

## What WAS measured on this box before landing

- Isolation probes CONFIRM the class end-to-end (the numbers above), and the
  same instrumentation on the fixed elaborator reports ZERO double-minted
  names on the same eight scripts.
- U2 battery GREEN through the unmodified gate on committed inputs, 36 pass /
  8 fail-pinned, all eight refusal pins on their exact fragments; the
  p45-inclusive run (37 pass / 8 fail-pinned) asserted with the same binary
  through a provenance-stripped copy of the gate.
- `cargo test --locked -j 2 -p clean-elab --lib test_r100_everyday_battery_full`:
  `1 passed; 0 failed; 0 ignored; 0 measured; 10922 filtered out; finished in
  693.92s` (63 snippets name-for-name; `CLEAN_EVERYDAY_UPDATE` unset —
  `reports/everyday-battery.json` untouched).
- `--lib unify`: `171 passed; 0 failed`. `--lib tactic_bridge`: `5 passed; 0
  failed` (the two stage-1 pins plus the three new stage-3 pins).
  `--lib level_mint`: `2 passed; 0 failed`. Broader regression slice
  `--lib infer::`: `1156 passed; 0 failed; 0 ignored; 0 measured; 9767
  filtered out; finished in 1997.12s` — the mint-name shift changes WHICH
  `u_N` a tactic block hands out, so this slice is the tripwire for any
  fixture that had been pinning a minted name.
- `cargo check --locked --workspace` GREEN (27 crates);
  `cargo clippy --locked --workspace --all-targets -- -D warnings` GREEN
  (`Finished dev profile … in 4m 59s`, no diagnostics);
  `cargo fmt --all --check` clean.
  NOTE: `scripts/rust_frontend.sh` REFUSES on this box —
  `rust-toolchain.toml` pins channel `trust` and the provisioned sysroot is
  `stable`, so the frontends were run directly on stable. That is a weaker
  lint set than the pinned toolchain's by construction; the `trust`-toolchain
  legs belong to a box that has it.
