# U2 stage-3 deferrals — obligations PENDING on this box (honest ledger)

Date: 2026-08-26 • Lane: U2 stage-3 deferrals (delta 3c items 1 and 2)
Note: `docs/analysis/u2-stage3-deferrals-2026-08-26.md`
Plan: `docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage 3, delta 3c.
Predecessor ledger: [`data/u2_stage3.PENDING.md`](u2_stage3.PENDING.md) — its
items 1-3 are still outstanding and unaffected by this work.

## What landed

1. **Deferral 1 — total rigidity classification.** A measured failure WAS
   exhibited (`crate::level_role`, fixtures p47/p48/p49/p50,
   `infer::tests::mint_name_collision`). The `LevelMVarId` half — separating
   two levels that share one `Name` — is NOT landed and is a kernel
   representation change; see the note's §1.4. The OTHER direction of the
   partial predicate ("should be assignable, treated as rigid") was probed and
   found unreachable — nothing was implemented for it, and p50 is the
   permanent tripwire left in its place (note §1.6).
2. **Deferral 2 — the legacy `level_constraints` map.** Verified dead
   mechanically, then removed.

## This box (8 GB, no Mathlib corpus, no clean-verify spec binaries) cannot run

1. **The 5-file Mathlib source-elab gate re-measurement.** On the corpus box:

   ```
   scripts/source_elab_gate.sh --jobs 3 --update
   ```

   NO-REGRESSION obligation, no per-declaration claim: the armed ratchet's
   success floor (154/77/13/8/58 on `Logic/Basic`, `Logic/Function/Basic`,
   `Data/Subtype`, `Logic/Unique`, `Order/Basic`) may not drop and the
   `sort/universe mismatch` class may not grow. Deferral 1 changes which names
   become rigid ONLY for a user-written universe spelled `u_N`; no source in
   the 5-file set writes such a name, so the expected delta is zero. Deferral
   2 is a removal with a measured zero divergence.

2. **The A/B wall-time profile on the corpus box** (stage-1 perf discipline,
   inherited unchanged). Deferral 1 replaces a `Vec<String>::contains` with a
   `HashSet` lookup that short-circuits before that `contains` on the common
   (rigid) path — strictly cheaper there, identical otherwise. Deferral 2
   removes a `HashMap` insert plus an undo record from every level
   assignment, and one map from `instantiate_levels`' hot early-out guard.
   A regression is not expected in either direction; per the plan a wall-time
   regression on the 5-file gate is a BLOCKER even with all verdicts green.

3. **E1 / kernel-obligation suite legs**: `clean-verify` spec test binaries
   are the 8.8 GB class and are banned on this box; those rows stay UNKNOWN
   here by policy — the pinned runner on the suite box owns them.

4. **`scripts/u2_battery.sh` green through its OWN gate.** The gate's
   provenance check requires its fixture inputs TRACKED and CLEAN, so with
   `p47_*.lean` … `p51_*.lean` uncommitted it refuses by
   design — the same condition stage 3 hit with p45. Run it once after commit;
   it re-mints `reports/u2-battery.json` with the derived split and the
   shipped binary's sha. Until then the equivalent assertion was executed with
   the same binary through a provenance-stripped copy of the gate, which
   reports **39 PASS-pinned / 11 FAIL-pinned, no drift** (HEAD `9cd4f68f6` was
   37 / 9; the delta is exactly p48 + p50 pass and p47 + p49 fail).

   Re-run 2026-08-26b with the mint-namespace reservation, same
   provenance-stripped route, binary built at `2ce2cf2c1` + this lane's diff:
   **40 PASS-pinned / 11 FAIL-pinned, no drift**. The delta from 39/11 is
   exactly p49 moving fail → pass and p51 arriving as a new fail pin; every
   other probe's verdict and pinned fragment is byte-stable, p47 included.

   `reports/u2-battery.json` is therefore DELIBERATELY STALE at 37 / 9 until
   that run, and must NOT be hand-edited to match. The gate DERIVES its split
   by parsing its own `pass_probe`/`fail_probe` calls precisely because a
   hand-maintained split had already drifted once — the 2026-08-23 artifact
   shipped 32 / 4 while the gate ran 34 / 6 (plan §4.1). Editing it by hand
   would re-create the defect that repair removed.

5. **`scripts/rust_frontend.sh` REFUSES on this box** — `rust-toolchain.toml`
   pins channel `trust` and the provisioned sysroot is `stable`, so the lint
   and format frontends were run directly on stable. That is a weaker lint set
   than the pinned toolchain's by construction; the `trust`-toolchain legs
   belong to a box that has it.

## Follow-up this work NAMED — route 1 LANDED 2026-08-26b

**The mint namespace was user-writable, and that was the remaining root
cause.** Minted level metavariables were spelled `u_0`, `u_1`, … — names a
user may also write. Deferral 1 made the *classification* total, so a written
name is never mistaken for a metavariable; it did NOT make the two levels
distinct, because level identity is `Level::Param(Name)`.

Two routes were named:

* **Reserve the mint namespace** so no surface identifier can collide. Cheaper
  than `LevelMVarId`.
* **A first-class `LevelMVarId`** — Lean's answer (`Level.mvar`, named only at
  `levelMVarToParam` when the full user-name set is known). This is a
  `clean_kernel::Level` representation change and therefore TCB-adjacent.

**Route 1 is done.** Metavariables mint into `?u_0`, `?u_1`, …
(`crate::level_mint::MINT_PREFIX`); `?` is not an identifier-start character,
so the level grammar has no production for one, and the single door that
bypasses the lexer's identifier rules — a guillemet identifier, measured
elaborating at `2ce2cf2c1` — is refused by `elab_level` with
`ElabError::ReservedUniverseName`. Written and minted names now inhabit
disjoint spellings, so the collision cannot be constructed. Route 2 is
therefore no longer needed for THIS class; whether level metavariables should
become first-class remains open on its own merits.

**The one worry in this ledger's route-1 bullet did not materialize, and the
reason is worth recording.** It read: "the mint name is user-visible — it
reaches generalized `level_params`, `@f.{…}` diagnostics and registered
declarations — so it needs the printing/olean surfaces to move with it".
Measured: it does not. `finalize_level_params` is the `levelMVarToParam`
boundary and already renamed every surviving mint at declaration close; that
rename now targets the WRITABLE space via
`ElabCtx::fresh_generalized_universe_param`, drawing from the same counter, so
the registered names are byte-identical (`holeOnly` kept `u_1` at `2ce2cf2c1`
and keeps `u_1` now). A reserved spelling reaches a user only in a diagnostic
that quotes an UNSOLVED metavariable — where `?u_0` is more honest than
`u_0`, which read as a declared parameter. A scan of all 127 `.lean` files
under `tests/fixtures/` and `demos/` found seven mentions — six such
diagnostics plus p51, which writes one on purpose — and ZERO registered
declarations carrying a reserved name.

**Flip landed.** `p49_mint_collision_overconstraint_MUST_FAIL.lean` is now
`p49_mint_collision_independence.lean` — three spellings, each with an arity
witness. `p48`'s `idCollide` gained the second universe parameter this ledger
predicted, `p51_reserved_mint_namespace_MUST_FAIL.lean` pins the reservation,
and `p47` keeps failing with its fragment byte-identical, which is what proves
the cost was removed without relaxing the refusal.
