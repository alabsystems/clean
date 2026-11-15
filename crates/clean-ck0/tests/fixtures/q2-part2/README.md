# Pinned Q2 part 2 controls

`general.ndjson` is minted by this worker's command, using pinned Lean
4.30.0-rc2 and lean4export 12581a6b680d8478175596338eb2d53383a323e3:

```
LEAN_EXPORT_MINT_CACHE=/private/tmp/clean-q2-part2-mint-cache scripts/lean_export_mint.sh --toolchain v4.30.0-rc2 --module Init.Prelude --decl List.rec --decl And.rec --decl Or.rec --decl Subtype.rec --decl Decidable.rec --decl Bool.rec --out crates/clean-ck0/tests/fixtures/q2-part2/general.ndjson
```

The script's gate admitted the run (exit 0); the sidecar records input/output
hashes and producer identity. These are original export bytes with no adapter.
`export_inductives.rs` mutates List's field type to exercise strict positivity
and the universe constraint, and mutates the seed's metadata and rules.

`forged-recursor.ndjson` and `ill-typed-body.ndjson` are unchanged copies of
Q3's independently minted bytes and producer sidecars from `/private/tmp/q3-exports`.
That worker generated ReplayForgedRec.olean and ReplayForged.olean with the
repository's `GenReplayForged.lean` under `clean-olean/tests/fixtures/lean/v4.30.0-rc2/replay_forged/`.
The sidecars name the modules and selected declarations. The checker accepts
their False family, then refuses FRT.rec's falsified numMinors and forged_bad's
ill-typed body for those semantic reasons, respectively.

`extra-axiom.ndjson` is Q3's synthetic addition to the same pinned seed bytes,
not an export admitted by Lean. It adds q3_extra_axiom and its user; no producer
sidecar is claimed. Q2's test requires all 22 seed declarations accepted and
the named planted axiom refused by axiom-policy, with no registered axiom closure.
