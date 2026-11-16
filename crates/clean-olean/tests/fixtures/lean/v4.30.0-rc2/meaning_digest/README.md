# Meaning digest mutation controls

`MeaningDigestBase.lean` and three single-change copies of it, each compiled
alone by the pinned Lean and loaded alone by
`crates/clean-olean/tests/meaning_digest.rs`, which compares the meaning
digest (`crates/clean-olean/tests/support/meaning_digest.rs`) of the same
names across them:

| Module | Change | Pins that must move |
|---|---|---|
| `MeaningDigestBody` | the recursive body of `Tm.instAll` (it lives in `Tm.instAll._f`) | `Tm.instAll`, `Reaches`, `reaches_leaf` |
| `MeaningDigestMention` | `SemLE`, which `leq_sound` names | `SemLE`, `leq_sound` |
| `MeaningDigestProof` | the proof of `leq_sound` | none |

The test also computes the digests the four statement-pin tests used before
(the constant's own type, value, or type and value) and requires them to miss
the first two changes: the controls are ones the old pins could not see.
