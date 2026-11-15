# Private family dependencies

Pinned Lean writes three cumulative parts of this module. The Prop structure
`ProofOnly` has a proof-only field mentioning a private definition. Its honest
recursor admits a motive universe; `DataField`, which contains actual data,
must remain Prop-only. Tests read the real parts, preserve source ordinals,
and mutate records only to exercise mandatory import refusals.
