# Strict Trust unit parser inputs

`trust_cg_sentinel_decide_caef982.lean` is an unchanged copy of
`proofs/sentinel_decide_spec.lean` from TrustCG
`caef982ce` (the TY locked dependency under investigation). Its SHA-256 is
`611ffa696abcc9580cf49fa6d625c3a364f9ab7a3de066f0c44c5365e8bb28b7`.
The source retains its original copyright/license and all declarations,
imports, comments, proof terms and theorem statements.

`trust_temporal_notation_add81bfd.lean` is the exact output of
`trust-temporal-prelude::notation()` at Trust
`add81bfd24b1c66a7e959aad280aa69cef5ed3bf`. The owner's implementation visits
`Temporal`, `FiniteModel`, `FiniteModelCheck`, `Binding`, then `Protocol`;
for each source line it splits the first whitespace-delimited word at `:`
and retains `prefix`, `postfix`, `infix`, `infixl`, `infixr` or `notation`,
adding a newline. It adds no declarations of its own.

The integration target `strict_trust_units` uses the same strict parser API
and empty tactic-pattern table as Trust's ordinary Rust parse-time consumer.
It retries with these served notation lines, filters the prepended
declarations, and retains the first error when both attempts fail. It does
not use the elaborator's broader builtin tactic patterns and never accepts
parser-recovery declarations. Parsing these inputs establishes syntax
admission only; theorem elaboration, kernel checking and machine-code
execution are separate obligations.
