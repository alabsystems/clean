This family imports canonical SemR and the unsigned primitive rules unchanged.
`SemRUnsignedDivision` proves positive, representable constant division over a
valid u64 input by composing the actual parameter-range Assume, zero-divisor
Assert, unsigned division, and return steps. Its raw_megabytes specialization
retains all 17 instructions of the original compiler capture.

The Rust regression keeps the complete original native bundle, including both
proof rows and inert metadata. It serializes that module through the shared
codec and proves exact canonical decoded-module equality before applying the
universal return theorem. Wrong-divisor, zero-divisor, and changed-return
mutants cannot accept the original theorem; the zero-divisor assertion still
panics. These are IR execution facts, not new numeric caller composition,
source identity, proof grades, or Rust-to-IR translation authority.

The closed replay lives in `tests/support/unsigned_division_replay.rs`, shared
with a small standalone harness that needs only the normal Clean libraries.
It checks the supplied raw bytes against the artifact's `rawBlob` in the
ReferenceKernel, rejects a changed divisor request by exact byte identity before
proof reuse, and retains all
four original universal refutations. `SemRDivisionTransfer` proves that each
universal bad claim implies its concrete counterexample result equality. The
regression tries to transfer the source theorem’s checked consequence to those
normalized targets, requiring `TypeMismatch`, never resource exhaustion. This
avoids reevaluating an unchanged decoder during every negative comparison.
Already admitted theorem constants supply the reused proofs. Native encoder
and interpreter checks remain separate; saved terms still undergo closed replay.

The retained v52 wire artifact is derived from the original compiler JSON.
The codec identity regression requires the current shared encoder to produce
those exact bytes before treating the previously checked question as unchanged.

The replay uses the default two-million-heartbeat allowance. Earlier direct
comparisons of the full universal statement types exhausted both two-million
and test-local eight-million allowances at `WrongDivisor`; those failed attempts remain evidence,
not semantic negatives. The new implication proofs preserve the original
claims while adding normalized-consequence controls. These do not demonstrate
that the original `raw_correct`-to-`Wrong*` API comparisons reach a semantic
rejection: the direct suite remains unqualified after that resource refusal. The checked original
`¬Wrong*` facts establish the semantic counterexamples. No production checker
default changes.
