# Native WP certificate integration witness

`universal-permuted.json` is the exact native request/result capture for the
explicit shared-IR `choose(condition, left, right)` calculus fixture. Its
SHA-256 is `7b3b4641d71ef4b9cb935d1e2f9d724cca268945ad23e174228e8867fcb1cd9a`.
The body is the 153-byte wire-v38 module already checked by
`SemRBooleanWPBranches`; it is not a Rust compiler output.

The capture comes from trust-wp's body-aware API at public source
`3f3159224de46b3437527a3c7f512c91371a767f`. The actual generated request is
preserved, including the original contract's Param/ResultSlot bindings and
the native replay certificate. Fixture provenance labels inside the request
are test metadata, not signed release attestations. Exact build/source and
run receipts are retained under `NOV3-NATIVE-WP-EXPLICIT-BRANCH`.

`native_wp_semr.rs` uses the existing typed claim decoder and certificate
replay API. Its small reifier admits only typed Boolean operations and known
names. It reifies the original contract too; the generated Lean theorem checks
the emitted VC against the guarded postconditions of the exact SemR body,
then applies the generic branch theorem. Thus the witness checks one actual
VC translation, not soundness of every Rust WP derivation or of the reifier
on arbitrary future schemas. Changed-VC evidence, unsupported expressions,
and changed module/contract proof claims are negative controls.
