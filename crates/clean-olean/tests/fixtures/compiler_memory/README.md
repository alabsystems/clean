# Compiler Boolean branch memory witness

`compiler-choose-native.json` is the unchanged schema-8 native bundle exported
by Trust compiler `6c9ad76dd38f001df3397e621667e038679ce3da` for
`compiler-choose.rs`. Its SHA-256 is
`9de059c02521b949c314cb92e1d68fea440f9c87925eb358d9b7ba5b09a19402`.
The original source, command, configuration, report, and capture hashes are
retained under `NOV3-CLEAN-BOOLEAN-WP-BRANCH/compiler-capture`.

The test deserializes that module with the shared IR codec and requires its
stable module digest to equal the capture. It derives a lossless wire-v38 image
without removing the scalar type catalog, function `Pure` annotation, pending
obligation or its formula. These are **derived bytes**, not bytes claimed to
have been emitted by the original compiler process. The original image is
754 bytes with SHA-256
`cf4e3886515526cab9c1e1f0e676a2ece7151741105e1480d35809bb62a0f997`.

`SemRBooleanWPMemory` proves reusable byte allocation/store/load WPs and a
computed finite-path theorem. The test kernel-checks that the derived image
decodes to the exact model, then applies the generic theorem for every Boolean
input. The target record, including its aggregate-classification tag, is kept.
Wrong-store, wrong-condition and uninitialized-load bodies have concrete
counterexamples and cannot reuse the valid proof in the same checked context.

SemR parses the non-authoritative metadata without treating its assertions as
facts. Non-scalar catalog entries and typed formula bindings remain refused.
The native WP engine still declines this memory fragment. This witness proves
the captured IR program's stated SemR result, not Rust lowering, arbitrary
memory programs, machine code, or the native WP generator's soundness.
