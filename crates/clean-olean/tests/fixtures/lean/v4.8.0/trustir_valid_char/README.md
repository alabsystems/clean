# `trustir_valid_char` — trust-ir's `validChar` lemmas, a Lean 4.8.0 fixture

`TrustIrValidChar.lean` is lines 417–451 of trust-ir's
`lean/trust_ir-semantics/TrustIr/Basic.lean` at trust-ir `524d8ded` (the
revision Trust's vendored bridge `.olean`s are built from), copied verbatim
inside `namespace TrustIr`: `validChar`, its `Decidable` instance, and the four
lemmas `validChar_of_lt_256`, `not_validChar_surrogate`,
`not_validChar_above_max` and `validChar_lt_two_pow_32`. Those four are the
constants Trust's default-on `bridge_gate_default_on` measured failing the
kernel re-check at Clean main `a3d6008de0` (`RecheckFailed { fail: 4, total:
2855 }`, each `check_type: TypeMismatch`), because their `omega` proofs need
`Nat` folds over Lean 4.8.0's `Init` and no Lean 4.8.0 digest was canonical.

The consuming test compiles the one module into a fresh temporary directory
with the binary of the toolchain this family directory is named for —
`leanprover/lean4:v4.8.0`, resolved by `clean_olean::installed_lean_lib_path` —
using the pinned fixture recipe's compile step (`lean --root . -o
TrustIrValidChar.olean TrustIrValidChar.lean`, cwd and `LEAN_PATH` the
directory; `tests/support/installed_lean.rs`, `compile_fixture`). Only the
source and this file are checked in; the `.olean` is a build product.

Consumer: `test_trustir_valid_char_lemmas_check_over_lean_v4_8_0_init`
(`crates/clean-olean/tests/native_fold_canon_lean_v4_8_0.rs`).

## Toolchain stamp and recipe

- `lean --version` (measured 2026-09-27):
  `Lean (version 4.8.0, aarch64-apple-darwin, commit df668f00e6c0, Release)`
- `lean --root . -o TrustIrValidChar.olean TrustIrValidChar.lean` exits 0 in
  0.37 s wall; two runs are byte-identical, SHA-256
  `63df8100069ea595a1f4e729e7a7ee39f10d050ba2e62f25c89f14ecfb7dcca3`
  (75,008 bytes).
