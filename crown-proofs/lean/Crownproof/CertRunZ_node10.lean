/-
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0

RUN the Lean-verified integer checker on the REAL ACAS whole-box leaf cert
node10, and obtain the leaf safety as a LEAN-KERNEL THEOREM (NOT from the Rust
`clean-extcert-verify` checker).

`checkEntailmentZ realCertZ = true` is decided by the Lean kernel itself
(`decide`, reducing GMP-backed `Int` cross-multiplications — NO `native_decide`),
and `checkEntailmentZ_sound` turns that Boolean fact into the entailment theorem.
-/
import Crownproof.CertCheckerZ
import Crownproof.CertRealZ_node10

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000000

namespace Crownproof.CertCheckerZ
open Crownproof
open Crownproof.CertChecker

/-- The Lean KERNEL itself verifies the leaf cert: `checkEntailmentZ` reduces to
    `true` by `decide` (GMP `Int` arithmetic), no `native_decide`. -/
theorem realCertZ_checks : checkEntailmentZ realCertZ = true := by decide

/--
**REAL ACAS leaf node10 is safe — by a Lean-kernel-verified computation.**

For every assignment `σ` that satisfies the (kept, nonzero-multiplier) premises of
the lifted ℚ certificate, the conclusion constraint holds.  Obtained purely from
`checkEntailmentZ_sound` applied to the kernel-decided `realCertZ_checks`.

The conclusion constraint is `y ≥ b` (a `ge` on the single output variable `y`):
this is exactly the leaf's CROWN lower-bound entailment that the Rust kernel used
to PASS — now a Lean theorem instead. -/
theorem node10_leaf_safe :
    ∀ σ : Assignment,
      (∀ lc ∈ (liftCert realCertZ).premises, lc.satisfies σ) →
      (liftCert realCertZ).conclusion.satisfies σ :=
  checkEntailmentZ_sound realCertZ realCertZ_checks

#print axioms node10_leaf_safe

end Crownproof.CertCheckerZ
