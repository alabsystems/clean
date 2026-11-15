# `p3_planted` — the planted proof of `False` of the patched-kernel control

`GenP3Planted.lean` is a `lean --run` **generator**, not a module source. It builds an
environment from `Init.Prelude`, adds one theorem through `Lean.Environment.addDeclCore`, and
writes the module with `Lean.writeModule`. The `planted` family passes `doCheck := false`, the
kernel bypass `set_option debug.skipKernelTC true` uses, so its `.olean` carries a declaration
Lean's kernel never admitted. The `honest` family passes `doCheck := true`.

The consumer is `crates/clean-olean/tests/patched_kernel_control.rs` (unit P3 of
`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`). It hands these bytes to Clean's `.olean`
re-check lanes and to the pinned `leanchecker`, once on the kernel in the tree and once on the
mutant `scripts/patched_kernel_control.py` builds, which accepts exactly `Nat.zero : False`.

| Output | Import | Declaration | `leanchecker --fresh` (pinned v4.30.0-rc2, 2026-11-13) |
|---|---|---|---|
| `P3Planted.olean` | `Init.Prelude` | `theorem planted : False := Nat.zero`, unchecked | rc 1: `(kernel) declaration type mismatch, 'planted' has type Nat but it is expected to have type False` |
| `P3Honest.olean` | `Init.Prelude` | `theorem p3_honest : True := True.intro`, checked | rc 0 |

The verdicts in the last column were measured by hand when the family was written; the test
asserts them on every run.
