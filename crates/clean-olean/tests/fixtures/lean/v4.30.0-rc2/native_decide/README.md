# `native_decide` — the axiom pinned Lean's `native_decide` adds

`NativeDecideAux.lean` is a module source the pinned `lean -o` compiles (`ORDER`). It imports
`Init.Tactics` (where the `native_decide` syntax lives) instead of `Init`, so the closure stays
small enough for a debug-build test.

| Declaration | Tactic | `#print axioms` (pinned v4.30.0-rc2, 2026-10-17) |
|---|---|---|
| `nd_two_add : Eq (Nat.add 2 2) 4` | `native_decide` | `[nd_two_add._native.native_decide.ax_1_1]` |
| `nd_beq : Eq (Nat.beq 3 4) false` | `native_decide` | `[nd_beq._native.native_decide.ax_1_1]` |
| `dc_two_add : Eq (Nat.add 2 2) 4` | `decide` | none |

Lean v4.30.0-rc2 (and v4.33.1) `native_decide` goes through `Lean.Meta.nativeEqTrue`
(`Lean/Meta/Native.lean`): it compiles and runs `decide p`, then adds the per-use axiom
`<decl>._native.native_decide.ax_N_M : decide p = true` and closes the goal with
`of_decide_eq_true p s <axiom>`. Lean v4.8.0, the trust-ir world, instead closed it with
`Lean.ofReduceBool <decl>._nativeDecide_1 true (Eq.refl true)` (`#print axioms` →
`[Lean.ofReduceBool]`, measured 2026-10-17), and v4.35.0 deleted `Lean.ofReduceBool` (#14953).
A closure audit that keyed native evaluation on `Lean.ofReduceBool` alone would miss every
v4.30.0-rc2 `native_decide` theorem; `tests/native_decide_axiom_audit.rs` pins that Clean's
closure audit (`Environment::axiom_deps`) names the per-use axiom.
