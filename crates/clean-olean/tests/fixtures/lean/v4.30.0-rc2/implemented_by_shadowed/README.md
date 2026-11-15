# `implemented_by_shadowed` — a binding whose target Clean's builtin prelude types otherwise

One source the pinned `lean` compiles (`ShadowLib.lean`, `prelude` over `Init.Prelude`), read by
clean-native's `compile_implemented_by_import_tests.rs` (`docs/DECISIONS.md` R149). Lean checks
an `@[implemented_by]` target's type against the declaration's when the attribute is applied,
against the declarations Lean holds. Clean resolves an imported binding's names in its own
environment, where the builtin prelude's declaration of the same name can have another type, so
each link is checked again where it is followed (`clean_compiler`'s `link_types_agree`) and a
link that fails is refused by name (`CompilerError::ImplementedByTypeMismatch`).

Since `6e12a7791` (and `docs/DECISIONS.md`, 2026-11-14) a Lean-written artifact's closure
gets the selected world's genuine Init, not the builtin prelude, so both targets resolve to the
declarations Lean held and neither is a resident of another type. The test now pins that:

| Program prints | Pinned Lean (`lean --run`, re-measured 2026-11-14) | Clean |
|---|---|---|
| `modVia 7 3` (genuine `Nat.modCore : Nat → Nat → Nat`, `@[extern "lean_nat_mod"]` with a body) | exit 1, "Failed to find LCNF signature for Nat.modCore" | refused by name at the followed link's end (`native-extern-body`) |
| `finSelfEq ()` (genuine `instDecidableEqFin : (n : Nat) → DecidableEq (Fin n)`) | `true` | `true`, exit 0 (the builtin-prelude over-refusal closed) |

The type check where a link is followed (`link_types_agree`) keeps its unit control in
`clean-compiler`.

Only the source, `ORDER` and this file are checked in; the `.olean` is a build product
(`clean_olean::test_support::compiled_fixture_dir`).
