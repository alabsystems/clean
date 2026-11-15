# `implemented_by_shadowed` — a binding whose target Clean's builtin prelude types otherwise

One source the pinned `lean` compiles (`ShadowLib.lean`, `prelude` over `Init.Prelude`), read by
clean-native's `compile_implemented_by_import_tests.rs` (`docs/DECISIONS.md` R149). Lean checks
an `@[implemented_by]` target's type against the declaration's when the attribute is applied,
against the declarations Lean holds. Clean resolves an imported binding's names in its own
environment, where the builtin prelude's declaration of the same name can have another type, so
each link is checked again where it is followed (`clean_compiler`'s `link_types_agree`) and a
link that fails is refused by name (`CompilerError::ImplementedByTypeMismatch`).

| Program prints | Pinned Lean (`lean --run`, 2026-10-21) | Clean |
|---|---|---|
| `modVia 7 3` (`Nat.modCore`: Lean `Nat → Nat → Nat`, Clean's prelude takes a fuel argument first) | exit 1, "Failed to find LCNF signature for Nat.modCore" | refused by name |
| `finSelfEq ()` (`instDecidableEqFin`: Lean `(n : Nat) → DecidableEq (Fin n)`, Clean's prelude the unfolded `(n : Nat) → (x y : Fin n) → Decidable (x = y)`) | `true` | refused by name (an over-refusal: the two types are definitionally equal, but the check is Lean's syntactic one) |

Only the source, `ORDER` and this file are checked in; the `.olean` is a build product
(`clean_olean::test_support::compiled_fixture_dir`).
