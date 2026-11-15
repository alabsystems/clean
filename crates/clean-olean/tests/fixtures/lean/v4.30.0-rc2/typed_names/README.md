# `typed_names` — quoted, hierarchical and digit names in one closure-free module (fixture family F3)

`TypedNames.lean` is a single `prelude` source with **no imports at all**, so its `.olean` can be
loaded directly (no dependency closure, no `Init` on any search path) and every declaration in
it is kernel-checkable from an empty environment. It carries:

- `Alias.value` (TWO components) and `«Alias.value»` (ONE component) with **different** bodies
  (`Type` vs `Type → Type`), so a loader that collapses the spelling changes a value;
- `«07»`, a one-component name that is all digits — a `Name.str`, never a `Name.num`;
- readers `readNested` / `readQuoted` / `read07` whose bodies reference exactly one twin each;
- `universe «u.dot»` and `keep`, whose single level parameter is the one-component name `u.dot`;
- three `Init`-free theorems `nestedExpected` / `quotedExpected` / `digitExpected :
  ∀ (p : Prop), p → p`, each provable by the kernel with no constants in scope.

`CONSTANTS` lists the ten constant names in Lean spelling (`«…»` marks a one-component name),
one per line, so a consuming test can derive the expected constant count from the fixture
directory instead of carrying a literal — `typed_names_constants` in
`crates/clean-olean/tests/typed_import_identity.rs` reads it through
`clean_olean::test_support::fixture_root().join("typed_names").join("CONSTANTS")` and parses
each line with `lean_spelled_name`. Only `TypedNames.lean`, `ORDER`, `CONSTANTS` and this file
are checked in; `TypedNames.olean` is a build product, re-minted by the fail-closed helper
`clean_olean::test_support::compiled_fixture_dir("typed_names")` (called by `fixture_file` in
`typed_import_identity.rs` and `actual_fixture` in `typed_cached_identity.rs`) or by the recipe
below. Both consuming tests were `#[ignore]` sites over a lost original until 2026-09-15.

## Toolchain stamp

- `lean-toolchain` at the repo root: `leanprover/lean4:v4.30.0-rc2`
- `lean --version` (measured 2026-09-15):
  `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`

## Recipe

```bash
while read -r m; do
  LEAN_PATH="$PWD" elan run leanprover/lean4:v4.30.0-rc2 \
    lean --root . -o "$m.olean" "$m.lean"
done < ORDER
```

Measured 2026-09-15 with the binary at `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`:
exit 0, **0.04 s** wall. A `prelude` source without `module` writes only `TypedNames.olean`.

### Why `keep` is a `noncomputable def`, not the `theorem` the survey sketched

Both alternatives were compiled on this toolchain and both FAIL:

- `theorem keep : ∀ (α : Sort «u.dot»), α → α := fun _ a => a` →
  `error: type of theorem `keep` is not a proposition  (α : Sort «u.dot») → α → α`
  (`src/lean/Lean/Elab/MutualDef.lean:1050`). `α → α : Sort (imax u u) = Sort u`, so the
  statement is not a `Prop` and v4.30.0-rc2 refuses it as a theorem.
- `def keep : ∀ (α : Sort «u.dot»), α → α := fun _ a => a` →
  `error(lean.unknownIdentifier): Unknown constant `lcAny``. The code generator erases the
  runtime-relevant body to `lcAny`, an `unsafe axiom` declared in `Init/Prelude.lean:30`, which an
  import-free `prelude` file does not have.

`noncomputable def` keeps the exact statement and universe parameter and is never handed to the
code generator; it compiles, and the consuming tests assert only `keep`'s `level_params`.
(A `Prop`-shaped `theorem keep : ∀ (α : Sort «u.dot») (p : Prop), α → p → p` also compiles, but
changes the statement.) The `Type`-valued `def`s and the three theorems need neither workaround:
type formers are not compiled and theorems never are.

## Measured (2026-09-15, `lean --run` of a `Lean.readModuleData` inspector over `TypedNames.olean`)

`isModule = false`, `imports = 0`, `constNames = constants = 10`, `extraConstNames = 0`
(**no auxiliary constants**), `entries = 7`, 9032 bytes, format byte `[5] = 2`; raw walk:
`root = 8976`, imports array `size = 0`, `constNames` array `size = 10`, `constants` array
`size = 10`, `isModule` scalar byte at `root+48 = 0`.

The ten constants (kind, `Name` structure, level params, type, value, referenced constants):

| kind | name | levels | type | value | value refs |
|---|---|---|---|---|---|
| definition | `Name.str (Name.str anon "Alias") "value"` | `[]` | `Type 1` | `Type` | `[]` |
| definition | `Name.str anon "Alias.value"` | `[]` | `Type 1` | `Type → Type` | `[]` |
| definition | `Name.str anon "07"` | `[]` | `Type 1` | `Prop → Type` | `[]` |
| definition | `readNested` | `[]` | `Type 1` | `Alias.value` | `[Name.str (Name.str anon "Alias") "value"]` |
| definition | `readQuoted` | `[]` | `Type 1` | `«Alias.value»` | `[Name.str anon "Alias.value"]` |
| definition | `read07` | `[]` | `Type 1` | `«07»` | `[Name.str anon "07"]` |
| definition | `keep` | `[Name.str anon "u.dot"]` | `∀ (α : Sort u.dot), α → α` | `fun α a => a` | `[]` |
| theorem | `nestedExpected` | `[]` | `∀ (p : Prop), p → p` | `fun p h => h` | `[]` |
| theorem | `quotedExpected` | `[]` | `∀ (p : Prop), p → p` | `fun p h => h` | `[]` |
| theorem | `digitExpected` | `[]` | `∀ (p : Prop), p → p` | `fun p h => h` | `[]` |

Every `type_refs` list is `[]`, and the only non-empty `value_refs` are the three readers — the
module references no constant outside itself (closure-free, measured, not inferred). Kind
census: 7 definitions, 3 theorems.

### Determinism

Two compiles into fresh directories were byte-identical:
`TypedNames.olean` `45a77b2bc5173b58efe5d3b4b7f24726905d8877e0d41bf79f9ac9966253e128` (`shasum -a 256`).

## Assertions this fixture satisfies (measured number beside each)

The two consumers are `real_pinned_lean_quoted_identity_is_not_overwritten`
(`crates/clean-olean/tests/typed_import_identity.rs`, direct load) and
`real_quoted_identity_and_all_three_local_theorem_checks_survive_cached_loading`
(`crates/clean-olean/tests/typed_cached_identity.rs`, cached and parallel loaders over a private
copy named `Fixture.olean`).

- **APPLIED.** The lost original's `added_constants == 20` / `env.constants().count() == 20`
  is gone — it did not describe this fixture (**measured: 10, not 20**).
  `real_pinned_lean_quoted_identity_is_not_overwritten` derives `expected` from
  `typed_names_constants()` (the `CONSTANTS` file, 10 lines) and asserts
  `added_constants == expected.len()`, `env.constants().count() == expected.len()`,
  `duplicate_constants == 0`, no skipped constants, and that every listed name is present → 10
  distinct names, measured.
- `real_pinned_lean_quoted_identity_is_not_overwritten` — the values of `Alias.value` and
  `«Alias.value»` differ → measured `Type` vs `Type → Type`.
- both tests — `readNested`'s body references `Alias.value` (2 components), `readQuoted`'s
  references `«Alias.value»` (1 component), `read07`'s references `«07»` → measured `value_refs`
  in the table.
- both tests — `keep.level_params == [Name::anon().str("u.dot")]` → measured
  `[Name.str anon "u.dot"]` (one component).
- both tests — `typecheck_constants_full` over `{nestedExpected, quotedExpected, digitExpected}`
  passes 3 / fails 0 → the three are theorems of type `∀ (p : Prop), p → p` with value
  `fun p h => h` and no referenced constants (Lean's kernel accepted them at compile time;
  Clean's re-check is the test's job and was not run in the fixture authoring phase).
- `load` in `typed_cached_identity.rs` pushes the copied fixture's parent directory and then the
  pinned toolchain's `lib/lean` (`clean_olean::pinned_lean_lib_path()`) as search paths — the
  module has `imports = 0`, so the closure load is trivial and reads nothing from the second.
