# `module_twins` — quoted vs hierarchical module-name twins (fixture family F1)

Three `prelude` (non-`module`) sources whose compiled `.olean` files let a loader prove
that `«Module.part»` (ONE name component, file `Module.part.olean`) and `Module.part`
(TWO components, file `Module/part.olean`) stay distinct end to end.

| Source | Module name Lean derives (`--root .`) | Output |
|---|---|---|
| `Module.part.lean` | `` `«Module.part» `` = `Name.str anon "Module.part"` | `Module.part.olean` |
| `Module/part.lean` | `` `Module.part `` = `Name.str (Name.str anon "Module") "part"` | `Module/part.olean` |
| `Root.lean` | `` `Root `` | `Root.olean` |

Only the `.lean` sources, `ORDER` and this file are checked in. The `.olean` outputs are
build products, re-minted from the pinned toolchain by the fail-closed helper
`clean_olean::test_support::compiled_fixture_dir("module_twins")` (or by the recipe below) —
they are deterministic, see *Determinism*. Three test files consume the compiled directory:
`crates/clean-olean/tests/typed_import_paths.rs` (`root()` / `bytes()` read `Root.olean`),
`typed_module_graph.rs` and `typed_uncached_graph.rs` (`fixture()`); every consumer below was
an `#[ignore]` site over a lost original until 2026-09-15 and now runs unconditionally.

## Toolchain stamp

- `lean-toolchain` at the repo root: `leanprover/lean4:v4.30.0-rc2`
- `lean --version` (measured 2026-09-15):
  `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`

## Recipe

`ORDER` lists the modules in dependency order, one per line; each line is the source path
relative to this directory without `.lean`, and its output is the same path with `.olean`.
Run from a copy of this directory (cwd = the family dir). `LEAN_PATH` is needed only so
`Root.lean` finds its two sibling `.olean` files; Lean finds nothing else here because every
source is `prelude`.

```bash
while read -r m; do
  LEAN_PATH="$PWD" elan run leanprover/lean4:v4.30.0-rc2 \
    lean --root . -o "$m.olean" "$m.lean"
done < ORDER
```

The measurements below invoked the same binary by its absolute path
(`~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`); all three compiles exited 0.
No `.olean.server` / `.olean.private` / `.ir` companions are written for `prelude` sources
without a `module` header.

## Measured (2026-09-15, `lean --run` of a `Lean.readModuleData` inspector over the outputs)

Per part (`isModule`, `imports`, `constNames`/`constants`, `extraConstNames`, `entries`):

| Part | bytes | isModule | imports | constants | extraConstNames | entries |
|---|---|---|---|---|---|---|
| `Module.part.olean` | 2032 | false | 0 | 1: `axiom quotedTag : Type` (no value) | 0 | 5 |
| `Module/part.olean` | 2032 | false | 0 | 1: `axiom nestedTag : Type` (no value) | 0 | 5 |
| `Root.olean` | 3176 | false | 2 (below) | 2: `def fromQuoted : Type := quotedTag`, `def fromNested : Type := nestedTag` | 0 | 5 |

**Total constants across the three files: 4** (1 + 1 + 2); `extraConstNames` is 0 in every part,
so Lean emitted **no auxiliary constants** for the two `Type`-valued `def`s.

`Root.olean` import rows, in the array order Lean wrote them (= source order):

| row | `module` (Name structure) | `importAll` | `isExported` | `isMeta` |
|---|---|---|---|---|
| 0 | `Name.str anon "Module.part"` | false | true | false |
| 1 | `Name.str (Name.str anon "Module") "part"` | false | true | false |

`isExported = true` for a non-`module` header is Lean's rule
`isExported := publicTk.isSome || moduleTk.isNone` (`src/lean/Lean/Elab/Import.lean`,
`HeaderSyntax.imports`), and `prelude` is what suppresses the two implicit `Init` rows a
non-`prelude` header would prepend (measured on the `import_flags` family: 3 rows without
`prelude`, 1 with).

Referenced constants (`Expr.getUsedConstants`): `fromQuoted` value → `[quotedTag]`;
`fromNested` value → `[nestedTag]`; both types → `[]`.

Raw layout of `Root.olean`, walked by hand in Python (`struct` over the file bytes):
format byte `[5] = 2`; `base = word(80)`, `root = word(88) - base = 3120`; root object tag 0;
`imports` array pointer at `root+8` → array at offset 368, tag 246, `size = 2` (at `+8`),
`capacity = 2` (at `+16`); row pointers at `array+24` and `array+32` → row 0 at 176, row 1 at
344, each tag 0 with the module `Name` pointer at `row+8` and the three flag bytes at
`row+16 / +17 / +18 = 0 / 1 / 0`; `constNames` array (`root+16`) size 2; `constants` array
(`root+24`) size 2; `isModule` scalar byte at `root+48 = 0`.

### Determinism

Compiling the family twice into two fresh directories gave byte-identical outputs
(`shasum -a 256`):

- `Module.part.olean` `a78b34f17aae04d2c5f2f746f1964471fdf5994eb6c3a79345051641076cb2c9`
- `Module/part.olean` `1108b599a899dff2bcb4f09e2e20816b09db09573d1ba70340c6260c73b4dc4a`
- `Root.olean` `f8c806e32c4b828368331f995305ba313235cd91fb6a9c7ca502d7c56c6e52bc`

## Assertions this fixture satisfies (measured number beside each)

`crates/clean-olean/tests/typed_import_paths.rs`:

- `actual_import_rows_preserve_names_and_all_modern_flags` — `imports.len() == 2` → measured 2;
  row 0 is `Name::anon().str("Module.part")`, row 1 is `Name::anon().str("Module").str("part")`
  → measured exactly those two structures, in that order; every row is
  `LeanV2 { import_all: false, is_exported: true, is_meta: false }` → measured
  `(false, true, false)` on both rows.
- `malformed_array_row_and_boolean_do_not_drop_imports` — `original[5] == 2` → measured 2;
  base at 80, root at 88, imports array at `root+8`, first row at `array+24` → the walk above
  resolves every pointer into the file (368, 176); the seven mutation offsets (`array+7`, `+16`,
  `+24`, `row+6`, `row+16/17/18`) land on the array tag, capacity, first row pointer, row header
  and the three flag bytes respectively → layout confirmed above (flag bytes read 0/1/0 before
  mutation).
- `explicit_typed_roots_resolve_their_own_files_in_both_modes` — loading `«Module.part»` yields
  exactly 1 constant (`quotedTag`, never `nestedTag`) and `Module.part` exactly 1 (`nestedTag`,
  never `quotedTag`); `cache.len() == 2` → each twin part carries exactly 1 constant, measured.

`crates/clean-olean/tests/typed_module_graph.rs`
(`actual_quoted_and_hierarchical_imports_remain_distinct_cold_and_warm`) and
`crates/clean-olean/tests/typed_uncached_graph.rs` (`assert_original_graph`, shared by
`ordinary_imports_keep_quoted_and_nested_dependencies`,
`shared_imports_keep_quoted_and_nested_dependencies`,
`prior_nested_import_does_not_hide_quoted_dependency`,
`union_imports_keep_quoted_and_nested_dependencies`,
`bounded_imports_count_exact_names_and_preserve_bodies` and
`bounded_shared_imports_count_only_exact_remaining_modules`):

- the loaded graph has exactly 4 constants → measured 1 + 1 + 2 = 4.
- `fromQuoted`'s body references exactly `{quotedTag}` and `fromNested`'s exactly `{nestedTag}`
  → measured `value_refs` `[quotedTag]` / `[nestedTag]`.
- `actual_quoted_and_hierarchical_imports_remain_distinct_cold_and_warm` — `cache.len() == 3`;
  `shared_imports_keep_quoted_and_nested_dependencies`,
  `prior_nested_import_does_not_hide_quoted_dependency` and
  `bounded_shared_imports_count_only_exact_remaining_modules` — `visited.len() == 3`;
  `bounded_imports_count_exact_names_and_preserve_bodies` — bounded limit 3 succeeds;
  `bounded_discovery_cannot_collapse_distinct_module_names` — limit 2 refuses → the graph is
  exactly three modules (`Root` + two imports), measured.
- `prior_nested_import_does_not_hide_quoted_dependency` — after loading the STRING
  `"Module.part"` (legacy API, resolves the hierarchical file `Module/part.olean`) the env has
  exactly 1 constant → `Module/part.olean` carries exactly 1 constant, measured.

Nothing in this family depends on a Clean-side loader result: every number above was read from
the compiled files with Lean's own `readModuleData` or from the raw bytes.
