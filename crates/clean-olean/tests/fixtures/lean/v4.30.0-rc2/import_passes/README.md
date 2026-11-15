# `import_passes` — pinned-Lean fixture family

Consumed by `crates/clean-olean/src/import/tests_import_passes_fixture.rs`.
Nothing here is a compiled artifact: `clean_olean::test_support::compiled_fixture_dir("import_passes")`
compiles the modules listed in `ORDER`, in that order, with the pinned
`leanprover/lean4:v4.30.0-rc2` binary (`lean --root . -o <M>.olean <M>.lean`,
cwd = a copy of this directory, `LEAN_PATH` = that copy) and caches the result
by content hash. Every module is `prelude` with no import from the toolchain,
so a load never reaches `Init`.

## Modules

| Module | Header | What it pins |
|---|---|---|
| `ImportPasses` | `prelude`, no `module`: one `.olean` | The per-module large-elimination decision (`Environment::recompute_imported_large_elim`) against Lean's own verdict read from the same file (a large-eliminating recursor carries one more universe parameter than its inductive), and the projection-derived field table of the structure-LIKE `inductive ImportPasses.Pair`. |
| `ImportPassesCarrier` | `module`: the `.olean{,.server,.private}` triple | Declares `StubParts.N`. It exists to be a whole EARLIER artifact, so that when `ImportPassesStubs` loads, the importer's projection index has already made a decision and is the incremental one, not a fresh rebuild from every constant. |
| `ImportPassesStubs` | `module`, imports `ImportPassesCarrier` | The structure-LIKE `StubParts.Pair` with public, non-`@[expose]` projection functions. Lean exports those as value-free `axiom` stubs in the `.olean` and `.olean.server` parts and as definitions only in the `.olean.private` part, so the projections reach the importer as stub UPGRADES of the private part, which adds none of their names. |

## Measured

With the pinned binary, read back by `lean --run` over
`readModuleDataParts` (the test re-derives this through the upstream oracle
`oracle/DumpOlean.lean` on every run, so a re-mint that changes it fails):

```
ImportPassesStubs.olean          StubParts.Pair.first : axiom       (no value)
ImportPassesStubs.olean.server   StubParts.Pair.first : axiom       (no value)
ImportPassesStubs.olean.private  StubParts.Pair.first : definition  fun (p : StubParts.Pair) => p.1
```

(and the same for `second`). A `structure`'s own projections are NOT
stubbed: measured on `public structure U where a b : N` in the same toolchain,
`U.a`/`U.b` are definitions with values in all three parts.

A second artifact cannot complete another's stubs: it must import the
artifact to name its structure, and then `lean` refuses the redeclaration
(`error: \`P1Import.U.a\` has already been declared`). The stub upgrade is
therefore always within one artifact's parts.
