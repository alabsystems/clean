# The compiled-checker refusal's negative controls

The packages Trust is to compile and run refuse every construct that changes
executed code without moving a meaning pin
(`crates/clean-olean/tests/support/compiled_code.rs`). Each module here,
compiled alone by the pinned Lean and loaded alone by
`crates/clean-olean/tests/compiled_code.rs`, carries exactly one of them, and
`CompiledCodeClean` carries none. The last three import `Lean`, which the
refusal refuses by itself; the test does not load them (a load of their closure
reads all of `Lean`), so each is also refused for its missing load summary, and
its other refusals come from the parser's reading of its compiled data:

| Module | Construct | Refusal the test requires |
|---|---|---|
| `CompiledCodeClean` | a definition, a theorem and a well-founded recursive definition | none (its compiler copy `CC.Clean.halve._unsafe_rec` is the one allowed) |
| `CompiledCodeImplementedBy` | `@[implemented_by]` | a row of `Lean.Compiler.implementedByAttr` |
| `CompiledCodeExtern` | `@[extern]` | a row of `Lean.externAttr` |
| `CompiledCodeCSimp` | `@[csimp]` | a row of `Lean.Compiler.CSimp.ext` |
| `CompiledCodeExport` | `@[export]` | a row of `Lean.exportAttr` |
| `CompiledCodeInit` | `initialize` | a row of `Lean.regularInitAttr`, and the `opaque` it declares |
| `CompiledCodeBuiltinInit` | `builtin_initialize` | a row of `Lean.builtinInitAttr`, and the `opaque` it declares |
| `CompiledCodeOpaque` | `opaque` with a value | `CC.Opaque.hidden` opaque |
| `CompiledCodePartial` | `partial def` | `CC.Partial.loop` opaque, and `CC.Partial.loop._unsafe_rec` partial and run in `loop`'s place |
| `CompiledCodeUnsafe` | `unsafe def` | `CC.Unsafe.raw` unsafe |
| `CompiledCodeUnsafeRec` | a hand-written safe `def <d>._unsafe_rec` | `CC.UnsafeRec.spec._unsafe_rec`, run in `spec`'s place |
| `CompiledCodeCPass` | `@[cpass]`: a compiler pass that compiles `spec` from another body | a row of `Lean.Compiler.LCNF.passManagerExt`, and the import of `Lean` |
| `CompiledCodeFolder` | a constant folder (`registerFolder`) that folds `spec k` to `k + 1` | a row of `Lean.Compiler.LCNF.Simp.ConstantFold.folderExt`, and the import of `Lean` |
| `CompiledCodeImportLean` | `import Lean` and a metaprogram (`addDecl`) that adds a partial `spec._unsafe_rec` with another body | the import of `Lean` only: the forged copy has the shape of the compiler's own and is counted as one |

Under the pinned Lean, `spec 3` evaluates to `4` in each of the last three (in
the module and in a module that imports it), beside a `rfl` proof that it is
`3`.

The test requires each module's refusals to be exactly the listed ones, so a
refusal that stops firing, or one that starts firing on the clean module, fails
it: removing the import rule fails `CompiledCodeImportLean`, and removing the
`@[cpass]` or the folder table fails its module.

Not covered: `attribute [local csimp] thm`. A local entry is never exported, so
no table holds it, and it needs no import of `Lean`; the pinned Lean compiles
the module's own calls of the replaced constant to the replacement. A `csimp`
lemma still needs a proved `@slow = @quick`. No module here carries it, since
nothing the refusal reads could refuse it.
