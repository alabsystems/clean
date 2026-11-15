# `ir_census` — compiled-IR decoder fixtures

Three sources the pinned `lean` compiles, read by `crates/clean-olean/src/lean_ir/tests.rs` and
`crates/clean-olean/src/lean_ir/adversarial_tests.rs`:

| Source | Header | What Lean writes |
|---|---|---|
| `IrPlain.lean` | none (not a `module`) | `.olean` only; every IR declaration in its `Lean.IR.declMapExt` entries |
| `IrModule.lean` | `module` | `.olean` / `.olean.server` / `.olean.private` plus `.ir`; the private part keeps only the `meta` closure with bodies and turns every other public declaration into an opaque `extern` (`declMapExt.exportEntriesFnEx`, `Lean/Compiler/IR/CompilerM.lean`); the `.ir` file carries every body |
| `IrAdv.lean` | none (not a `module`) | `.olean` only; shapes the Mathlib closure never carries (see below) |

`IrPlain` exercises `case` over scalar and object scrutinees, nested join points,
`sset`/`sproj`/`uset`/`uproj`, `isShared`, string and multi-limb `Nat` literals, `UInt64`
literals, closures, `partial def`, `@[extern]`, `@[implemented_by]` and `initialize`.

`IrAdv` carries what the Mathlib-closure differential never meets: `adhoc` and `inline` extern
entries and a two-entry `@[extern]`, `sorryDep?` in a non-`module` file, `Nat` literals at the
tagged/MPZ boundary (2^63 - 1, 2^63, 2^64), a string literal with NUL/CR/DEL and `»«`,
`float32`, and names that need escaping — one containing a newline, which Lean's formatter
breaks at the current nesting.

The tests never hard-code what Lean prints for these files: they run
`../oracle/IRCensusOracle.lean` with the same pinned binary and compare its complete output
(rows, rendered declarations, attribute lines) with `clean_olean::lean_ir::census::run_census`,
the function behind `clean olean ir-census`. Only the sources, `ORDER` and this file are checked
in; the artifacts are build products.
