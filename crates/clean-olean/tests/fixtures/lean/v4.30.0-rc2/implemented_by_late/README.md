# `implemented_by_late` — `@[implemented_by]` bindings Lean applied after compiling code

Seven sources the pinned `lean` compiles (`prelude` over `Init.Prelude`, and `LateHyg` over
`Init.Notation`, which its macro needs), read by
clean-olean's `import::late_binding` tests and by clean-native's
`compile_implemented_by_import_tests.rs` (`docs/DECISIONS.md` R149). Lean compiles a declaration
when it is added, so a binding written after the declaration (`attribute [implemented_by t] d`)
finds code compiled from `d`'s own body, and Clean, which substitutes `t` at every reference,
would print another number than Lean. The import loader records such a binding in the order
record, and `clean run` refuses every root.

| Program prints | Pinned Lean (`lean --run`) | Clean with the binding applied |
|---|---|---|
| `lateCaller 1` (`LateLib`: caller before the command) | `30` | `20` (measured at exit 0 before this fixture's fix) |
| `lateAfter 1` (`LateLib`: caller after the command) | `20` | `20` (refused all the same: the module has a late binding) |
| `macroCaller 1` (`LateMacro`: `@[macro_inline]`, caller before) | `30` | `20` |
| `macroSlow 1` (`LateMacro`) | `3` (the body is expanded, binding or not) | `2` |
| `inlineCaller 1` (`LateInline`: `@[inline]`, caller before) | `30` | `20` |
| `inlineSlow 1` (`LateInline`) | `3` (the pre-binding body is inlined) | `2` |
| `okSlow 1` (`LateOk`: `@[noinline]`, nothing in the module calls it) | `2` | `2` |
| `recCaller 3` (`LateOk`: recursive `recSlow` bound on itself) | `90` | `90` |
| `recSlow 3` (`LateOk`) | `9` | `9` |
| `hygCaller 1` (`LateHyg`: bound on its declaration inside a macro, hygienic name) | `20` | `20` |
| `hygFast 1` (`LateHyg`) | `2` | `2` |
| `ctorUse 1` (`LateCtor`: `attribute [implemented_by pf] P.mk`) | `1` (a constructor binding is never run) | refused (exit 139 when registered as on-declaration) |
| `tUse 1` (`LateCtor`: `attribute [implemented_by tf] T.leaf`) | `1` | refused |
| `(pf 1).a` (`LateCtor`) | `11` | refused |
| `axCaller 1` (`LateAx`: `@[implemented_by axFast] axiom axSlow`) | `20` | `20` |
| `axFast 1` (`LateAx`) | `2` | `2` |

`LateMacro`'s binding is never registered (Lean expands a `@[macro_inline]` body at every call
site), so its programs print Lean's bytes. `LateOk`'s bindings are not late: `okSlow` is
`@[noinline]` and unreached, and `recSlow`'s IR calls `recFast` where it recurses, so it was
compiled after its binding. `LateHyg`'s binding is written on its declaration by a macro, so the
declaration's name is hygienic and ends in a number (`hygSlow._@.LateHyg.<hash>._hygCtx._hyg.3`),
the shape of the `TypeName` instances pinned `Std` derives (`Std.Http.Body.inst._@...`); Lean
compiled no IR for it, and it is not late. `LateCtor`'s constructor bindings are never run by
Lean, which compiles a constructor structurally; Clean records them as late, so every root of the
module is refused (an over-refusal, and the fail-closed one). `LateAx`'s axiom is called, and Lean
runs its implementation; a `module`'s public part exports a definition or opaque whose body it does
not expose as an axiom too.

Only the sources, `ORDER` and this file are checked in; the `.olean` files are build products
(`clean_olean::test_support::compiled_fixture_dir`).
