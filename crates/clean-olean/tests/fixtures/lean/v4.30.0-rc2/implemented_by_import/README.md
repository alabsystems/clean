# `implemented_by_import` — compiler attributes read from a Lean-built `.olean`

One source the pinned `lean` compiles (`ImplByLib.lean`, `prelude` over `Init.Prelude`), read by
`crates/clean-olean/tests/compiler_attr_import.rs` and by clean-native's
`compile_implemented_by_import_tests.rs` (`docs/DECISIONS.md` R149). Every
`@[implemented_by]` target differs observably from the logical body it replaces, so a build
that compiled the body prints another number than pinned Lean:

| Program prints | Pinned Lean (`lean --run`) | The logical body |
|---|---|---|
| `implSlow 1` | `2` (runs `implFast`) | `3` |
| `implCaller 1` | `20` | `30` |
| `chainHead 1` (`chainHead → chainMid → chainEnd`) | `8` (the END of the chain) | `10` |
| `unsafeSlow 1` (`unsafe` implementation) | `101` | `201` |
| `externBody 1` (`@[extern]` with a body, no such symbol) | exit 1, "Could not find native implementation of external declaration 'externBody'" | `4` |
| `plainLib 1` (no attribute) | `6` | `6` |

Only the source, `ORDER` and this file are checked in; the `.olean` is a build product
(`clean_olean::test_support::compiled_fixture_dir`).
