# `implemented_by_late` — a late `attribute [implemented_by]` in a Lean 4.8.0 `.olean`

`LateLib.lean` is byte-identical to the pinned family's
(`../../v4.30.0-rc2/implemented_by_late/LateLib.lean`), compiled here by
`leanprover/lean4:v4.8.0` (the v1 layout). What Lean 4.8.0 prints for `main :=
IO.println (toString (<expr>))` over the module (`lean --run`, measured 2026-10-20, `Lean
(version 4.8.0, aarch64-apple-darwin, commit df668f00e6c0, Release)`):

| `<expr>` | Lean 4.8.0 | With the binding applied everywhere |
|---|---|---|
| `lateCaller 1` (compiled before the command) | `30` | `20` |
| `lateAfter 1` | `20` | `20` |
| `lateSlow 1` | `2` | `2` |

Clean's loader judges the binding late (`lateSlow` has IR in `Lean.IR.declMapExt`, so Lean
compiled it before the command), records the module's referrers and `lateSlow` itself in the
order record, and `clean run` refuses every root (`native-implemented-by-order`;
`docs/DECISIONS.md` R149).

Consumers: `crates/clean-olean/tests/compiler_attr_import_lean_v4_8_0.rs` and
`crates/clean/tests/implemented_by_lean_v4_8_0_cli.rs`. The `.olean` is a build product.
