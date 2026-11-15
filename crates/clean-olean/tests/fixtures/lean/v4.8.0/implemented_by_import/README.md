# `implemented_by_import` — compiler attributes read from a Lean 4.8.0 `.olean`

`ImplByLib.lean` is byte-identical to the pinned family's source
(`../../v4.30.0-rc2/implemented_by_import/ImplByLib.lean`), compiled here by
`leanprover/lean4:v4.8.0`, whose `.olean` is the v1 layout. Lean 4.8.0 is a
supported second target (trust-ir's operational semantics). Its
`ExternAttrData` is `{ arity? : Option Nat, entries : List ExternEntry }`, where
v4.30's has only `entries` (`docs/DECISIONS.md` R149).

What Lean 4.8.0 prints for `main := IO.println (toString (<expr>))` over the
module (`lean --run`, measured 2026-10-20, `Lean (version 4.8.0,
aarch64-apple-darwin, commit df668f00e6c0, Release)`):

| `<expr>` | Lean 4.8.0 | The logical body |
|---|---|---|
| `implSlow 1` | `2` | `3` |
| `implCaller 1` | `20` | `30` |
| `chainHead 1` | `8` | `10` |
| `unsafeSlow 1` | `101` | `201` |
| `externBody 1` | exit 1, "Could not find native implementation of external declaration 'externBody'" | `4` |
| `plainLib 1` | `6` | `6` |

Before R149, Clean read every v1 extension row as `Unmeasured`. A `clean run`
over this `.olean`, with the source moved away, printed `3` for `implSlow 1`
at exit 0.

Consumers:

- `crates/clean-olean/tests/compiler_attr_import_lean_v4_8_0.rs` (registration,
  and Lean 4.8.0's own `Init` rows);
- `crates/clean/tests/implemented_by_lean_v4_8_0_cli.rs` (the bytes `clean run`
  prints).

Both compile the module into a fresh temporary directory with `lean --root . -o
ImplByLib.olean ImplByLib.lean` (cwd and `LEAN_PATH` the directory). Only the
source and this file are checked in.
