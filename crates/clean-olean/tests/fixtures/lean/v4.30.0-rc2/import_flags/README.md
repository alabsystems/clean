# `import_flags` — the four module-system import modifiers (fixture family F2)

Four `module`-header sources, each importing exactly `Lean` with one modifier, so a reader can
prove that the three `Import` flags (`importAll`, `isExported`, `isMeta`) are decoded from
their own bytes and not from each other.

| Source | Header | Expected `(importAll, isExported, isMeta)` |
|---|---|---|
| `FlagPlain.lean` | `module` / `prelude` / `import Lean` | `(false, false, false)` |
| `FlagAll.lean` | `module` / `prelude` / `import all Lean` | `(true, false, false)` |
| `FlagPublic.lean` | `module` / `prelude` / `public import Lean` | `(false, true, false)` |
| `FlagMeta.lean` | `module` / `prelude` / `meta import Lean` | `(false, false, true)` |

Grammar: `optional public >> optional meta >> "import " >> optional all >> ident`
(`src/lean/Lean/Parser/Module/Syntax.lean`, `Module.import`); derivation:
`importAll := allTk.isSome`, `isExported := publicTk.isSome || moduleTk.isNone`,
`isMeta := metaTk.isSome` (`src/lean/Lean/Elab/Import.lean`, `HeaderSyntax.imports`). The
`module` header is what makes the plain control `isExported = false`.

**Why every file also says `prelude`.** `HeaderSyntax.imports` prepends
`{ module := Init }` and `{ module := Init, isMeta := true }` to every header without
`prelude`, and `mkModuleData` writes `env.header.imports` verbatim. Measured on this toolchain
with a `module` + `import Lean` probe: **3** import rows — `Init (false,true,false)`,
`Init (false,true,true)`, `Lean (false,false,false)`; with `module` + `prelude` + `import Lean`:
**1** row. The consuming test (`actual_four_modern_flag_controls_have_distinct_meanings` in
`crates/clean-olean/tests/typed_import_paths.rs`) asserts `imports.len() == 1` with
`imports[0] == Lean`, so the `prelude` line is load-bearing, not cosmetic. (`Lean` imports `Init`
itself, so the empty body elaborates either way.)

Only the `.lean` sources, `ORDER` and this file are checked in; outputs are build products,
re-minted by the fail-closed helper
`clean_olean::test_support::compiled_fixture_dir("import_flags")` (once per content hash, into
the cargo target dir) or by the recipe below. Until 2026-09-15 the consuming test was an
`#[ignore]` site over a lost original; it now runs unconditionally through that helper.

## Toolchain stamp

- `lean-toolchain` at the repo root: `leanprover/lean4:v4.30.0-rc2`
- `lean --version` (measured 2026-09-15):
  `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`

## Recipe

The four modules are independent; `ORDER` lists them anyway so one loop compiles every family.
`import Lean` resolves through the toolchain sysroot (`lib/lean/Lean.olean{,.server,.private}`),
so no `LEAN_PATH` is required — it is set for uniformity with the other families.

```bash
while read -r m; do
  LEAN_PATH="$PWD" elan run leanprover/lean4:v4.30.0-rc2 \
    lean --root . -o "$m.olean" "$m.lean"
done < ORDER
```

Each compile writes FOUR files — `<Mod>.olean`, `<Mod>.olean.server`, `<Mod>.olean.private`
(`Lean.writeModule`, `src/lean/Lean/Environment.lean`, the `isModule` branch) and `<Mod>.ir`
(same function, `writeIR := true` default). Only the base `.olean` is read by
`parse_typed_imports`.

Cost, measured with `/usr/bin/time -p` on 2026-09-15: the first `import Lean` compile of the
session took **3.12 s** wall; the remaining ones **0.24–0.30 s** each. The Lean `.olean` files are
memory-mapped, not copied — the survey's "seconds, ~1-2 GB" estimate was an over-estimate.

## Measured (2026-09-15, `lean --run` of a `Lean.readModuleData` inspector over the base parts)

| Part | bytes (`.olean` / `.server` / `.private` / `.ir`) | isModule | imports | row 0 `module` | importAll | isExported | isMeta | constants | entries |
|---|---|---|---|---|---|---|---|---|---|
| `FlagPlain.olean` | 1064 / 96 / 96 / 1104 | true | 1 | `Name.str anon "Lean"` | false | false | false | 0 | 3 |
| `FlagAll.olean` | 1064 / 96 / 96 / 1104 | true | 1 | `Name.str anon "Lean"` | **true** | false | false | 0 | 3 |
| `FlagPublic.olean` | 1064 / 96 / 96 / 1104 | true | 1 | `Name.str anon "Lean"` | false | **true** | false | 0 | 3 |
| `FlagMeta.olean` | 1064 / 96 / 96 / 1104 | true | 1 | `Name.str anon "Lean"` | false | false | **true** | 0 | 3 |

Format byte `[5] = 2` in all four. Raw walk of `FlagPlain.olean` (Python `struct`): `root =
word(88) - word(80) = 1008`; imports array at offset 192, tag 246, `size = 1`; row 0 at 168 with
flag bytes `row+16/+17/+18 = 0/0/0`; `constNames` and `constants` arrays both `size = 0`;
`isModule` scalar byte at `root+48 = 1`.

### Determinism

Two compiles into fresh directories were byte-identical (`shasum -a 256`):

- `FlagPlain.olean` `a78f2e1b82ca544872e009b3904c105118a703ca058c3834caec10153636b2d6`
- `FlagAll.olean` `89966f7921c5dc41646f35371caf2a4969165521e4f13048c32ff9d5190c4baf`
- `FlagPublic.olean` `8cebe8e87cbbc189323ad2fc4e2ffc0851b52e80326bca3336c2fe3e5090e065`
- `FlagMeta.olean` `285582105d7caa18ef762146682b706ac55927b9b0118d2ba7b72bb6ca81da86`
- `FlagPlain.olean.server` `c315e3e8abca230e336705061a1a3d4bdc2986aaec268ceac95949d31777f296`,
  `FlagPlain.olean.private` `88e44c4e015699f22646afc7349c1de943542c475e63968709e2cfcbb2ac7cb9`,
  `FlagPlain.ir` `70f2c18c8fe60571892bbc1b3f61907cd1ac3a183d9d112caf6208d04fdc0063`

## Assertions this fixture satisfies (measured number beside each)

All in `actual_four_modern_flag_controls_have_distinct_meanings`
(`crates/clean-olean/tests/typed_import_paths.rs`), which reads each `<Mod>.olean` out of
`compiled_fixture_dir("import_flags")` and runs `parse_typed_imports` over it:

- `imports.len() == 1` for each of the four files → measured 1, 1, 1, 1.
- `imports[0].module_name == Name::anon().str("Lean")` → measured `Name.str anon "Lean"` in all
  four.
- `(import_all, is_exported, is_meta)` is `(false,false,false)` / `(true,false,false)` /
  `(false,true,false)` / `(false,false,true)` for `FlagPlain` / `FlagAll` / `FlagPublic` /
  `FlagMeta` → measured exactly those four triples.

Every number above was read from the compiled files with Lean's own `readModuleData` or from
the raw bytes; nothing depends on a Clean-side result.
