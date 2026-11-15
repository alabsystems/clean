# `companion_probe` — fixture family [F7] `CompanionProbe`

Pinned-Lean source for the seven tests in
`crates/clean-olean/src/import/load_parse/companion_extension_tests.rs` —
`actual_all_three_extension_snapshots_match_independent_upstream_rows`,
`actual_unknown_companion_rows_keep_positions_and_full_population`,
`actual_private_metadata_registers_without_duplicate_public_targets`,
`actual_companion_bad_extension_array_is_not_silently_omitted`,
`actual_companion_malformed_row_keeps_its_slot_and_other_rows`,
`borrowed_base_root_preserves_snapshot_without_doubling_registries` and
`borrowed_roots_require_captured_objects_not_zero_filled_gaps` — which were
`#[ignore]` sites over a lost original until 2026-09-15 and now run
unconditionally. The tests measure how Clean's typed extension decoder and
direct loader transport `Lean.Meta.instanceExtension`, `Lean.classExtension`,
`Lean.Meta.simpExtension` and `Lean.aliasExtension` rows out of a
module-system triple `CompanionProbe.olean{,.server,.private}`, including
byte mutations at fixed layout offsets and the borrowed roots between parts.

Nothing in this directory is a compiled artifact. The `.olean` triple is
minted at test time by the fail-closed helper [H]
(`clean_olean::test_support::compiled_fixture_dir("companion_probe")`, called
once per process by the file's `fixture()`) from the recipe below, and the
same `fixture()` reads the three parts back through the independent upstream
oracle [O] (`run_oracle(&[base, server, private])`, raw mode). The recorded
numbers exist so that a re-mint can be checked against them, not so that a
test can quote them: every whole-module census a test compares against is
derived from [O] or from an unmutated parse of the same bytes.

## Contents

| Path | Role |
|---|---|
| `CompanionProbe.lean` | The single fixture module (module-system header). |
| `ORDER` | Modules in dependency order, one per line: `CompanionProbe`. |
| `tools/InspectCompanionProbe.lean` | The measuring instrument (a `lean --run` program). NOT a fixture module: it is not in `ORDER` and is never compiled to an `.olean`. |
| `README.md` | This file. |

## Toolchain stamp

Every number below was produced by this binary and no other:

```
$ $HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean --version
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

That is the toolchain `$HOME/clean/lean-toolchain` pins
(`leanprover/lean4:v4.30.0-rc2`), resolved by
`clean_olean::pinned_lean_lib_path()` (`crates/clean-olean/src/lib.rs`)
to `<toolchain>/lib/lean`; the binary is `<toolchain>/bin/lean`
(`clean_olean::pinned_lean_binary()`, which [H] wraps as `pinned_lean_bin`).

## Recipe

cwd = this directory. The `--root .` is what makes the main module
`CompanionProbe` (`Lean/Shell.lean:522-526`, `moduleNameOfFileName fileName
rootDir?`); the private-name mangling below depends on it.

```
$ LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean
$ time "$LEAN" --root . -o CompanionProbe.olean CompanionProbe.lean
"$LEAN" --root . -o CompanionProbe.olean CompanionProbe.lean  0.08s user 0.06s system 95% cpu 0.145 total
```

Exit 0, no diagnostics. Because the source carries the `module` header,
`writeModule` (`Lean/Environment.lean:1868-1876`) writes the three-part
triple, and because `-o` implies compilation it ALSO writes an IR file
(`Lean/Elab/Frontend.lean:198`, `writeIR := !postponeCompile`):

```
$ ls -l CompanionProbe.olean CompanionProbe.olean.server CompanionProbe.olean.private CompanionProbe.ir
-rw-r--r--  14304 CompanionProbe.olean
-rw-r--r--   5080 CompanionProbe.olean.server
-rw-r--r--   5128 CompanionProbe.olean.private
-rw-r--r--   1664 CompanionProbe.ir
```

The consumers read the triple only; `CompanionProbe.ir` is a by-product that
[H] leaves in its cache directory and that no test opens.

**The output is byte-deterministic.** Compiled three times on 2026-09-15 (once
here, twice in fresh scratch copies of the source) and every digest agreed:

```
$ shasum -a 256 CompanionProbe.lean CompanionProbe.olean CompanionProbe.olean.server CompanionProbe.olean.private CompanionProbe.ir
28ac10e5b5195b6af0eb0446cfbe0f7d4d02b0280bb2d6faeff0c97c65641dc1  CompanionProbe.lean
2733bbb406cdd1b27a331ea64854b1543fdfd5655096bb7ebc8780570f09c5f5  CompanionProbe.olean
c022d28b21d07a2fb3f92bf7701b989fbd4a499bd340d7dc13c747ffa8c13908  CompanionProbe.olean.server
dba6aa07112ff29a56e11721bac3e9c4a05b66988f40790272f62a13c6b4a48d  CompanionProbe.olean.private
13ec4a20f11187fa258c717ab4b635e22decf38b11e5e7f8c2485f1d2c3ffee9  CompanionProbe.ir
```

(The `.lean` digest is of the source as committed; edit the source and every
line below is stale until re-measured.)

### Measuring

```
$ "$LEAN" --run tools/InspectCompanionProbe.lean \
    CompanionProbe.olean CompanionProbe.olean.server CompanionProbe.olean.private > inspect.json
```

Exit 0 in ~0.1 s. One JSON document: `parts[i]` for the base, server and
private parts in that order, each with `constants` (name, kind, `hasValue
(allowOpaque := true)`), `entries` (every extension in `ModuleData.entries`
order with its row count and, for the four extensions Clean decodes, every row
decoded by `unsafeCast` to Lean's own entry type), `entry_count`, `row_total`
and `recognized`. The parts are read with `Lean.readModuleDataParts` over the
whole prefix, because a later part shares objects with the earlier ones and
cannot be read alone (`Lean/Environment.lean:1740-1745`). The decoded row shape
(`{"value": {"kind": "instance"|"class"|"theorem"|"alias", "name"|"alias",
"priority", ...}}`) is the oracle [O] `entries` shape that `oracle_known` in
`companion_extension_tests.rs` reads, so the two instruments can be compared
row for row. The shared dumper `../oracle/DumpOlean.lean` did not exist when
this instrument was written (`ls ../` then listed `companion_probe
import_flags module_twins numeric_probe runtime_probe typed_names`, no
`oracle`); it exists now and is what `fixture()` runs, so
`InspectCompanionProbe.lean` is kept as the family-local instrument that
produced the tables below, not as anything a test executes.

## What the source declares, and why each shape is the way it is

All eight declarations sit in `namespace CompanionProbe`, so the public names
are `CompanionProbe.*` and the private ones mangle to
`_private.CompanionProbe.0.CompanionProbe.*` (`Lean/PrivateName.lean:29-30`:
`mkPrivateNameCore mainModule n = Name.mkNum (_private ++ mainModule) 0 ++ n`).
These are exactly the names `registry` and
`actual_private_metadata_registers_without_duplicate_public_targets` in
`companion_extension_tests.rs` build.

| Source | Visibility | Why |
|---|---|---|
| `public class «public.class» : Prop where holds : True` | public | Under `module`, a declaration with no modifier is PRIVATE (`Lean/Elab/DeclModifiers.lean:68-69`, `Visibility.isInferredPublic`), so `public` is explicit. |
| `private class «private.class» : Prop where holds : True` | private | |
| `public instance «public.instance» : «public.class» := ⟨trivial⟩` | public | Default priority (1000) — `actual_private_metadata_registers_without_duplicate_public_targets` filters on `row.priority == 1000`. |
| `private instance «private.instance» : «private.class» := ⟨trivial⟩` | private | |
| `@[simp] public theorem «public.lemma» : (0 : Nat) + 0 = 0 := rfl` | public | `is_simp_lemma` in the same test. Attributes precede visibility in `declModifiers` (`Lean/Parser/Command.lean:114-117`). |
| `@[simp] private theorem «private.lemma» : (1 : Nat) + 0 = 1 := rfl` | private | |
| `namespace PublicExports` / `public def «target.dot» : Nat := 0` | public | The alias target. |
| `export PublicExports («target.dot»)` | — | Adds `Lean.aliasExtension` row `CompanionProbe.«target.dot» ↦ CompanionProbe.PublicExports.«target.dot»` (`Lean/Elab/BuiltinCommand.lean:294-306`, `currNamespace ++ id`); `get_export_alias` in the same test. |

**The classes are `Prop`-valued on purpose.** A `Type`-valued structure makes
Lean register `<class>._sizeOf_inst` as a global instance through
`registerInstance` (`Lean/Meta/SizeOf.lean:493-528`, skipped when
`isInductivePredicate`) and tag `<class>.mk.injEq` `@[simp]`. Either would add
rows to the two extensions whose row counts the tests read — exactly 2
`Lean.Meta.instanceExtension` rows in the private part
(`actual_companion_malformed_row_keeps_its_slot_and_other_rows`, `source_rows
== Some(2)`) and recognized rows `[5, 5, 7]`
(`actual_unknown_companion_rows_keep_positions_and_full_population`, derived
from the oracle rows `oracle_known` decodes) — and the `_sizeOf_inst` row for
the PUBLIC class would become the private part's second instance row while
living in the base region, which the mutation test's
`expect("private row is in private part")` refuses.

**Which part carries which row is a property of each extension's export
function, measured below and explained here.** `Lean.Meta.instanceExtension`
exports an entry below `OLeanLevel.private` only if its `globalName?` is not
private (`Lean/Meta/Instances.lean:95-96`); `Lean.Meta.simpExtension` likewise
(`Lean/Meta/Tactic/Simp/SimpTheorems.lean:664-675`). `Lean.classExtension` and
`Lean.aliasExtension` are `SimplePersistentEnvExtension`s with no
`exportEntriesFnEx?`, so they export `.uniform` to all three levels
(`Lean/EnvExtension.lean:51-53`). Hence base and server each carry alias 1 +
class 2 + instance 1 + simp 1 = **5** recognized rows and the private part adds
the private instance and the private lemma = **7**.

## Measured facts, keyed to the assertions

Source of every figure: `inspect.json` from the *Measuring* step plus a Python
walk of the raw bytes (header words at 80/88, `ModuleData.entries` at
root+40, Lean object headers `rc:i32 cs_sz:u16 other:u8 tag:u8`), both run on
2026-09-15 against the digests above.

### Header layout (`word` / `root_offset` helpers; `word(.., 88)` and `word(.., 80)` in `actual_companion_malformed_row_keeps_its_slot_and_other_rows`)

| Part | bytes | byte 5 (version) | base address (word at 80) | root (word at 88) | root inside its own part |
|---|---|---|---|---|---|
| `CompanionProbe.olean` | 14304 | 2 | `0x10f221520000` | `0x10f2215237a8` | yes |
| `CompanionProbe.olean.server` | 5080 | 2 | `0x10f221530000` | `0x10f2215313a0` | yes |
| `CompanionProbe.olean.private` | 5128 | 2 | `0x10f221540000` | `0x10f2215413d0` | yes |

`ModuleData` (`Lean/Environment.lean:124-143`) lays its pointer fields out as
`imports`(+8) `constNames`(+16) `constants`(+24) `extraConstNames`(+32)
`entries`(+40) with the `isModule : Bool` scalar after them, so the `+ 40` in
`actual_companion_bad_extension_array_is_not_silently_omitted` and
`actual_companion_malformed_row_keeps_its_slot_and_other_rows` is the
`entries` field on this toolchain. Every part reports `is_module = true`.

### Per-part census (derived by `actual_all_three_extension_snapshots_match_independent_upstream_rows`, `actual_unknown_companion_rows_keep_positions_and_full_population`, `actual_companion_malformed_row_keeps_its_slot_and_other_rows`, `borrowed_base_root_preserves_snapshot_without_doubling_registries`)

| Part | `entries.len()` (extensions) | Σ `source_rows` | `constants.len()` | recognized rows |
|---|---|---|---|---|
| 0 base | **20** | **47** | **13** | **5** |
| 1 server | **22** | **59** | **13** | **5** |
| 2 private | **24** | **66** | **19** | **7** |

* **APPLIED.** The lost original's `[(22, 76, 17), (24, 90, 17), (26, 106, 28)]`
  counted every persistent extension Lean happened to write and could not be
  reproduced by authoring; it is gone.
  `actual_all_three_extension_snapshots_match_independent_upstream_rows` now
  derives `entries.len()`, Σ `count` and `constants.len()` per part from the
  oracle (`parts[i].entries`, `parts[i].constants`). This fixture measures
  `[(20, 47, 13), (22, 59, 13), (24, 66, 19)]`.
* **APPLIED.** Recognized rows are no longer the literal `[5, 5, 7]`:
  `actual_unknown_companion_rows_keep_positions_and_full_population` counts
  the oracle rows `oracle_known` decodes per part and holds Clean's recognized
  count to that. This fixture measures `[5, 5, 7]`, which happens to equal the
  lost original's literal.
* **APPLIED.** The lost original's `26` private extensions is gone;
  `actual_companion_malformed_row_keeps_its_slot_and_other_rows` asserts
  `changed.entries.len() == private.entries.len()` against the unmutated parse
  of the same bytes. Measured **24**.
* **APPLIED.** The lost original's `22` base extensions (the borrowed-root
  server/private parts resolve to the base's `entries`) is gone;
  `borrowed_base_root_preserves_snapshot_without_doubling_registries` asserts
  `summary.extension_accounting.len() == base.entries.len()`. Measured **20**.

### Extension roster per part, in `ModuleData.entries` order

Base part (20; rows decoded by Clean marked `*`):

```
[ 0]  4  Lean.auxRecExt
[ 1]  2  Lean.protectedExt
[ 2]  3  _private.Lean.Namespace.0.Lean.namespacesExt
[ 3]  1  Lean.aliasExtension                                   *
[ 4]  2  Lean.classExtension                                   *
[ 5]  4  reducibilityCore
[ 6]  2  Lean.projectionFnInfoExt
[ 7] 13  _private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt
[ 8]  4  _private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt
[ 9]  1  _private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt
[10]  2  _private.Lean.Structure.0.Lean.structureExt
[11]  1  Lean.Meta.instanceExtension                           *
[12]  1  Lean.IR.declMapExt
[13]  1  Lean.Compiler.LCNF.baseExt
[14]  1  Lean.Compiler.LCNF.monoExt
[15]  1  Lean.Compiler.LCNF.impureSigExt
[16]  1  Lean.defeqAttr
[17]  1  Lean.Meta.simpExtension                               *
[18]  1  symbolFrequency
[19]  1  sineQueNon
```

Server part (22): the base roster plus `Lean.declRangeExt` (11 rows) at
index 1 and `_private.Lean.DocString.Extension.0.Lean.moduleDocExt` (1 row) at
index 5; the four decoded extensions sit at indices 4 (alias), 6 (class),
13 (instance, 1 row), 19 (simp, 1 row).

Private part (24): the server roster plus `Lean.extraModUses` (3 rows) at
index 15 and `Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt`
(1 row) at index 19; `Lean.defeqAttr` grows 1 → 2 rows. The four decoded
extensions sit at indices 4 (alias, 1), 6 (class, 2), **13 (instance, 2)**,
21 (simp, 2).

### The decoded rows (`actual_all_three_extension_snapshots_match_independent_upstream_rows`, `actual_private_metadata_registers_without_duplicate_public_targets`)

| Extension | Part(s) | Row | Measured fields |
|---|---|---|---|
| `Lean.aliasExtension` | 0, 1, 2 | `CompanionProbe.«target.dot»` → `CompanionProbe.PublicExports.«target.dot»` | (`get_export_alias` in `actual_private_metadata_registers_without_duplicate_public_targets`) |
| `Lean.classExtension` | 0, 1, 2 | `CompanionProbe.«public.class»` | `outParams = []`, `outLevelParams = []` |
| `Lean.classExtension` | 0, 1, 2 | `_private.CompanionProbe.0.CompanionProbe.«private.class»` | `outParams = []`, `outLevelParams = []` |
| `Lean.Meta.instanceExtension` | 0, 1, 2 | `CompanionProbe.«public.instance»` | `priority 1000`, `attrKind global`, `Entry.global`, `synthOrder []`, 1 key |
| `Lean.Meta.instanceExtension` | 2 only | `_private.CompanionProbe.0.CompanionProbe.«private.instance»` | `priority 1000`, `attrKind global`, `Entry.global`, `synthOrder []`, 1 key |
| `Lean.Meta.simpExtension` | 0, 1, 2 | `SimpEntry.thm`, origin `.decl CompanionProbe.«public.lemma»` | `priority 1000`, `post true`, `inv false`, `perm false`, `rfl true` |
| `Lean.Meta.simpExtension` | 2 only | `SimpEntry.thm`, origin `.decl _private.CompanionProbe.0.CompanionProbe.«private.lemma»` | `priority 1000`, `post true`, `inv false`, `perm false`, `rfl true` |

Every simp row is the `thm` constructor with `origin.inv = false`, which is the
one shape `simp` in `module/typed_extensions/decode.rs` decodes (an `inv` row
is refused as "inverse simp theorem direction remains unmeasured");
every instance row is `Entry.global` wrapping an `InstanceEntry` whose
`globalName?` is `some`.

### The private instance row the mutation test corrupts (`actual_companion_malformed_row_keeps_its_slot_and_other_rows`)

Walking the private part's bytes exactly as that test does — `entries` array
at root+40, then the pair whose `extension_name` is
`Lean.Meta.instanceExtension` (the test finds it by name over the unmutated
parse; on this fixture it is index **13**) → rows array (itself in the private
part) of **2** rows:

| Row | Pointer | Lives in | Offset in that part | Object header (rc, cs_sz, other, tag) |
|---|---|---|---|---|
| 0 (`«public.instance»`) | `0x10f221522d68` | base part | 11624 | (0, 16, 1, 0) |
| 1 (`«private.instance»`) | `0x10f221540ca8` | **private part** | **3240** | (0, 16, 1, 0) |

So `row - word(&original[2], 80)` in that test is **3240**, in bounds
(`private row is in private part` holds), and `changed[2][offset + 7]` is the
object's TAG byte — currently `0`, `ScopedEnvExtension.Entry.global` — which
the test sets to 255 so `decode.rs` `scoped()` refuses the row and it becomes
`Unmeasured { index: 1 }` while row 0 stays `Instance` (the test's
`source_rows == Some(2)`, `undecoded_entries == 1`). Row 0 is a BORROWED base
object: `saveModuleDataParts` never duplicates an object already written to an
earlier part (`Lean/Environment.lean:1740-1745`), which is also why the test's
subtraction would underflow on it and why the fixture must put the PRIVATE
instance second.

### Borrowed roots (`actual_companion_bad_extension_array_is_not_silently_omitted`, `borrowed_base_root_preserves_snapshot_without_doubling_registries`, `borrowed_roots_require_captured_objects_not_zero_filled_gaps`)

The server and private parts each carry their own root inside their own
region (table above) and reference base objects (row 0 above is one). Hence:
`borrowed_base_root_preserves_snapshot_without_doubling_registries` can
truncate parts 1 and 2 to 96 bytes and point their root word at the base root
(the base's 20 `entries` are then what its `extension_accounting.len() ==
base.entries.len()` sees);
`borrowed_roots_require_captured_objects_not_zero_filled_gaps` can point a
root at `base_address + base_len + 8`, a gap no part owns, and must be
refused; and the same test can point the private root at the authentic server
root, which resolves with the server region present and must fail without it.
`actual_companion_bad_extension_array_is_not_silently_omitted` corrupts the
`entries` pointer at root+40 of parts 1 and 2 (`1`, `u64::MAX - 7`, and
`base_address + 8`) and requires a parse error each time.

### Constants per part (`actual_all_three_extension_snapshots_match_independent_upstream_rows`, `module.constants.len()` against `parts[i].constants`)

Kinds are Lean's `ConstantInfo` constructor; "value" is `hasValue (allowOpaque
:= true)` — `ConstantInfo.value?` alone answers `none` for every theorem
(`Lean/Declaration.lean:482-487`) and would misreport.

Base and server (13 each, identical rosters; census axiom 4, constructor 2,
definition 3, inductive 2, recursor 2). The module system stores every public
theorem, the `Prop`-typed instance and the un-`@[expose]`d public `def` as
value-less axiom-shaped stubs here (the Sigma precedent recorded in the
module doc of `crates/clean-mathverse/src/lean4/olean/batch/tests_module_system.rs`):

```
axiom        no-value  CompanionProbe.«public.lemma»
axiom        no-value  CompanionProbe.«public.instance»
axiom        no-value  CompanionProbe.PublicExports.«target.dot»
axiom        no-value  CompanionProbe.«public.class».holds
inductive    no-value  CompanionProbe.«public.class»
constructor  no-value  CompanionProbe.«public.class».mk
recursor     no-value  CompanionProbe.«public.class».rec
definition   value     CompanionProbe.«public.class».casesOn
definition   value     CompanionProbe.«public.class».recOn
definition   value     CompanionProbe.«public.class».mk._flat_ctor
inductive    no-value  _private.CompanionProbe.0.CompanionProbe.«private.class»
constructor  no-value  _private.CompanionProbe.0.CompanionProbe.«private.class».mk
recursor     no-value  _private.CompanionProbe.0.CompanionProbe.«private.class».rec
```

Private (19; census constructor 2, definition 7, inductive 2, recursor 2,
theorem 6): the 13 above with the four stubs restored to their real kinds
(`«public.lemma»`, `«public.instance»`, `«public.class».holds` → `theorem`
with value; `PublicExports.«target.dot»` → `definition` with value) plus the
six private-only declarations `_private.CompanionProbe.0.CompanionProbe.
{«private.lemma», «private.instance», «private.class».holds}` (theorems with
value) and `«private.class».{casesOn, recOn, mk._flat_ctor}` (definitions
with value). `extraConstNames` is empty in every part; `constNames.len() ==
constants.len()` in every part.

### Imports (not consumed by these tests; recorded because `word` / `root_offset` read the same header)

Every part lists two `Import` rows, both `Init`: `(importAll false,
isExported true, isMeta false)` and `(importAll false, isExported true,
isMeta true)` — the implicit pair a non-`prelude` header receives
(`Lean/Elab/Import.lean:30-31`: `#[{module := Init}, {module := Init, isMeta
:= true}]`, `isExported` defaulting to `true` in `Lean/Setup.lean`).

## Reproduced vs. unreproducible

Reproduced exactly: recognized rows `[5, 5, 7]` (now derived by
`actual_unknown_companion_rows_keep_positions_and_full_population`); exactly 2
private `Lean.Meta.instanceExtension` rows with the second in the private
region (`actual_companion_malformed_row_keeps_its_slot_and_other_rows`); every
name in `registry()` and
`actual_private_metadata_registers_without_duplicate_public_targets`; priority
1000 for both instances and the alias pair (same test); v2 header with base at
80 and root at 88 (`word` / `root_offset`); `entries` at root+40
(`actual_companion_bad_extension_array_is_not_silently_omitted`,
`actual_companion_malformed_row_keeps_its_slot_and_other_rows`).

Unreproducible whole-module censuses of the lost original, with this
fixture's measured values: `(22, 76, 17)/(24, 90, 17)/(26, 106, 28)` →
`(20, 47, 13)/(22, 59, 13)/(24, 66, 19)`; `26` → `24`; `22` → `20`. **The
conversion is APPLIED**: no test carries any of those literals any more; each
is derived from the parsed parts and the oracle as the *Per-part census*
bullets record, and the values here exist only so a drift on a toolchain bump
is visible.
