# `instance_parity` — `InstanceParity`, explicit instance/class metadata parity (fixture family F8)

Pinned-Lean source for the six tests in
`crates/clean-olean/src/import/load_register/instance_metadata_tests.rs` —
`raw_constant_and_extension_rosters_remain_complete`,
`explicit_classes_and_instances_match_upstream`,
`ordinary_values_and_plain_structure_are_not_registrations`,
`deferred_finalization_only_retries_explicit_metadata`,
`repeated_import_does_not_invent_registrations` and
`unrelated_preexisting_class_value_is_not_discovered_as_an_instance` — which
were `#[ignore]` sites over a lost original until 2026-09-15 and now run
unconditionally. The tests load a single base `.olean` through
`parse_load_module` + the direct loader and compare Clean's `is_instance` /
`is_class` / instance priorities against two readings of the SAME artifact by
the pinned Lean binary: the raw `ModuleData` (constants and extension rows)
and a live `importModules` environment (`Meta.isInstanceCore`, `isClass`).
Both readings come from the shared dumper `../oracle/DumpOlean.lean` ([O]),
run by the file's `fixture()` through `run_oracle(..)` once per process.

Only `InstanceParity.lean`, `ORDER` and this file are checked in.
`InstanceParity.olean` is a build product, re-minted from the pinned toolchain
by the fail-closed helper [H]
(`clean_olean::test_support::compiled_fixture_dir("instance_parity")`, called
by `fixture()`) or by the recipe below; every number here exists so a re-mint
can be checked against it, never so a test can quote it.

## Contents

| Path | Role |
|---|---|
| `InstanceParity.lean` | The single fixture module (`prelude`, no imports, no `module` header). |
| `ORDER` | Modules in dependency order, one per line: `InstanceParity`. |
| `README.md` | This file. |

## Toolchain stamp

Every number below was produced by this binary and no other:

```
$ $HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean --version
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

That is the toolchain `$HOME/clean/lean-toolchain` pins
(`leanprover/lean4:v4.30.0-rc2`), resolved by `clean_olean::pinned_lean_lib_path()`
(`crates/clean-olean/src/lib.rs`) to `<toolchain>/lib/lean`; the binary is
`<toolchain>/bin/lean` (`clean_olean::pinned_lean_binary()`, wrapped by [H] as
`pinned_lean_bin`).

## Recipe

cwd = a copy of this directory. `--root .` is what makes the main module
`InstanceParity` (`Lean/Shell.lean:526`, `moduleNameOfFileName fileName
opts.rootDir?`) — the same string the test file's `load` helper passes as the
module name (`Some("InstanceParity".into())`). `LEAN_PATH` is set for
uniformity with the other families; this module imports nothing, so nothing is
looked up through it.

```bash
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean
while read -r m; do
  LEAN_PATH="$PWD" "$LEAN" --root . -o "$m.olean" "$m.lean"
done < ORDER
```

Measured 2026-09-15: exit **0**, **0 bytes** of diagnostics, **0.043 s** wall.
A `prelude` source without a `module` header writes only the base file — no
`.olean.server`, `.olean.private` or `.ir`:

```
-rw-r--r--   1917  InstanceParity.lean
-rw-r--r--  16776  InstanceParity.olean
```

**The output is byte-deterministic.** Compiled in two fresh scratch copies of
the committed source (`final1/` and `final2/deeper/path/`), `shasum -a 256`
agreed on both files:

```
7d2341be479a0d57ad8fcbdf43e1df164d16ff905c8ff88f81c69f43d9d98b7e  InstanceParity.lean
0987acf3b04791e890a58060f787ecca145d80cb9f0a934dd9f356ce3dffe95d  InstanceParity.olean
```

The `.lean` digest is of the source as committed. `Lean.declRangeExt` stores
line/column ranges, so ANY edit — a comment line included — changes the
`.olean` and every figure below is stale until re-measured.

## The two oracle invocations the tests need

`DIR` is the compiled fixture directory ([H]'s content-addressed cache dir, or
the recipe's cwd); `ORACLE` is
`crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/oracle/DumpOlean.lean`.
Both were verified 2026-09-15 against the dumper at sha256
`32f09b6cc8ed06a9deceb4de622b1504bee2bb34bdabb7c1f0c0eee7d4d5d712` (the digest
was the same before and after the measurement run); re-verify if that file
changes.

### 1. Raw mode — `run_oracle(&[<DIR>/InstanceParity.olean])` in `fixture()`

```bash
"$LEAN" --run "$ORACLE" "$DIR/InstanceParity.olean" > raw.json
# Rust (fixture()): let olean = compiled_fixture_dir("instance_parity").join("InstanceParity.olean");
#                   let raw = run_oracle(&[olean.to_str().expect("utf-8 fixture path")]);
```

Measured: exit **0**, stderr **0 bytes**, stdout **45,394 bytes**, **0.567 s**
wall. Must return (and does):

* `parts.len() == 1`, `regions_kept == 1`; `parts[0].path == "InstanceParity.olean"`,
  `is_module == false`, `imports == []`.
* `parts[0].constants`: **20** rows, **20 distinct names**, in the same order
  as `const_names` (20); `extra_const_names == []`. Census below.
* `parts[0].entries`: **17** extensions, **83** rows in total. Exactly two
  extensions carry decodable rows: `Lean.classExtension` (index 4, 2 rows:
  `InstanceParity.Actual`, `InstanceParity.Removed`, `out_params []`) and
  `Lean.Meta.instanceExtension` (index 9, 2 rows, both `attr_kind global`,
  `synth_order []`, `scope null`, `global_name_present true`):
  `InstanceParity.«registered.dot»` **priority 731** and `InstanceParity.removed`
  **priority 1000**. Each instance name occurs in **exactly one** row. The other
  15 extensions (79 rows) print `null` rows — present and counted, not decoded.
* Every `NAME` is a list of `str` components; the quoted `«registered.dot»` is
  ONE component `{"kind":"str","value":"registered.dot"}`, matching
  `Name::anon().str("InstanceParity").str("registered.dot")` in
  `assert_priorities` and `repeated_import_does_not_invent_registrations`.

### 2. Env mode — `run_oracle(&["--env", "InstanceParity", "--search-path", <DIR>])` in `fixture()`

```bash
"$LEAN" --run "$ORACLE" --env InstanceParity --search-path "$DIR" > env.json
# Rust (fixture()): run_oracle(&["--env", "InstanceParity", "--search-path", dir.to_str().expect("utf-8 fixture path")])
```

Measured: exit **0**, stderr **0 bytes**, stdout **7,416 bytes**, **0.566 s**
wall (`importModules` of a `prelude` module with no imports loads nothing else).
Must return (and does):

* `module == InstanceParity`; `rows` **20** entries and `classes` **20**
  entries, both over `constNames` in stored order (the dumper's default probe);
  `constant_present == true` for all **40**.
* `is_instance == true` for exactly `InstanceParity.«registered.dot»` and
  `InstanceParity.removed`; `is_class == true` for exactly
  `InstanceParity.Actual` and `InstanceParity.Removed`. So **4 positive
  verdicts** and **36 negative** verdicts (see *Literals that do NOT hold*).

The `--search-path` is load-bearing: without it the same command exits **1**
with `DumpOlean: unknown module prefix 'InstanceParity'` (measured), because
`initSearchPath` seeds only the sysroot `lib/lean`.

Optional narrowed probe, if a consumer prefers to name what it checks — same
verdicts on the eight authored declarations, **16** entries, **4 positive / 12
negative** (measured, exit 0):

```bash
"$LEAN" --run "$ORACLE" --env InstanceParity --search-path "$DIR" \
  --name InstanceParity.Actual --name InstanceParity.Removed \
  --name 'InstanceParity.«registered.dot»' --name InstanceParity.removed \
  --name InstanceParity.plainActual --name InstanceParity.plainRemoved \
  --name InstanceParity.Plain --name InstanceParity.plainValue
```

## What the source declares, and why each shape is the way it is

| Source line | Role | Why this shape |
|---|---|---|
| `prelude` (no imports) | closure-free | Every `type_refs`/`value_refs` name of every constant is one of the module's own 20 names (measured: external refs **NONE**). The direct loader registers it into an empty `Environment` with nothing to resolve, and env mode imports nothing else. Compare `import Init.Prelude` → refs `Eq, Eq.ndrec, Nat`; `import Init` → 8 external refs (table at the end). |
| no `module` header | single part | `writeModule` writes only `InstanceParity.olean`; `parse_load_module` reads the base part and `parts.len() == 1` (`raw_constant_and_extension_rosters_remain_complete`) holds without dropping anything. |
| `class InstanceParity.Actual : Type where` / `class InstanceParity.Removed : Type where` | the two classes | `Type`-valued so the instances stay `definition`s (`Lean/Elab/MutualDef.lean:1225-1227` gives a non-`Prop` instance `implicit_reducible` status; a `Prop`-valued class turns its instances into `theorem`s — measured on the rejected variant). With no `SizeOf` in scope no `_sizeOf_inst` can be generated (`Lean/Meta/SizeOf.lean:497` requires `SizeOf`; `Lean/Elab/MutualInductive.lean:1570-1571` already skips it for classes but NOT for the plain structure below). Type is `Sort 1`, so Clean's `class_param_arity` is `Some(0)`. |
| `instance (priority := 731) InstanceParity.«registered.dot» : Actual := ⟨⟩` | positive, explicit priority | Grammar `Term.attrKind >> "instance" >> optNamedPrio >> optional declId >> declSig >> declVal` (`Lean/Parser/Command.lean:200-202`); `evalPrio` of the literal (`Lean/Elab/Util.lean:42-47`). The quoted `«registered.dot»` is one `Name.str` component. Serialized row: priority **731**. |
| `instance InstanceParity.removed : Removed := ⟨⟩` | positive, default priority | `expandOptNamedPrio` with no `(priority := …)` is `eval_prio default` = `1000` (`Lean/Elab/Util.lean:43-45`, `Init/Notation.lean:135`). Serialized row: priority **1000**. |
| `@[reducible] def InstanceParity.plainActual : Actual := ⟨⟩` / `…plainRemoved : Removed := ⟨⟩` | negatives: ordinary defs whose type is a class | Not `instance`, so no `instanceExtension` row and `Meta.isInstanceCore` is false. `@[reducible]` only silences `warn.classDefReducibility` (`Lean/Elab/MutualDef.lean:1241-1248`, a warning on every class-typed `def` without a reducibility attribute); it adds two `reducibilityCore` rows and registers no instance. Without it the compile still exits 0 but prints two warnings. |
| `structure InstanceParity.Plain : Type where` | negative: a plain structure | Not a `class`, so no `classExtension` row; `isClass` false. |
| `def InstanceParity.plainValue : Plain := ⟨⟩` | negative: a value of a non-class type | Neither an instance nor a class. |

Declaring with fully-qualified names (`class InstanceParity.Actual`) rather than
inside `namespace InstanceParity` produces the identical names; the spelling
mirrors the test file's literals.

## Measured facts

Source of every figure: the two oracle documents above (`raw.json`, `env.json`,
`env8.json`) and a Python `struct` walk of the raw bytes, all over the digest
`0987acf3…` on 2026-09-15.

### Constants — 20, in `ModuleData.constants` order (`raw_constant_and_extension_rosters_remain_complete`)

Kinds: definition **11**, inductive **3**, constructor **3**, recursor **3**.
Stored values: **11** (every definition; no inductive/constructor/recursor
stores one). `constants` order equals `const_names` order.

| # | kind | value | name | levels | type | value refs |
|---|---|---|---|---|---|---|
| 0 | recursor | — | `InstanceParity.Actual.rec` | `[u]` | `{motive : Actual → Sort u} → (mk : motive ⟨⟩) → (t : Actual) → motive t` | — |
| 1 | definition | yes | `InstanceParity.«registered.dot»` | `[]` | `InstanceParity.Actual` | `[Actual.mk]` |
| 2 | definition | yes | `InstanceParity.Removed.mk._flat_ctor` | `[]` | `InstanceParity.Removed` | `[Removed.mk]` |
| 3 | definition | yes | `InstanceParity.Plain.recOn` | `[u]` | `{motive} → (t : Plain) → motive ⟨⟩ → motive t` | `[Plain, Plain.mk, Plain.rec]` |
| 4 | definition | yes | `InstanceParity.removed` | `[]` | `InstanceParity.Removed` | `[Removed.mk]` |
| 5 | definition | yes | `InstanceParity.Actual.mk._flat_ctor` | `[]` | `InstanceParity.Actual` | `[Actual.mk]` |
| 6 | constructor | — | `InstanceParity.Removed.mk` | `[]` | `InstanceParity.Removed` | — |
| 7 | inductive | — | `InstanceParity.Plain` | `[]` | `Sort 1` | — |
| 8 | recursor | — | `InstanceParity.Removed.rec` | `[u]` | as `Actual.rec` over `Removed` | — |
| 9 | recursor | — | `InstanceParity.Plain.rec` | `[u]` | as `Actual.rec` over `Plain` | — |
| 10 | definition | yes | `InstanceParity.plainValue` | `[]` | `InstanceParity.Plain` | `[Plain.mk]` |
| 11 | constructor | — | `InstanceParity.Plain.mk` | `[]` | `InstanceParity.Plain` | — |
| 12 | inductive | — | `InstanceParity.Actual` | `[]` | `Sort 1` | — |
| 13 | definition | yes | `InstanceParity.Actual.recOn` | `[u]` | as `Plain.recOn` over `Actual` | `[Actual, Actual.mk, Actual.rec]` |
| 14 | definition | yes | `InstanceParity.plainRemoved` | `[]` | `InstanceParity.Removed` | `[Removed.mk]` |
| 15 | inductive | — | `InstanceParity.Removed` | `[]` | `Sort 1` | — |
| 16 | definition | yes | `InstanceParity.plainActual` | `[]` | `InstanceParity.Actual` | `[Actual.mk]` |
| 17 | definition | yes | `InstanceParity.Removed.recOn` | `[u]` | as `Plain.recOn` over `Removed` | `[Removed, Removed.mk, Removed.rec]` |
| 18 | constructor | — | `InstanceParity.Actual.mk` | `[]` | `InstanceParity.Actual` | — |
| 19 | definition | yes | `InstanceParity.Plain.mk._flat_ctor` | `[]` | `InstanceParity.Plain` | `[Plain.mk]` |

(`InstanceParity.` is elided inside the type/refs columns.) Under bare
`prelude` Lean generates `rec`, `recOn`, `mk._flat_ctor` per structure and
nothing else: `noConfusionType`/`noConfusion`/`casesOn`/`ctorIdx` need `Eq` in
scope and `_sizeOf_*` needs `SizeOf` (see the variant table). **No name
contains `_cstage1`, `_cstage2`, `_rarg`, `_unsafe_rec`, `_elambda*`,
`_lambda*` or `_spec*`** — the components `is_typed_compiler_ir_name`
(`import/load_register.rs`) skips — so the direct loader has nothing to divert
into `skipped_constants` (`summary.skipped_constants.is_empty()` in
`raw_constant_and_extension_rosters_remain_complete`); `_flat_ctor` is not in
that list.

### Extension roster — 17 entries, 83 rows, in `ModuleData.entries` order (`raw_constant_and_extension_rosters_remain_complete`)

Rows Clean decodes are marked `*`.

```
[ 0]   3  Lean.auxRecExt
[ 1]  11  Lean.declRangeExt
[ 2]   3  Lean.protectedExt
[ 3]   4  _private.Lean.Namespace.0.Lean.namespacesExt
[ 4]   2  Lean.classExtension                                   *  Actual, Removed (out_params [])
[ 5]   7  reducibilityCore
[ 6]  20  _private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt
[ 7]   1  _private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt
[ 8]   3  _private.Lean.Structure.0.Lean.structureExt
[ 9]   2  Lean.Meta.instanceExtension                           *  «registered.dot» @731, removed @1000
[10]   5  Lean.IR.declMapExt
[11]   5  Lean.Compiler.LCNF.baseExt
[12]   5  Lean.Compiler.LCNF.monoExt
[13]   5  Lean.Compiler.LCNF.impureSigExt
[14]   5  Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt
[15]   1  symbolFrequency
[16]   1  sineQueNon
```

Decoded extensions **2** (4 rows); extensions with no decodable row **15**
(79 rows). `Lean.Meta.simpExtension` and `Lean.aliasExtension` are absent:
nothing here is `@[simp]` and nothing is `export`ed. The `reducibilityCore`
count is **7** with the two `@[reducible]` attributes and was **5** without
them (measured on the otherwise identical pre-`@[reducible]` variant).

### Env-mode verdicts (`assert_membership` — `Some(true)` in `explicit_classes_and_instances_match_upstream`, `Some(false)` in `ordinary_values_and_plain_structure_are_not_registrations`, `None` in `deferred_finalization_only_retries_explicit_metadata`, `repeated_import_does_not_invent_registrations` and `unrelated_preexisting_class_value_is_not_discovered_as_an_instance`)

Default probe (20 `constNames`): `rows` 20, `classes` 20, all 40
`constant_present`; `is_instance` true for `«registered.dot»` and `removed`
only; `is_class` true for `Actual` and `Removed` only → **positives 4,
negatives 36, total 40**. Eight-name probe: **positives 4, negatives 12, total
16**. The probe order of the default run equals `const_names` order (measured).

### Raw layout (`parse_load_module` reads these fields)

`16776` bytes; magic `olean`, format byte `[5] = 2`; `base = word(80) =
0x777e86e70000`, `root = word(88) − base = 16720`; root object header
`rc 0, cs_sz 56, other (field count) 5, tag 0`. Pointer fields (Lean arrays:
tag 246, `size` at `+8`, `capacity` at `+16`, data at `+24`):

| field | offset | resolves to | size |
|---|---|---|---|
| `imports` | `root+8` | 96 (the shared empty array) | 0 |
| `constNames` | `root+16` | 1360 | 20 |
| `constants` | `root+24` | 7224 | 20 |
| `extraConstNames` | `root+32` | 96 (same empty array) | 0 |
| `entries` | `root+40` | 16560 | 17 |

`isModule` scalar byte at `root+48` = **0**.

## Assertions this fixture satisfies (measured value beside each)

Helpers shared by the six tests: `fixture()` (compile + both oracle runs),
`load` (direct load under a policy), `expected_verdicts` (positive/total
verdict counts derived from the RAW oracle), `assert_membership` (per-name
`is_instance` / `is_class` parity against the ENV oracle) and
`assert_priorities` (priority parity against the raw
`Lean.Meta.instanceExtension` rows).

* `load` — module name `"InstanceParity"` → the name `--root .` derives for
  `InstanceParity.lean`; env mode's `module` field reads `InstanceParity`.
* `assert_membership` — every oracle row has `constant_present == true` →
  40/40 (default probe); every probed name is a constant Clean loads → all 20
  are ordinary kernel kinds with no compiler-IR component (roster above).
* `assert_membership` with `Some(true)`
  (`explicit_classes_and_instances_match_upstream`) — `is_instance`/`is_class`
  true rows are exactly `«registered.dot»`, `removed` / `Actual`, `Removed` →
  **4** rows.
* `assert_membership` with `Some(false)`
  (`ordinary_values_and_plain_structure_are_not_registrations`) — every other
  verdict is false → **36** rows (default probe).
* `assert_priorities` — `parts[0].entries` contains an entry named
  `Lean.Meta.instanceExtension` → index 9; rows whose `value.name` is
  `InstanceParity.«registered.dot»`: **1**, `priority` **731**; rows for
  `InstanceParity.removed`: **1**, `priority` **1000**; one registered instance
  per class after load → each class has exactly one instance row in the
  artifact, so `get_class_instances` can carry at most one for each name
  (Clean-side; the artifact supplies the bound).
* `raw_constant_and_extension_rosters_remain_complete` — `parts.len() == 1` →
  one part; oracle names are distinct → 20 distinct of 20;
  `module.constants.len() == expected.len()` → 20 (the `constants` array at
  `root+24` has `size 20`); all 20 present, `added_constants ==
  constants.len()`, `skipped_constants` empty → no skippable name (roster), no
  duplicates within the module; `extension_accounting.len() == entries.len()`
  → 17; per entry `source_rows == Some(count)` with the counts in the roster
  and `decoded + undecoded == count`; `extension_undecoded_entries > 0` → 15
  of 17 extensions carry only rows the dumper (and Clean) leave undecoded.
* `deferred_finalization_only_retries_explicit_metadata` — three
  `finalize_global_instance_backfill` rounds change nothing → the artifact's
  only instance rows are the two explicit ones; there is no other row a
  backfill could act on.
* `repeated_import_does_not_invent_registrations` —
  `adopt_instance_priority(«registered.dot», 13) == Some(731)` → serialized
  priority 731; the second load of the same `LoadModule` adds 0 constants →
  same 20 names.
* `unrelated_preexisting_class_value_is_not_discovered_as_an_instance` — the
  seeded `unattributed seed : InstanceParity.Actual :=
  InstanceParity.«registered.dot»` mirrors `plainActual`'s shape (a value of a
  class type that is not in `instanceExtension`); the artifact carries no row
  naming it.

## Literals that did NOT hold, with the measured values — both remedies APPLIED

* **APPLIED.** The lost original's `assert_eq!(expected.len(), 54, …)` is
  gone. This fixture has **20** constants; the 54 was the whole-module census
  of the lost original (very probably an `import Init` file: the same
  declarations under `import Init` measure 38 here, with `noConfusion`,
  `casesOn`, `ctorIdx` and `_sizeOf_*` auxiliaries) and cannot be authored
  back. `raw_constant_and_extension_rosters_remain_complete` now pins
  `module.constants.len() == expected.len()` against the oracle's own
  duplicate-free name set and nothing else.
* **APPLIED.** The lost original's `checked == 9 / 5 / 4` was **unreachable
  by ANY fixture under the [O] env schema**: the dumper emits `rows` and
  `classes` over the SAME probe list (M names → 2M verdicts), so `checked` for
  `None` is always even; 9 is impossible, and `Some(true)`/`Some(false)` sum
  to 2M. (The original's 5/4 split implies its oracle probed different name
  lists for instances and classes — e.g. 5 instance probes and 4 class probes;
  a `_sizeOf_inst` of the plain structure is the likely third instance, since
  `import Init` mints exactly one here, `InstanceParity.Plain._sizeOf_inst`
  @1000, measured on the rejected variant.) `expected_verdicts` now derives
  `(positive, total)` from the raw oracle — every decoded `instance` + `class`
  row is a positive, `rows.len() + classes.len()` is the total — and
  `assert_membership` asserts `checked == total / positive / total − positive`
  for `None` / `Some(true)` / `Some(false)`. This fixture measures **40 / 4 /
  36**; the eight-name probe above would measure **16 / 4 / 12**.

## Variants measured and rejected (all compile, exit 0; 2026-09-15)

| header | class universe | constants | entries / rows | `instanceExtension` rows | external refs | why rejected |
|---|---|---|---|---|---|---|
| `prelude` | `Prop` | 20 (theorem 2, definition 9, …) | 12 / 54 | 2 (731, 1000) | none | the two instances are `theorem`s, not the `definition` shape the seeded constant in `unrelated_preexisting_class_value_is_not_discovered_as_an_instance` mirrors |
| `prelude`, no `@[reducible]` | `Type` | 20 | 17 / 81 | 2 | none | identical artifact shape to the committed one but prints two `warn.classDefReducibility` warnings |
| **`prelude` + `@[reducible]` (committed)** | `Type` | **20** | **17 / 83** | **2** | **none** | — |
| `prelude` + `import Init.Prelude` | `Type` | 35 | 21 / 156 | 2 | `Eq`, `Eq.ndrec`, `Nat` | not closure-free; adds `noConfusion*`, `casesOn`, `ctorIdx`, `toCtorIdx` per structure |
| (default `import Init`) | `Type` | 38 | 24 / 156 | **3** (adds `Plain._sizeOf_inst` @1000) + 1 `simpExtension` row (`Plain.mk.sizeOf_spec`) | `Eq`, `Eq.refl`, `Nat`, `OfNat.ofNat`, `SizeOf`, `SizeOf.mk`, `SizeOf.sizeOf`, `instOfNatNat` | an accidental third instance and a simp lemma; env positives become 5 |

Every row was measured with the same dumper in both modes; the committed
variant is the smallest artifact in which the instances are definitions, the
extension rows are exactly the four the tests name, and nothing outside the
module is referenced.
