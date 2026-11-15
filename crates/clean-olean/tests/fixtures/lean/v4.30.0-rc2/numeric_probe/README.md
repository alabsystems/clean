# `numeric_probe` — numeric `Name` components minted by Lean's own serializer (fixture families F4 / F5)

Lean surface syntax cannot spell a `Name.num` component, so this family has no `.lean` module
source; its `ORDER` file holds two `run …` steps (the test-support helper's `lean --run` form)
rather than module stems. `GenNumericProbe.lean` is a `lean --run` **generator**: it builds an
import-free environment (`importModules #[] {}`), names the main module `NumericProbe`,
kernel-checks one `def <name> : Sort 1 := Sort 0` (i.e. `: Type := Prop`) per name through
`Lean.Environment.addDeclCore` (`doCheck := true`), and writes the result with
`Lean.writeModule` — the serializer that writes every stdlib `.olean`. Output has
`imports = #[]`, so a loader needs no dependency closure.

| Invocation (cwd irrelevant; `import Lean` resolves via the toolchain sysroot) | Output | Names |
|---|---|---|
| `lean --run GenNumericProbe.lean <dir>/NumericProbeSupported.olean` | F4, the six supported names | `NumericProbe.{num 0, num 7, num 2^63, str "0", str "7", str "07"}` |
| `lean --run GenNumericProbe.lean <dir>/NumericProbeSeven.olean --over-u64` | F5, the six plus one | … plus `NumericProbe.num 2^64` |

Exit status: 0 on success; **2** on a usage error (measured: `lean --run GenNumericProbe.lean`
with no argument prints the usage line to stderr and exits 2); 1 if the kernel rejects a
declaration (not exercised — every declaration is accepted).

Only `GenNumericProbe.lean`, `ORDER` and this file are checked in; the two `.olean` outputs are
build products re-minted by the fail-closed test-support helper
(`clean_olean::test_support::compiled_fixture_dir("numeric_probe")`, which executes the two
`run` lines of `ORDER` with the copied family directory as cwd). Five tests in three files
consume them — `real_pinned_lean_supported_numeric_names_are_exact` and
`real_pinned_lean_over_u64_name_is_explicit_refusal` (`crates/clean-olean/tests/typed_import_identity.rs`,
via `fixture_file`), `real_numeric_and_numeric_string_twins_survive_cached_loading` and
`original_over_u64_name_is_refused_by_both_cached_paths` (`typed_cached_identity.rs`, via
`actual_fixture`), and `actual_seven_name_oracle_preserves_population_and_refusal`
(`crates/clean-olean/src/region/parsed_name_tests.rs`) — every one an `#[ignore]` site over a
lost original until 2026-09-15.

## Toolchain stamp

- `lean-toolchain` at the repo root: `leanprover/lean4:v4.30.0-rc2`
- `lean --version` (measured 2026-09-15):
  `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`

## Recipe (`ORDER` spells exactly these two command lines as `run` steps)

```bash
LEAN="elan run leanprover/lean4:v4.30.0-rc2 lean"
$LEAN --run GenNumericProbe.lean "$OUT/NumericProbeSupported.olean"
$LEAN --run GenNumericProbe.lean "$OUT/NumericProbeSeven.olean" --over-u64
```

Measured 2026-09-15 with `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`: both
runs exit 0; the first took **0.48 s** wall (`/usr/bin/time -p`). Note for anyone editing the
generator: a `/-! … -/` module doc must come AFTER `import Lean` — placed before it, Lean rejects
the file with `invalid 'import' command, it must be used in the beginning of the file` (measured).

## Measured (2026-09-15, `lean --run` of a `Lean.readModuleData` inspector, plus a raw byte walk)

Both outputs: `isModule = false`, `imports = 0`, `extraConstNames = 0`, `entries = 4`, format
byte `[5] = 2`. Every constant is a `definition` with `type = Sort 1` (prints `Type`) and
`value = Sort 0` (prints `Prop`), `levels = []`, no referenced constants.

`NumericProbeSupported.olean` — 2888 bytes, `constNames = constants = 6`, in the order Lean
serialized them (`SMap.foldStage2` order, i.e. hash order — not declaration order):

| # | `Name` structure |
|---|---|
| 0 | `Name.num (Name.str anon "NumericProbe") 0` |
| 1 | `Name.num (Name.str anon "NumericProbe") 9223372036854775808` (= 2^63) |
| 2 | `Name.str (Name.str anon "NumericProbe") "7"` |
| 3 | `Name.str (Name.str anon "NumericProbe") "07"` |
| 4 | `Name.num (Name.str anon "NumericProbe") 7` |
| 5 | `Name.str (Name.str anon "NumericProbe") "0"` |

`NumericProbeSeven.olean` — 3128 bytes, `constNames = constants = 7`: the same six in the same
order followed by `Name.num (Name.str anon "NumericProbe") 18446744073709551616` (= 2^64).

Big-number layout in the compacted region (Python `struct` scan for objects with tag byte 250 =
`LeanMPZ`; `base = word(80)`):

- 2^63 (both files): mpz object at file offset **232**, header `00000000 2000 00 fa`,
  `_mp_alloc = 1`, `_mp_size = 1` (word `0x0000000100000001`), limb pointer → `base+0x100`,
  **one limb** `0x8000000000000000` at offset 256. It is an mpz and not a boxed scalar because
  Lean's boxed scalars carry 63 bits.
- 2^64 (`Seven` only): mpz object at offset **544**, header `00000000 2800 00 fa`,
  `_mp_alloc = 2`, `_mp_size = 2` (word `0x0000000200000002`), **two limbs** `[0x0, 0x1]` at
  offsets 568–583. A reader that carries the value in a `u64` must refuse this object rather
  than read one limb.

`Name.num` takes a `Nat`, so `2 ^ 63` and `2 ^ 64` in the generator are exact; the hash Lean
stores beside the component uses `17` for any value `≥ 2^64` (`Name.mkNum`), which is why the
over-u64 name still has a well-formed header.

### Determinism

Two generator runs into fresh directories were byte-identical (`shasum -a 256`):

- `NumericProbeSupported.olean` `b1f7e07af8d385a8f8c1fd1558ce80dc15193a177a404c0fba9043ba91b39119`
- `NumericProbeSeven.olean` `fa9e1139c5ee631cec13bb96e024fbeedbcde444b906027190366636a366f76b`

## Assertions this fixture satisfies (measured number beside each)

F4 (`NumericProbeSupported.olean`):

- `real_pinned_lean_supported_numeric_names_are_exact` (`typed_import_identity.rs`) —
  `added_constants == 6`, `env.constants().count() == 6` → measured 6; the six names
  `NumericProbe.{num 0, num 7, num (1<<63), str "0", str "7", str "07"}` each present with
  `type_ == Expr::type_()` and `value == Some(Expr::prop())` → measured exactly those six `Name`
  structures, each `Sort 1 := Sort 0`. The 6 is the generator's declared name list
  (`GenNumericProbe.lean`, `probeNames`), not a whole-module census of a lost original.
- `real_numeric_and_numeric_string_twins_survive_cached_loading` (`typed_cached_identity.rs`) —
  the population of constants whose parent is `NumericProbe` is 6 → measured 6 (and nothing else
  is in the file: `imports = 0`); same six names, same type/value → measured as above.

F5 (`NumericProbeSeven.olean`):

- `real_pinned_lean_over_u64_name_is_explicit_refusal` (`typed_import_identity.rs`) and
  `original_over_u64_name_is_refused_by_both_cached_paths` (`typed_cached_identity.rs`) — the
  loader refuses the module with an error containing `"Nat"` and registers 0 constants. What this
  fixture contributes, measured: exactly one two-limb mpz (`_mp_size = 2`) under a `Name.num`
  component; the refusal itself is a Clean-loader property that was NOT run in the fixture
  authoring phase (no cargo) — it is the consuming test's verdict, not the fixture's.
- `actual_seven_name_oracle_preserves_population_and_refusal` (`parsed_name_tests.rs`) —
  `constNames` array at `root+16` with `count == 7` and an oracle listing 7 names → measured
  `constNames = 7`; exactly one component whose `num` value fails `as_u64()` → measured: the
  single component `18446744073709551616 > u64::MAX`; the other six numeric/string components fit
  (`0`, `7`, `9223372036854775808`); `(supported, refused) == (6, 1)` → measured 6 in-range names
  + 1 over-u64 name.

The oracle JSON for `actual_seven_name_oracle_preserves_population_and_refusal` is produced by
the shared dumper `../oracle/DumpOlean.lean` (see its README), run by that test through
`clean_olean::test_support::run_oracle(&[<DIR>/NumericProbeSeven.olean])`; the `const_names` it
emits for this file are the seven `Name` structures tabulated above, with the 2^64 component
printed as the bare integer `18446744073709551616` so `serde_json` parses it as a non-`u64`
number.
