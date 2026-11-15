# DumpOlean — the independent upstream oracle (Lean v4.30.0-rc2)

`DumpOlean.lean` is a `lean --run` program executed by the **pinned** Lean
binary (`leanprover/lean4:v4.30.0-rc2`, the workspace `lean-toolchain`). It
reads `.olean` artifacts with Lean's own `readModuleDataParts` and prints one
JSON document, so the real-fixture tests in `clean-olean` compare Clean's
reading of an artifact against Lean's reading of the same bytes — never against
a number somebody typed.

The Rust side is `clean_olean::test_support` (implemented in the private module
`crates/clean-olean/src/test_support/pinned_lean.rs`): `compiled_fixture_dir`
compiles a sibling fixture family with the pinned binary (once per content
hash, cached under the cargo target dir) and `run_oracle` runs this script and
parses its stdout. Both **fail closed** — a missing toolchain is a test failure
(`explicit pinned Lean fixture is required`), never a skip.

## Invocation

```text
lean --run DumpOlean.lean <part.olean> [<part.olean.server> <part.olean.private>] ...
lean --run DumpOlean.lean --env <Module> [--search-path <dir>]... [--name <Name>]...
```

* **Raw mode.** Every argument is a part path. Consecutive `X.olean`,
  `X.olean.server`, `X.olean.private` arguments are the parts of one module and
  are read by ONE `readModuleDataParts` call in that order (the only order the
  parts of a module may be read in — `Lean/Environment.lean`, `findOLeanParts`).
  Any other argument starts a new module. No `CompactedRegion` is ever freed;
  `regions_kept` at the top level counts them.
* **Env mode.** `importModules #[{module := <Module>}] {} (loadExts := true)`
  after `initSearchPath <sysroot> [<dir>...]` (sysroot = the running binary's
  `bin/..`, never `PATH`) and `enableInitializersExecution`. Without `--name`
  the probed names are the module's own `constNames`, read from the `.olean`
  `findOLean` locates. `--name` accepts `A.B.«c.d».7` (`«»` protects dots; an
  unquoted all-digit component is `Name.num`).

Exit status is 0 on success; on failure the message goes to stderr as
`DumpOlean: <error>` and the status is 1. Output goes to stdout via
`Json.pretty` — keys within an object print in Lean's `RBNode` order
(descending), which no consumer depends on.

## Schema

Nat values are bare integer literals of arbitrary size (`Lean.JsonNumber` is
exact). A `Name.num` component above `u64::MAX` therefore reaches `serde_json`
(no `arbitrary_precision`) as an `f64`, and `as_u64()` is `None` — the
over-u64 refusal predicate
`actual_seven_name_oracle_preserves_population_and_refusal`
(`src/region/parsed_name_tests.rs`) relies on.

```text
NAME  = [ {"kind":"str","value":<string>} | {"kind":"num","value":<nat>} ]   -- root first, [] = anonymous
LEVEL = {"tag":"zero"} | {"tag":"succ","inner":LEVEL} | {"tag":"param","name":NAME}
      | {"tag":"max"|"imax","left":LEVEL,"right":LEVEL} | {"tag":"mvar-unmeasured","name":NAME}
EXPR  = {"tag":"bvar","index":<nat>}
      | {"tag":"sort","level":LEVEL}
      | {"tag":"const","name":NAME,"levels":[LEVEL]}
      | {"tag":"app","fun":EXPR,"arg":EXPR}
      | {"tag":"lam"|"pi","binder":0..3,"binder_name":NAME,"type":EXPR,"body":EXPR}   -- 0 default, 1 implicit, 2 strict implicit, 3 inst implicit
      | {"tag":"let","name":NAME,"type":EXPR,"value":EXPR,"body":EXPR,"nondep":<bool>}
      | {"tag":"proj","name":NAME,"index":<nat>,"value":EXPR}
      | {"tag":"nat","value":<nat>} | {"tag":"str","value":<string>}
      | {"tag":"mdata-unmeasured","value":EXPR}
      | {"tag":"fvar-unmeasured"|"mvar-unmeasured","name":NAME}                        -- never in a stored constant
```

Raw mode:

```text
{ "regions_kept": <nat>,
  "parts": [ PART ... ] }                       -- one PART per argument, in argument order

PART = { "path": <string>, "is_module": <bool>,
         "imports": [ {"module":NAME,"import_all":<bool>,"is_exported":<bool>,"is_meta":<bool>} ],
         "constants": [ CONSTANT ],             -- ModuleData.constants, in stored order
         "entries": [ ENTRY ],                  -- ModuleData.entries, in stored order
         "const_names": [ NAME ],               -- ModuleData.constNames
         "extra_const_names": [ NAME ] }        -- ModuleData.extraConstNames

CONSTANT = { "name": NAME,
             "kind": "axiom"|"definition"|"theorem"|"opaque"|"quotient"|"inductive"|"constructor"|"recursor",
             "levels": [ NAME ],
             "type_core": EXPR,
             "value_core": EXPR | null,         -- null iff no value is STORED (axiom, quotient, inductive, constructor, recursor)
             "value": {"hash": <nat>} | null,   -- non-null iff a value is stored (Expr.hash of it); theorems and opaques DO store one
             "family": FAMILY,
             "type_refs": [ NAME ],             -- every const/proj name in type_core, first occurrence order, deduplicated
             "value_refs": [ NAME ] | null }    -- same over value_core; null iff value_core is null

FAMILY (by kind):
  axiom       {"is_unsafe"}
  definition  {"all":[NAME],"safety":"safe"|"unsafe"|"partial","hints":{"kind":"opaque"|"abbrev"} | {"kind":"regular","height"}}
  theorem     {"all":[NAME]}
  opaque      {"all":[NAME],"is_unsafe"}
  quotient    {"quot_kind":"type"|"ctor"|"lift"|"ind"}
  inductive   {"all","constructors","num_params","num_indices","num_nested","is_recursive","is_unsafe","is_reflexive"}
  constructor {"inductive":NAME,"index","num_params","num_fields","is_unsafe"}
  recursor    {"all","num_params","num_indices","num_motives","num_minors","k","is_unsafe",
               "rules":[{"constructor":NAME,"num_fields","rhs":EXPR}]}
  -- `all` is emitted for every kind that carries Lean's `all` list, because Clean's
  -- `mutual_declarations` is compared against it for definitions/theorems/opaques too.

ENTRY = { "name": NAME,                         -- the extension's registered name
          "count": <nat>,                       -- rows Lean wrote for this part
          "rows": [ {"value": ROW | null} ] }   -- null = present and counted, not decoded

ROW (four extensions are decoded, identified by the name Lean registered at run time, not by a literal):
  Lean.Meta.instanceExtension  {"kind":"instance","name":NAME,"global_name_present","priority","attr_kind","synth_order":[nat],"scope":NAME|null}
  Lean.classExtension          {"kind":"class","name":NAME,"out_params":[nat]}
  Lean.Meta.simpExtension      {"kind":"theorem","name":NAME,"priority","post","perm","rfl","origin":{...},"scope"}
                               | {"kind":"to_unfold","name":NAME,"scope"} | {"kind":"to_unfold_theorems","name":NAME,"theorems":[NAME],"scope"}
  Lean.aliasExtension          {"kind":"alias","alias":NAME,"target":NAME}
```

Env mode:

```text
{ "module": NAME,
  "rows":    [ {"name":NAME,"is_instance":<bool>,"constant_present":<bool>} ],   -- Meta.isInstanceCore env n / env.contains n
  "classes": [ {"name":NAME,"is_class":<bool>,"constant_present":<bool>} ] }     -- isClass env n
```

Consumers of each field, every one calling `run_oracle(..)` from
`clean_olean::test_support` with the pinned binary over a family
`compiled_fixture_dir` has just compiled:

* `tests/runtime_declarations.rs` (`fixture()`, raw mode over the
  `runtime_probe` triple) — `constants` with `kind`, `levels`, `type_core`,
  `value_core`, `value`, `family`, `type_refs`, `value_refs`
  (`actual_all_part_rows_match_independent_upstream_identity_kind_and_body_presence`,
  `each_actual_declaration_kind_refuses_changed_value_header_shape`,
  `existing_logical_import_policy_still_refuses_runtime_artifacts_and_unpinned_admission`);
* `crates/clean-compiler/src/runtime_lcnf/tests/mod.rs`
  (`oracle_constant_counts`, same triple) — `parts[i].constants.len()`;
* `src/expr/bvar_tests.rs`
  (`actual_source_bvar_occurrences_match_all_base_rows`, same triple) —
  `parts[0].constants[*].type_core` / `value_core` bvar occurrences;
* `src/region/parsed_name_tests.rs`
  (`actual_seven_name_oracle_preserves_population_and_refusal`, raw mode over
  `numeric_probe/NumericProbeSeven.olean`) — `const_names`;
* `src/import/load_parse/companion_extension_tests.rs` (`fixture()`, raw mode
  over the `companion_probe` triple) — `entries` with `name`, `count` and the
  decoded `rows` (`oracle_known`), plus `constants.len()`;
* `src/import/load_register/instance_metadata_tests.rs` (`fixture()`, raw AND
  env mode over `instance_parity`) — raw `constants` + `entries`
  (`raw_constant_and_extension_rosters_remain_complete`, `assert_priorities`,
  `expected_verdicts`) and env-mode `rows` / `classes` (`assert_membership`).

## Validation — measured 2026-09-15

`L=~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`
(`$L --version` = `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit
3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`). The probe modules are
the `selftest/` family beside this file; compile them from that directory with
`LEAN_PATH=$PWD` and `$L --root . -o <Mod>.olean <Mod>.lean` in `ORDER` order
(what `compiled_fixture_dir("oracle/selftest")` does).

```sh
# raw mode, plain (non-`module`) file importing two prelude twins
$ time $L --run DumpOlean.lean Probe.olean > probe.json      # 0.65 s wall, exit 0
$ python3 -m json.tool probe.json > /dev/null && echo JSON_OK  # JSON_OK; `wc -lc` = 9262 lines, 316859 bytes
#   parts=1, is_module=false, constants=49 (= const_names), entries=31,
#   kinds: definition 33, theorem 7, constructor 3, recursor 2, inductive 2, axiom 1, opaque 1
#   decoded rows: Lean.aliasExtension 1 (alias target.dot -> Probe.Exports.target.dot),
#     Lean.classExtension 1 (Probe.Cls), Lean.Meta.instanceExtension 2
#     (Unary._sizeOf_inst @1000, Probe.instCls @731), Lean.Meta.simpExtension 4 theorems
#   imports: Init (is_meta=false), Init (is_meta=true), Sib, Sub.part — all import_all=false, is_exported=true

# raw mode, module-system triple
$ $L --run DumpOlean.lean ModProbe.olean ModProbe.olean.server ModProbe.olean.private   # 0.58 s, exit 0
#   regions_kept=3; constants 1 / 1 / 3: `public def ModProbe.visible` is an AXIOM stub in the
#   base and server parts and a definition with a stored value only in .private, beside
#   _private.ModProbe.0.ModProbe.hidden and _private.ModProbe.0.ModProbe.internal; entries 10 / 11 / 13

# env mode
$ $L --run DumpOlean.lean --env Probe --search-path $PWD    # 0.92 s, exit 0
#   rows=49, classes=49; is_instance: Unary._sizeOf_inst, Probe.instCls; is_class: Probe.Cls;
#   every probed constant present
$ $L --run DumpOlean.lean --env Probe --search-path $PWD --name Probe.instCls --name NoSuch.thing
#   Probe.instCls is_instance=true constant_present=true; NoSuch.thing false/false

# the toolchain's own Prelude
$ time $L --run DumpOlean.lean ~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean/Init/Prelude.olean > prelude.json
#   2.0 s wall, exit 0; 27,932,175 bytes; python3 -m json.tool parses it in 2.5 s
#   constants=2213 (= const_names), entries=49, is_module=true, imports=[]
#   kinds: definition 1537, axiom 259, constructor 157, recursor 129, inductive 127, quotient 4
#   EXPR tags seen: app bvar const lam let mdata-unmeasured nat pi proj sort str; LEVEL: zero succ max imax param
```

First 40 lines of `probe.json` (pretty-printed by `Json.pretty`, keys in
descending order):

```json
{"regions_kept": 1,
 "parts":
 [{"path": "Probe.olean",
   "is_module": false,
   "imports":
   [{"module": [{"value": "Init", "kind": "str"}],
     "is_meta": false,
     "is_exported": true,
     "import_all": false},
    {"module": [{"value": "Init", "kind": "str"}],
     "is_meta": true,
     "is_exported": true,
     "import_all": false},
    {"module": [{"value": "Sib", "kind": "str"}],
     "is_meta": false,
     "is_exported": true,
     "import_all": false},
    {"module":
     [{"value": "Sub", "kind": "str"}, {"value": "part", "kind": "str"}],
     "is_meta": false,
     "is_exported": true,
     "import_all": false}],
   "extra_const_names":
   [[{"value": "Probe", "kind": "str"},
     {"value": "strLit", "kind": "str"},
     {"value": "_closed_0", "kind": "str"}],
    [{"value": "Probe", "kind": "str"},
     {"value": "letProbe", "kind": "str"},
     {"value": "_boxed", "kind": "str"}],
    [{"value": "Probe", "kind": "str"},
     {"value": "count", "kind": "str"},
     {"value": "_boxed", "kind": "str"}],
    [{"value": "Unary", "kind": "str"},
     {"value": "succ", "kind": "str"},
     {"value": "elim", "kind": "str"},
     {"value": "_redArg", "kind": "str"}],
    [{"value": "Unary", "kind": "str"},
     {"value": "zero", "kind": "str"},
     {"value": "elim", "kind": "str"},
     {"value": "_redArg", "kind": "str"}],
```

Two facts from that run worth carrying into fixture authoring: a plain
(non-`module`) file records `import Init` twice — once with `is_meta=false`
and once with `is_meta=true` — so a fixture whose import rows must be exactly
its explicit imports needs a `prelude` header; and a `module`-header source
compiled with `lean -o X.olean` writes `X.olean.server`, `X.olean.private`
and an `X.ir` beside it, while a plain source writes only the base `.olean`.

## Regression

`clean_olean::test_support::pinned_lean::pinned_lean_tests::test_selftest_family_compiles_and_the_oracle_reads_it_in_both_modes`
(`crates/clean-olean/src/test_support/pinned_lean_tests.rs`)
compiles `selftest/` through `compiled_fixture_dir` and reads it back through
`run_oracle` in raw (single part and triple) and env modes, asserting only
relations the oracle itself establishes (constants = const_names, an inductive
carrying `num_nested`, three parts and three regions for the triple, at least
one instance and one class in env mode). Run it with the crate's unit tests:

```sh
TARGO="$(trustc --print sysroot)/bin/targo"
"$TARGO" --unverified test --locked -p clean-olean --lib test_support::pinned_lean
```

# IRCensusOracle — the compiled-IR census, as the pinned toolchain sees it

`IRCensusOracle.lean` is a second, independent oracle: an ordinary `lean <file>` run (not
`--run`) whose `#eval` prints, per module of an import closure, the `Lean.IR.declMapExt`
declaration counts (`getModuleEntries` and `getModuleIREntries`) and the entry counts of
`externAttr`, `implementedByAttr`, `regularInitAttr` (both levels) and `builtinInitAttr` — the
same row format `clean olean ir-census` prints (`crates/clean-olean/src/lean_ir/census.rs`). It
was extended from the audit probe `~/.cache/clean-lane/audit/metaprogramming/probes/IRCensus.lean`
(per-package sums) to one row per module.

It must stay a standalone Lean program: consumers insert the closure's roots as `import` lines
directly after `import Lean`, and the census covers the transitive closure of
`IR_CENSUS_ROOTS`, never of the file itself. Optional outputs: `IR_CENSUS_PRINT` (declaration
names) and `IR_CENSUS_PRINT_MODULES` (module names, or `*`) print declarations with Lean's own
`IR.Decl` formatter; `IR_CENSUS_ATTRS=1` prints every attribute entry, every extern
declaration's `ExternAttrData` and every `sorryDep?`. The header comment of the file is the
schema.

Consumers: `lean_ir::tests::test_run_census_fixture_closure_equals_pinned_lean_oracle` (the
`../ir_census/` family, diffed byte for byte) and `scripts/ir_census_diff.py run` (any closure,
e.g. the Mathlib one, diffed through the production `clean` binary).

# IRFlagsOracle — IR data the formatter never prints

`IRFlagsOracle.lean` counts, over the closure of `IR_FLAGS_ROOTS`, what Lean's `IR.Decl`
formatter drops and the census's byte-exact declaration diff therefore cannot check: the `c` and
`persistent` flags and counts of `inc`/`dec`, borrowed `fdecl` parameters, `ctor` expressions
whose argument count differs from `CtorInfo.size`, and the distinct `case` type ids. It prints
one `FLAGS k=v …` line in the keys of `clean olean ir-census --profile`. Consumer:
`lean_ir::adversarial_tests::test_run_census_profile_unrendered_fields_equal_pinned_lean` (the
`../ir_census/` family). Measured 2026-09-26 with the release binary: over `Init`'s closure (590
modules) and over the `Mathlib.Tactic.Common` + `Mathlib.Algebra.Group.Defs` closure (2,580
modules) the pinned toolchain and `clean olean ir-census --closure … --profile` agree on every
key. Run it like the census oracle: insert the roots as `import` lines after `import Lean`, set
`LEAN_PATH` and `IR_FLAGS_ROOTS`, and run `lean` on the file.
