# `runtime_probe` — the RuntimeProbe module-system fixture (family F6)

Source of the `RuntimeProbe.olean{,.server,.private}` triple, compiled at test
time by the fail-closed helper
`clean_olean::test_support::compiled_fixture_dir("runtime_probe")` and consumed by

* `crates/clean-olean/tests/runtime_declarations.rs` — 12 tests sharing its
  `fixture()` (the three parts plus `run_oracle(&[base, server, private])`):
  `actual_all_part_rows_match_independent_upstream_identity_kind_and_body_presence`,
  `actual_generated_partial_body_and_safe_quoted_twins_remain_distinct`,
  `actual_recursor_rhs_and_family_names_are_not_dropped_from_dependencies`,
  `exact_nested_family_counts_zero_one_two_do_not_collapse_to_bool`,
  `actual_private_provenance_binds_borrowed_base_and_server_bytes`,
  `malformed_recursor_rule_list_retains_error_and_unchanged_sibling_population`,
  `actual_valid_body_pointer_mutation_changes_owned_content_not_authority`,
  `same_private_bytes_resolve_changed_typed_content_when_borrowed_base_changes`,
  `existing_logical_import_policy_still_refuses_runtime_artifacts_and_unpinned_admission`,
  `null_family_nats_and_recursor_rule_headers_refuse_per_row_not_as_zero`,
  `legacy_flag_only_nested_metadata_is_explicitly_incomplete` and
  `each_actual_declaration_kind_refuses_changed_value_header_shape`;
* `crates/clean-olean/src/expr/bvar_tests.rs` —
  `actual_source_bvar_occurrences_match_all_base_rows` (base part against the
  oracle's `parts[0]`);
* `crates/clean-compiler/src/runtime_lcnf/tests/{mod.rs,part_two.rs}` and
  `crates/clean-compiler/src/runtime_lcnf/emission_tests.rs` — 11 `actual_*`
  tests through `actual_context()` in `tests/mod.rs`, whose `pinned_inputs`
  resolves the same `compiled_fixture_dir("runtime_probe")` plus the pinned
  toolchain's `Init/Prelude.olean`, and `oracle_constant_counts` runs the same
  `run_oracle(..)` over the triple. Until 2026-09-15 these read a
  `CLEAN_RUNTIME_LCNF_FIXTURE` environment variable that nothing in the tree
  set; no environment variable is consulted any more.

Every consumer above was an `#[ignore]` site over a lost original until
2026-09-15 and now runs unconditionally.

The original `.lean` was never committed (see the 2026-09-15 ignore survey); this
file is a reconstruction from the assertions, and every number below was
**measured on the compiled output**, not typed. Where a literal in a consumer
could not be reproduced under the pinned toolchain, § *Literals that did NOT
hold* records the measured value and the test that now DERIVES it — the
consumer moved, not this source.

## Toolchain and recipe

Pinned toolchain (`$HOME/clean/lean-toolchain` = `leanprover/lean4:v4.30.0-rc2`):

```
$ ~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean --version
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

Compile, cwd = this directory (module name `RuntimeProbe` is derived from the
path under `--root`; the `_private.RuntimeProbe.0.…` mangling depends on it):

```
lean --root . -o RuntimeProbe.olean RuntimeProbe.lean
```

`ORDER` lists the single module. Because the source carries a `module` header,
`Lean.writeModule` (`src/lean/Lean/Environment.lean`, `writeModule`) emits the
exported/server/private triple **and** a `RuntimeProbe.ir` beside it. Measured
outputs (sha256, bytes), byte-identical when recompiled from a different
directory (`.../final/` vs `.../final2/deeper/path/`, all four hashes equal):

| file | bytes | sha256 |
|---|---|---|
| `RuntimeProbe.lean` | 1604 | `3ec78d363f784a056d07078bda4a6b5f39d00057fd9aa09be421c3e20efe461a` |
| `RuntimeProbe.olean` | 37168 | `19ef62dd1e915d75848c275a596492d35475084de2ea2b48254c23505e10751f` |
| `RuntimeProbe.olean.server` | 2256 | `b2ea9f8feb4c41d710fa2e40e33f25d30636e0f8cd3ec181f2c2d6ab49fc44d7` |
| `RuntimeProbe.olean.private` | 12344 | `5bf4e57fba37744fc94ccc6a25c39dd6eb15876e1adf0905d2384c1b54d5d780` |
| `RuntimeProbe.ir` | 7528 | `097e031f665abe32eccda09cdde1e125ef13772b7701d4ea35bf4a2a40f27fdc` |

The first candidate compile was timed at 0.18 s wall (`time lean …`, v1 below);
the final source is smaller. Exit status 0, no diagnostics.

Header facts read back with python (`struct.unpack_from("<Q", b, 80/88)`):
every part starts `b'olean\x02'` (version byte 5 == 2, so the consumers' "base
word at 80, root at 88" branch is the one taken); base/root = `0x1d8629990000`
/ `0x1d86299990f8` (base part), `0x1d86299a0000` / `0x1d86299a0898` (server),
`0x1d86299b0000` / `0x1d86299b3000` (private). The private part's exposed
definitions point their `DefinitionVal.value` (word at +16) INTO part 0 — that
is the "borrowed base bytes" the provenance tests rely on — while the four
private-authored bodies (`count._unsafe_rec`, the two safe twins, the matcher)
point into part 2.

## What the source declares and why

```lean
module
prelude
public import Init.Prelude
public inductive Unary | zero | succ (n : Unary)
public partial def RuntimeProbe.count : Unary → Unary   -- by `match`, .zero => .zero | .succ n => .succ (count n)
public def RuntimeProbe.«count._unsafe_rec» : Unary → Unary := fun x => x
public def RuntimeProbe.safe._unsafe_rec : Unary → Unary := fun x => x
public opaque RuntimeProbe.sealed : Nat
public axiom RuntimeProbe.postulate : Nat
```

* `module`: in a module, a declaration is exported only when marked `public`
  (`Lean/Elab/DeclModifiers.lean:69`), and a non-`@[expose]`d body is exported
  as a **value-less `axiomInfo`** carrying the private constant's type
  (`Environment.lean` `mkFallbackConstInfo`, the `.axiom` arm at :1000). That is
  what makes `count._unsafe_rec` an Axiom stub in base/server and a Partial
  definition in private. Theorems and opaques export the same way (measured:
  `Unary.brecOn.eq`, `RuntimeProbe.count`, `RuntimeProbe.sealed` are all
  `axiom` in base/server).
* `prelude` + `public import Init.Prelude`: the compiler tests capture exactly
  `[RuntimeProbe, Init/Prelude.olean]` (`pinned_inputs` / `actual_context` in
  `runtime_lcnf/tests/mod.rs`), so every reference this module makes resolves
  inside that context. It also keeps
  `SizeOf` (Init.SizeOf) and `Eq.propIntro` (Init.Core:1595, the gate of
  `mkInjectiveTheorems`, `Lean/Meta/Injective.lean:188`) out of scope, so the
  inductive generates no `_sizeOf_1`/`_sizeOf_inst`/`*.sizeOf_spec`/`succ.inj`/
  `succ.injEq` — that is how the exported part lands on **24** (see the variant
  table). `Unary.brecOn.eq` is a theorem generated unconditionally with
  `brecOn` (`Lean/Meta/Constructions/BRecOn.lean:287-308`) whenever `PUnit` and
  `Prod` exist, and both live in Init.Prelude, so it cannot be avoided.
* `partial def … : Unary → Unary` needs an inhabitant; `mkInhabitantFor`
  (`Lean/Elab/PreDefinition/MkInhabitant.lean:58`) finds it from the argument
  itself (measured value of `count`:
  `fun a => let inst : Inhabited Unary := ⟨a⟩; default`), so no `Inhabited Unary`
  instance is declared — an auto-named `instInhabitedUnary` would have embedded
  a second `"Unary\0"` string in the base part.
* `RuntimeProbe.count._unsafe_rec` is minted by `addAndCompilePartialRec`
  (`Lean/Elab/PreDefinition/Basic.lean:280-292`) with
  `safety := DefinitionSafety.partial` and `modifiers := default`; measured
  `safety=partial`, body references itself.
* `RuntimeProbe.«count._unsafe_rec»` (single quoted component) and
  `RuntimeProbe.safe._unsafe_rec` (three components) are the SAFE twins whose
  bodies are `fun x => x`; both are `definition safety=safe hasValue=true` in the
  private part and `axiom` stubs in base/server.
* `public opaque RuntimeProbe.sealed : Nat` and `public axiom
  RuntimeProbe.postulate : Nat` bring the exported count from 22 to 24 and give
  the private part a genuine value-less Axiom (`postulate` is the ONLY axiom in
  the private part) beside the `partial`-generated Opaque. **No explicit theorem
  is declared**: the theorem kind is already supplied by `Unary.brecOn.eq`, and
  adding one moves the counts to 25/25/26 (variant v3 below).
* No docstrings, no other identifier contains `Unary`.

## Constant roster (measured with `lean --run Inspect.lean` — script in the appendix)

Exported part `RuntimeProbe.olean` (24 constants, 24 `constNames`, `isModule=true`,
imports `#[Init.Prelude]`) and `RuntimeProbe.olean.server` (identical roster, 24):

| # | name | kind (base/server) |
|---|---|---|
| 0 | `Unary.zero.elim` | definition |
| 1 | `Unary.brecOn.go` | definition |
| 2 | `RuntimeProbe.postulate` | axiom |
| 3 | `Unary.noConfusionType` | definition |
| 4 | `Unary.ctorElim` | definition |
| 5 | `Unary.rec` | recursor (all=[Unary], 2 rules: zero nfields=0, succ nfields=1; numMinors=2, numMotives=1, k=false) |
| 6 | `Unary.ctorElimType` | definition |
| 7 | `Unary.casesOn` | definition |
| 8 | `Unary.recOn` | definition |
| 9 | `Unary.below` | definition |
| 10 | `Unary.ctorIdx` | definition |
| 11 | `RuntimeProbe.count._unsafe_rec` | **axiom stub** (value-less) |
| 12 | `Unary.succ.elim` | definition |
| 13 | `RuntimeProbe.«count._unsafe_rec»` | axiom stub |
| 14 | `Unary.succ.noConfusion` | definition |
| 15 | `Unary` | inductive (all=[Unary], ctors=[zero, succ], numParams=0, numIndices=0, numNested=0, isRec=true, isReflexive=false, isUnsafe=false) |
| 16 | `Unary.brecOn` | definition |
| 17 | `Unary.zero` | constructor (cidx=0, numFields=0) |
| 18 | `Unary.succ` | constructor (cidx=1, numFields=1) |
| 19 | `RuntimeProbe.sealed` | axiom stub |
| 20 | `Unary.noConfusion` | definition |
| 21 | `RuntimeProbe.safe._unsafe_rec` | axiom stub |
| 22 | `Unary.brecOn.eq` | axiom stub |
| 23 | `RuntimeProbe.count` | axiom stub |

Distinct kinds in base and in server: 5 each (`definition, axiom, recursor,
inductive, constructor`).

Private part `RuntimeProbe.olean.private` (25 constants): the same 24 names with
their real kinds — `RuntimeProbe.count` **opaque** (value = the inhabitant
above), `RuntimeProbe.sealed` opaque, `Unary.brecOn.eq` theorem,
`RuntimeProbe.postulate` axiom, `RuntimeProbe.count._unsafe_rec` **definition
safety=partial hasValue=true**, `RuntimeProbe.«count._unsafe_rec»` and
`RuntimeProbe.safe._unsafe_rec` definition safety=safe hasValue=true — plus
exactly one private-only constant, the matcher
`_private.RuntimeProbe.0.RuntimeProbe.count.match_1` (components
`[str:_private, str:RuntimeProbe, num:0, str:RuntimeProbe, str:count, str:match_1]`,
definition, level params `[u_1]`). Distinct kinds in the private part: 7.

Measured bodies (private part, `lean --run Detail.lean`):

```
RuntimeProbe.count._unsafe_rec : Unary → Unary :=
  fun x => _private.RuntimeProbe.0.RuntimeProbe.count.match_1.{1} (fun _ : Unary => Unary) x
             (fun (_ : Unit) => Unary.zero) (fun (n : Unary) => Unary.succ (RuntimeProbe.count._unsafe_rec n))
_private.RuntimeProbe.0.RuntimeProbe.count.match_1.{u_1}
  : (motive : Unary → Sort u_1) → (x : Unary) → (Unit → motive Unary.zero) → ((n : Unary) → motive (Unary.succ n)) → motive x :=
  fun motive x h_1 h_2 => Unary.casesOn.{u_1} (fun x => motive x) x (h_1 Unit.unit) (fun n => h_2 n)
Unary.rec rules: zero ↦ fun motive zero succ => zero ; succ ↦ fun motive zero succ n => succ n (Unary.rec motive zero succ n)
```

## Assertions this fixture satisfies (assertion → measured)

`rd` = `crates/clean-olean/tests/runtime_declarations.rs`; `mod` / `p2` /
`em` = `crates/clean-compiler/src/runtime_lcnf/tests/mod.rs` / `tests/part_two.rs`
/ `emission_tests.rs`; `bv` = `crates/clean-olean/src/expr/bvar_tests.rs`.

| consumer (test function) | assertion | measured |
|---|---|---|
| `rd::actual_all_part_rows_match_independent_upstream_identity_kind_and_body_presence`, `mod::actual_partial_helper_lowers_stored_body_and_keeps_exact_calls` (via `oracle_constant_counts`) | rows per part equal the oracle's `parts[i].constants.len()` — the lost original's literal `[24, 24, 25]` is derived, not typed | **24 / 24 / 25** (Lean `data.constants.size`; raw array size words at root+24 read 24, 24, 25) |
| `rd::malformed_recursor_rule_list_retains_error_and_unchanged_sibling_population`, `rd::actual_valid_body_pointer_mutation_changes_owned_content_not_authority`, `rd::null_family_nats_and_recursor_rule_headers_refuse_per_row_not_as_zero`, `rd::existing_logical_import_policy_still_refuses_runtime_artifacts_and_unpinned_admission`, `bv::actual_source_bvar_occurrences_match_all_base_rows` | private row population unchanged under mutation (against the unmutated extraction / the oracle's `parts[2]`); base constants equal the oracle's `parts[0]` | 25; 24 |
| `rd::actual_generated_partial_body_and_safe_quoted_twins_remain_distinct`, `mod::actual_partial_helper_lowers_stored_body_and_keeps_exact_calls` | `RuntimeProbe.count._unsafe_rec` is `DefinitionSafety::Partial` with a stored body in the private part that references itself | `definition safety=partial hasValue=true`; body applies `RuntimeProbe.count._unsafe_rec n` |
| `rd::actual_generated_partial_body_and_safe_quoted_twins_remain_distinct` | the same name is an `Axiom` with no stored value in base and server | `kind=axiom hasValue=false` in both |
| `rd::actual_generated_partial_body_and_safe_quoted_twins_remain_distinct`, `mod::actual_quoted_twin_and_matcher_are_distinct_source_bodies`, `p2::actual_runtime_ir_quoted_twin_never_borrows_recursive_body`, `em::actual_quoted_identity_emits_its_own_nonrecursive_body` | `RuntimeProbe.«count._unsafe_rec»` and `RuntimeProbe.safe._unsafe_rec` are Safe definitions with stored bodies distinct from the partial one | both `definition safety=safe hasValue=true`, value `fun (x : Unary) => x` |
| `mod::actual_partial_helper_lowers_stored_body_and_keeps_exact_calls`, `mod::actual_quoted_twin_and_matcher_are_distinct_source_bodies`, `p2::actual_partial_runtime_ir_retains_calls_tags_and_unresolved_rows` | matcher `_private.RuntimeProbe.0.RuntimeProbe.count.match_1`, calling `Unary.casesOn`; it is the ONLY private-only row (`private − base == [matcher]`) | present, private-only, body head `Unary.casesOn` |
| `mod::actual_partial_helper_lowers_stored_body_and_keeps_exact_calls` | matcher applied to motive `fun _ : Unary => Unary`, the argument, a `Unit → Unary` zero closure and the succ closure; universe `[succ zero]` | exactly that shape (`match_1.{1}`) |
| `mod::actual_partial_helper_lowers_stored_body_and_keeps_exact_calls` | closure names `Unary`, `Unary.rec`, `Unary.casesOn`, `Unit`, `Unit.unit`, `PUnit`, `PUnit.unit` | the first three are in this module; `Unit`, `Unit.unit` appear in the matcher; `PUnit(.unit)` come from Init.Prelude, which is the only import |
| `p2::actual_partial_runtime_ir_retains_calls_tags_and_unresolved_rows` | ctor tags/fields `Unary.zero=(0,0)`, `Unary.succ=(1,1)` | cidx 0 / numFields 0; cidx 1 / numFields 1 |
| `rd::actual_recursor_rhs_and_family_names_are_not_dropped_from_dependencies` | `Unary.rec` has exactly 2 rules, `all == [Unary]` | 2 rules (zero, succ), all=[Unary] |
| `rd::same_private_bytes_resolve_changed_typed_content_when_borrowed_base_changes` | `b"Unary\0"` occurs EXACTLY once in the base part | 1 occurrence, byte offset 328 (`bytes.count(b"Unary\0")`); 0 in server, 0 in private; no other NUL-terminated string contains `Unary` |
| `rd::kind_label` (panics on any kind outside the oracle vocabulary), `rd::family_oracle` (panics on `UnsupportedQuotientMetadata`) | never a Quot / unknown kind | kinds seen: axiom, definition, theorem, opaque, inductive, constructor, recursor |
| `rd::exact_nested_family_counts_zero_one_two_do_not_collapse_to_bool` (write at `InductiveVal+48`) | numNested word of `Unary` | raw word `0x1` (boxed Nat 0) at +48, so `count*2+1` is the right encoding |
| `rd::malformed_recursor_rule_list_retains_error_and_unchanged_sibling_population`, `rd::null_family_nats_and_recursor_rule_headers_refuse_per_row_not_as_zero` (`RecursorVal+56`) | rules list pointer of `Unary.rec` | list → rule0 ctor `Unary.zero` (nfields word 0x1), rule1 `Unary.succ` (0x3) |
| `rd::null_family_nats_and_recursor_rule_headers_refuse_per_row_not_as_zero` (+16 on `Unary`, +40 on `Unary.succ`/`Unary.rec`) | Nat header words | `Unary`+16 numParams 0x1; `Unary.succ`+40 numFields 0x3; `Unary.rec`+40 numMotives 0x3 |
| `rd::actual_valid_body_pointer_mutation_changes_owned_content_not_authority` (`DefinitionVal+16`) | body pointer of the private definitions | `count._unsafe_rec`, both twins and the matcher point into part 2; every exposed auto-definition points into part 0 |
| `rd::actual_private_provenance_binds_borrowed_base_and_server_bytes` (`reachable_census` over the private `constants`, control over `entries`), `mod::actual_partial_helper_lowers_stored_body_and_keeps_exact_calls` (`borrowed_prefix == [Base, Server]`) | private part borrows base bytes and NO server bytes through `constants` — `(census[0], census[2]) == (617, 150)`, `census[1] == 0`, `via_entries[1] > 0`; the server dependency is then made explicit by redirecting the private root at the authentic server root | 617 base / 150 private / 0 server objects reachable from `constants`, 66 server objects via `entries` (appendix); three regions, three distinct base addresses |
| `bv::actual_source_bvar_occurrences_match_all_base_rows` | `total > 0` BVar occurrences | every `Unary.*` definition body is a lambda over bound variables (e.g. `casesOn`) |

## Literals that did NOT hold under v4.30.0-rc2 — remedy APPLIED

**The lost original's `kinds.len() == 6` across the three parts measures 7,
for every candidate source.** `each_actual_declaration_kind_refuses_changed_value_header_shape`
(`runtime_declarations.rs`) now derives the expected kind set from the
oracle's `kind` fields over all three `parts[*].constants` and asserts Clean's
set equals it; the literal is gone. The union over the parts is
`{axiom, definition, theorem, opaque, inductive, constructor, recursor}`:

* `axiom` is forced by the module system (every non-exposed body is an axiom
  stub in base/server, and
  `actual_generated_partial_body_and_safe_quoted_twins_remain_distinct` asserts
  exactly that for `count._unsafe_rec`);
* `opaque` is forced by `partial def` (`addAndCompilePartial` adds `count` with
  `kind := DefKind.opaque`, `Lean/Elab/PreDefinition/Main.lean:32-35`; measured
  `RuntimeProbe.count kind=opaque` in the private part);
* `theorem` is forced by `Unary.brecOn.eq`, minted unconditionally beside
  `brecOn` (`BRecOn.lean:287-308`) whenever `PUnit` and `Prod` are in scope —
  and they are in Init.Prelude, which the compiler tests require.

So the only way to lose a kind would be to lose `Init.Prelude`, the inductive,
or the `partial def`, each of which another assertion forbids. The literal was
true of the lost original only if it was compiled by a Lean that did not yet
mint `brecOn.eq`; it is not true of any v4.30.0-rc2 output. The remedy the
survey named — derive the expected kind set from the oracle's `kind` fields
instead of the literal 6 — is what
`each_actual_declaration_kind_refuses_changed_value_header_shape` does.

A second consumer shape that could not hold is recorded in the doc comment of
`actual_private_provenance_binds_borrowed_base_and_server_bytes`: the lost
original extracted base + private with NO server and demanded a refusal, which
asks the private CONSTANTS to name a server-owned object — and on this
toolchain they never do: `reachable_census` in that test derives 617 base /
150 private / **0** server objects reachable from the private `constants` on
every run and asserts all three, with a control showing server objects ARE
reachable through `entries` (66 of them, which the runtime extractor does not
read); the appendix Python reproduces the same counts independently. The test
now makes the server dependency explicit instead of assumed: it
redirects the private root word at the authentic server root, which resolves
while the server is captured and must not read as a success without it — the
same move `companion_extension_tests::borrowed_roots_require_captured_objects_not_zero_filled_gaps`
makes for the loader.

Variant table — each compiled with the same command, counts are
`base / server / private`, "kinds" is the union over the three parts:

| variant | change from the committed source | counts | kinds | `Unary\0` in base |
|---|---|---|---|---|
| v1 | full `Init` (no `prelude`), explicit theorem + opaque + axiom | 31 / 31 / 32 (adds `_sizeOf_1`, `_sizeOf_inst`, `zero.sizeOf_spec`, `succ.sizeOf_spec`, `succ.inj`, `succ.injEq`, `identityHolds`) | 7 | 1 |
| **v2 = committed** | `prelude` + `public import Init.Prelude`, opaque + axiom | **24 / 24 / 25** | 7 | 1 |
| v3 | v2 plus `public theorem RuntimeProbe.identityHolds : ∀ (p : Prop), p → p` | 25 / 25 / 26 | 7 | 1 |
| v4 | v3 with `set_option genCtorIdx false in` on the inductive | 20 / 20 / 21 (drops `ctorIdx`, `ctorElim`, `ctorElimType`, `zero.elim`, `succ.elim`) | 7 | 1 |
| v5 | full `Init`, `set_option genSizeOf false in`, no opaque/axiom/theorem | 24 / 24 / 25 (keeps `succ.inj`/`succ.injEq` theorems) | 7 (private part alone: 6, having no axiom) | 1 |

v5 also hits 24/24/25; v2 was chosen because its closure is entirely inside
Init.Prelude and it carries a genuine axiom and a user opaque as the spec asks.

## Appendix — measurement scripts (run with `lean --run <script> <base> <server> <private>`)

`Inspect.lean` (per-part roster, kinds, safety, value presence, family data):

```lean
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def safetyOf : ConstantInfo → String
  | .defnInfo d => match d.safety with
    | .safe => "safe"
    | .unsafe => "unsafe"
    | .partial => "partial"
  | .opaqueInfo o => if o.isUnsafe then "unsafe" else "safe"
  | .axiomInfo a => if a.isUnsafe then "unsafe" else "safe"
  | _ => "-"

def nameComponents : Name → List String
  | .anonymous => []
  | .str p s => nameComponents p ++ [s!"str:{s}"]
  | .num p n => nameComponents p ++ [s!"num:{n}"]

def main (args : List String) : IO Unit := do
  let mut regions : Array CompactedRegion := #[]
  for path in args do
    let (data, region) ← readModuleData path
    regions := regions.push region
    IO.println s!"== {path}: constants={data.constants.size} constNames={data.constNames.size} isModule={data.isModule} imports={data.imports.map (·.module)}"
    let mut kinds : Array String := #[]
    for c in data.constants do
      let k := kindOf c
      unless kinds.contains k do kinds := kinds.push k
      IO.println s!"  {c.name} | {nameComponents c.name} | kind={k} safety={safetyOf c} hasValue={c.hasValue (allowOpaque := true)} levels={c.levelParams}"
      match c with
      | .recInfo r =>
        IO.println s!"    rec all={r.all} rules={r.rules.length} ctors={r.rules.map (·.ctor)} numMinors={r.numMinors} numMotives={r.numMotives} k={r.k}"
      | .inductInfo i =>
        IO.println s!"    ind all={i.all} ctors={i.ctors} numParams={i.numParams} numIndices={i.numIndices} numNested={i.numNested} isRec={i.isRec} isReflexive={i.isReflexive} isUnsafe={i.isUnsafe}"
      | .ctorInfo k =>
        IO.println s!"    ctor induct={k.induct} cidx={k.cidx} numParams={k.numParams} numFields={k.numFields}"
      | _ => pure ()
    IO.println s!"  distinct kinds in this part ({kinds.size}): {kinds}"
```

`Detail.lean` (types, values and recursor rules of the probe constants, read
from the last part given, i.e. the private one):

```lean
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let mut regions : Array CompactedRegion := #[]
  let mut last : Option ModuleData := none
  for path in args do
    let (data, region) ← readModuleData path
    regions := regions.push region
    last := some data
  let some data := last | throw <| IO.userError "no parts"
  for c in data.constants do
    let show_ := c.name.getRoot == `RuntimeProbe || c.name.getRoot == `_private || c.name == `Unary.rec || c.name == `Unary.casesOn
    if show_ then
      IO.println s!"--- {c.name} ({c.levelParams})"
      IO.println s!"  type  = {c.type}"
      match c.value? (allowOpaque := true) with
      | some v => IO.println s!"  value = {v}"
      | none => IO.println s!"  value = <none>"
      match c with
      | .recInfo r =>
        for rule in r.rules do
          IO.println s!"  rule {rule.ctor} nfields={rule.nfields} rhs={rule.rhs}"
      | _ => pure ()
```

Interned-string count (python 3.14, cwd = the directory holding the triple):

```python
import struct
for part in ["RuntimeProbe.olean", "RuntimeProbe.olean.server", "RuntimeProbe.olean.private"]:
    b = open(part, "rb").read()
    print(part, b[:6], "base", hex(struct.unpack_from("<Q", b, 80)[0]),
          "root", hex(struct.unpack_from("<Q", b, 88)[0]),
          "Unary\\0 count", b.count(b"Unary\0"),
          "offsets", [i for i in range(len(b) - 5) if b[i:i + 6] == b"Unary\0"])
```

### Reachability census — which part owns what the private part reaches

The `617 / 150 / 0` figure that
`actual_private_provenance_binds_borrowed_base_and_server_bytes` asserts is
DERIVED inside that test on every run by `reachable_census` / `owner` in
`runtime_declarations.rs` (over the private root's `constants`, with a control
over its `entries` that must reach server objects). The Python below is the
independent instrument that produced the figure on 2026-09-15, before the
in-test derivation existed, and it is kept so the Rust walk can be cross-checked
by a reader without cargo: run it and the two must print the same three counts.
Ownership is by base-address range: an object pointer `p` belongs to
the part whose `[base, base + len)` (base = the word at 80) contains it. A Lean
object header is 8 little-endian bytes `rc:i32 cs_sz:u16 other:u8 tag:u8`; a
constructor object (tag ≤ 244) carries `other` pointer fields at +8, an `Array`
(tag 246) carries `size` at +8 and one pointer per element from +24, and scalar
arrays (248), strings (249) and mpz (250) carry no object pointers. A pointer
with its low bit set is a boxed scalar, not an object. Every object is counted
once, the start object included. `ModuleData`'s pointer fields sit at
`imports` +8, `constNames` +16, `constants` +24, `extraConstNames` +32,
`entries` +40 (`Lean/Environment.lean`, `structure ModuleData`).

```python
# python3.14 reach.py RuntimeProbe.olean RuntimeProbe.olean.server RuntimeProbe.olean.private 2
import struct, sys
from collections import deque

FIELDS = {"imports": 8, "constNames": 16, "constants": 24, "extraConstNames": 32, "entries": 40}

def load(paths):
    parts = []
    for path in paths:
        b = open(path, "rb").read()
        assert b[:5] == b"olean" and b[5] == 2, path
        parts.append((path, b, struct.unpack_from("<Q", b, 80)[0], struct.unpack_from("<Q", b, 88)[0]))
    return parts

def owner(parts, ptr):
    for index, (_, b, base, _) in enumerate(parts):
        if base <= ptr < base + len(b):
            return index
    raise AssertionError(f"uncaptured pointer {ptr:#x}")

def word(parts, ptr):
    _, b, base, _ = parts[owner(parts, ptr)]
    return struct.unpack_from("<Q", b, ptr - base)[0]

def children(parts, ptr):
    _, b, base, _ = parts[owner(parts, ptr)]
    _rc, _cs_sz, other, tag = struct.unpack_from("<iHBB", b, ptr - base)
    if tag <= 244:
        return [word(parts, ptr + 8 + 8 * i) for i in range(other)]
    if tag == 246:
        return [word(parts, ptr + 24 + 8 * i) for i in range(word(parts, ptr + 8))]
    if tag in (247, 248, 249, 250):
        return []
    raise AssertionError(f"unexpected tag {tag} at {ptr:#x}")

def census(parts, start):
    seen, queue = set(), deque([start])
    while queue:
        ptr = queue.popleft()
        if ptr & 1 or ptr in seen:
            continue
        seen.add(ptr)
        queue.extend(children(parts, ptr))
    counts = [0] * len(parts)
    for ptr in seen:
        counts[owner(parts, ptr)] += 1
    return counts

parts = load(sys.argv[1:4])
part = int(sys.argv[4]) if len(sys.argv) > 4 else len(parts) - 1
root = parts[part][3]
names = [p.rsplit("/", 1)[-1] for p, *_ in parts]
print(f"root of part {part} ({names[part]}) = {root:#x}")
for field, offset in FIELDS.items():
    counts = census(parts, word(parts, root + offset))
    print(f"{field:16} " + " / ".join(f"{n}={c}" for n, c in zip(names, counts)))
```

Measured 2026-09-15 on the triple whose digests are tabulated above (the
`.olean` re-minted from the committed source that day reproduced all three
digests before the walk ran):

```
root of part 2 (RuntimeProbe.olean.private) = 0x1d86299b3000
imports          RuntimeProbe.olean=6 / RuntimeProbe.olean.server=0 / RuntimeProbe.olean.private=0
constNames       RuntimeProbe.olean=51 / RuntimeProbe.olean.server=0 / RuntimeProbe.olean.private=7
constants        RuntimeProbe.olean=617 / RuntimeProbe.olean.server=0 / RuntimeProbe.olean.private=150
extraConstNames  RuntimeProbe.olean=25 / RuntimeProbe.olean.server=0 / RuntimeProbe.olean.private=4
entries          RuntimeProbe.olean=446 / RuntimeProbe.olean.server=66 / RuntimeProbe.olean.private=192
```

So from the private root's `constants` field **617** objects are base-owned,
**150** private-owned and **0** server-owned; the **66** server-owned objects
the private part can reach at all are reached only through `entries`. For the
controls, the same walk from part 0's root gives `constants` 628 / 0 / 0 and
`entries` 453 / 0 / 0 (the base is self-contained), and from part 1's root
`constants` 628 / 0 / 0 and `entries` 452 / 67 / 0 (the server adds its own
root, `Lean.declRangeExt` rows and a module-doc slot, nothing the runtime
extractor reads).
