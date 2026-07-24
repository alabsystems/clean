# Mathverse Coq Depth: kernel-verified Coq proof terms

Mathverse can re-check **real Coq proof terms** with Clean's own kernel, reporting
each constant as genuinely `KernelVerified` (the proof term type-checks against its
type), `AxiomAccepted` (a well-formed axiom, no proof), or `AxiomFallback` (a claimed
value that did *not* type-check). Coq is the **first non-Lean prover** in mathverse
to carry real, kernel-checked proofs rather than name+type signatures.

This document is the reproducible record of that pipeline.

## Why a separate toolchain

The importer consumes SerAPI's serialized kernel `Constr`. SerAPI (`coq-serapi`) tops
out at Coq `8.20` and does **not** support the system's Rocq `9.1`. So depth import
uses an **isolated opam switch** that never touches the system prover:

```
opam switch create mathverse-serapi ocaml-base-compiler.4.14.2
opam repo add coq-released https://coq.inria.fr/opam/released --switch=mathverse-serapi
opam install coq.8.20.0 coq-serapi --switch=mathverse-serapi
# binaries: ~/.opam/mathverse-serapi/bin/{sertop,sercomp,coqc}
eval $(opam env --switch=mathverse-serapi)
```

## The pipeline

```
sertop  ──serialize──▶  .sexp (CoqConstant / CoqAxiom / CoqInductive)
                            │
              coq::alpha::CoqImporter::import_sexp
              (normalize_if_serapi rewrites SerAPI-native Constr → importer dialect)
                            │
        mathverse_structured_import coq-sexp <sexpdir> <shards>
                            │
        mathverse_shard verify-kernel --corpus <shards> --emit-verified=<json>
                            ▼
        KernelVerified / AxiomAccepted / AxiomFallback / Failed
```

The `--corpus` verifier is dependency-closed and topologically ordered: every
referenced inductive/constant must be imported into the same shard set, and it is
seeded + added in order before each constant is checked. That is what lets a proof
referencing `nat`/`eq` verify — its dependencies are present in the env.

### Extracting Constr from sertop (anti-hang: always pipe + `timeout`, never interactive)

```
printf '(Add () "Theorem refl_n : forall n:nat, n = n. Proof. intro n. reflexivity. Qed.")\n(Exec 6)\n(Query () (TypeOf refl_n))\n(Query () (Definition refl_n))\n' \
  | timeout 60 ~/.opam/mathverse-serapi/bin/sertop --printer=sertop
```

Notes that took experimentation to pin down:
- Add each constant + `(Exec <last-sid>)` as its own step; a multi-constant `Add`
  string returns empty queries.
- `(Query () (Definition X))` returns the **full elaborated proof term even for
  `Qed`-opaque theorems** in this build (you must `Exec` *through* the `Qed` sid).
  `(Query () (TypeOf X))` gives the type.

### The importer's three sexp forms

- `(CoqConstant <name> <type-constr> <value-constr>)` — a definition or a theorem
  whose body is the proof term. `value_idx != NO_VALUE` ⇒ the kernel checks it.
- `(CoqAxiom <name> <type-constr>)` — type only, `NO_VALUE` ⇒ `AxiomAccepted`.
- `(CoqInductive <name> <block> <arity> (NumParams <k>) (Ctor <cname> <ctype>)...)` —
  imported as a `DeclKind::Inductive` constant (with `num_params`) + `DeclKind::Constructor`
  constants, so the corpus verifier's checked `add_inductive` replay fires.

`normalize_if_serapi` rewrites SerAPI's native encoding (binder records, 1-based `Rel`,
sub-listed `App` args, `KerName`/`MutInd`/`Instance`) into the importer dialect, firing
only on unambiguous SerAPI markers so hand-written datasets pass through verbatim.

### Naming reconciliation

`cic_to_flat_expr` lowers `(Ind name i) → name.i` and `(Construct name i j) → name.i.(j-1)`,
so an inductive is imported as `name.<block>` (e.g. `mynat.0`, `eq.0`) and constructor
*k* as `name.<block>.k`. Dependent terms then resolve against the imported family.

### Universe quirk

Coq `Set` / `Type@{0}` (the universe of `nat`) maps to the importer dialect's
`(Sort (Type 1))`, **not** `(Type 0)` — the dialect maps `Type(u)` to kernel level `u`
while `Set` is level 1. Using `(Type 0)` mis-types e.g. `eq`'s parameter as `Prop`.

## What is proven (with negative controls)

| Capability | Result | Commit |
|---|---|---|
| Self-contained terms (`fun A x => x`) | KernelVerified; axiom-import control → AxiomAccepted | `8bac7538` |
| Dependent terms referencing an imported inductive | KernelVerified; remove inductive → `Failed` | `71d2fff2` |
| Opaque `Qed` theorem + parameterized inductive (`eq`) | KernelVerified; axiom-import control → AxiomAccepted | `fb5ebbba` |

Each step asserts the verdict via `verify-kernel --corpus` and a negative control
(dropping the proof term flips `KernelVerified → AxiomAccepted`), so the verdict
reflects a genuine kernel check of the proof against its type — not a rubber stamp.
The honest verdict split itself depends on the precision-fix that distinguishes
`KernelVerified` from axiom fallbacks (see `verify/incremental`).

A latent corpus-merge bug surfaced and was fixed along the way: `load_shard` discarded
inductive metadata (`num_params`, mutual `all_names`) on every merge — see
`remap_inductive_metadata` in `library.rs`.

## Status and next steps

- **Done:** the pipeline handles self-contained terms, dependent terms, inductives
  (incl. parameterized), and opaque `Qed` proof terms — i.e. real Coq theorems.
- **First real count (`ba8e49fb`):** a curated-but-genuine set verified at **50/50
  KernelVerified, 0 axiom-fallback** — **33 `Qed`-proved Coq theorems** (logic
  combinators, connective intros/projections, equality/existential, incl.
  universe-polymorphic) plus 7 inductives + 10 constructors. The negative control
  (an ill-typed proof term) is rejected as `axiom_fallback`.
- **`Case`/match lowering (`8739ddfc`):** Coq `match` has no kernel primitive — every
  match is an application of the matched inductive's auto-generated recursor. A
  `CicCase` payload (inductive, params, motive, discriminant, branches) lowers to that
  recursor application, which the kernel type-checks. A `match`-using proof (`or_comm`
  via `destruct`) KernelVerifies (with the ill-typed-branch negative control).
- **`Fix` lowering (`bc12c192`) — ALL core CIC constructs now complete:** Clean's
  kernel has no native fix/recursor *node* — recursion exists only through the
  recursors `add_inductive` generates (`<ind>.rec`, with iota reduction). A structural
  `Fix` lowers to a recursor application where the recursive self-call is the IH
  argument each minor premise receives. The recursor's motive **universe instance**
  must be supplied (level 1 for a `nat→nat` motive). Result: the recursive definition
  `my_add` KernelVerifies, AND the computational theorem `my_add 2 2 = 4` — which
  requires the kernel to iota-*reduce* the recursion — KernelVerifies (7/7), with
  negative controls (universe corruption rejected; `2+2=5` rejected).
- **Recursor minor-premise soundness question — RESOLVED (2026-07-04).** The
  reported quirk (an ill-typed branch may be accepted inside a recursor
  application) was diagnosed as a **real kernel bug**: `App` arguments were
  inferred with forced `infer_only=true`, so ill-typedness nested *inside* a
  minor premise whose top-level type matched was accepted. Fixed the same day
  in commit `dabf7a35` ("clean-kernel: deep-check nested App args + Let values;
  close False-proof soundness holes", verified an ancestor of HEAD): the
  `tc/infer.rs` App-arg and Let-value paths, the certificate path
  (`tc/cert/infer_core.rs`), and `infer_sort` depth-cap hardening, with 10
  regression tests in
  `crates/clean-kernel/src/tc/tests2/soundness_nested_arg.rs`. Residual
  by-design truth: `TypeChecker::infer_type` with `infer_only=true` (the
  default) still skips App-arg checks (Lean 4 parity), so verdict surfaces
  must go through `add_decl`/`check_type` — which every verdict-minting path
  (including `verify-kernel --corpus`) does.
- **Beyond Coq:** the same shape (toolchain → serialize → import → `verify-kernel
  --corpus`) is the template for adding real depth to other provers.

## 2026-07-04 — corpus scale: the full Coq 8.20 stdlib, one command

The COQ-0…COQ-6 lane of `docs/plans/MATHVERSE_CLEAN_PROOF_IMPORT_PLAN.md` is
built and run end-to-end at full-stdlib scale. This section is the dated,
reproducible record of the first corpus-scale run.

**Acquisition (COQ-0).** `scripts/build_coq_serapi_dumps.sh` drives the new
`mathverse_coq_dump` bin (pipe-only sertop, `Print Module` enumeration with
recursive submodules, `CoqMInd` parsing, per-module `.meta.json` sidecars,
`--validate`) over the pinned `mathverse-serapi` opam switch. Result:
**549/549 stdlib modules dumped, 0 failures** — 19,720 constants (**all**
carrying elaborated proof values, Qed-opaque included), 522 axioms, 209
inductive blocks / 753 constructors (~1.1 GB of importer-form sexps under
`data/corpora/coq-sexp/stdlib/`, gitignored). 7,973 names skipped-with-reason,
~98% of them functor/module-type members that are not global kernel constants
(the module wall), plus universe-polymorphic `@{u}` names (out of model).

**Import + verify + stamp (COQ-1a…COQ-6).**

```
mathverse_shard coq-import --sexp-root=data/corpora/coq-sexp \
    --out=<out-dir> --json=<report.json>
```

One command, 35 seconds for the whole corpus on an M-series laptop:
convert (two-pass cross-file inductive registry; every dropped value counted
with a reason) → soundness floor (any import-time `KernelVerified` outside
inductive family certificates aborts) → merged dependency-closed
`verify_corpus_incremental` in a prelude-seeded env (masked-failure taint
withholds every dependent of a rejected proof) → `kernel-verified.json`
manifest → stamp → stored-count audit → BEDROCK count.

**Results (first corpus-scale Coq kernel verification):**

| metric | value |
|---|---|
| declarations imported | 20,380 (549 files, 0 failed) |
| translated with proof values | 15,003 (74%) |
| **KernelVerified (Clean kernel re-check)** | **3,340** |
| **BEDROCK (empty non-foundational axiom closure)** | **1,925** |
| stored `KernelVerified` after stamp | 3,612 (incl. checked inductive families) |
| axiom-accepted (genuine axioms/valueless) | 2,488 |
| axiom-fallback roots (kernel rejected, masked) | 3,515 |
| taint-withheld dependents (`failed`) | 11,037 |
| **modules 100% KernelVerified** | **16** (e.g. `Coq.ZArith.Int` 30 consts, `Coq.Bool.Sumbool`, `Coq.Logic.ClassicalChoice`; 191 more partial) |

Milestone **M6** (≥ 1 full stdlib module stored KernelVerified; per-library
trust distribution reported) is met.

**Honest loss census** (from the run's `--json` report; nothing is silent):
4,919 values dropped at import — dominant classes: template-polymorphic
inductives (`prod`/`sigT`, whose absence cascades into `fst`/`snd` and all
dependents), nested/non-structural fixpoints (`Acc`/`Fix_F` well-founded
machinery), residual motive-universe underivability, coinductives (by
design), SProp/algebraic universes (by design, trust-gated). Kernel-side
fallback root classes: sealed-signature module members
(`RbaseSymbolsImpl.R`), typeclass records (`Proper`), primitive floats, and
a beta-redex expected-type mismatch on the `internal_*_dec_*` family under
diagnosis. These are the next coverage bricks; each unlocks its taint
cascade multiplicatively.

**Maintenance recipe** (regular reimport): re-run the two commands above;
dumps are idempotent per module (`--force` to refresh); diff
`kernel-verified.json` across runs as the regression gate. Toolchain pin:
opam switch `mathverse-serapi` = ocaml 4.14.2 + coq **8.20.0** + coq-serapi
(SerAPI dead-ends at 8.20; Rocq 9.x full fidelity requires the `.vo`
proof-term reconstructor, still deferred). MathComp on macOS/arm64 is
blocked by `coq-elpi`/`elpi` build failures (three pinned attempts; ocamlopt
fixup-out-of-range and cmxs packaging) — use a Linux runner for MathComp
dumps when that lane opens.

## 2026-07-05 — coverage bricks: 3,340 → 5,948 KernelVerified

The next tranche of importer and dump bricks landed and the full corpus was
re-dumped (`--force`) and re-verified with the same one-command harness. This
section is the dated record; the 2026-07-04 section above is the baseline it
is measured against.

**What changed.**

- *Importer* (`crates/clean-mathverse/src/coq/alpha.rs`): a general
  post-abstracted `Fix` encoding replacing the strict path that froze
  non-structural arguments (this — not index lifting — was the real cause of
  the `internal_*_dec_*` beta-redex expected-type mismatch), and
  template-polymorphism collapse that accepts an n-ary `max` of named universe
  levels as `Type 1` (unblocking the `prod`/`sigT`/`fst`/`snd` cascade).
- *Dump* (`mathverse_coq_dump`): enumerate `Variant`-keyword inductives
  (`Decimal`/`Hexadecimal` `signed_int`/`decimal` were invisible before),
  `Record`/`Class`, and sealed-signature module members + functor bodies.
- *Rocq-9 groundwork* (`crates/clean-mathverse/src/coq/vo/`): an OCaml Marshal
  object-graph decoder + `ObjFile` container + `Constr` decode reads a real
  Qed-opaque proof (`and_comm`) out of compiled `Logic.vo`, structurally
  agreeing with the SerAPI dump — the route past SerAPI's 8.20 dead-end.
- *MathComp lane* (`docker/coq-linux-runner/`, `scripts/coq_linux_sertop.sh`,
  `scripts/build_mathcomp_dumps.sh`): a Debian/arm64 container carrying Coq
  8.20 + SerAPI + MathComp 1.19.0, driven by the unmodified host dump binary
  over a `docker exec -i` pipe shim (round-trip proven). The elpi-free 1.19.0
  lane ships because MathComp 2.x + coq-elpi 2.x fails on the
  `elpi_plugin.cmxs` dune packaging bug on Linux *and* macOS.

**Dump enrichment** (manifest aggregate, vs the 2026-07-04 dump):

| dump metric | 2026-07-04 | 2026-07-05 |
|---|---|---|
| inductive blocks | 209 | 338 |
| constructors | 753 | 932 |
| records | 0 | 129 |
| template-collapsed | — | 40 |
| skipped names | 7,973 | 1,815 |

**Verify + stamp results** (one 50 s corpus run):

| metric | 2026-07-04 | 2026-07-05 | Δ |
|---|---|---|---|
| declarations imported | 20,380 | 20,655 | +275 |
| translated with proof values | 15,003 | 16,772 | +1,769 |
| **KernelVerified** | **3,340** | **5,948** | **+2,608 (+78 %)** |
| **BEDROCK** | **1,925** | **3,618** | **+1,693 (+88 %)** |
| stored KernelVerified after stamp | 3,612 | 6,143 | +2,531 |
| axiom-accepted | 2,488 | 3,066 | +578 |
| axiom-fallback roots | 3,515 | 4,092 | +577 |
| taint-withheld dependents (`failed`) | 11,037 | 7,549 | −3,488 |
| **modules 100 % KernelVerified** | **16** | **52** | **+36** |

(Fully-KV modules counted as `Coq.Dir.File`-prefixed groups with ≥1 KV and 0
non-KV value-bearing declarations.)

**Regression census — the honest cost of a richer dump.** Diffing
`kernel-verified.json` against the 3,340 baseline: 36 constants that were KV
are now trust-withheld (against 2,644 newly gained). All 36 are
dependency-failure cascades, not own-term encoding regressions:

- 35 are taint-withheld — "value typechecks only against a masked-failure
  axiom fallback in its dependency closure." The dominant failing root is the
  `Coq.micromega.OrderedRing.SOR` Sound-Ordered-Ring **typeclass record**
  (×9 dependents: `Rle_refl`/`Rle_trans`/…), then `Coq.QArith.Qcanon`'s `Qc`
  record (×11: `Qc_eq_dec`/`Qred_iff`/…), Setoid `Proper`/`arrows`, and by-
  design `PrimFloat`/`FloatAxioms` primitives. These verified in the baseline
  only because the richer dump had **not yet imported** those dependencies'
  (failing) values; now that it does, the masked-failure taint correctly
  withholds their dependents. More honest, not less.
- 1 is own-value (`Coq.Logic.Berardi.g`): `Unknown constant:
  Coq.Logic.Berardi.j2` — a missing impredicative Section sibling, i.e. still
  a dependency gap, not a mis-encoding of `g` itself.

No soundness regressions (a withheld verdict is conservative by construction).
Net verified constants **+2,608**.

**Next brick (highest lever):** typeclass records — `OrderedRing.SOR`,
`Qcanon.Qc`, Setoid `Proper`/`arrows`. Closing it recovers all 36 regressions
and unlocks the Classes / micromega / Reals lanes multiplicatively.

**Triage aid:** `COQ_IMPORT_FULL_REASONS=1 mathverse_shard coq-import … --json=…`
emits the untruncated per-name fallback (own-value-rejected) and failed
(taint-withheld) verdict lists — the basis for the census above.

### Typeclass-records brick, step 1: the `Set+1` universe arm — 5,948 → 6,755

Tracing the census roots with `COQ_IMPORT_FULL_REASONS` gave a precise cause,
not "typeclass records are hard": the record type `micromega.OrderedRing.SOR`
failed `add_inductive`, and its constructor referenced `Setoids.Setoid.
Setoid_Theory`, which referenced `Relations.Relation_Definitions.relation`,
which was **dropped at conversion**. `relation A := A -> A -> Prop` has sort
`Type@{max(Set+1, u)}`, and the universe classifier required EVERY `max` arm to
carry increment 0 — so the `Set+1` arm (a pierced runtime-`Set` level with
increment 1) tripped the "algebraic universe" rejection and the whole
Relations → Setoid → Classes → Morphisms hierarchy taints behind it.

But `Set + 1 = Type 1` is exactly the template-collapse target: a pierced-`Set`
arm with increment 0 or 1 is `<= Type 1`, so `max(Set+1, named→Type 1) = Type 1`
is sound in the existing model (`classify_serapi_type_universe`, per-datum
increment rule; named levels and `Var` still require increment 0; `Set + n` for
`n >= 2` stays out of model). One classifier change:

| metric | before (5,948) | after | Δ |
|---|---|---|---|
| KernelVerified | 5,948 | **6,755** | **+807 (+13.6 %)** |
| BEDROCK | 3,618 | **3,944** | +326 |
| taint-withheld (`failed`) | 7,549 | 6,117 | −1,432 |

Regression gate: **0 regressions** vs the 5,948 baseline (807 gained, 0 lost);
9 of the 36 Phase-E regressions recovered directly (the whole OrderedRing /
micromega lane). Canonical on-disk baseline now KV **6,755**.

### Step 2: bare-`Sort` universe payloads reach normalization — 6,755 → 6,947

The next roots (`ConstructiveReals` ×313, `Tlist`, ssreflect `predArgType`)
were dropped at conversion with a misleading `expected atom at 1`. Cause:
`is_serapi_native` — the gate that decides whether the SerAPI→importer sort
normalizer runs — recognized binder/kername/`Instance` markers but NOT a bare
universe payload (`(hash …)`/`(data …)` fields). So a term whose only SerAPI
content is a lone `(Sort (Type <payload>))` — a record arity like
`ConstructiveReals : Type@{Set+1}`, or `Definition predArgType := Type` — skipped
normalization, and the raw payload hit `sexp_to_cic`'s sort parser (which
expects the already-collapsed `(Type N)` atom). Adding `hash`/`data` to the
marker set (never used by the hand-written importer dialect) routes those sorts
through the universe classifier as intended.

`ConstructiveReals` now registers (its arity `Set+1` is admitted; its
constructor fields carry no out-of-model shape). KernelVerified **6,755 →
6,947** (+192), BEDROCK 3,944 → 3,987, taint-withheld 6,117 → 5,470, **0
regressions**. `predArgType`/`Tlist` now fail LOUDLY (honest out-of-model)
rather than with the confusing parser error.

### Step 3: increment-aware universe collapse — 6,947 → 7,678

The next roots (ssreflect `predArgType`/`pred_sort`, `RelationClasses.Tlist`)
were all the `Type@{named+1}` shape — `Definition foo := Type` has type
`Type@{u+1}` and value `Type@{u}`, so the collapse must put the type ONE level
above the value. The old classifier hard-mapped every in-model `Type@{…}` to
`Type 1` and rejected any nonzero increment. Replace it with an increment-aware
collapse that returns the level: each `max` arm's level is `base(datum) +
increment` with `base(named Level) = 1` and `base(pierced Set) = 0` (`Set` is
`Type 0`, so `Set+1 = Type 1`, `named+1 = Type 2`); the sort is `max(1,
max_arms(base+incr))`. This SUBSUMES both earlier universe fixes (the `Set+1`
arm and the single-level collapse are the increment-0/1 special cases). Only
bound `(Var _)` levels and non-global datums stay out of model; the kernel
re-checks every collapsed term, so an over/under-shot level fails loudly.

`predArgType`/`pred_sort`/`Tlist` recover. KernelVerified **6,947 → 7,678**
(+731), BEDROCK 3,987 → 4,183, axiom-fallback 4,602 → 2,727 (−1,875 constants
whose values were previously rejected on universe grounds now check), **0
regressions**. Total: **3,340 → 7,678 across the three universe/normalization
bricks (+130 %)**.

**Remaining roots** (post-fix, by taint) — now the harder inductive bricks:
- `Sets.Ensembles`/`Finite_sets` (~70): the inductive ARITY ends in a defined
  type synonym (`Empty_set : Ensemble U`, `Ensemble U := U -> Prop`) — the
  kernel validator wants a syntactic sort, so the arity head needs delta-
  unfolding to reach `Prop`.
- `Init.Wf.Acc`, `Relations.Relation_Operators.clos_*` (~70): NON-UNIFORM
  parameters — a constructor's return type instantiates a "parameter" position
  with a varying value, so those positions are really INDICES; the checked
  `add_inductive` replay correctly rejects them (`… does not match declared
  parameter`). Needs non-uniform-parameter → index demotion at import (the
  well-founded-recursion brick; `Acc` is pinned by
  `test_real_dump_acc_nonuniform_param_family_replay_fails_closed`).
- `FSet/MSet/FMapPositive` module-internal types (the module/functor brick).

Canonical on-disk regression baseline: `data/corpora/coq-mathverse/stdlib/
kernel-verified.json` (KV **7,678**); reproduce with `--out=data/corpora/coq-mathverse`
(library `stdlib` nests one level). Raise the drop-census detail with
`COQ_REASON_LIST_CAP=<N>` (env; default 200) alongside `COQ_IMPORT_FULL_REASONS=1`.

### Step 4: MathComp via the Linux runner + joint verification — 7,678 → 8,212

MathComp's `coq-elpi`/`elpi` toolchain is unbuildable on macOS/arm64 (three
pinned attempts failed: `ocamlopt` fixup-out-of-range on elpi 2.x; `cmxs`
packaging failure on elpi 1.18.2). The runner is therefore a Linux container,
`mathverse-coq-linux:mc1.19.0-coq8.20.0` (Coq 8.20.0 + `coq-mathcomp-ssreflect`
1.19.0 + `coq-serapi` 8.20.0, provenance stamped in
`data/corpora/coq-sexp/mathcomp/container-toolchain.json`). `sertop` runs inside
the container behind `scripts/coq_linux_sertop.sh`, so the SAME dump code path
serves MathComp and the local stdlib.

`scripts/build_mathcomp_dumps.sh --only=mathcomp.ssreflect.` dumped **23
ssreflect modules** — 4,009 constants, 69 inductives (92 ctors), 60 records, 6
template-collapsed, 0 dump failures — exercising module/functor elaboration on
real MathComp (`ssrnat` 540, `seq` 879, `prime` 219, `tuple` 171, `eqtype`,
`order`, `bigop`, `fingraph`, …).

MathComp depends on the Coq stdlib, so it must be verified WITH it. The
per-library `coq-import` pipeline verifies each library in isolation (mathcomp
alone → only 11 KV), but `verify-kernel --corpus <dir>` merges every `.mathverse`
shard in a directory into ONE kernel env. Dropping the stdlib shard
(`coq_stdlib.mathverse`) and the mathcomp shard (`coq_mathcomp.mathverse`) into
one directory and running `verify-kernel --corpus` yields the JOINT result:
**24,852 constants, 8,212 KernelVerified, 4,324 BEDROCK** — MathComp ssreflect
contributes **+534 kernel-verified constants** once it can see its stdlib base.
This is real MathComp math checked by the Clean kernel (no re-elaboration): the
module/functor elaboration path works end to end, dump → convert → joint verify.

Recipe (joint verify): `cp <stdlib>/coq_stdlib.mathverse <mathcomp>/coq_mathcomp.mathverse <joint>/`
then `mathverse_shard verify-kernel --corpus <joint> --json=<out>`.

**Full-lane MathComp (2026-07-05):** `scripts/build_mathcomp_dumps.sh` (no
`--only`) dumps every installed lane — `ssreflect` + `fingroup` + `algebra`
1.19.0. Result: **48 / 52 modules, 11,306 constants** (143 inductives, 125
records). 4 modules fail SerAPI's dump on NOTATION-level replay conflicts
(`algebra.poly`/`polyXY`: `Egramcoq.NotationLevelMismatch` — a notation level
re-declared with different associativity; `fingroup.all_fingroup`/`presentation`:
`Custom entry group_presentation has already a rule…`). These are dump-tool gaps
(the `Print Module` replay re-runs notation commands into a session that already
has them) — a fixable dumper change (reset/scope notations per module), not
importer bugs. Joint verify (stdlib 7,890 + full MathComp): **32,266 constants,
8,527 KernelVerified, 4,489 BEDROCK** — MathComp contributes ~640 kernel-verified
once it sees its stdlib base.

### Step 5: the `.vo` import route — past SerAPI's 8.20 dead-end (Rocq 9.x)

SerAPI ends at Coq 8.20; Rocq 9.x ships compiled `.vo` only. The `.vo`
reconstructor in `crates/clean-mathverse/src/coq/vo/` (marshal parser →
`ConstrDecoder` → `constr_sexp`) is now WIRED as an import route:
`coq::vo::export::export_vo_constants(data, lib_name)` decodes a `.vo` file's
constants (transparent `Def` bodies inline; `OpaqueDef`/Qed bodies through the
`opaques` table) straight to importer-form `(CoqConstant …)` sexp — the exact
shape the SerAPI dump emits — so `CoqImporter::import_sexp` consumes
`.vo`-reconstructed terms UNCHANGED, no live `sertop`. Proven end to end by
`test_real_vo_export_route_imports_end_to_end`: `Init/Logic.vo` yields **162 / 162
constants decoded** from the raw marshal graph (0 decoder gaps), all 162 reach
the importer (62 fully translated, 89 type-only, 11 skipped). Every constant the
decoder cannot yet reconstruct is SKIPPED with its name counted, never silently
dropped.

Scope today: the constant lane. Inductive blocks are not yet rendered — the
`read_library` walk collects constructor types but not the block's arity /
parameter count, so `CoqInductive` emission needs that extraction next; until
then constants referencing an inductive import type-only.

### Step 6: non-uniform-parameter → index demotion (`Acc`) — 7,678 → 7,818

Coq's `Acc` declares `NumParams 3` (`A`, `R`, `x`) but `x` is NON-UNIFORM:
`Acc_intro`'s recursive field is `Π y, R y x → Acc A R y`, so the recursive
occurrence puts `y` (not `x`) at the third parameter position. Lean-shaped
kernels require UNIFORM parameters — a "parameter" a constructor re-instantiates
is really an INDEX — so Clean's strict `add_inductive` rejected it (`Constructor
Coq.Init.Wf.Acc.0.0 return type parameter at index 2 does not match declared
parameter`), tainting the entire well-founded-recursion lane.

`compute_uniform_num_params` (alpha.rs) detects this at import and demotes the
non-uniform suffix to indices. A leading parameter `i` is uniform iff, in every
recursive occurrence `(App (Ind …) a0 a1 …)`, `ai` is that parameter binder's
de Bruijn `Rel` — at an occurrence reached after `depth` binders the `i`-th
parameter is `Rel(depth-1-i)` (0-based dialect). The first non-uniform position
`k` demotes `k..declared` to indices; `Acc` becomes `num_params 2` (the Lean
`Acc`), the replay accepts, and `Acc.0` mints KernelVerified. This ONLY shrinks
`num_params`, and only on a provable uniform-spine violation, so every uniform
inductive (`list`, `eq`, `vec`, …) is untouched; the kernel re-checks the
result, so a wrong count can only become a loud rejection, never a silent accept.

Measured (full corpus, diff vs the 7,678 baseline `kernel_verified_names`): **0
regressions, +140 gained** — `Wellfounded.*` (Lexicographic_Product,
Inverse_Image, Transitive_Closure, Union, …), `Relation_Operators.clos_*`,
`Sets.Relations_2/3` + facts, `ConstructiveEpsilon`, `Program.Wf`,
`funind.Recdef`, `Init.Wf` (Acc itself). **KernelVerified 7,678 → 7,818**,
BEDROCK 4,183 → 4,236. Pinned by
`test_real_dump_acc_nonuniform_param_demotes_and_verifies` (was the fail-closed
pin, now asserts Acc verifies). Remaining well-founded gap: constants that
`match` on `Acc` still fail closed (the dump `Case` carries `ci_npar 3` vs the
demoted registry 2 → loud `ci_npar disagrees`); Case reparameterization on
demoted inductives is the next piece.

**Remaining stdlib roots** after step 6: `Sets.Ensembles`/`Finite_sets` (~70,
inductive arity ends in a defined type synonym — needs arity-head delta-
unfolding); `FSet/MSet/FMapPositive` module-internal types; `Case`-on-`Acc`
reparameterization; primitive floats/`Int63` (fail-closed by design).

### Confirmed own-term root census (post-step-6, 2026-07-05)

Full-corpus triage (`COQ_IMPORT_FULL_REASONS=1 COQ_REASON_LIST_CAP=100000`)
separates the 6,518 stdlib `failed` into **5,914 pure taint** (dependents of a
failed root — they light up when the root does, the way Acc's fix added 140 from
one change) and ~600 OWN-TERM roots. Ranked by the kernel's actual verdict:

| n | root shape | example | nature |
|--:|---|---|---|
| 252 | `Type mismatch: expected Sort(Succ(Zero)), got Sort(Succ(Succ(Zero)))` (expected `Type 1`, got `Type 2`) | `JMeq.*`, `Hurkens.paradox`, `Uint63.cast`, `FunctionalExtensionality.*`, `Morphisms.*` | universe: the finite Sort-tower collapse over-levels a polymorphic `Type` by one; the real fix is universe polymorphism / cumulativity, and re-tuning the collapse risks the load-bearing 7,818 |
| 49 | `inductive-family skeleton … does not end in a sort` **or** ctor universe mismatch | `Sets.Ensembles.{Empty_set,Singleton,Union,…}` (arity ends in `Ensemble U := U→Prop`); `Berardi.retract` (`Sort 1` vs `Sort 0` in a ctor) | arity-synonym delta-unfold (import-side, zero-regression by construction) + a universe case |
| 42 | `Type mismatch: expected Const(Int63 …)` | `Sint63.asr_1`, `Uint63.*` | primitive machine ints — fail-closed by design |
| 18 | `Type mismatch: expected Pi(…)` | `EqdepFacts.eq_dep_eq_sig` | dependent-type/JMeq-shaped mismatch |

### Step 7: arity-synonym delta-unfold (`Ensembles`) — 7,818 → 7,890 (LANDED)

The inductive `Empty_set : ∀(U:Type), Ensemble U` (`Ensemble := fun U ⇒ U→Prop`,
so `Ensemble`'s type is `∀U, Type`) failed the kernel's "type former ends in a
sort" check (`inductive_builder.rs:840`) because `get_return_type` peels only
syntactic `Pi`s and stops at the delta-redex `Ensemble U`. A faithful KERNEL fix
would whnf the codomain everywhere the arity telescope is derived (sort check,
index count, recursor gen) — deep trusted-core surgery. Instead the fix is
IMPORT-side and zero-regression by construction: `SerapiNormCtx` now tracks
type-synonym constant bodies (`type_synonym_body`: a `λ`-telescope over a
`Π`-telescope ending in a sort — `Ensemble = λU. U→Prop`), and
`parse_serapi_inductive` calls `unfold_arity_synonym_codomain`, which
beta-delta-unfolds an arity codomain of shape `(App (Const synonym) args)` into
its `Π`-telescope-ending-in-sort (`∀U, Ensemble U` → `∀U, U→Prop`) before the
`InductiveDecl` is built. New `CicTerm` de-Bruijn helpers `cic_lift` /
`cic_subst_top` / `cic_beta_apply` do the β-reduction (0-based `Rel`), unit-tested
by `test_cic_beta_apply_and_arity_synonym_unfold`.

Only synonym-codomain arities change (every other inductive is byte-identical),
and the kernel re-checks the result, so a bug can only make an Ensembles-shaped
inductive FAIL, never corrupt the 7,818 or mint an unsound accept. Measured
against the 7,818 baseline: **0 regressions, +72 gained** — the whole `Coq.Sets.*`
family: `Cpo` (+22), `Ensembles` (+14), `Constructive_sets`, `Finite_sets`,
`Powerset`/`Powerset_facts`/`Powerset_Classical_facts`, `Infinite_sets`,
`Classical_sets`. **KernelVerified 7,818 → 7,890**, BEDROCK 4,236 → 4,265.
(In-file order — the `Ensemble` definition precedes its inductive users — makes
the synonym visible; a cross-file synonym would need the pre-pass extended.)
