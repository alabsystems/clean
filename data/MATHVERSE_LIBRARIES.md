# Mathverse Library — Historical Formal Mathematics Census

> Historical note: this file records the v0.9.0 census/importer story. The
> current release summary is `mathverse-v1.2.0` in `docs/MATHVERSE_CHANGELOG.md`.
> Treat the 68/69 source-system and 3.25M-declaration figures below as
> historical census/importer metadata, not current kernel-verification evidence.

**Date:** 2026-04-16 (audit refresh 2026-04-20)
**Current Release:** mathverse-v0.9.0 (2026-04-01) — published as GitHub Release assets on `alabsystems/Clean`.
**Total (census):** 30,049,434 declarations counted across 238 census target repos in 229.7 seconds.
**Total (converted pipeline):** 3,254,463 declarations across 107 `.mathverse` shards (`shards_produced: 107`; release manifest `mathverse_summary.json`).
**Importer source systems:** historical 68-system figure; later provenance uses
69 importer enum variants (see `SourceSystem` in `crates/clean-mathverse/src/types.rs`).
**Note:** The headline 30M is a keyword-scan census. See MATHVERSE_KERNEL_COMPATIBILITY.md for what Clean can actually kernel-type-check (measured 156/47,301 on Init, 0.33%).

### Canonical Count Vocabulary (#3623)

Four separate numbers describe the library at different layers. They answer different questions and are emitted by data/MATHVERSE_PROVENANCE.json (`schema_version: 2`) as the fields below.

| Field | Value | What it counts |
|------|-------|----------------|
| `importer_source_systems` | 69 | `SourceSystem` enum variants. Canonical importer count. |
| `provenance_records` | 131 | Distinct repo clones with reproducibility metadata (`.sources` length). |
| `census_target_repos` | 238 | Repositories scanned by the wide census (this file). |
| `shards_produced` | 107 | `.mathverse` shard files in release `mathverse-v0.9.0`. |

`crates/clean-mathverse/data/mathverse_summary.json` carries an older
`systems: 158` value. That field is the v0.9.0 pipeline's sub-package rollup
(Mathlib4 split across several sub-sections). Prefer `source_systems: 69` in
`data/mathverse_summary_v1.0.0.json`, which matches `importer_source_systems`.
The v0.9.0 file now embeds a `systems_definition` note recording this
disposition.

**Landed since v0.9.0 (staging for a future release):**
- Binder_info reconstruction fix: 0% reconstruction failures on Lean 4 Init
- 5 additional structured importers: Isabelle, Dafny, ACL2, Lean 3, Coq .v
  (source files exist under `crates/clean-mathverse/src/`)
- 7 further source importers (name+type, no-stub): Agda, F*, Idris2, PVS, Twelf/LF, Mizar (toolchain-free `.miz` surface), and Matita (the last adding `SourceSystem::Matita`, bringing `importer_source_systems` to 69)
- **F* / Project-Everest importer upgraded to full surface coverage** (`fstar_source.rs`): refinement types `x:t{φ}`, computation/effect result types (`Tot`/`ST`/`Stack`/`Lemma`/…), dependent + implicit binders, `let f (x:t) : ret` binder reconstruction, `type` abbreviations and GADT/nullary constructors, tuples, `'a` type variables, `Type u#n`. Measured 43/44 (97.7%) import on a representative HACL*/F*/Everest fixture (`fstar_coverage_tests.rs`), no stubs; still `Unverified` statement-level confidence. See `docs/MATHVERSE_CHANGELOG.md` (Unreleased). This covers the **F*** and **HACL*** rows in §9 below (127,145 + 644,610 declarations) plus the KaRaMeL/EverParse/Vale/AlgoStar/miTLS/Pulse `.fst` corpus.
- Dependency-closed corpus kernel re-verifier (`verify-kernel --corpus`): replays the whole corpus in one prelude-seeded kernel env and classifies each constant honestly as KernelVerified (genuine value typecheck), AxiomAccepted (NO_VALUE axiom), or AxiomFallback (claimed value failed to typecheck); emits a `kernel-verified.json` manifest the loader consumes to upgrade trust
- Coq `.vo` marshal-decoder fixes (PREFIX_SMALL_STRING opcode + Rocq 9.x `Coq!` magic) so real `coqc`/Rocq output decodes — prerequisite for a future real Coq proof-term importer
- Cross-system knowledge graph with equivalence detection
- Source refresh pipeline for upstream re-import
- 40 integration tests for end-to-end pipeline validation
- Unified `mathverse` CLI binary with search/find/inspect/list/stats/systems/graph/deps/sample/diff/verify/download/export/release/version subcommands

These changes are on `main` but are NOT part of the shipped `mathverse-v0.9.0` assets. The next release will bundle them.

---

## Summary

| Metric | Count |
|--------|-------|
| Census target repos | 238 |
| Theorems/lemmas | 12,080,730 |
| Definitions | 14,169,665 |
| Axioms | 3,799,039 |
| **Total declarations** | **30,049,434** |
| Import time | 229.7s |
| Source files | ~400,000+ |

---

## Complete Library Index

### 1. Metamath Family

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **set.mm** | metamath/set.mm | 1 .mm (48 MB) | 47,224 theorems — ZFC set theory |
| **iset.mm** | metamath/set.mm | 1 .mm (11 MB) | 15,772 theorems — Intuitionistic set theory |
| **nf.mm** | metamath/set.mm | 1 .mm (2.8 MB) | 5,981 theorems — New Foundations |
| **ql.mm** | metamath/set.mm | 1 .mm | 1,178 theorems — Quantum logic |
| **hol.mm** | metamath/set.mm | 1 .mm | 151 theorems — Higher-order logic |

### 2. Lean 4 Ecosystem

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Mathlib4** | leanprover-community/mathlib4 | 9,009 .lean | 164,962 theorems — Main math library |
| **Lean 4 source** | leanprover/lean4 | 96,435 .lean | 561,705 theorems — Compiler + stdlib + deps |
| **Lean 4 Std** | leanprover/std4 | 3,615 .lean | 19,770 theorems — Standard library |
| **Mathlib3** (legacy) | leanprover-community/mathlib | 52,020 .lean | 1,017,000 theorems — Lean 3 math |
| **Aesop** | leanprover-community/aesop | 250 .lean | 215 theorems — Auto tactic |
| **Sphere eversion** | leanprover-community/sphere-eversion | 975 .lean | 13,155 theorems |
| **FLT** | ImperialCollegeLondon/FLT | 174 .lean | 1,059 lemmas — Fermat's Last Theorem |
| **Liquid tensor** | leanprover-community/lean-liquid | 6,180 .lean | 46,725 lemmas — Scholze challenge |
| **PFR** | teorth/pfr | 71 .lean | 863 lemmas — Polynomial Freiman-Ruzsa |
| **FLT-regular** | leanprover-community/flt-regular | 480 .lean | 4,095 theorems |
| **miniF2F** | AI Provider/miniF2F | 45 .lean | 7,335 theorems — AI benchmark |
| **miniF2F-lean4** | yangky11/miniF2F-lean4 | 7,380 .lean | 7,320 theorems — AI benchmark (Lean 4) |
| **Unit fractions** | lean-community/unit-fractions | 150 .lean | 7,950 lemmas |
| **ProofWidgets4** | leanprover-community/ProofWidgets4 | 41 .lean | 181 declarations |
| **ProofNet** | zhangir-azerbayev/ProofNet | 131 .lean | 2,423 theorems — AI benchmark |
| **SciLean** | lecopivo/SciLean | 568 .lean | 2,043 theorems — Scientific computing |
| **Con-NF** | leanprover-community/con-nf | 170 .lean | 2,810 theorems — Consistency of NF |
| **PNT** | AlexKontorovich/PrimeNumberTheoremAnd | 77 .lean | 1,942 theorems — Prime Number Theorem |
| **Perfectoid spaces** | leanprover-community/lean-perfectoid-spaces | 66 .lean | 521 lemmas |
| **PutnamBench** | trishullab/PutnamBench | 674 .lean | 672 theorems — AI competition benchmark |
| **Formal conjectures** | google-deepmind/formal-conjectures | 731 .lean | 2,556 theorems — Open conjectures |
| **LeanEuclid** | loganrjmurphy/LeanEuclid | 234 .lean | 206 theorems — Euclidean geometry |
| **IMOSL Lean4** | mortarsanjaya/IMOSLLean4 | 237 .lean | 2,265 theorems — IMO shortlist |
| **math2001** | hrmacbeth/math2001 | 87 .lean | 204 theorems — Proof course |
| **lean-mlir** | opencompl/lean-mlir | 9,446 .lean | 27,655 theorems — Verified MLIR |
| **ArkLib** | Verified-zkEVM/ArkLib | 179 .lean | 1,377 theorems — Verified ZK proofs |

### 3. Coq/Rocq Ecosystem

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **UniMath** | UniMath/UniMath | 1,616 .v | 14,382 theorems — Univalent mathematics |
| **Coq stdlib** | coq/coq | 2,763 .v | 2,281 theorems — Standard library |
| **MathComp** | math-comp/math-comp | 120 .v | 15,738 theorems — Mathematical Components |
| **MathComp Analysis** | math-comp/analysis | 1,860 .v | 102,735 lemmas — Real analysis |
| **CompCert** | AbsInt/CompCert | 253 .v | 7,666 theorems — Verified C compiler |
| **Iris** | iris/iris | 214 .v | 4,634 lemmas — Separation logic |
| **Coq-HoTT** | HoTT/Coq-HoTT | 618 .v | 1,536 theorems — Homotopy Type Theory |
| **HoTT** (full) | HoTT/HoTT | 9,270 .v | 23,040 theorems |
| **VST** | PrincetonUniversity/VST | 1,424 .v | 26,923 theorems — Verified Software Toolchain |
| **CertiCoq** | CertiCoq/certicoq | 159 .v | 4,138 theorems — Verified Coq compiler |
| **Vellvm** | vellvm/vellvm | 180 .v | 3,682 theorems — Verified LLVM |
| **GeoCoq** | GeoCoq/GeoCoq | 460 .v | 4,644 lemmas — Formalized geometry |
| **Four Color Theorem** | coq-community/fourcolor | 119 .v | 1,396 theorems |
| **CoRN** | coq-community/corn | 5,625 .v | 104,070 theorems — Constructive reals |
| **CoqPrime** | thery/coqprime | 5,805 .v | 161,220 theorems — Prime numbers |
| **Interaction Trees** | DeepSpec/InteractionTrees | 143 .v | 1,315 theorems |
| **Hydra Battles** | coq-community/hydra-battles | 3,075 .v | 59,370 theorems — Ordinal arithmetic |
| **Math Classes** | coq-community/math-classes | 1,950 .v | 11,820 theorems |
| **Topology** | coq-community/topology | 1,170 .v | 13,110 theorems |
| **Ceramist** | verse-lab/ceramist | 23 .v | 392 theorems — Probabilistic verification |
| **RegLang** | coq-community/reglang | 180 .v | 4,815 theorems — Regular languages |
| **Monae** | affeldt-aist/monae | 750 .v | 18,450 lemmas — Monadic effects |
| **LibHyps** | Matafou/LibHyps | 24 .v | 115 lemmas — Hypothesis manipulation |
| **fiat-crypto** | mit-plv/fiat-crypto | 9,795 .v | 75,075 lemmas — Verified crypto primitives |
| **bedrock2** | mit-plv/bedrock2 | 290 .v | 2,154 lemmas — Verified low-level programming |
| **Jasmin** | jasmin-lang/jasmin | 2,700 .v | 58,215 lemmas — Verified assembly |
| **Rupicola** | mit-plv/rupicola | 1,035 .v | 7,800 lemmas — Verified C from Coq |
| **Verdi** | uwplse/verdi | 40 .v | 579 theorems — Verified distributed systems |
| **Verdi Raft** | uwplse/verdi-raft | 209 .v | 2,138 theorems — Verified Raft consensus |
| **MetaCoq** | MetaCoq/metacoq | 596 .v | 8,561 theorems — Coq formalized in Coq |
| **Undecidability** | uds-psl/coq-library-undecidability | 686 .v | 8,378 theorems — Mechanized undecidability |
| **Infotheo** | affeldt-aist/infotheo | 87 .v | 2,992 theorems — Information theory |
| **Odd Order** | math-comp/odd-order | 34 .v | 1,062 theorems — Feit-Thompson |
| **Gaia** | coq-community/gaia | 42 .v | 10,544 theorems — Bourbaki's Elements |
| **Category Theory** | jwiegley/category-theory | 229 .v | 716 theorems — Axiom-free categories |
| **Graph Theory** | coq-community/graph-theory | 44 .v | 2,115 theorems — Formalized graphs |
| **CoqEAL** | CoqEAL/CoqEAL | 52 .v | 1,135 theorems — Effective algebra |
| **Coqtail Math** | coq-community/coqtail-math | 161 .v | 2,435 theorems — Arithmetic to analysis |
| **SSProve** | SSProve/ssprove | 101 .v | 1,295 theorems — Cryptographic proofs |
| **ConCert** | AU-COBRA/ConCert | 189 .v | 1,103 theorems — Verified smart contracts |
| **WasmCert** | WasmCert/WasmCert-Coq | 48 .v | 756 theorems — Verified WebAssembly |
| **CoLoR** | fblanqui/color | 264 .v | 5,997 theorems — Termination of rewriting |
| **ALEA** | coq-community/alea | 10 .v | 1,212 theorems — Probability library |
| **RISC-V** | mit-plv/riscv-coq | 101 .v | 202 lemmas — RISC-V specification |
| **Koika** | mit-plv/koika | 125 .v | 444 theorems — Verified hardware design |
| **Fiat** | mit-plv/fiat | 677 .v | 4,597 theorems — Correct-by-construction |
| **Cerberus** | rems-project/cerberus | 66 .v | 786 theorems — C semantics |

### 4. Isabelle/HOL

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Isabelle AFP** | mirror-afp-2024 | 9,105 .thy | 264,583 theorems — Archive of Formal Proofs (source name-scan) |
| **Isabelle stdlib** | mirror-isabelle | 1,844 .thy | 1,082,850 theorems — Standard library (source name-scan) |
| **Isabelle stdlib (real YXML kernel export)** | Isabelle2025-2 | 5,093 .yxml | **1,082,531** decls (`SourceVerified`) — full stdlib distribution (476,204) + 395 AFP entries (606,327), kernel-checked; 3,883 Mathlib cross-links |
| **seL4** | seL4/l4v | 1,880 .thy | 956,010 lemmas — Verified microkernel |

### 5. HOL Family

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **HOL Light** | jrh13/hol-light | 569 .ml | 2,912 theorems |
| **HOL4** | HOL-Theorem-Prover/HOL | 2,840 .sml | 5,978 theorems |
| **CakeML** | CakeML/cakeml | 14,790 .sml | 8,580 theorems — Verified ML compiler |
| **Flyspeck** | flyspeck/flyspeck | 1,665 .ml | 7,695 defs — Kepler conjecture |
| **OpenTheory** | gilith/opentheory | 234 .art | 15 theorems |
| **HOLMS** | HOLMS-lib/HOLMS | 32 .ml | 114 declarations — Modal systems |

### 6. Mizar

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Mizar MML** | mizar-server v8.1.14 | 2,874 .miz | 74,918 theorems — Mathematical Library |

### 7. Agda

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Agda stdlib** | agda/agda-stdlib | 1,252 .agda | 12,884 type sigs |
| **Cubical Agda** | agda/cubical | 17,580 .agda | 297,105 type sigs — HoTT/Cubical |
| **1lab** | the1lab/1lab | 780 .agda | 11,640 type sigs — Univalent math |
| **agda-unimath** | UniMath/agda-unimath | 2,979 .lagda.md | Univalent mathematics |

### 8. Idris 2

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Idris 2** | idris-lang/Idris2 | 1,926 .idr | 21,413 type sigs |

### 9. F* / Project Everest

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **F*** | FStarLang/FStar | 4,244 .fst | 127,145 declarations |
| **HACL*** | project-everest/hacl-star | 14,865 .fst | 644,610 declarations — Verified crypto |
| **KaRaMeL** | FStarLang/karamel | 3,540 .fst | 32,370 declarations — F*-to-C compiler |
| **EverParse** | project-everest/everparse | 636 .fst | 21,658 declarations — Verified parsers |
| **Vale** | project-everest/vale | 65 .fst | 1,353 declarations — Verified assembly |
| **AlgoStar** | FStarLang/AlgoStar | 443 .fst | 10,817 declarations — CLRS algorithms |

### 10. Program Verification

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Dafny** | dafny-lang/dafny | 2,201 .dfy | 14,161 declarations |
| **Why3** | AdaCore/why3 | 1,546 .mlw | 26,514 declarations |
| **ACL2** | acl2/acl2 | 13,454 .lisp | 293,947 declarations |
| **Stainless** | epfl-lara/stainless | 1,764 .scala | 3,037 contracts — Scala verification |
| **Liquid Haskell** | ucsd-progsys/liquidhaskell | 2,482 .hs | 13,024 specs — Refinement types |
| **VeriFast** | verifast/verifast | 11,580 .c | 333,375 specs — C verification |
| **Stainless Bolts** | epfl-lara/bolts | 204 .scala | 9,173 contracts — Verified examples |

### 11. PVS

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **NASA PVS Library** | nasa/pvslib | 2,248 .pvs | 4,885 declarations — Aviation + real analysis |
| **PVS source** | SRI-CSL/PVS | 214 .pvs | 465 declarations |

### 12. Arend

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Arend Library** | JetBrains/arend-lib | 304 .ard | 6,691 declarations — HoTT math library |

### 13. Metamath Zero

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **mm0** | digama0/mm0 | 80 .mm0/.mm1 | 8,956 declarations — Minimal verified proofs |

### 14. Rust Verification

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Verus** | verus-lang/verus | 834 .rs | 18,975 specs — Static Rust verification |
| **Creusot** | creusot-rs/creusot | 650 .rs | 3,304 specs — Deductive Rust verification |

### 15. Semantic Frameworks

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Sail** | rems-project/sail | 1,355 .sail | 12,725 declarations — ISA definitions (ARM, RISC-V) |
| **KEVM** | runtimeverification/evm-semantics | 274 .k | 1,685 declarations — Verified EVM |
| **KeYmaera X** | LS-Lab/KeYmaeraX-release | 153 .kyx/.key | 379 declarations — Hybrid systems |

### 16. Verified Systems

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **SV-COMP** | sosy-lab/sv-benchmarks | 67,714 .c | 9,048 assertions — Software verification competition |
| **TLA+ Examples** | tlaplus/Examples | 316 .tla | 237 theorems/invariants |
| **Alloy Models** | AlloyTools/models | 116 .als | 1,082 declarations |
| **Quint** | informalsystems/quint | 184 .qnt | 1,621 declarations |

### 17. TPTP (Theorem Prover Benchmarks)

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **TPTP NCL** | TPTPWorld/NonClassicalLogic | 441,420 .p/.ax | 11,278,965 formulas |

### 18. SMT/SAT Benchmarks

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **SMTLIB** | SMT-LIB/benchmark-submission | 12,218 .smt2 | 4,574,195 assertions |
| **CVC5** | cvc5/cvc5 | 4,080 .smt2 | 154,536 assertions |
| **Yices2** | SRI-CSL/yices2 | 1,726 .smt2 | 45,628 assertions |

### 19. Type Theory / Logical Frameworks

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Dedukti** | Deducteam/Dedukti | 6,150 .dk | 573,795 declarations — Logical framework |
| **Lambdapi** | Deducteam/lambdapi | 3,495 .lp | 19,695 declarations — Proof assistant |
| **CubicalTT** | mortberg/cubicaltt | 1,170 .ctt | 95,985 declarations — Cubical Type Theory |
| **Abella** | abella-prover/abella | 1,005 .thm | 13,125 declarations — Proof assistant |
| **Beluga** | Beluga-lang/Beluga | 8,715 .bel | 43,320 declarations — Contextual type theory |
| **Naproche** | naproche/naproche | 285 .ftl | 3,825 declarations — Natural language proofs |
| **cooltt** | RedPRL/cooltt | 32 .cooltt | 399 declarations — Cubical proof assistant |
| **redtt** | RedPRL/redtt | 66 .red | 629 declarations — Cubical proof assistant |
| **Minlog** | minlog-tool/minlog | 136 .scm | 8,697 declarations — Constructive proofs |
| **Arend** | JetBrains/arend | 1 .ard | Prover source (Java) |
| **Metamath Zero** | digama0/mm0 | 80 .mm0/.mm1 | 8,956 declarations |

### 20. Wave 4 — Coq Textbooks & Datasets

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Software Foundations** | DeepSpec/sf | 265 .v | Coq textbook proofs |
| **FRAP** | achlipala/frap | 67 .v | Formal Reasoning textbook |
| **CoqGym** | princeton-vl/CoqGym | 6,678 .v | AI theorem proving dataset |
| **Proverbot9001** | UCSD-PL/proverbot9001 | 1,220 .v | AI proof search |
| **Coq 100 Theorems** | coq-community/coq-100-theorems | 10 .v | 100 theorem challenge |

### 21. Wave 4 — Additional Coq Libraries

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Coq ExtLib** | coq-community/coq-ext-lib | 129 .v | Extended standard library |
| **CoqHammer** | lukaszcz/coqhammer | 28 .v | Automated reasoning |
| **Coq SerAPI** | ejgallego/coq-serapi | 38 .v | Serialization/machine learning |
| **Equations** | mattam82/Coq-Equations | 228 .v | Dependent pattern matching |
| **Relation Algebra** | damien-pous/relation-algebra | 52 .v | Kleene algebra |
| **Coq-of-Rust** | formal-land/coq-of-rust | 1,833 .v | Verified Rust translation |
| **Coq-of-OCaml** | formal-land/coq-of-ocaml | 52 .v | Verified OCaml translation |
| **Paco** | snu-sf/paco | 43 .v | Parameterized coinduction |
| **RefinedC** | iris/refinedc | 114 .v | Verified C with Iris |
| **Iris Examples** | iris/examples | 102 .v | Separation logic examples |
| **Flocq** | flocq/flocq | 43 .v | Floating-point formalization |
| **std++** | iris/stdpp | 86 .v | Coq standard library for Iris |
| **Coquelicot** | coquelicot/coquelicot | 29 .v | Real analysis (Inria GitLab) |

### 22. Wave 4 — Additional Lean 4

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Batteries** | leanprover-community/batteries | 241 .lean | Lean 4 standard extensions |
| **Lean4Checker** | leanprover/lean4checker | 16 .lean | Verified type checker |
| **Lean Auto** | leanprover-community/lean-auto | 98 .lean | Automated tactics |
| **Duper** | leanprover-community/duper | 133 .lean | Superposition prover |
| **Verso** | leanprover/verso | 255 .lean | Documentation tool |
| **Lean4Game** | leanprover-community/lean4game | 34 .lean | Interactive proof games |
| **Lean Verbose** | PatrickMassot/verbose-lean4 | 57 .lean | Natural language proofs |
| **LeanSAT** | leanprover/leansat | .lean | SAT solver |

### 23. Wave 4 — Additional Agda

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **PLFA** | plfa/plfa.github.io | 107 .agda | Programming Language Foundations |
| **HoTT-Agda** | HoTT/HoTT-Agda | 420 .agda | Homotopy Type Theory |
| **Agda Categories** | agda/agda-categories | 518 .agda | Category theory |
| **TypeTopology** | martinescardo/TypeTopology | 926 .lagda | Type topology |
| **Agda Prop** | jonaprieto/agda-prop | 23 .agda | Propositional logic |

### 24. Wave 4 — Rust & Program Verification

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Kani** | model-checking/kani | 1,772 .rs | Model checking for Rust |
| **Prusti** | viperproject/prusti-dev | 1,941 .rs | Deductive Rust verification |
| **Move Prover** | move-language/move | 686 .rs | Smart contract verification |
| **Boogie** | boogie-org/boogie | 754 .bpl | Intermediate verification language |
| **Viper** | viperproject/silver | 149 .scala | Verification infrastructure |
| **LISA** | epfl-lara/lisa | 171 .scala | Proof assistant (Scala) |

### 25. Wave 4 — Type Theory & Logical Frameworks

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Twelf** | standardml/twelf | 1,004 .elf | Logical framework |
| **Cedille** | cedille/cedille | 139 .ced | Dependent intersection types |
| **ATS2/Postiats** | githwxi/ATS-Postiats | 3,048 .sats/.dats | Theorem proving + systems programming |
| **K Framework** | runtimeverification/k | 1,511 .k | Semantics-based verification |

### 26. Wave 5 — Coq Community Libraries

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **QuickChick** | QuickChick/QuickChick | 137 .v | Randomized testing for Coq |
| **SMTCoq** | smtcoq/smtcoq | 160 .v | SAT/SMT proof witnesses in Coq |
| **Coq-Elpi** | LPCIC/coq-elpi | 224 .v | Lambda-Prolog metaprogramming |
| **Hierarchy Builder** | math-comp/hierarchy-builder | 105 .v | MathComp hierarchy declaration |
| **TLC** | chargueraud/tlc | 62 .v | Classical Coq standard library |
| **DBLib** | coq-community/dblib | 10 .v | De Bruijn indices library |
| **Finmap** | math-comp/finmap | 3 .v | Finite maps (MathComp) |
| **Bignums** | coq-community/bignums | 27 .v | Big numbers library |
| **DSSS17** | DeepSpec/dsss17 | 537 .v | DeepSpec Summer School 2017 |
| **Kami** | mit-plv/kami | 110 .v | Verified hardware synthesis |
| **Lemma Overloading** | coq-community/lemma-overloading | 28 .v | Canonical structure patterns |
| **Huffman** | coq-community/huffman | 25 .v | Verified Huffman coding |
| **Buchberger** | coq-community/buchberger | 53 .v | Gröbner bases algorithm |
| **Stalmarck** | coq-community/stalmarck | 41 .v | Tautology checker |
| **QArith** | coq-community/qarith-stern-brocot | 38 .v | Rational arithmetic |
| **ParamCoq** | coq-community/paramcoq | 18 .v | Parametricity plugin |
| **ATBR** | coq-community/atbr | 46 .v | Algebraic theory of binary relations |
| **Chapar** | coq-community/chapar | 29 .v | Verified causal consistency |
| **DPDGraph** | coq-community/coq-dpdgraph | 9 .v | Dependency graph analysis |
| **Zorns Lemma** | coq-community/zorns-lemma | 25 .v | General topology foundations |
| **Almost Full** | coq-community/almost-full | 12 .v | Almost-full relations |
| **Coq Art** | coq-community/coq-art | 193 .v | Coq'Art textbook exercises |
| **Hoare Tutorial** | coq-community/hoare-tut | 5 .v | Hoare logic tutorial |
| **Bertrand** | coq-community/bertrand | 23 .v | Bertrand's postulate |
| **Exact Real Arithmetic** | coq-community/exact-real-arithmetic | 29 .v | Constructive real arithmetic |
| **hs-to-coq** | nomeata/hs-to-coq | 374 .v | Haskell to Coq translation |
| **Coq ZFC** | coq-contribs/zfc | 11 .v | ZFC set theory |
| **Cats in ZFC** | coq-contribs/cats-in-zfc | 22 .v | Category theory in ZFC |

### 27. Wave 5 — More Lean 4

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **CvxLean** | verified-optimization/CvxLean | 121 .lean | Verified convex optimization |
| **lean-smt** | ufmg-smite/lean-smt | 241 .lean | SMT integration for Lean 4 |
| **Import Graph** | leanprover-community/import-graph | 37 .lean | Dependency visualization |
| **Plausible** | leanprover-community/plausible | 24 .lean | Property-based testing |
| **Lean4 Metaprogramming** | leanprover-community/lean4-metaprogramming-book | 23 .lean | Metaprogramming guide |
| **Doc-Gen4** | leanprover/doc-gen4 | 49 .lean | Documentation generator |
| **Lake** | leanprover/lake | 145 .lean | Lean 4 build system |

### 28. Wave 5 — More Agda

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Agda (source)** | agda/agda | 5,104 .agda | Agda prover source code |

### 29. Wave 5 — Rust Verification Extensions

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Aeneas** | AeneasVerif/aeneas | 73 .rs | Rust to pure lambda translation |
| **Hax** | hacspec/hax | 364 .rs | Rust verification extraction |
| **CreuSAT** | sarsko/CreuSAT | 77 .rs | Verified SAT solver in Rust |

### 30. Wave 5 — Other Proof Systems

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Kind** | kindelia/kind | — | Dependent type language |
| **Rzk** | rzk-lang/rzk | 19 .rzk | Simplicial HoTT proof assistant |
| **LaTTe** | LATTe-central/LaTTe | 10 .clj | Type theory in Clojure |
| **Krajono** | Deducteam/Krajono | 1 .dk | Dedukti library (classical) |
| **Dedukti Libraries** | Deducteam/Libraries | 46 .dk | Dedukti proof libraries |

### 31. Wave 5 — F* / Everest Extensions

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **miTLS** | project-everest/mitls-fstar | 277 .fst/.fsti | Verified TLS implementation |
| **Pulse** | FStarLang/pulse | — .fst | F* separation logic |

### 32. Wave 5 — Dafny & TLA+ Extensions

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Dafny Libraries** | dafny-lang/libraries | 109 .dfy | Standard Dafny libraries |
| **Apalache** | informalsystems/apalache | 477 .tla | Symbolic TLA+ model checker |
| **P Language** | p-org/P | 670 .p | State machine verification |

### 33. Wave 6 — Coq Verification & Logic

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Gödel** | coq-community/goedel | 7 .v | Gödel's incompleteness theorems |
| **Sudoku** | coq-community/sudoku | 13 .v | Verified Sudoku solver |
| **Comp Dec Modal** | coq-community/comp-dec-modal | 42 .v | Decidable modal logics |
| **Bits** | coq-community/bits | 13 .v | Bitset library |
| **Dedekind Reals** | coq-community/dedekind-reals | 10 .v | Constructive real numbers |

### 34. Wave 6 — Lean 4 Education & Tools

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Lean4 Samples** | leanprover-community/lean4-samples | 146 .lean | Example programs |
| **LeanDojo** | lean-dojo/LeanDojo | 2 .lean | AI theorem proving framework |

### 35. Wave 6 — TLA+ & Solvers

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **TLAPM** | tlaplus/tlapm | 355 .tla | TLA+ proof manager |
| **TLA+ Source** | tlaplus/tlaplus | 1,027 .tla | TLA+ tools source |
| **Z3 Source** | Z3Prover/z3 | 10 .smt2 | Z3 solver test suite |
| **cvc5 Source** | cvc5/cvc5 | 4,080 .smt2 | cvc5 solver test suite |

### 36. Wave 7 — Coq Compiler & Semantics

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Sisyphus** | verse-lab/sisyphus | — .v | Automated Coq proof repair |
| **Vélus** | INRIA/velus | — .v | Verified Lustre compiler |
| **CdF Mech Sem** | xavierleroy/cdf-mech-sem | — .v | Mechanized semantics course |
| **CdF Program Logics** | xavierleroy/cdf-program-logics | — .v | Program logics course |

### 37. Wave 7 — ISA & Hardware Verification

| Library | Source | Files | Key Metric |
|---------|--------|-------|------------|
| **Sail ISA (ref)** | rems-project/sail | 1,355 .sail | ISA specification language |
| **KEVM (ref)** | runtimeverification/evm-semantics | 274 .k | Ethereum VM semantics |
| **Ethereum Act** | ethereum/act | 264 .act | Smart contract specifications |

---

## Reproduction

```bash
# Download all 238+ libraries and run the import pipeline
./scripts/download_all_libraries.sh [data-dir]

# Or run converter on existing data
cargo run -p clean-mathverse --bin mathverse_convert --release -- all <data-dir>
```

## Systems Not Yet Imported (known gaps)

- Matita (no public GitHub mirror found)
- Event-B/Rodin
- Imandra (commercial, limited open source)
- NuPRL (no public mirrors found)
- CertiKOS (not publicly available)
