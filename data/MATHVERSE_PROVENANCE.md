# Mathverse Library — Source Provenance Index

**Generated:** 2026-03-30 (audit refresh 2026-04-20)
**Release:** mathverse-v0.9.0 (2026-04-01) — published as GitHub Release assets on `alabsystems/Clean`

## Canonical Count Vocabulary (#3623)

Four distinct numbers describe the Mathverse Library. They answer different questions and
MUST NOT be confused. All four are emitted by data/MATHVERSE_PROVENANCE.json
(`schema_version: 2`) under the named fields below.

| JSON field | Value | Definition | Authority |
|-----------|-------|------------|-----------|
| `importer_source_systems` | 69 | `SourceSystem` enum variants. Canonical importer count. | crates/clean-mathverse/src/types.rs |
| `provenance_records` | 131 | Distinct repo clones with reproducibility metadata (`.sources` length). Canonical provenance record count. | data/MATHVERSE_PROVENANCE.json |
| `census_target_repos` | 238 | Census target repos scanned by the wide census. Canonical census target count. | data/MATHVERSE_LIBRARIES.md |
| `shards_produced` | 107 | `.mathverse` shard files in release `mathverse-v0.9.0`. Canonical shard count. | GitHub Release assets |

**Declarations counts (two):**

| JSON field | Value | Definition |
|-----------|-------|------------|
| `total_declarations_census` | 30,049,434 | Keyword-scan census over 238 census target repos (see `MATHVERSE_LIBRARIES.md`) |
| `total_declarations_in_records` | Σ of `.sources[].declarations` | Sum over provenance records with a populated `declarations` field (currently partial — see `populated_records` audit) |

The older unqualified `total_systems` / `total_declarations` fields remain as back-compat aliases for `census_target_repos` / `total_declarations_census` respectively. New consumers MUST prefer the canonical field names.

The legacy crates/clean-mathverse/data/mathverse_summary.json `systems: 158` field reflects the
v0.9.0 pipeline's per-sub-package rollup (e.g., Mathlib4 split across several sub-sections).
It is superseded by data/mathverse_summary_v1.0.0.json `source_systems: 69`, which matches
`importer_source_systems` above. See data/MATHVERSE_LIBRARIES.md for the definition.

**Total Declarations (Converted Pipeline):** 3,254,463 (data/mathverse_summary_v1.0.0.json / release `mathverse_summary.json`)

## Provenance Records

Each record includes the source URL, git commit hash at time of download, download date, and file counts for reproducibility. All repositories were cloned with `--depth 1` (shallow clone). Commit hashes represent the HEAD at clone time.

### 1. Metamath Family

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| set.mm | https://github.com/metamath/set.mm | `5a55b96b559b` | 2026-03-30 | 9 | .mm | 47,224 |
| iset.mm | https://github.com/metamath/set.mm | `5a55b96b559b` | 2026-03-30 | (same repo) | .mm | 15,772 |
| nf.mm | https://github.com/metamath/set.mm | `5a55b96b559b` | 2026-03-30 | (same repo) | .mm | 5,981 |
| ql.mm | https://github.com/metamath/set.mm | `5a55b96b559b` | 2026-03-30 | (same repo) | .mm | 1,178 |
| hol.mm | https://github.com/metamath/set.mm | `5a55b96b559b` | 2026-03-30 | (same repo) | .mm | 151 |

### 2. Lean 4 Ecosystem

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Mathlib4 | https://github.com/leanprover-community/mathlib4 | `b301d257a1c1` | 2026-03-30 | 9,009 | .lean | 164,962 |
| Lean 4 source | https://github.com/leanprover/lean4 | `f395593ffce1` | 2026-03-30 | 6,426 | .lean | 561,705 |
| Lean 4 Std | https://github.com/leanprover/std4 | `36752f7c96ae` | 2026-03-31 | 241 | .lean | 19,770 |
| Mathlib3 | https://github.com/leanprover-community/mathlib | `65a1391a0106` | 2023-10-30 | 3,468 | .lean | 1,017,000 |
| Aesop | https://github.com/leanprover-community/aesop | `7152850e7b21` | 2026-03-28 | 250 | .lean | 215 |
| Sphere eversion | https://github.com/leanprover-community/sphere-eversion | `5b63797f9452` | 2026-02-18 | 65 | .lean | 13,155 |
| FLT | https://github.com/ImperialCollegeLondon/FLT | `3343d9db843b` | 2026-03-25 | 174 | .lean | 1,059 |
| Liquid tensor | https://github.com/leanprover-community/lean-liquid | `087fffad55dc` | 2024-01-22 | 412 | .lean | 46,725 |
| PFR | https://github.com/teorth/pfr | `80daaf135131` | 2026-03-20 | 71 | .lean | 863 |
| FLT-regular | https://github.com/leanprover-community/flt-regular | `045237372750` | 2026-03-23 | 32 | .lean | 4,095 |
| miniF2F | https://github.com/AI Provider/miniF2F | `4e433ff5cadf` | 2022-06-02 | 3 | .lean | 7,335 |
| miniF2F-lean4 | https://github.com/yangky11/miniF2F-lean4 | `5746b7d6c478` | 2026-03-25 | 492 | .lean | 7,320 |
| Unit fractions | https://github.com/b-mehta/unit-fractions | `10ef71a300cf` | 2023-12-03 | 10 | .lean | 7,950 |
| ProofWidgets4 | https://github.com/leanprover-community/ProofWidgets4 | `00fe208b8e13` | 2026-03-30 | 41 | .lean | 181 |
| ProofNet | https://github.com/zhangir-azerbayev/ProofNet | `509ad79710ed` | 2024-10-13 | 131 | .lean | 2,423 |
| SciLean | https://github.com/lecopivo/SciLean | `95f8119a2884` | 2026-02-18 | 568 | .lean | 2,043 |
| Con-NF | https://github.com/leanprover-community/con-nf | `55b939a3acf9` | 2025-06-18 | 170 | .lean | 2,810 |
| PNT | https://github.com/AlexKontorovich/PrimeNumberTheoremAnd | `dee373f28eb3` | 2026-03-30 | 77 | .lean | 1,942 |
| Perfectoid spaces | https://github.com/leanprover-community/lean-perfectoid-spaces | `95a6520ce578` | 2021-12-06 | 66 | .lean | 521 |
| PutnamBench | https://github.com/trishullab/PutnamBench | `b391f48b645c` | 2026-02-22 | 674 | .lean | 672 |
| Formal conjectures | https://github.com/google-deepmind/formal-conjectures | `e1e26e7239a9` | 2026-03-30 | 731 | .lean | 2,556 |
| LeanEuclid | https://github.com/loganrjmurphy/LeanEuclid | `7c8f38bcd4f7` | 2025-11-25 | 234 | .lean | 206 |
| IMOSL Lean4 | https://github.com/mortarsanjaya/IMOSLLean4 | `5f6998907e36` | 2026-03-20 | 237 | .lean | 2,265 |
| math2001 | https://github.com/hrmacbeth/math2001 | `e660f42b13dd` | 2024-12-09 | 87 | .lean | 204 |
| lean-mlir | https://github.com/opencompl/lean-mlir | `a3f568cbe02a` | 2026-03-12 | 9,446 | .lean | 27,655 |
| ArkLib | https://github.com/Verified-zkEVM/ArkLib | `a741e5c9867d` | 2026-03-28 | 179 | .lean | 1,377 |

### 3. Coq/Rocq Ecosystem

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| UniMath | https://github.com/UniMath/UniMath | `ca8bc1dfdef5` | 2026-03-19 | 1,616 | .v | 14,382 |
| Coq stdlib | https://github.com/coq/coq | `93c35c91ed42` | 2026-03-30 | 2,763 | .v | 2,281 |
| MathComp | https://github.com/math-comp/math-comp | `6b80436d0c15` | 2026-03-26 | 120 | .v | 15,738 |
| MathComp Analysis | https://github.com/math-comp/analysis | `bd05c57283ab` | 2026-03-27 | 124 | .v | 102,735 |
| CompCert | https://github.com/AbsInt/CompCert | `1b71fecf694b` | 2026-03-18 | 253 | .v | 7,666 |
| Iris | https://gitlab.mpi-sws.org/iris/iris.git | `d94013ac1622` | 2026-03-30 | 214 | .v | 4,634 |
| Coq-HoTT | https://github.com/HoTT/Coq-HoTT | `5a2c575c89df` | 2026-03-22 | 618 | .v | 1,536 |
| HoTT (full) | https://github.com/HoTT/HoTT | `5a2c575c89df` | 2026-03-22 | 618 | .v | 23,040 |
| VST | https://github.com/PrincetonUniversity/VST | `1a3075f3c401` | 2026-03-03 | 1,424 | .v | 26,923 |
| CertiCoq | https://github.com/CertiCoq/certicoq | `a8267f799d82` | 2026-03-26 | 159 | .v | 4,138 |
| Vellvm | https://github.com/vellvm/vellvm | `6a074f35d317` | 2026-03-30 | 180 | .v | 3,682 |
| GeoCoq | https://github.com/GeoCoq/GeoCoq | `8848449c79c7` | 2025-11-18 | 460 | .v | 4,644 |
| Four Color Theorem | https://github.com/coq-community/fourcolor | `43a1b511e44c` | 2026-03-03 | 119 | .v | 1,396 |
| CoRN | https://github.com/coq-community/corn | `225384e459d9` | 2025-09-28 | 375 | .v | 104,070 |
| CoqPrime | https://github.com/thery/coqprime | `3371791217c6` | 2026-01-28 | 387 | .v | 161,220 |
| Interaction Trees | https://github.com/DeepSpec/InteractionTrees | `bd356ec0d2ea` | 2025-10-02 | 143 | .v | 1,315 |
| Hydra Battles | https://github.com/coq-community/hydra-battles | `ed8e6048018a` | 2025-01-22 | 205 | .v | 59,370 |
| Math Classes | https://github.com/coq-community/math-classes | `257619f0479a` | 2025-09-28 | 130 | .v | 11,820 |
| Topology | https://github.com/coq-community/topology | `4b1f95200f1e` | 2024-10-19 | 78 | .v | 13,110 |
| Ceramist | https://github.com/verse-lab/ceramist | `fd5e522f2c38` | 2020-04-13 | 23 | .v | 392 |
| RegLang | https://github.com/coq-community/reglang | `dd7521632d84` | 2026-03-03 | 12 | .v | 4,815 |
| Monae | https://github.com/affeldt-aist/monae | `f5d5fa5b9bba` | 2025-12-18 | 50 | .v | 18,450 |
| LibHyps | https://github.com/Matafou/LibHyps | `ded47282cc89` | 2025-10-06 | 24 | .v | 115 |
| fiat-crypto | https://github.com/mit-plv/fiat-crypto | `222ba12ce0b1` | 2026-03-30 | 653 | .v | 75,075 |
| bedrock2 | https://github.com/mit-plv/bedrock2 | `d201bb53a847` | 2026-03-19 | 286 | .v | 2,154 |
| Jasmin | https://github.com/jasmin-lang/jasmin | `0369ec3dcc83` | 2026-03-23 | 180 | .v | 58,215 |
| Rupicola | https://github.com/mit-plv/rupicola | `ff1319e647db` | 2026-03-20 | 69 | .v | 7,800 |
| Verdi | https://github.com/uwplse/verdi | `7e1641b758d8` | 2026-01-27 | 40 | .v | 579 |
| Verdi Raft | https://github.com/uwplse/verdi-raft | `a3375e867326` | 2023-12-08 | 209 | .v | 2,138 |
| MetaCoq | https://github.com/MetaCoq/metacoq | `10d992c04141` | 2026-03-25 | 596 | .v | 8,561 |
| Undecidability | https://github.com/uds-psl/coq-library-undecidability | `70dfc56f33a6` | 2024-09-18 | 686 | .v | 8,378 |
| Infotheo | https://github.com/affeldt-aist/infotheo | `4550b8c67887` | 2026-03-05 | 87 | .v | 2,992 |
| Odd Order | https://github.com/math-comp/odd-order | `647bb4b58d19` | 2026-03-27 | 34 | .v | 1,062 |
| Gaia | https://github.com/coq-community/gaia | `c44a7def755b` | 2026-03-03 | 42 | .v | 10,544 |
| Category Theory | https://github.com/jwiegley/category-theory | `524269d09705` | 2026-03-16 | 229 | .v | 716 |
| Graph Theory | https://github.com/coq-community/graph-theory | `0fe983788d37` | 2026-03-05 | 44 | .v | 2,115 |
| CoqEAL | https://github.com/CoqEAL/CoqEAL | `a66d00f5e646` | 2026-03-24 | 52 | .v | 1,135 |
| Coqtail Math | https://github.com/coq-community/coqtail-math | `a0c6e4716` | 2026-03-25 | 161 | .v | 2,435 |
| SSProve | https://github.com/SSProve/ssprove | `0e49a86ef39d` | 2026-03-30 | 101 | .v | 1,295 |
| ConCert | https://github.com/AU-COBRA/ConCert | `350ab8a9be1f` | 2026-03-30 | 189 | .v | 1,103 |
| WasmCert | https://github.com/WasmCert/WasmCert-Coq | `6acc7be59d1a` | 2026-03-20 | 48 | .v | 756 |
| CoLoR | https://github.com/fblanqui/color | `943f0c27d916` | 2026-01-27 | 264 | .v | 5,997 |
| ALEA | https://github.com/coq-community/alea | `0cd6868722` | 2021-11-03 | 10 | .v | 1,212 |
| RISC-V | https://github.com/mit-plv/riscv-coq | `99c0ba6bd907` | 2026-01-05 | 101 | .v | 202 |
| Koika | https://github.com/mit-plv/koika | `8921e30434d9` | 2025-12-10 | 125 | .v | 444 |
| Fiat | https://github.com/mit-plv/fiat | `07749ebcf75c` | 2026-03-27 | 677 | .v | 4,597 |
| Cerberus | https://github.com/rems-project/cerberus | `f9a2a4dbccc7` | 2026-03-26 | 66 | .v | 786 |
| NuPRL-Coq | (not cloned) | -- | -- | -- | .v | -- |

### 4. Isabelle/HOL

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Isabelle AFP | https://github.com/isabelle-prover/mirror-afp-2024 | `1549ea5b788b` | 2025-03-04 | 9,105 | .thy | 264,583 |
| Isabelle stdlib | https://github.com/isabelle-prover/mirror-isabelle | `620ab5e9d513` | 2026-03-27 | 1,844 | .thy | 1,082,850 |
| **Isabelle stdlib (YXML kernel export)** | **Isabelle2025-2 distribution** | `Isabelle2025-2` | 2026-06-20 | 5,093 | .yxml | **1,082,531** |
| seL4 | https://github.com/seL4/l4v | `c097c61cb42d` | 2026-03-31 | 1,869 | .thy | 956,010 |

> **Isabelle stdlib YXML kernel export (2026-06-20).** The `.thy` rows above are
> *name/statement scans of the upstream source repos* (the 1,082,850 figure is the
> full distribution + all sessions). The **YXML kernel export** row is the *real,
> kernel-checked* import produced this session: 25 math-heavy sessions
> (`HOL`, `HOL-Library`, `HOL-Analysis`, `HOL-Algebra`, `HOL-Number_Theory`,
> `HOL-Computational_Algebra`, `HOL-Combinatorics`, `HOL-Probability`,
> `HOL-Decision_Procs`, `HOL-Cardinals`, `HOL-Types_To_Sets`, `HOL-IMP`,
> `HOL-Hoare`, `HOL-ex`, `HOL-Homology`, `HOL-Real_Asymp`, `HOL-Auth`,
> `HOL-Data_Structures`, `HOL-Datatype_Examples`, `HOL-Corec_Examples`,
> `HOL-Imperative_HOL`, `HOL-Nonstandard_Analysis`, `HOL-Matrix_LP`, `HOL-Induct`,
> `HOL-Statespace`) were built with Isabelle2025-2, each theory exported via
> an `Export_Theory`-style ML script
> (`scripts/isabelle/export_mathverse.ML`) into the normalized YXML schema, then
> imported through `hol::isabelle` → `clean_kernel::Expr` → `FlatExpr` into a
> `.mathverse` shard. **1,082,531 declarations** across 5,093 theories — full stdlib (476,204) + 395 AFP entries (606,327) — expr/const ratio 8.61 — matching the 1,082,850 provenance figure with REAL kernel-exported facts (`DenseTypeTrees`, no stub).
> Includes the AFP entry `List-Index`; the AFP-2025 mirror otherwise has version
> skew with Isabelle2025-2 (`Code_Target_Bit_Shifts`/`Define_Time_Function`
> removed in 2025-2), so bulk AFP needs the version-matched AFP release — the
> pipeline is AFP-ready (`data/mathverse-library/isabelle/manifest.json`).
> Cross-linked to Mathlib via 722 `isabelle_mathlib_equivalences.json` links.
> Proved theorems are stored
> `SourceVerified` (Isabelle's LCF kernel checked them; clean's CIC kernel cannot
> re-check foreign HOL/Pure terms such as `Pure.eq`, so they are **not**
> `KernelVerified`). Shard + manifest:
> `data/mathverse-library/isabelle/` (shard gitignored as a release artifact).
> The remaining ~0.87M of the source scan are additional stdlib/AFP sessions; the
> pipeline scales to them by building + exporting more sessions.

### 5. HOL Family

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| HOL Light | https://github.com/jrh13/hol-light | `1c7690ec1231` | 2026-03-23 | 569 | .ml | 2,912 |
| HOL4 | https://github.com/HOL-Theorem-Prover/HOL | `b32dc44fb920` | 2026-03-31 | 2,840 | .sml | 5,978 |
| CakeML | https://github.com/CakeML/cakeml | `4e312c0f7e18` | 2026-03-25 | 979 | .sml | 8,580 |
| Flyspeck | https://github.com/flyspeck/flyspeck | `1ce0353008eb` | 2024-05-10 | 111 | .ml | 7,695 |
| OpenTheory | https://github.com/gilith/opentheory | `4e7d25943446` | 2023-03-21 | 271 | .art | 15 |
| HOLMS | https://github.com/HOLMS-lib/HOLMS | `70c2d08c72ba` | 2026-02-16 | 32 | .ml | 114 |

### 6. Mizar

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Mizar MML | https://github.com/mimosa-project/mizar-server | `61f3169a6edc` | 2024-04-04 | 5,748 | .miz/.abs | 74,918 |

### 7. Agda

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Agda stdlib | https://github.com/agda/agda-stdlib | `82b007fadb06` | 2026-03-17 | 1,252 | .agda | 12,884 |
| Cubical Agda | https://github.com/agda/cubical | `5c1bccf5d486` | 2026-03-30 | 1,172 | .agda | 297,105 |
| 1lab | https://github.com/the1lab/1lab | `087d4fdd93fe` | 2026-03-30 | 52 | .agda | 11,640 |
| agda-unimath | https://github.com/UniMath/agda-unimath | `f217ea9ffc99` | 2026-03-23 | 2,979 | .lagda.md | -- |

### 8. Idris 2

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Idris 2 | https://github.com/idris-lang/Idris2 | `37d29157a3d5` | 2026-03-21 | 1,926 | .idr | 21,413 |

### 9. F* / Project Everest

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| F* | https://github.com/FStarLang/FStar | `70671ffb81fa` | 2026-03-24 | 3,402 | .fst/.fsti | 127,145 |
| HACL* | https://github.com/project-everest/hacl-star | `8a2366d891cd` | 2026-03-24 | 991 | .fst/.fsti | 644,610 |
| KaRaMeL | https://github.com/FStarLang/karamel | `d8595565be5d` | 2026-03-30 | 236 | .fst/.fsti | 32,370 |
| Everest | https://github.com/project-everest/everest | `2a3f67dab56b` | 2025-10-14 | 0 | .fst/.fsti | -- |
| EverParse | https://github.com/project-everest/everparse | `f0f08d9bcdbdae` | 2026-03-27 | 636 | .fst/.fsti | 21,658 |
| Vale | https://github.com/project-everest/vale | `bbae0eb89143` | 2024-02-07 | 65 | .fst/.fsti | 1,353 |
| AlgoStar | https://github.com/FStarLang/AlgoStar | `eeb0fdb16a2c` | 2026-03-16 | 443 | .fst/.fsti | 10,817 |

### 10. Program Verification

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Dafny | https://github.com/dafny-lang/dafny | `9c1b58e01477` | 2026-03-18 | 2,201 | .dfy | 14,161 |
| Why3 | https://github.com/AdaCore/why3 | `44f650b03792` | 2026-03-30 | 1,546 | .mlw/.why | 26,514 |
| ACL2 | https://github.com/acl2/acl2 | `630a362ac6f0` | 2026-03-30 | 13,454 | .lisp | 293,947 |
| Stainless | https://github.com/epfl-lara/stainless | `0b611c0db5b2` | 2026-03-23 | 1,764 | .scala | 3,037 |
| Liquid Haskell | https://github.com/ucsd-progsys/liquidhaskell | `9ce1148983ad` | 2026-03-27 | 2,482 | .hs | 13,024 |
| VeriFast | https://github.com/verifast/verifast | `6048614c512f` | 2026-03-19 | 770 | .c | 333,375 |
| Stainless Bolts | https://github.com/epfl-lara/bolts | `4144e346dbe6` | 2026-03-31 | 192 | .scala | 9,173 |

### 11. PVS

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| NASA PVS Library | https://github.com/nasa/pvslib | `62b35bdb1138` | 2026-03-10 | 2,230 | .pvs | 4,885 |
| PVS source | https://github.com/SRI-CSL/PVS | `becb01535` | 2026-03-12 | 214 | .pvs | 465 |

### 12. Arend

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Arend Library | https://github.com/JetBrains/arend-lib | `373ed3c493f4` | 2024-11-11 | 304 | .ard | 6,691 |
| Arend (prover) | https://github.com/JetBrains/arend | `900528c79af4` | 2024-11-20 | 1 | .ard | -- |

### 13. Metamath Zero

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| mm0 | https://github.com/digama0/mm0 | `6d5f0d4fae8e` | 2025-12-22 | 80 | .mm0/.mm1 | 8,956 |

### 14. Rust Verification

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Verus | https://github.com/verus-lang/verus | `fc4528f50628` | 2026-03-29 | 834 | .rs | 18,975 |
| Creusot | https://github.com/creusot-rs/creusot | `1faf8fd0e981` | 2026-03-27 | 650 | .rs | 3,304 |

### 15. Semantic Frameworks

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Sail | https://github.com/rems-project/sail | `538c6b4112f0` | 2026-03-30 | 1,355 | .sail | 12,725 |
| KEVM | https://github.com/runtimeverification/evm-semantics | `33cacc816da8` | 2026-03-13 | 274 | .k | 1,685 |
| KeYmaera X | https://github.com/LS-Lab/KeYmaeraX-release | `ded9dfda7fd6` | 2024-09-23 | 153 | .kyx/.key | 379 |

### 16. Verified Systems

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| SV-COMP | https://github.com/sosy-lab/sv-benchmarks | `2e1723fde6aa` | 2021-10-03 | 67,714 | .c | 9,048 |
| TLA+ Examples | https://github.com/tlaplus/Examples | `dc6470ac55fe` | 2026-03-26 | 316 | .tla | 237 |
| Alloy Models | https://github.com/AlloyTools/models | `886447d3369a` | 2025-06-16 | 116 | .als | 1,082 |
| Quint | https://github.com/informalsystems/quint | `513910b6a383` | 2026-03-30 | 184 | .qnt | 1,621 |

### 17. TPTP (Theorem Prover Benchmarks)

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| TPTP NCL | https://github.com/TPTPWorld/NonClassicalLogic | `bd7ed2b152aa` | 2025-05-14 | 29,428 | .p/.ax | 11,278,965 |

### 18. SMT/SAT Benchmarks

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| SMTLIB | https://github.com/SMT-LIB/benchmark-submission | `37c6cd5d98ed` | 2025-05-20 | 12,218 | .smt2 | 4,574,195 |
| CVC5 | https://github.com/cvc5/cvc5 | `5c6b53b365c1` | 2026-03-29 | 4,080 | .smt2 | 154,536 |
| Yices2 | https://github.com/SRI-CSL/yices2 | `016a6243de76` | 2026-03-09 | 1,726 | .smt2 | 45,628 |

### 19. Type Theory / Logical Frameworks

| Library | Source URL | Commit Hash | Download Date | Files | Extension | Declarations |
|---------|-----------|-------------|---------------|-------|-----------|-------------|
| Dedukti | https://github.com/Deducteam/Dedukti | `ad27afd9ca6f` | 2025-11-25 | 410 | .dk | 573,795 |
| Lambdapi | https://github.com/Deducteam/lambdapi | `217ef3cbc089` | 2026-03-30 | 233 | .lp | 19,695 |
| CubicalTT | https://github.com/mortberg/cubicaltt | `9baa6f2491cc` | 2023-09-21 | 78 | .ctt | 95,985 |
| Abella | https://github.com/abella-prover/abella | `6332b52c6792` | 2026-01-25 | 67 | .thm | 13,125 |
| Beluga | https://github.com/Beluga-lang/Beluga | `820615cc4758` | 2025-09-30 | 581 | .bel | 43,320 |
| Naproche | https://github.com/naproche/naproche | `18c206ae056b` | 2025-12-03 | 19 | .ftl | 3,825 |
| cooltt | https://github.com/RedPRL/cooltt | `b39bf2990045` | 2023-10-21 | 32 | .cooltt | 399 |
| redtt | https://github.com/RedPRL/redtt | `ae76658873a6` | 2022-03-25 | 66 | .red | 629 |
| Minlog | https://github.com/minlog-system/minlog | `7c27ca155` | 2025-07-28 | 136 | .scm | 8,697 |

---

## Notes

- All repositories were cloned with `git clone --depth 1` (shallow clone). The commit hash represents HEAD at clone time.
- Download dates are derived from the commit timestamp of the most recent commit in the shallow clone.
- File counts are actual counts from the cloned repositories as of 2026-03-30.
- Declaration counts are from MATHVERSE_LIBRARIES.md and represent the output of the `mathverse_convert` keyword scanning pipeline.
- Metamath files (set.mm, iset.mm, nf.mm, ql.mm, hol.mm) all reside in the same `metamath/set.mm` repository.
- NuPRL-Coq was listed in MATHVERSE_LIBRARIES.md but the corresponding `/tmp/nuprl-coq` clone was not found.
- The Everest meta-repository has no `.fst` files directly (it is a build orchestrator).
- The `hott-coq` and `coq-hott` clones appear to share the same commit hash, suggesting they are the same repository (HoTT/HoTT and HoTT/Coq-HoTT).
- Arend prover source is Java; the single `.ard` file is minimal.

## Reproduction

```bash
# Re-download all libraries (wave 1: 14 systems)
./scripts/download_all_libraries.sh /tmp/mathverse-data

# Wave 2-3 systems were cloned individually:
git clone --depth 1 <source_url> /tmp/<repo_name>

# Run the full import pipeline
cargo run -p clean-mathverse --bin mathverse_convert --release -- all /tmp/mathverse-data
```
