# Mathverse Library — Historical Clean Kernel Compatibility Audit

> Historical/superseded note: this audit predates the current
> `mathverse-v1.2.0` release and mixes earlier meanings of `KernelVerified`.
> In old Lean4-path notes, `KernelVerified` can mean "verified by the source
> system / Lean 4 kernel"; it must not be read as Clean-kernel verification
> unless a current Clean replay/full-validation artifact says so.

**Date:** 2026-04-16 (audit refresh 2026-04-20)
**Current Release:** mathverse-v0.9.0 (2026-04-01)
**Tree State:** post-v0.9.0 `main` (Tier 0 Clean-native + tag-based search + arXiv bridge landed; scheduled for the next release)
**Source Systems in Importers:** historical 68 figure (later provenance uses 69
importer enum variants)
**Target Repositories (census):** 238
**Total Declarations Counted (census):** 30,049,434
**Total Declarations Converted (pipeline):** 3,254,463
**Declarations Kernel Type-Checked by Clean:** 156 (0.33% of Init's 47,301 constants — see Measurement below)

---

## Executive Summary

**The 30M declaration count is a census — but the pipeline now produces real artifacts.**

As of this update, `mathverse_convert all` produces `.mathverse` shard files for Tier 1–4 systems (~27M declarations). The Coq kernel translator feeds real `Declaration` objects to `Environment::add_decl()` for type-checking. The `verify_foreign` method uses the FlatExpr→Expr reverse bridge to perform actual kernel type-checking. The .olean binary pipeline is wired into convert_all for Lean 4 systems.

---

## What `mathverse_convert all` Actually Does

For each of the 238 systems, the converter:
1. Finds source files by extension (`.v`, `.lean`, `.agda`, `.thy`, `.rs`, etc.)
2. Reads each file as a string
3. Checks if lines start with keywords (`Theorem `, `lemma `, `Definition `, etc.)
4. Increments u64 counters
5. Returns `(theorems: u64, definitions: u64, axioms: u64)`

The `convert_all` function sums these counts across all systems and writes `mathverse_summary.json`. **No kernel objects are created. No `.mathverse` shards are written. No type-checking occurs.**

---

## Import Tier Classification (Honest Assessment)

### Tier 1: OpenTheory — Kernel `Declaration` objects (NOT in convert_all pipeline)

`clean_kernel::open_theory::import_article_with_options` produces real `Declaration::Axiom` objects with `Expr` type trees. These CAN be added to a kernel `Environment`.

**Limitations:**
- All HOL proofs are **axiomatized** — only the type (statement) is translated, proof trees are discarded
- The `mathverse_convert` pipeline calls the OpenTheory bridge but **discards the returned declarations** — it only keeps the count
- Scale: ~89 declarations across test articles
- NOT invoked by `convert_all` in a way that produces persistent output

**Source:** `crates/clean-kernel/src/open_theory/import.rs`, `crates/clean-mathverse/src/hol/opentheory_bridge.rs`

### Tier 2: Lean 4 .olean — `FlatExpr` in `.mathverse` shards (SEPARATE code path)

`lean4_alpha::import_module` lowers `.olean` binary `ParsedExpr` to `FlatExpr` and writes to `.mathverse` shards via `ShardWriter`. This is the most complete import pipeline.

**Limitations:**
- `convert_lean4_olean_dir` is a SEPARATE function — it is **NOT listed in the `sources` vec** of `convert_all`
- **No `FlatExpr` → kernel `Expr` bridge exists.** `flat/convert.rs` only converts Expr→FlatExpr (one direction). The kernel type-checker (`BatchVerifier`) works on `Expr`, not `FlatExpr`.
- Universe polymorphism is lost (`levels_list_idx` always `u32::MAX`)
- `KernelVerified` confidence means "verified by Lean 4's kernel," NOT "verified by Clean's kernel"
- Scale: ~100,000+ constants round-trip through `.mathverse` shards

**Source:** `crates/clean-mathverse/src/lean4_alpha.rs`, `crates/clean-mathverse/src/build_library.rs`

### Tier 3: Coq — Two paths, neither connected to type-checker

**Path A (mathverse-level):** `coq_alpha.rs` converts CIC s-expressions to `FlatExpr`. Same `FlatExpr→Expr` bridge gap as Tier 2.

**Path B (kernel-level):** `coq_import/translate/translator.rs` produces real kernel `Declaration` objects with `Expr` trees (handling Rel, Var, Sort, Prod, Lambda, LetIn, App, Const, Ind, Construct, Case, Fix, CoFix, Proj). This is the most complete translator.

**Limitations:**
- Path B declarations are **translated and counted, then dropped** — `import_sources` returns `ImportStats`, not the declarations
- No code path feeds translated Coq declarations to `Environment::add_decl()` followed by type-checking
- `MathverseVerify::verify_foreign` (library.rs:564-567) contains: `"In a full implementation this would run the kernel type-checker; here we accept and store with Translated confidence."`

**Source:** `crates/clean-mathverse/src/coq_alpha.rs`, `crates/clean-kernel/src/coq_import/translate/translator.rs`

### Tier 4: Structured Parse — String names extracted, immediately discarded (5 systems)

`convert_lean4_dir`, `convert_coq_dir`, `convert_agda_dir`, `convert_idris_dir` parse source files and extract `(name, kind, type_signature_string)` into structured records. These are NOT kernel objects — type signatures are raw strings, not parsed `Expr` trees.

**Critical:** The returned `Vec<Lean4Theorem>` / `Vec<CoqDeclaration>` / etc. are **immediately discarded** by `convert_all`. Only the count survives.

| System | Parser | Output type | What happens to it |
|--------|--------|------------|-------------------|
| Lean 4 source | `import_lean4_file` — line-prefix matching | `Vec<Lean4Theorem>` (name + string type) | Discarded |
| Coq source | `import_coq_file` — line-prefix matching | `Vec<CoqDeclaration>` (name + string type) | Discarded |
| Agda | `import_agda_file` — understands postulates, modules | `Vec<AgdaDeclaration>` | Discarded |
| Idris 2 | `import_idris_file` — understands data/record | `Vec<IdrisDeclaration>` | Discarded |
| Metamath | `MetamathImporter::import_database` — full .mm parse | `MetamathDatabase` with `Vec<String>` tokens | Writes `.mathverse.json` stats only |

### Tier 5: Keyword Scan — Line counting only (229 systems)

All remaining 229 systems use inline `Box::new(|d| { ... })` closures that:
1. `collect_files_recursive(d, "ext", &mut f)`
2. `for l in t.lines() { if l.trim().starts_with("keyword ") { count += 1; } }`
3. `println!("--- System ---\n  files: {}, Count: {count}");`
4. Return `(count1, count2, 0)`

This is `grep -c` reimplemented in Rust. No parsing, no AST, no names, no types.

---

## Declaration Count by Import Tier

| Tier | Systems | Declarations | % of Total | Kernel-loadable? | Type-checked by Clean? |
|------|---------|-------------|------------|-----------------|----------------------|
| **Tier 1: OpenTheory** | 1 | 89 | <0.001% | YES — written to .mathverse shards | Axioms via add_decl() |
| **Tier 2: .olean binary** | 1 (now in convert_all) | ~100,000+ | ~0.3% | YES — FlatExpr→Expr bridge complete | Via reconstruct→add_decl |
| **Tier 3: Coq translated** | 2 | varies | varies | YES — verify_declarations() wired | Via add_decl()/add_inductive() |
| **Tier 4: Structured parse** | 5 | ~27,000,000 | ~90% | YES — .mathverse shard files written | String metadata (not Expr) |
| **Tier 5: Keyword scan** | 229 | ~3,000,000 | ~10% | NO — counts only | **NO** |

### What Would Be Needed to Close the Gaps

1. ~~**FlatExpr → Expr bridge**~~ — **DONE** (`flat/reconstruct.rs`). Bottom-up O(N) reconstruction. All 11 FlatTag + 5 FlatLevel variants. 13 round-trip tests passing. (#3121)
2. ~~**Wire Coq translator output to `Environment::add_decl()`**~~ — **DONE** (`coq_import/verify.rs`). `verify_declarations()` feeds `TranslatedGlobalDecl` to `Environment::add_decl()` / `add_inductive()`. 6 tests passing. (#3123)
3. ~~**Implement `MathverseVerify::verify_foreign` for real**~~ — **DONE** (`library.rs`). Uses FlatDb → reconstruct_expr → Declaration::Axiom/Theorem → Environment::add_decl(). Confidence: KernelVerified (full theorem), Translated (statement only), Unverified (parse failure). 3 tests. (#3124)
4. ~~**Make `convert_all` write persistent output**~~ — **DONE** (`mathverse_convert.rs`). Tier 4 systems (Lean4, Coq, Agda, Idris) now write `.mathverse` shard files via ShardWriter with structured constant headers. (#3125)
5. ~~**Wire .olean pipeline into convert_all**~~ — **DONE** (`mathverse_convert.rs`). `convert_lean4_olean_dir_to` wired into convert_all for all 42 Lean4 source dirs with `.olean` files. Plus `olean` CLI subcommand. (#3122)
6. ~~**Wire OpenTheory + Isabelle translators to ShardWriter**~~ — **DONE** (`mathverse_convert.rs`). `write_opentheory_shard()` converts kernel Expr → FlatExpr via FlatBuilder and writes to ShardWriter. Isabelle uses structured `.yxml` import with fallback to keyword scanning. (#3126)
7. **Per-system term translators** for Tier 5 systems (Mizar, etc.) — substantial but bounded work

---

## What IS Real

Despite the gaps above, the following infrastructure is **genuinely implemented and tested**:

1. **`.mathverse` shard format** — binary format with string table (zstd), expression arena (16 bytes/expr), constant headers (32 bytes/entry), bloom filter, sorted name index. Read/write round-trip tested.
2. **`.olean` parser** — correctly parses Lean 4 binary module files (1,138+ files from Init library tested)
3. **`FlatExpr` lowering** — `ParsedExpr` → `FlatExpr` conversion handles all Lean 4 expression kinds
4. **`FlatExpr` reconstruction** — `FlatExpr` → kernel `Expr` reverse bridge (**NEW**: `flat/reconstruct.rs`, 13 round-trip tests)
5. **OpenTheory kernel import** — produces real kernel `Declaration` objects with `Expr` types
6. **Coq kernel translator** — handles all CIC term constructors → kernel `Expr`; batch importer now retains declarations (**NEW**: `import_sources_collecting`)
7. **Kernel type-checker** — `BatchVerifier` / `TypeChecker::infer_type` works on hand-constructed `Expr` in unit tests
8. **Census pipeline** — the keyword scan across 238 systems is a real, reproducible inventory of formal math on the internet

---

## Kernel TC Measurement (2026-04-16)

Measured on Lean 4 Init module (v4.30.0-rc1) using `verify_measurement::test_measure_init_kernel_tc_pass_rates`:

| Metric | Value |
|--------|-------|
| Total constants | 47,301 |
| Reconstruction failures | **0** (binder fix eliminated all) |
| Kernel verified (theorem+defn) | 93 |
| Axiom accepted | 63 |
| Total accepted | 156 (0.33%) |
| Unknown constant reference | 25,410 |
| Universe level error | 21,728 |
| Unsupported expression tag | 7 |

**Analysis:** The 0% reconstruction failure rate confirms the binder_info fix works. The 99.67% TC failure rate is because each constant is verified in an **empty environment** — real constants reference other constants (25,410 failures) and universe parameters (21,728 failures). To improve TC pass rate, the measurement needs to load constants incrementally into a shared environment in dependency order.

**Before binder fix:** 100% reconstruction failure (all 47,301 constants). Root cause: `binder_info_from_u8` rejected byte 0xA2 (Lean 4 v4.27+ encoding).

---

## Post-v0.9.0 Additions on `main`

The following items landed after the `mathverse-v0.9.0` tag and are **not** part of the
released assets; they will ship in the next release.

### Native Theorem Export Pipeline

Adds a **reverse pipeline**: Clean-proved kernel `Declaration` objects can be exported to `.mathverse` shards via `mathverse export` / `mathverse_shard build-native`. This closes the Math-to-Mathverse-to-Math loop, allowing Clean to both consume and produce verified mathematics in the `.mathverse` format. Source: `crates/clean-mathverse/src/build_library_native.rs`, `crates/clean-mathverse/src/native_export.rs`, `crates/clean-mathverse/src/bin/mathverse_shard/native_build.rs`.

| Direction | Pipeline | Status |
|-----------|----------|--------|
| Import (existing) | `.olean` / `.mm` / `.v` / ... -> `.mathverse` | Production (in v0.9.0) |
| Export (new) | kernel `Declaration` -> `.mathverse` shard | On `main`, post-v0.9.0 |

### Tag-Based Search

Constants in `.mathverse` shards can carry keyword tags (e.g., "algebra", "topology", "number-theory"). The `mathverse find --tag` command searches across all loaded shards by tag. Tags are assigned during import based on content-domain classification and can be manually overridden.

### arXiv Formalization Bridge

The arXiv pipeline (`scripts/arxiv_formalize.py`, `crates/clean-mathverse/src/arxiv/`) bridges directly to `.mathverse` shard output. Formalized theorems from arXiv papers are tagged with their arXiv ID and written to dedicated shards, enabling search by paper reference.

### Updated Import Tier Table (tree state on `main`)

| Tier | Systems | Declarations | Kernel-loadable? | Type-checked by Clean? | Added post-v0.9.0 |
|------|---------|-------------|-----------------|----------------------|---------------|
| **Tier 0: Clean-native** | 1 | varies | YES | YES (kernel-proved) | NEW |
| **Tier 1: OpenTheory** | 1 | 89 | YES | Axioms via add_decl() | |
| **Tier 2: .olean binary** | 1 | ~100,000+ | YES | Via reconstruct->add_decl | |
| **Tier 3: Coq translated** | 2 | varies | YES | Via add_decl()/add_inductive() | |
| **Tier 4: Structured parse** | 5 | ~27,000,000 | YES | String metadata (not Expr) | |
| **Tier 5: Keyword scan** | 229 | ~3,000,000 | NO | NO | |

**Tier 0 (new):** Theorems proved natively by Clean's kernel. These carry `TrustLevel::KernelVerified` with zero axiom dependencies beyond the foundational axioms. The highest trust level in the system.

---

## How to Verify

```bash
# 1. Run the census pipeline (produces counts only, no kernel objects)
cargo run -p clean-mathverse --bin mathverse_convert --release -- all /tmp/mathverse-data

# 2. Run kernel TC measurement (requires Lean 4 toolchain under ~/.elan/)
cargo test -p clean-mathverse --lib --release -- verify_measurement::tests::test_measure_init_kernel_tc_pass_rates --nocapture

# 3. Run kernel-level tests (these DO produce real kernel objects)
cargo test -p clean-kernel --lib -- open_theory  # OpenTheory → Declaration
cargo test -p clean-mathverse --lib -- build_library  # .olean → FlatExpr → .mathverse shard
cargo test -p clean-mathverse --lib -- coq_alpha      # Coq → FlatExpr → .mathverse shard

# 4. Verify .mathverse shard integrity
cargo test -p clean-mathverse --lib -- shard           # Shard read/write round-trip
```
