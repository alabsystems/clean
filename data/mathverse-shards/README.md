# Mathverse Library — Local Shard Inventory

Last updated: 2026-07-04 (release `mathverse-v1.3.0`; doc corrections only)

## What is actually in this directory

`mathverse_fidelity_check data/mathverse-shards` is the source of truth for
the *structural density* of each shard. It is NOT a verification report: the
tool only compares `expr_count / constant_count` from the shard header and
runs no Clean-kernel proof check. Today's snapshot (after de-duplicating the
Metamath shards that appeared under two name conventions and were inflating
the corpus count):

- **14 `.mathverse` shards** (release `mathverse-v1.3.0`, rebuilt from raw
  upstream sources)
- **1,052,886 declarations**, **100% classified above `SurfaceNamesOnly`**
- **0 name-only stub shards** — see "Stub regression prevention" below

### Per-system tally (full rebuild, 2026-06-22)

| System | Shards | Density tier † | Constants |
|---|---|---|---|
| Lean 4 mathlib4 (@ HEAD, v4.32.0-rc1) | 1 | DenseTypeTrees | 482,407 |
| Lean 4 stdlib (v4.32.0-rc1) | 1 | DenseTypeTrees | 158,608 |
| Metamath set/iset/nf/ql/hol | 5 | ProofVerified / HolImported | 161,308 |
| ACL2 | 1 | DenseTypeTrees | 85,202 |
| Isabelle AFP (2024) | 1 | ProofVerified | 55,609 |
| Lean 3 (mathlib3) | 1 | ProofVerified | 46,366 |
| Coq (UniMath) | 1 | ProofVerified | 22,049 |
| OpenTheory (`.art`) | 1 | ProofVerified | 18,839 |
| F\* | 1 | HolImported | 12,320 |
| Dafny | 1 | HolImported | 10,178 |

Note: v1.2.0 shipped a ~4.9M-constant **name-only Isabelle stub** plus duplicate
shards. v1.3.0's structured importers (Isabelle/ACL2/Coq/Lean 3/Dafny/F\*) now
emit real reconstructed type trees instead of name-only placeholders — which is
why the Isabelle shard fell from 4.9M name-only constants to 55,609 real ones,
and the corpus total dropped from 5.77M (mostly stubs) to 1.05M (all real).

† **Density tier is a structural metric, NOT a Clean-kernel proof check.**
`DenseTypeTrees` (`expr/const >= 5.0`) means the Lean 4 shards carry dense,
fully-elaborated type signatures — many `FlatExpr` nodes per constant — which
is what distinguishes them from name-only stub shards. It makes no claim that
these 625,622 constants have been re-verified by Clean's own kernel. Per-constant
kernel verification is tracked separately by `ImportConfidence::KernelVerified`,
which is only stamped on constants Clean's kernel independently re-checks
(see `crates/clean-mathverse/src/lean4/olean/`); the un-typechecked import path
stamps `SourceVerified` at most. The tier names `ProofVerified` / `HolImported`
are likewise density buckets named after the source system's own proof format,
not Clean-kernel results.

Earlier counts in this file claimed Isabelle/AFP, ACL2, Dafny, Coq
(UniMath), and Lean 3 (mathlib3) shards as imported. Those were
**name-only stub shards** — the importer parsed declaration names and
kinds, then emitted a single shared `FlatExpr::sort(0)` placeholder as
the type signature for every constant. They were **deleted from disk**,
and the importers have since been rebuilt as real type-tree translators
(the v1.3.0 shards in the tally above). Regression tests prevent any
importer from re-emitting stub shards — see "Stub regression
prevention" below.

## Stub regression prevention

Three layers, all on by default in `cargo test --release -p clean-mathverse`:

1. **`mathverse_fidelity_check --strict <dir>`** — CLI audit, exits non-zero
   if any shard has ≥1000 constants and ≤2 `FlatExpr` entries.
2. **`tests/no_stub_shards.rs`** — refuses to validate
   `data/mathverse-shards/` if the audit finds an offender.
3. **`tests/structured_importers_refuse_stubs.rs`** — five per-importer
   fixture tests. Each `convert_*_dir` must either refuse non-empty
   input (stub guard fires, no shard written) or emit a shard where
   `expr_count > constant_count` (real type translation).

The structured importers historically shared a stub pattern: parse
names + kinds, emit one shared `FlatExpr::sort(0)` placeholder per
constant. That era is over: **all six structured importers now emit
real reconstructed type trees** via dedicated type parsers —
`lean3_import.rs` + `lean3_type_parser.rs`, `acl2_import.rs` +
`acl2_term_translator.rs`, `dafny_import.rs` + `dafny_type_parser.rs`,
`isabelle_thy_import.rs` + `isabelle_term_parser.rs`, `fstar_source.rs`,
and the Coq `.v` lane, which was refactored from the old
`coq_v_import.rs` into `coq/v_import.rs` + `coq/v_type_parser.rs`. Zero
`STUB GUARD` blocks remain in the crate; declarations whose types fail
to parse are skipped, never stubbed. All six stamp
`ImportConfidence::Unverified` (statement-level trust, no proof terms,
no Clean-kernel re-check) — this is what built the v1.3.0 shards in the
tally above. A separate Coq *depth* pipeline (kernel-checked proof
terms via SerAPI) is in progress — see
[`data/MATHVERSE_COQ_DEPTH.md`](../MATHVERSE_COQ_DEPTH.md); no
corpus-scale Coq `KernelVerified` counts exist yet.

## Currently NOT imported

| System | Reason / status |
|---|---|
| HOL Light | Requires OCaml evaluation — chain via OpenTheory articles |
| HOL4, Why3 | No importer code path |
| Agda stdlib, Idris2 | Source importers exist (`mathverse_structured_import agda` / `idris`) but no shard shipped in v1.3.0 |
| Mizar | Upstream `digama0/mizar-rs` removed; no source available |

(Coq, Dafny, ACL2, Isabelle, Lean 3, and F\* — previously listed here as
stub-guarded or importer-less — now ship real statement-level shards; see
the per-system tally above.)

## Reproduction

```bash
# 1. Tooling (Homebrew on macOS)
brew install coq agda dafny idris2 ocaml opam ghc stack

# 2. Source repos
bash scripts/setup_mathlib_oleans.sh
bash scripts/download_metamath.sh
for repo in mathlib:leanprover-community/mathlib \
            opentheory:gilith/opentheory ; do
  name=${repo%%:*}; url=${repo##*:}
  git clone --depth 1 https://github.com/$url /tmp/sources/$name
done

# 3. Imports — only the ones that produce real shards today
./target/release/mathverse_convert mathlib --output-dir data/mathverse-shards
for db in set iset nf ql hol; do
  ./target/release/mathverse_convert metamath \
    /tmp/sources/metamath-set.mm/$db.mm --output-dir data/mathverse-shards
done
./target/release/mathverse_convert opentheory \
  /tmp/sources/opentheory --output-dir data/mathverse-shards
# Lean 3 now also produces a real shard:
git clone --depth 1 https://github.com/leanprover-community/mathlib /tmp/sources/mathlib3
./target/release/mathverse_structured_import lean3 \
  /tmp/sources/mathlib3 data/mathverse-shards/structured

# 4. Verify
./target/release/mathverse_fidelity_check data/mathverse-shards --strict
cargo test --release -p clean-mathverse --test no_stub_shards \
                                    --test structured_importers_refuse_stubs
```

## Search

```bash
mathverse systems              # source-system inventory
mathverse stats                # corpus-wide counts
mathverse list --limit 100     # enumerate declarations
mathverse find <query>         # tag/name/semantic/cross-system search
mathverse search <query>       # fuzzy/exact name search
mathverse graph                # cross-system equivalence
```

## Gaps found and fixed (audit pass, 2026-05-17)

Five real fakes found by a fresh skeptical pass and patched:

1. **Binder-loss in `extract_type_sig`** — Lean 3 theorem/def syntax
   carries binders BEFORE the `:` (e.g. `theorem foo (n : Nat) : n + 0
   = n`). The historical extractor returned only the text AFTER the
   first top-level `:`, silently dropping the binders. The new
   `extract_binders_and_type` captures both and the importer
   synthesises `∀ <binders>, <body>` before parsing, so binder names
   resolve to BVars instead of leaking as free Const references.
   Pinned by `theorem_binders_before_colon_must_become_pi_nodes`.
2. **`instance`/`example`/`abbreviation` missing from `DECL_STARTS`** —
   the lean3 declaration parser was silently dropping these three
   keywords. Mathlib uses `instance` heavily.
3. **Logical connectives `∧ ∨ ↔` not lexed** — type bodies using them
   parsed as `Unknown` and the whole decl was skipped. Added to the
   infix table with Lean-3-comparable precedences.
4. **`Type*` lexed as `Type` then Mul** — universe-polymorphic
   shorthand collided with the multiplication operator. Special-cased
   in `emit_name`.
5. **`ShardWriter::new()` dedup bootstrap bug** — `strings` and
   `levels` were pre-seeded with sentinels but their dedup maps were
   left empty, so `add_string("")` and `add_level(zero)` pushed
   duplicate entries instead of returning index 0. Bloated every shard
   ever written and broke ≥18 test assertions across the codebase.
6. **Metamath shards duplicated under two name conventions** —
   `metamath-set.mathverse` (root) and `base/metamath_set.mathverse` are the
   same data. The audit double-counted them as 10 shards / ~70K
   constants when the reality is 5 shards / ~35K constants. Removed
   the hyphenated copies in the root.

## Code fixes shipped this session (historical note, 2026-05-17 era)

> Kept as a historical record of the audit-era state. Several items below
> describe code that has since been superseded — in particular the
> `STUB GUARD` blocks are gone (all structured importers now emit real type
> trees; see "Stub regression prevention" above) and `coq_v_import.rs` was
> refactored into `coq/v_import.rs` + `coq/v_type_parser.rs`.

- `crates/clean-mathverse/src/lean3_type_parser.rs` (new) — Pratt-style
  Lean 3 type-signature parser → `FlatExpr` tree. Handles `∀`/`Π`
  binders (bracketed and unbracketed forms), `→`/`->` arrows,
  application, parens, identifier references with de-Bruijn resolution,
  `Prop`/`Type`/`Sort` universe atoms, numeric literals, and infix
  `= ≠ < ≤ > ≥ + - * /` mapped to free `Const` references under their
  canonical Lean 3 typeclass names (`Eq`, `Le`, `Add`, …). 11 unit
  tests in the module + `lean3_import` integration test.

- `crates/clean-mathverse/src/lean3_import.rs::write_lean3_shard` — replaces
  the per-constant `FlatExpr::sort(0)` placeholder with the real
  type-parser output. Declarations whose type signature is missing or
  fails to parse are **skipped**, never falsified with a placeholder.

- `crates/clean-mathverse/src/{acl2,coq_v,dafny,isabelle_thy}_import.rs`
  — `STUB GUARD` blocks emitting any constant unless a real type
  translator is in place. Refuses rather than silently lies.

- `crates/clean-mathverse/src/bin/mathverse_fidelity_check.rs` (new) — reads
  the 256-byte shard header without decompressing, classifies each
  shard into one of five fidelity tiers, exits non-zero in `--strict`
  mode when ≥1000-constant stub shards are present.

- `crates/clean-mathverse/tests/no_stub_shards.rs` and
  `tests/structured_importers_refuse_stubs.rs` — six regression tests
  that fail CI if any future change reintroduces a stub.

- `crates/clean-mathverse/src/shard.rs` — added `expr_count`,
  `string_count`, `constant_count` getters on `ShardWriter` so importer
  tests can assert the real-vs-stub contract directly.

- `crates/clean-kernel/src/open_theory/import.rs::register_const_schema`
  — was strictly rejecting any second usage of a polymorphic constant
  with a different instantiated type. Now keeps the first-seen schema
  and accepts subsequent usages, which is what the OT articles require
  for any constant like `!` / `=` / list / option / natural etc.

- `crates/clean-mathverse/src/bin/mathverse_convert.rs::process_ot_articles` —
  per-article progress logging with stdout flush, plus `OT_MAX_ARTICLES`
  / `OT_PER_ARTICLE_SECS` env-var diagnostics.

- `crates/clean-mathverse/src/bin/mathverse_convert.rs` — adds `opentheory` and
  `isabelle-binary` direct subcommands, calling the existing
  `convert_opentheory_dir` / `convert_isabelle_dir` functions for
  isolated, per-system invocations.

- `crates/clean-mathverse/src/bin/mathverse_structured_import.rs` (new) — direct
  CLI to each `structured_import::convert_*_dir` function (dafny / acl2
  / lean3 / coq / isabelle), so each runs in isolation with strict
  timeouts and visible progress.
