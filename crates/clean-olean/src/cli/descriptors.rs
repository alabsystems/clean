// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors for every `clean olean <verb>` subcommand.
//!
//! The top-level binary registers these via
//! `v.extend(clean_olean::cli::FEATURES)` in `clean-cli`'s `registry.rs`.
//! Keep the path segments in sync with the clap tree defined in
//! [`super::OleanCommands`]; the drift tests in
//! `crates/clean-cli/tests/feature_coverage.rs` enforce this contract.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const UNIFIED_CLI_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "CLI orphan inventory — .olean binary absorption",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3441: Reference = Reference {
    kind: RefKind::Issue,
    label: "Absorb verify_olean_batch into clean olean verify-batch",
    target: "#3441",
};

const ISSUE_3442: Reference = Reference {
    kind: RefKind::Issue,
    label: "Absorb generate_namespace_overlay into `clean olean generate-overlay`",
    target: "#3442",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-olean",
    target: "clean-olean",
};

const GENERATE_OVERLAY_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "generate-overlay"],
    summary: "Generate namespace overlay payload modules for `clean-kernel`",
    description:
        "Snapshots declaration payloads (`ConstantInfo`) from a source environment, \
         filters by namespace prefix, and emits deterministic Rust modules under the \
         requested `--output-dir` (typically `crates/clean-kernel/src/env/generated/`). \
         The source environment can be built from stdlib `.olean` modules \
         (`--module Init.Core --module Std.Data.List`) and/or seeded with the kernel's \
         `Topology.Manifold` / `Topology.LieGroup` helpers via `--seed-topology-env`. \
         Each namespace produces a `<module>.rs` alongside a bincode `<module>.payload.bin`; \
         a top-level `mod.rs` lists every emitted module. Absorbs the deprecated \
         `generate_namespace_overlay` standalone binary (#3442, Epic #3436).",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean olean generate-overlay --output-dir crates/clean-kernel/src/env/generated --namespace Topology.Manifold --seed-topology-env",
            what: "Seed Topology.Manifold from kernel init paths and emit the overlay module.",
        },
        Example {
            cmd: "clean olean generate-overlay --output-dir out --namespace Mathlib.Algebra --module Mathlib.Algebra.Basic --search-path /lean/lib",
            what: "Snapshot a Mathlib namespace from an explicit `.olean` search path.",
        },
    ],
    see_also: &[],
    references: &[
        UNIFIED_CLI_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3442,
        CRATE_REF,
    ],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

const VERIFY_BATCH_DESCRIPTION: &str = "\
Type-check every `.olean` module in a directory using a shared cumulative \
kernel environment.

Walks the directory recursively, extracts import declarations from each \
`.olean`, topologically sorts the modules, and loads them one-by-one into a \
single `Environment`. Each module's newly-added constants are type-checked \
before the next module is loaded. Pass `--isolated` to fall back to the legacy \
per-module verification path (useful for bisecting missing dependencies). Pass \
`--parallel N` to type-check each module's new constants with N threads.

The `--cache-file` option enables incremental verification ON THE SERIAL \
PATH: modules whose file content hash matches the cache are skipped during \
type-checking (the load step still runs because subsequent modules depend on \
their declarations), and the cache is updated and saved on exit. Under \
`--parallel N` the cache is neither consulted nor written — a parallel run \
re-checks everything and leaves the cache file untouched.

Pass `--json` to emit a structured `ExtendedBatchSummary` JSON report to \
stdout. `--json-report <FILE>` additionally writes a comprehensive \
`VerificationReport` to disk, suitable for automation artifact collection.

Part of Epic #3436 (unified `clean` CLI feature index). Absorbs the legacy \
standalone `verify_olean_batch` binary.
";

const VERIFY_BATCH_EXAMPLES: &[Example] = &[
    Example {
        cmd: "clean olean verify-batch /path/to/olean/dir",
        what: "cumulative type-check every module in the directory",
    },
    Example {
        cmd: "clean olean verify-batch /tmp/oleans --parallel 8 --json-report report.json",
        what: "parallel type-check with 8 threads and write a structured JSON report",
    },
    Example {
        cmd: "clean olean verify-batch /tmp/oleans --cache-file verify.cache --load-only",
        what: "load-only pass with incremental cache (no type-checking)",
    },
];

const VERIFY_BATCH_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "verify-batch"],
    summary: "Batch type-check every `.olean` module in a directory",
    description: VERIFY_BATCH_DESCRIPTION,
    category: Category::Verification,
    stability: Stability::Usable,
    examples: VERIFY_BATCH_EXAMPLES,
    see_also: &[],
    references: &[
        ORPHAN_INVENTORY_REF,
        UNIFIED_CLI_REF,
        ISSUE_3436,
        ISSUE_3441,
        CRATE_REF,
    ],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

const IMPORT_REVERIFY_METRIC_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "import-reverify-metric"],
    summary: "Measure + ratchet the fraction of imported constants that pass the local \
              assumed-environment check",
    description: "Loads the requested bootstrap module closure (`--module Init`, \
         optionally `--module Std`; transitive imports load automatically), runs \
         the LOCAL assumed-environment check (`typecheck_constants_full`: each \
         constant's type inhabits a Sort and its value has that type, ASSUMING \
         every declaration outside the checked set; the checked set is replayed in \
         Lean's order and each of its inductive blocks is rebuilt by the kernel and \
         compared with the stored members — no dependency-closed replay, no import \
         authority) over exactly those \
         imported constants, and writes `{total_imported, reverified, fraction, \
         ...}` to a \
         JSON metric file (default `data/import_reverification_metric.json`). \
         The write RATCHETS: a measurement whose fraction regresses below the \
         recorded baseline for the same `--lane` is refused, turning the \
         import-trust residual into a measured, monotonically-rising number. \
         Deterministic by default; `--timestamp` stamps the run time. \
         `--max-heartbeats` is a pure resource limit, never a soundness gate.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean olean import-reverify-metric --module Init",
            what: "measure the Init lane and ratchet data/import_reverification_metric.json",
        },
        Example {
            cmd: "clean olean import-reverify-metric --module Init --module Std --lane Init+Std --out target/metric.json",
            what: "measure a wider lane into an explicit metric file",
        },
    ],
    see_also: &["olean verify-batch"],
    references: &[UNIFIED_CLI_REF, ISSUE_3436, CRATE_REF],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

const SIMP_SET_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "simp-set"],
    summary: "Report the `@[simp]` set a module closure actually decodes",
    description: "Loads the requested `.olean` closure (`--module Init` by default; \
         transitive imports load automatically) and reports what reached \
         `Environment::get_simp_lemmas()` — the count, optionally the whole list \
         (`--list`), and a fail-closed assertion that named constants are present \
         (`--require beq_iff_eq`, repeatable; a missing name exits non-zero). \
         It reads `is_simp_lemma`/`get_simp_lemmas` and nothing else, deliberately: \
         a `simp only [name]` proof passes with an EMPTY decoded set, because \
         simp's by-name path resolves the constant with `get_const` and never \
         consults the registry. Before this verb an imported `@[simp]` entry that \
         the decoder dropped surfaced only as `simp made no progress` in a Mathlib \
         row, days later and one layer from the cause.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean olean simp-set --module Init",
            what: "count the simp lemmas Init's closure decodes",
        },
        Example {
            cmd: "clean olean simp-set --module Init --require beq_iff_eq --require Nat.add_zero",
            what: "fail closed unless both lemmas are in the decoded set",
        },
    ],
    see_also: &["olean verify-batch", "olean import-reverify-metric"],
    references: &[UNIFIED_CLI_REF, ISSUE_3436, CRATE_REF],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

const IR_CENSUS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "ir-census"],
    summary: "Decode each module's compiled Lean IR and print a per-module census",
    description: "Decodes the compiled IR Lean stores for every requested module \
         (`--closure`: the whole transitive import closure) — `Lean.IR.declMapExt` \
         from the module's main data (the `.olean.private` part of a `module`, the \
         `.olean` otherwise) and from its `.ir` file, plus the `externAttr`, \
         `implementedByAttr`, `regularInitAttr` and `builtinInitAttr` entries — exactly \
         as a root-level `private` import sees them, and prints one `MOD` row per module \
         and a `TOTAL` row in the format of the pinned-Lean oracle \
         `crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/oracle/IRCensusOracle.lean`, so `scripts/ir_census_diff.py` can \
         diff them. Every row is backed by a full decode of every declaration; one that \
         does not decode fails the command instead of being skipped. `--print-decl NAME` \
         renders matching declarations with a port of Lean's `IR.Decl` formatter.",
    category: Category::Verification,
    stability: Stability::Building,
    examples: &[
        Example {
            cmd: "clean olean ir-census Init.Prelude",
            what: "census the IR of one module",
        },
        Example {
            cmd: "clean olean ir-census --closure Init --print-decl Nat.add._boxed",
            what: "census Init's closure and render one declaration as Lean prints it",
        },
    ],
    see_also: &["olean simp-set"],
    references: &[UNIFIED_CLI_REF, ISSUE_3436, CRATE_REF],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

const REPLAY_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "replay"],
    summary: "Replay `.olean` modules through Clean's kernel with `leanchecker`'s semantics",
    description: "Replays Lean-built `.olean` modules the way the pinned toolchain's \
         `leanchecker` does (`LeanChecker.lean`, `Lean/Replay.lean`), with Clean's kernel as \
         the checker. The environment is built from `.olean` files only, in Lean's kernel \
         theory (`KernelTheory::Lean`): no Clean prelude, and before the load no \
         declaration but the kernel's quotient (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, \
         as Lean's `quotDecl` adds them, and `Quot.sound`, which Lean declares in \
         `Init.Core`). By \
         default each selected module's imports are the trusted starting environment and \
         its own declarations are replayed in Lean's order, each checked before it is \
         admitted; a declaration that refers to itself or sits on a dependency cycle is an \
         unknown constant, every stored inductive block is rebuilt by the kernel and its \
         stored constructors and recursors must equal the rebuilt ones, a redeclared name \
         is refused, and `unsafe`/`partial` constants are left out as Lean's replay leaves \
         them out. `--fresh` replays the whole import closure of one module into an \
         environment that holds no declaration but the seeded quotient. A module argument \
         selects every module it is a dotted-name prefix of (exactly the named modules \
         under `--exact`, a Clean addition for per-module sweeps, and exactly one module \
         under `--fresh`), searched on `--search-path`, then \
         `LEAN_PATH`, then the pinned toolchain's `lib/lean`. The first refusal is printed \
         with the declaration and the reason (or, for a module whose `.olean` closure could \
         not be loaded, the load error) and the exit status is 1, or 2 when every refusal \
         is only the `--max-heartbeats` budget running out; `--json` prints one record per \
         module. `--from-export FILE` reads a lean4export NDJSON export (format 3.1) strictly \
         instead, registers it in the `.olean` loader's structural tier and replays \
         every declaration it declares into an empty environment, the quotient entering \
         only through `add_quot` after `Eq`: exit 0 accepts, 1 rejects (a malformed \
         export, an inductive record that is not one block or stores `isRec`/\
         `isReflexive` flags its constructors contradict, or a refused declaration), 2 \
         declines (an unsupported format or Lean version, a resource budget, a limit of \
         Clean's representation, a level the kernel's constructors build otherwise than \
         Lean reads it, an inductive block over a rewritten level, two names stored \
         alike, a declared name Lean's kernel computes by name that Clean does not \
         compute as Lean does (an unadmitted fold head, `Lean.reduceBool`, \
         `Lean.reduceNat`), a replay that panicked, or a `partial` definition left \
         unchecked), as Lake's external kernels and the Kernel Arena read it.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean olean replay Init.Core",
            what: "replay Init.Core's own declarations over its trusted imports",
        },
        Example {
            cmd: "clean olean replay Init --keep-going --json",
            what: "replay every Init module, one JSON record per module",
        },
        Example {
            cmd: "clean olean replay --fresh Init.Prelude",
            what: "replay a module's whole closure into an environment holding only the seeded quotient",
        },
        Example {
            cmd: "clean olean replay --from-export Init.Prelude.ndjson",
            what: "replay a lean4export NDJSON export; exit 0 accepts, 1 rejects, 2 declines",
        },
    ],
    see_also: &["olean verify-batch"],
    references: &[UNIFIED_CLI_REF, ISSUE_3436, CRATE_REF],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

/// Static feature descriptor array registered by the top-level `clean` CLI.
///
/// Add new verbs here when extending `OleanCommands`; the drift tests in
/// `crates/clean-cli/tests/feature_coverage.rs` fail the build if a clap
/// path is missing from this list (or vice versa).
pub const FEATURES: &[FeatureDescriptor] = &[
    GENERATE_OVERLAY_DESC,
    VERIFY_BATCH_DESC,
    IMPORT_REVERIFY_METRIC_DESC,
    SIMP_SET_DESC,
    IR_CENSUS_DESC,
    REPLAY_DESC,
];
