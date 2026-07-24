// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors for every `clean mathverse <verb>` subcommand.
//!
//! The top-level binary registers these via
//! `v.extend(clean_mathverse::cli::FEATURES)` in `clean-cli`'s `registry.rs`.
//! Categories are `Import` — the Mathverse Library is an import/retrieval index
//! over 68+ external proof systems. Stability is `Usable`: the shard format
//! and verb surface are shipping in `mathverse-v0.9.0` (2026-04-01) but haven't
//! reached semver-stable `V1` status.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const MATHVERSE_DESIGN_REF: Reference = Reference {
    kind: RefKind::Doc,
    label: "Mathverse Library architecture",
    target: "docs/DESIGN.md#mathverse-library",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "CLI orphan inventory — mathverse_search absorption",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const UNIFIED_CLI_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3440: Reference = Reference {
    kind: RefKind::Issue,
    label: "Absorb mathverse_search into clean mathverse",
    target: "#3440",
};

const SEARCH_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "search"],
    summary: "Search Mathverse Library declarations by name or semantic type",
    description: "Searches the loaded `.mathverse` shards for declarations matching a pattern. \
         `--mode name` runs a case-insensitive substring match on declaration \
         names — fast, suitable for interactive browsing. `--mode type` runs a \
         BM25 semantic search over names and types — slower, higher recall when \
         you know what you want to prove but not its Lean 4 name. Results \
         include the source system, import confidence, and declaration kind. \
         Pass `--json` for machine-readable output.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse search Nat.add",
            what: "name-substring search for `Nat.add`",
        },
        Example {
            cmd: "clean mathverse search \"group theory\" --mode type --limit 10",
            what: "BM25 semantic search, top 10 results",
        },
    ],
    see_also: &["mathverse info", "mathverse stats", "mathverse systems"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_INVENTORY_REF,
        UNIFIED_CLI_REF,
        ISSUE_3440,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const INFO_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "info"],
    summary: "Show full details of a single Mathverse Library declaration",
    description: "Looks up a declaration by exact name and prints its header fields: \
         source system, import confidence (KernelVerified, Translated, \
         Axiomatized, …), content domain, declaration kind (theorem, \
         definition, axiom, inductive, …), trust-gate status, and axiom \
         profile bitmap. Use this after `mathverse search` to inspect a hit, or \
         when debugging trust contamination reports.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse info Nat.add_comm",
        what: "print header for `Nat.add_comm`",
    }],
    see_also: &["mathverse search", "mathverse stats"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3440],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const STATS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "stats"],
    summary: "Print aggregate statistics over the loaded Mathverse Library shards",
    description: "Counts total declarations and breaks them down by source system, \
         import confidence, content domain, and declaration kind. Also reports \
         how many declarations carry proof terms, how many are axiomatized, \
         and how many are trust-gated. Useful for capacity planning and for \
         checking a local shard set against the expected corpus profile \
         (e.g. `mathverse-v0.9.0` records 3,254,463 declarations; it does not \
         include a downloader-compatible `mathverse-library-v*.tar.zst` archive).",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse stats",
        what: "aggregate stats for the default shard dir",
    }],
    see_also: &["mathverse systems", "mathverse search"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const SYSTEMS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "systems"],
    summary: "List every source system in the Mathverse Library with counts",
    description: "Enumerates the `SourceSystem` enum variants present in the loaded \
         shards, with the number of declarations contributed by each \
         (Lean4, Coq, HOL Light, Mizar, Metamath, Agda, Idris2, F*, \
         gamma-crown, and ~60 more). Sorted by count descending. Pair with \
         `mathverse stats` for a full capacity snapshot.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse systems --json",
        what: "machine-readable system counts",
    }],
    see_also: &["mathverse stats", "mathverse search"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const REPLAY_CORPUS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "replay-corpus"],
    summary: "Generate deterministic Mathverse replay production-corpus evidence",
    description: "Scans the checked-in Mathlib/Batteries Mathverse tactic corpus and \
         writes fail-closed replay accounting as JSON. This is the Rust-owned \
         replacement for the old Python production-corpus generator; it records \
         found, rejected, unsupported, and bounded native-gate-witness obligations \
         without granting strict mathverse_use credit until a real per-obligation \
         application runner exists.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse replay-corpus --production --json --output reports/mathverse-replay-production-corpus.json",
        what: "regenerate the Mathverse replay production corpus artifact",
    }],
    see_also: &["mathverse validate-replay-report"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const REPLAY_STRICT_ATTEMPT_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "replay-strict-attempt"],
    summary: "Run the focused Mathverse strict replay attempt bridge (Experimental)",
    description: "Lowers the checked benchmark.lean:65 replay fixture into an \
         active clean proof state, verifies and loads the selected CleanNative \
         shard fixture, then invokes strict mathverse_use fail-closed. The report is \
         diagnostic replacement evidence: native-shard verification alone does \
         not grant per-obligation strict replay credit.",
    category: Category::Import,
    stability: Stability::Experimental,
    examples: &[Example {
        cmd: "clean mathverse replay-strict-attempt --line65 --json",
        what: "emit fail-closed strict mathverse_use replay attempt evidence for benchmark.lean:65",
    }],
    see_also: &[
        "mathverse replay-corpus",
        "mathverse validate-replay-report",
    ],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const VALIDATE_REPLAY_REPORT_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "validate-replay-report"],
    summary: "Validate Mathverse replay replacement report artifacts",
    description: "Checks the Mathverse replay replacement report and production corpus \
         artifact from Rust: schema, scorecard scoping, evidence paths, native-gate \
         test count, production-corpus counts, and the absence of Python wrapper \
         commands in the focused replacement gate.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse validate-replay-report --report reports/mathverse-replay-replacement.json --corpus reports/mathverse-replay-production-corpus.json --json",
        what: "machine-readable validation of Mathverse replay replacement artifacts",
    }],
    see_also: &["mathverse replay-corpus"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const STAMP_VERIFIED_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "stamp-verified"],
    summary: "Convert .olean(s), re-verify in Clean's kernel, and stamp KernelVerified on disk",
    description: "Productionizes the WS5 stamping pipeline. Converts one or more \
         `.olean` files (or directories) to `.mathverse` shards via the heuristic \
         importer — which stores zero KernelVerified — then re-verifies the merged \
         corpus in Clean's own kernel and destructively stamps `KernelVerified` into \
         the shard bytes for exactly the constants whose value passed the kernel's \
         `check_type`. The stored KernelVerified count is re-read from disk and \
         reported. Pass `--closure-root <lib/lean>` to load a target module's \
         TRANSITIVE IMPORT CLOSURE (plus sibling lake packages) into the kernel \
         environment first, so real Mathlib modules — whose proofs reference \
         imported constants — can re-check; the closure is trusted imported \
         context and is never stamped, only the target module's own decls are. \
         SOUNDNESS: only kernel-accepted names are stamped; heuristic confidence \
         is never promoted. Pure inductives may not verify under the current \
         kernel — value-bearing definitions/theorems do.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse stamp-verified Init/SimpLemmas.olean --out-dir target/stamped --json",
            what: "convert one real .olean, kernel-re-verify, and stamp KernelVerified on disk",
        },
        Example {
            cmd: "clean mathverse stamp-verified .lake/build/lib/lean/Mathlib/Logic/Basic.olean --closure-root .lake/build/lib/lean --out-dir target/stamped --json",
            what: "load a real Mathlib module's import closure, then kernel-re-verify and stamp its own decls",
        },
    ],
    see_also: &["mathverse verify", "mathverse convert"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const PER_CONSTANT_VERIFY_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "per-constant-verify"],
    summary: "Kernel-verify named constant(s) by demand-loading only their constant closure",
    description: "Kernel-verifies ONE (or a few) named constant(s) declared by \
         `--target` by demand-loading only the transitive CONSTANT closure of the \
         target — the Rust analog of Lean's `getUsedConstants` fold — into a shared \
         trusted kernel environment, then running the `add_decl`-equivalent \
         `check_type` gauntlet on the target alone. Avoids the eager reconstruction \
         of the whole module IMPORT closure (250k–429k constants) that \
         `stamp-verified --closure-root` pays even for a single leaf lemma. \
         `--all-declared` widens the run to every value-bearing constant the module \
         declares (a whole-module receipt under one Merkle root). `--kv-cache` adds \
         a content-addressed verdict cache — sound by construction: the demand walk \
         still recomputes every digest, so a hit proves byte-identical content and a \
         changed proof always re-verifies. `--receipt` mints a Merkle trust receipt \
         (P4) over the kernel-verified target(s); `--print-digests` audits \
         determinism of the demand walk. SOUNDNESS: the closure is trusted imported \
         context — only the named target(s) are kernel-checked and stamped.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse per-constant-verify --target .lake/build/lib/lean/Mathlib/Data/Real/Basic.olean --constant Real.zero_lt_one --closure-root .lake/build/lib/lean",
            what: "kernel-verify a single Mathlib lemma via its demand-loaded constant closure",
        },
        Example {
            cmd: "clean mathverse per-constant-verify --target Init/SimpLemmas.olean --all-declared --closure-root .lake/build/lib/lean --receipt target/receipt.json",
            what: "verify every value-bearing constant a module declares and mint a Merkle trust receipt",
        },
    ],
    see_also: &["mathverse stamp-verified", "mathverse trust-receipt corpus"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_IMPORT_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-import"],
    summary: "Isabelle raw-export -> corpus -> replay -> snapshot import pipeline",
    description: "Drives the Isabelle/zproof import lane end to end: assembles \
         per-theory `.jsonl` exports (the zproof capture hook's `ISA_ZPROOF_OUT`) \
         into a serial-sorted corpus file, then replays that corpus into Clean \
         state. Stage selection: `--raw-dir` runs assembly into `--corpus`; omit \
         it to replay an existing corpus; `--assemble-only` skips the replay. \
         `--snapshot-in`/`--snapshot-out` make long replays resumable — a resume \
         is refused unless the corpus is an append-only extension of the \
         snapshotted prefix (fail closed, no silent divergence). `--workers 0` \
         selects the serial streaming driver. Pathological recorded proofs are \
         cut by `--translate-budget` and honestly rejected, never silently \
         accepted.",
    category: Category::Import,
    stability: Stability::Building,
    examples: &[
        Example {
            cmd: "clean mathverse isabelle-import --raw-dir target/isa-raw --corpus target/isa-corpus.jsonl",
            what: "assemble raw per-theory exports into a corpus and replay it",
        },
        Example {
            cmd: "clean mathverse isabelle-import --corpus target/isa-corpus.jsonl --snapshot-in target/isa.snap --snapshot-out target/isa.snap",
            what: "resume a replay of an extended corpus from the previous snapshot",
        },
    ],
    see_also: &["mathverse convert", "mathverse stats"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_SLICE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-slice"],
    summary: "Extract a closure-complete replay slice from an Isabelle corpus",
    description: "Builds a serial-sorted, replay-ready corpus slice from seed \
         serials, theorem-name substrings, or reject-dump rows, then closes the \
         selection over every transitive proof dependency. Registration rows are \
         included by default so PASS-1 registries match a full grand replay; \
         `--no-registrations` is an explicit minimal-slice mode. Uses the corpus \
         index when available and fails closed on missing seeds or dependencies.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse isabelle-slice --corpus target/isa-corpus.jsonl --out target/isa-slice.jsonl --serials 83088,83089",
        what: "extract two seed proofs and their complete replay dependency closure",
    }],
    see_also: &[
        "mathverse isabelle-index",
        "mathverse isabelle-verify-one",
        "mathverse isabelle-flip-gate",
    ],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_TARGETS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-targets"],
    summary: "Rank rejected Isabelle proofs by their transitive blocking weight",
    description: "Joins a serial-sorted corpus with a completed replay snapshot \
         and ranks every rejected proof by the number of downstream proofs it \
         exclusively or jointly blocks. An optional reject dump adds the current \
         reason and signature, yielding the gatekeeper table used to prioritize \
         engine work rather than merely counting rejection families.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse isabelle-targets --corpus target/isa-corpus.jsonl --snapshot target/isa.snap --top 50",
        what: "print the fifty highest-impact rejected proof gatekeepers",
    }],
    see_also: &["mathverse isabelle-slice", "mathverse isabelle-index"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_INDEX_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-index"],
    summary: "Build the seekable sidecar index for an Isabelle replay corpus",
    description: "Scans a serial-sorted corpus once and writes its `.idx` \
         sidecar: byte offsets and lengths, theorem names, registration flags, \
         and dependency edges. Slice extraction, one-proof diagnostics, corpus \
         diffs, and target ranking use this exact sidecar to avoid repeatedly \
         scanning a multi-gigabyte corpus.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse isabelle-index --corpus target/isa-corpus.jsonl",
        what: "write target/isa-corpus.jsonl.idx for indexed corpus operations",
    }],
    see_also: &["mathverse isabelle-slice", "mathverse isabelle-corpus-diff"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_CORPUS_DIFF_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-corpus-diff"],
    summary: "Classify changes between two indexed Isabelle corpus versions",
    description: "Compares two corpora through their current `.idx` sidecars \
         and emits a typed JSON report classifying each row as unchanged, new, \
         changed, or removed. The report is the fail-closed input for incremental \
         replay: only additions and changed proofs are reconsidered against the \
         previous standing snapshot.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse isabelle-corpus-diff --old target/isa-old.jsonl --new target/isa-new.jsonl --out target/isa-diff.json",
        what: "emit the typed incremental-replay delta between two indexed corpora",
    }],
    see_also: &["mathverse isabelle-index", "mathverse isabelle-import"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_VERIFY_ONE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-verify-one"],
    summary: "Replay one Isabelle proof with full translation and kernel diagnostics",
    description: "Seeks one exact proof serial in a corpus and runs the real \
         translation and kernel-verification path with bounded, per-mode \
         diagnostics. A completed snapshot may provide the accepted environment \
         and registries; without one, the command reconstructs the minimal state \
         from the corpus. Diagnostic execution never mints a release verdict.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse isabelle-verify-one --corpus target/isa-corpus.jsonl --serial 83088 --modes --full",
        what: "diagnose one proof through every escalation mode with exact mismatch output",
    }],
    see_also: &["mathverse isabelle-slice", "mathverse isabelle-import"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_LEAN_GOAL_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-lean-goal"],
    summary: "Translate an Isabelle theorem statement into a faithful Lean 4 goal",
    description: "Reads a theorem by serial or exact name and emits a Lean 4 \
         statement only when the Path-B translation is faithful. Unsupported \
         source constructs produce an explicit unsupported verdict rather than a \
         plausible but weaker goal. Batch mode writes per-theorem stubs, curation \
         markers, and a manifest for a candidate list.",
    category: Category::Import,
    stability: Stability::Building,
    examples: &[Example {
        cmd: "clean mathverse isabelle-lean-goal --corpus target/isa-corpus.jsonl --serial 83088 --lean-name imported_goal",
        what: "translate one indexed Isabelle statement into a named Lean 4 goal",
    }],
    see_also: &["mathverse isabelle-slice", "mathverse isabelle-verify-one"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_SESSIONS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-sessions"],
    summary: "Emit checkpointed Isabelle session-ROOT fragments for the AFP capture waves",
    description: "Generates the session ROOT fragments the AFP zproof-capture \
         lane builds from (Rust port of the retired \
         `scripts/isabelle/afp_session_gen.py`; byte-identical outputs). \
         `--mode afp` emits one chained session per AFP entry (Wave A / Wave C \
         bodies), splitting any entry past `--cap` theories into checkpointed \
         sub-sessions so cumulative record_proofs=4 RSS resets per Poly/ML \
         process (the Lib3 lesson). `--mode spine` emits the six HOL-* Wave-B \
         spine capture heaps, chained per the real HOL session DAG; its source \
         is `--hol-src` or `$ISABELLE_HOME/src/HOL`, with no machine-specific \
         fallback. `--mode \
         wavec` computes the AFP-on-AFP transitive-provider closure and its \
         topological build order with assigned parent heaps (unresolved bases \
         are reported honestly, never guessed). Pure file I/O: reads AFP \
         ROOTs/theories, writes fragments + manifests; builds nothing.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse isabelle-sessions --mode afp --entries scripts/isabelle/afp_wave_a.txt --parent ZP-Lib3e --out ~/isabelle-work/zp_afp_wave_a",
            what: "emit checkpointed per-entry fragments for the Wave-A entry list",
        },
        Example {
            cmd: "clean mathverse isabelle-sessions --mode spine --hol-src /opt/Isabelle/src/HOL --out ~/isabelle-work/zp_spine",
            what: "emit the six chained HOL-* spine capture heaps for Wave B",
        },
        Example {
            cmd: "clean mathverse isabelle-sessions --mode wavec --entries scripts/isabelle/afp_wave_c_seed.txt --out ~/isabelle-work/zp_wave_c",
            what: "compute the Wave-C AFP-on-AFP topo build order and parent heaps",
        },
    ],
    see_also: &["mathverse isabelle-import"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_CAPTURE_CHAIN_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-capture-chain"],
    summary: "Self-healing driver for a chained Isabelle record_proofs capture build",
    description: "Mechanizes the three manual interventions a record_proofs \
         capture-chain backfill needs. Takes a typed JSON spec (an ordered list \
         of chained segments — session, dir, theories, parent, record_proofs — \
         plus global build opts: isabelle_home, extra -d dirs, threads, and a \
         capture collect config) and drives it end to end. `--isabelle-home` \
         portably overrides only the installation path in a reusable spec. Per \
         segment it GENERATES \
         the session ROOT from the spec (the spec is the source of truth), shells \
         out to `isabelle build -b -o record_proofs=<n> -o threads=<t>` (via \
         `nice`), and heal-recovers from the Poly/ML arm64_32 'Run out of store' \
         OOM through a response ladder: (a) retry the segment at threads=1; \
         (b) bisect its theory list into two downward-closed chained sub-sessions; \
         (c) isolate a single stubborn theory as a proofless (record_proofs=2) \
         heap-bake. Every segment heap-saves (-b) so successors never rebuild \
         predecessors. Durable JSON state is written after each transition, so \
         `--resume` continues exactly where a crash or halt left off and never \
         retries an exhausted ladder rung; `--dry` prints the plan and generated \
         ROOTs. Non-OOM failures halt loudly with the log tail (no blind retry \
         loops).",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse isabelle-capture-chain --spec scripts/isabelle/lib3_backfill_chain.spec.json --isabelle-home /opt/Isabelle --work-dir ~/isabelle-work",
            what: "run the Lib3 backfill chain, auto-recovering from any OOM",
        },
        Example {
            cmd: "clean mathverse isabelle-capture-chain --spec scripts/isabelle/lib3_backfill_chain.spec.json --dry",
            what: "print the planned segments + generated ROOTs without building",
        },
        Example {
            cmd: "clean mathverse isabelle-capture-chain --spec scripts/isabelle/lib3_backfill_chain.spec.json --resume",
            what: "resume an interrupted chain from its durable state file",
        },
    ],
    see_also: &["mathverse isabelle-sessions", "mathverse isabelle-doctor"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_DOCTOR_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-doctor"],
    summary: "Ops preflight/health checks for a fresh or busy Isabelle re-import",
    description: "Mechanizes every operational failure mode the Isabelle import \
         campaign hit, so a re-import on a fresh or busy machine fails LOUD before \
         burning hours. Checks: the running binary's embedded git SHA + build time \
         vs. repo HEAD and the newest `crates/` commit (STALE BINARY); a held \
         verify flock or running verify/import processes (CONCURRENT VERIFY, which \
         silently corrupts KV numbers); `*.sh` scripts in the ops dir referencing \
         since-deleted absolute paths, especially `.claude/worktrees/…` launchers \
         (DEAD SCRIPT REFS); a corpus `.jsonl` vs. its `.idx` sidecar (line count / \
         stored size / serial range); a snapshot's ENV-LAYOUT fingerprint vs. this \
         binary (LayoutDrift); any path under `/tmp` (the macOS temp cleaner \
         destroys corpora); and free disk headroom on the ops volume. Exits nonzero \
         on any FAIL; `--json` emits a machine-readable report.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse isabelle-doctor",
            what: "preflight the default ops dir (~/isabelle-work) before a grand run",
        },
        Example {
            cmd: "clean mathverse isabelle-doctor --corpus target/isa-corpus.jsonl --snapshot target/isa.snap --json",
            what: "check a specific corpus/index + snapshot and emit a JSON report",
        },
    ],
    see_also: &["mathverse isabelle-import", "mathverse isabelle-index"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_SNAPSHOT_PRESERVE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-snapshot-preserve"],
    summary: "Copy the current binary into a durable SHA-named dir to keep a snapshot resumable",
    description: "A replay snapshot only loads under a binary whose ENV-LAYOUT \
         matches the one that wrote it (upstream kernel serde churn silently \
         invalidates the pairing), so a snapshot is only durably resumable if the \
         exact building binary is kept. This copies the CURRENT running binary \
         (`current_exe`) into `--binaries-dir` named `clean-<sha>` — one command \
         instead of the manual `cp` dance — and reports the snapshot↔binary \
         pairing (MATCH/MISMATCH/UNVERIFIABLE) from the snapshot's \
         `<snap>.provenance.json` sidecar. Limitation: it copies `current_exe`, so \
         under a `cargo test`/integration harness it copies the TEST binary; copy \
         the real release harness manually in that case.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse isabelle-snapshot-preserve --snapshot ~/isabelle-work/isa.snap --binaries-dir ~/isabelle-work/binaries",
        what: "copy the running clean binary to ~/isabelle-work/binaries/clean-<sha> and report the pairing",
    }],
    see_also: &["mathverse isabelle-doctor", "mathverse isabelle-import"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ISABELLE_FLIP_GATE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "isabelle-flip-gate"],
    summary: "Corpus-routing-verify every claimed Isabelle flip, before a grand",
    description: "Closes the gap that burned a 29-hour grand: fixture tests \
         proved a prover/discharge arm worked, but at corpus scale the escalation \
         never routed the target serials to it — the claimed flips silently did \
         not happen, discovered only after the grand. A flip gate pins a durable, \
         closure-complete SLICE (the target serial plus its transitive proof \
         dependencies, with corpus registration lines so the PASS-1 registries \
         match the grand — the same slice `isabelle-slice` extracts) and \
         `--check` replays it through the REAL library stream-verify driver (the \
         same one `isabelle-import` drives, never a subprocess), asserting the \
         pinned serial lands `KernelVerified`. A bounded per-serial replay — \
         orders of magnitude cheaper than a whole-corpus grand. It reports \
         PASS/FAIL per gate and exits nonzero on any FAIL. Slices are too large \
         to commit and live under \
         `~/isabelle-work/corpora/flip_gates/`; the committed registry \
         (`data/isabelle_flip_gates.json`) pins each slice's blake3 + line count \
         so drift is caught, never silently replayed. `--add --corpus <c> --serial \
         <s>` builds the slice, confirms it flips under the current binary, pins \
         it, and appends the entry. Acquires the machine verify lock for the \
         replay and WAITS on a sibling-held lock rather than bypassing.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse isabelle-flip-gate --check",
            what: "replay every registered gate and assert each serial KernelVerifies (pre-grand gate)",
        },
        Example {
            cmd: "clean mathverse isabelle-flip-gate --add --corpus ~/isabelle-work/corpora/main_v3.jsonl --serial 83088 --description \"eq_ac flip\" --round eq-ac",
            what: "build+verify+register a flip gate for a serial that now KernelVerifies",
        },
    ],
    see_also: &["mathverse isabelle-slice", "mathverse isabelle-import"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const TRUST_RECEIPT_BUILD_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "trust-receipt", "build"],
    summary: "(Re)build a Merkle trust receipt from a published leaves manifest",
    description: "Rebuilds the receipt JSON (root hash, leaf count, axiom closure, \
         within-TCB claim) from an auditable `(name, content_hash)` leaves \
         manifest, e.g. one minted by `per-constant-verify --receipt-leaves`. \
         Deterministic: the same leaves always re-derive the same root, so a \
         receipt lost or held back from publication can be reconstructed by \
         anyone holding the manifest. A commitment to what the kernel accepted — \
         NOT a verification shortcut: building never re-checks proofs.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse trust-receipt build --leaves target/receipt-leaves.json --source-id Mathlib@abc123 --out target/receipt.json",
            what: "re-derive the receipt from its published leaves manifest",
        },
    ],
    see_also: &[
        "mathverse trust-receipt verify",
        "mathverse trust-receipt merge",
        "mathverse per-constant-verify",
    ],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const TRUST_RECEIPT_VERIFY_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "trust-receipt", "verify"],
    summary: "Independently re-derive a receipt's root from its leaves and confirm every claim",
    description: "The auditor's verb: independently recomputes the Merkle root from \
         the leaves manifest and confirms every claim the receipt makes — root \
         hash, leaf count, axiom closure, within-TCB verdict. Fails closed on any \
         mismatch. Requires only the receipt + leaves JSON (no `.olean` tree, no \
         kernel run), so a third party can audit a published certification \
         without the corpus that produced it.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse trust-receipt verify --receipt target/receipt.json --leaves target/receipt-leaves.json",
            what: "re-derive the root and fail closed on any claim mismatch",
        },
    ],
    see_also: &["mathverse trust-receipt build", "mathverse trust-receipt prove"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const TRUST_RECEIPT_PROVE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "trust-receipt", "prove"],
    summary: "Emit + self-check an O(log N) Merkle membership proof for one named theorem",
    description: "Produces a compact membership proof that a single fully-qualified \
         declaration's `(name, content_hash)` leaf is under a receipt's root — \
         the sibling-hash path from leaf to root, O(log N) in corpus size — and \
         self-checks it before emitting. Lets a consumer confirm one theorem is \
         covered by a corpus certification without downloading or re-hashing the \
         full leaves manifest.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse trust-receipt prove --receipt target/receipt.json --leaves target/receipt-leaves.json --name Real.zero_lt_one --out target/membership.json",
            what: "mint and self-check a membership proof for one declaration",
        },
    ],
    see_also: &["mathverse trust-receipt verify", "mathverse trust-receipt build"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const TRUST_RECEIPT_MERGE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "trust-receipt", "merge"],
    summary: "Merge per-module leaves manifests into ONE whole-corpus receipt",
    description: "Unions many per-module leaves manifests into a single \
         whole-corpus receipt: the union of all `(name, content_hash)` leaves \
         under one root, the union axiom closure, complete iff every input is \
         complete. This is the composable path to a `Mathlib@<sha> -> root` \
         artifact — run `per-constant-verify --all-declared` per module (in \
         parallel, on separate machines if desired), then merge the manifests.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse trust-receipt merge --leaves mod1-leaves.json --leaves mod2-leaves.json --source-id Mathlib@abc123 --out corpus-receipt.json",
            what: "union two per-module manifests into one corpus receipt",
        },
    ],
    see_also: &[
        "mathverse trust-receipt corpus",
        "mathverse per-constant-verify",
        "mathverse trust-receipt build",
    ],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const TRUST_RECEIPT_CORPUS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "trust-receipt", "corpus"],
    summary: "End-to-end library certification: kernel-verify every module under a directory into one receipt",
    description: "The turnkey `Mathlib@<sha> -> root, N decls, axioms ⊆ TCB` \
         artifact: recursively scans `--modules-dir`, kernel-verifies EVERY \
         value-bearing constant of EVERY module (the `--all-declared` \
         per-constant path, demand-loading each module's constant closure from \
         `--closure-root`), then unions everything into ONE corpus receipt with \
         a provenance record. `--checkpoint` makes long runs resumable — \
         already-verified modules replay from the checkpoint instead of \
         re-checking. `--limit` bounds the module count for smoke runs. \
         SOUNDNESS: every certified leaf passed the kernel's `check_type`; \
         imported closure context is trusted but never certified.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse trust-receipt corpus --modules-dir .lake/build/lib/lean/Mathlib --closure-root .lake/build/lib/lean --source-id Mathlib@abc123 --out corpus-receipt.json --checkpoint target/corpus.ckpt",
            what: "kernel-verify an entire library into one resumable corpus receipt",
        },
    ],
    see_also: &[
        "mathverse trust-receipt merge",
        "mathverse per-constant-verify",
        "mathverse stamp-verified",
    ],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const TRUST_RECEIPT_FROM_SHARDS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "trust-receipt", "from-shards"],
    summary: "Build a receipt directly from a stamped .mathverse shard directory",
    description: "The Mathverse-native path: certifies exactly the constants a \
         stamped shard directory (e.g. a `stamp-verified --out-dir`) marked \
         `KernelVerified`, reading their content + axiom closure straight from \
         the shard bytes — no re-verification, no `.olean` re-walk. Emits the \
         receipt, the auditable union leaves manifest, and the provenance \
         record. SOUNDNESS: trusts the shards' stamps (which only \
         kernel-accepted names ever receive); constants without the stamp are \
         never certified.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse trust-receipt from-shards --shard-dir target/stamped --source-id Mathlib@abc123 --out target/receipt.json --out-leaves target/leaves.json",
            what: "certify a stamped shard directory into a receipt without re-verifying",
        },
    ],
    see_also: &["mathverse stamp-verified", "mathverse trust-receipt build"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const BUILD_CLOSURE_SHARDS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "build-closure-shards"],
    summary: "Build the v3 fail-closed closure-shard cache for fast lazy re-import",
    description: "Builds the v3 fail-closed `.mathverse` closure-shard cache that \
         a later `stamp-verified --closure-root` re-import serves LAZILY from \
         mmap'd shards instead of eagerly reconstructing the whole `.olean` \
         import closure. Converts every module in `--target`'s transitive import \
         closure (the target itself is EXCLUDED — its decls are re-minted by the \
         replay) into one shard each under `--out`, resolved against \
         `--closure-root` exactly as the eager loader resolves them. Each shard \
         is bound to its source `.olean` by a blake3 digest and carries a \
         per-constant reconstruction digest, so a stale, foreign, or corrupt \
         cache fails the load-time gate and forces the trusted eager fallback — \
         the cache can never serve a wrong verdict. Point a later run's \
         `--closure-shards <out>` here, or place it at the auto-discovered \
         `<out-dir>/../.clean-closure-shards` sibling so no env vars are needed. \
         `--closure-elide` is recorded for parity but the shards are \
         policy-independent (elision is a load-time memory cap).",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse build-closure-shards .lake/build/lib/lean/Mathlib/Logic/Basic.olean --closure-root .lake/build/lib/lean --out target/stamped/.clean-closure-shards",
            what: "build the lazy closure cache for one Mathlib module's import closure",
        },
        Example {
            cmd: "clean mathverse build-closure-shards Init/SimpLemmas.olean --closure-root .lake/build/lib/lean --out /tmp/closure-cache",
            what: "build a reusable closure cache to point a later `stamp-verified --closure-shards` at",
        },
    ],
    see_also: &["mathverse stamp-verified"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const BUILD_LIBRARY_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "build-library"],
    summary: "Build a Mathverse Library archive from configured upstream sources",
    description: "Orchestrates the complete pipeline that produces a \
         downloader-compatible `mathverse-library-v*.tar.zst` release: \
         verifies/installs prereqs (git, cargo, b3sum, zstd), clones the \
         upstream proof system sources configured in `data/mathverse_sources.toml` \
         (including Lean 3 mathlib3 — note \
         that Lean 3 import is text-based and does not require a Lean 3 \
         toolchain), runs `mathverse_convert all` to produce `.mathverse` shards, \
         packages them with a fresh blake3 manifest, and optionally publishes \
         the archive + manifest to a GitHub Release. Each stage is \
         independently skippable via `--skip-*` flags so the command supports \
         partial rebuilds (e.g. re-package an existing shard tree, or publish \
         an already-packaged archive). See \
         [docs/MATHVERSE_RELEASE_PROCESS.md](docs/MATHVERSE_RELEASE_PROCESS.md) for \
         the underlying workflow.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse build-library",
            what: "configured-source pipeline: prereqs → download → convert → package (no publish)",
        },
        Example {
            cmd: "clean mathverse build-library --skip-download --skip-convert",
            what: "re-package an existing shard tree at /tmp/mathverse-data",
        },
        Example {
            cmd: "clean mathverse build-library --auto-install-prereqs --publish --tag mathverse-v1.2.0",
            what: "install missing prereqs, build, and publish to mathverse-v1.2.0",
        },
    ],
    see_also: &["mathverse download", "mathverse verify", "mathverse release"],
    references: &[MATHVERSE_DESIGN_REF, UNIFIED_CLI_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const GRADUATE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "graduate"],
    summary: "Graduate kernel-verified project theorems into a Cake-tagged shard (Experimental)",
    description:
        "Experimental. Runs the graduation intake gate — the only front door from project-side \
         proofs into the Mathverse corpus. For each candidate the gate \
         (1) replays the declaration through a fresh kernel environment via \
         the real `add_decl` path (a theorem is stamped KernelVerified only \
         when the kernel re-checks it WITH its proof value); \
         definition-valued dependencies are carried under the same kernel \
         discipline — re-checked with their defining values, in dependency \
         order, and recorded in the record's carried_definitions section — \
         and value-less inductive-family carriers (structures, classes, \
         quotient raw types) are carried through the kernel's full checked \
         `add_inductive` replay (positivity, universes, recursor generation; \
         single-type non-nested families only) and recorded in the record's \
         carried_inductives section, and theorem-valued dependencies are \
         carried under the exact candidate discipline (re-checked WITH their \
         proof values, recorded in the record's carried_theorems section as \
         supporting material — never counted as graduated, and exempt from \
         the on-duplicate policy: their baseline novelty is recorded \
         honestly, e.g. `duplicate` for carried mathlib lemmas), \
         (2) computes the transitive axiom closure — which includes carried \
         definitions' and theorems' closures and, for families, the union \
         over all member types — and rejects anything outside \
         FOUNDATIONAL_AXIOMS (non-foundational closures are recorded as \
         AxiomDependent, never laundered), (3) dedups against the pinned \
         baseline corpus by name + canonical statement hash, and (4) writes a \
         `SourceSystem::Cake` shard whose provenance is digest-bound to a \
         `mathverse-graduation-v3.1` JSON record (legacy v3/v2/v1 records \
         remain verifiable). The produced shard is immediately re-verified through \
         the cake gate (`shard_verify::cake_gate`), which is also what makes \
         hand-rolled Cake shards fail library verification. Accepted AND \
         rejected candidates are both recorded for audit.",
    category: Category::Proof,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean mathverse graduate \
                  --project tests/fixtures/graduation/pilot/math-project.json \
                  --env native --candidates NNVerify.Rat.min_le_max \
                  --baseline data/mathverse-shards --out /tmp/graduated --json",
            what: "graduate one native-pipeline theorem against the local shard baseline",
        },
        Example {
            cmd: "clean mathverse graduate \
                  --project tests/fixtures/graduation/pilot/math-project.json \
                  --env native --all \
                  --baseline-index /tmp/mathverse-v1.2.0.mvix \
                  --baseline-release mathverse-v1.2.0 --out /tmp/graduated --json",
            what: "pin the full release corpus via a prebuilt baseline index (seconds, not hours)",
        },
    ],
    see_also: &[
        "mathverse index-build",
        "mathverse verify",
        "mathverse stats",
        "mathverse info",
    ],
    references: &[MATHVERSE_DESIGN_REF, UNIFIED_CLI_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const INDEX_BUILD_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "index-build"],
    summary: "Build a persistent novelty-baseline index over a release's shards (Experimental)",
    description:
        "Experimental. Scans a `.mathverse` release directory (or a single shard) once and \
         writes a flat `MVBIDX01` index: sorted unique declaration names plus \
         sorted 16-byte statement-hash prefixes, each mapped to the first \
         baseline name carrying that statement. Statement hashes use the SAME \
         canonical primitive the graduation gate compares \
         (`expr_canonical_digest` over the shard-reconstruction path), so \
         `graduate --baseline-index` answers exactly the novelty question \
         `--baseline` would — in microsecond binary-search lookups after a \
         seconds-scale load, instead of the ~10ms/constant full re-scan \
         (>=16h for the 5.77M-declaration mathverse-v1.2.0 release). The file \
         carries a versioned header, the blake3 corpus digest used for the \
         graduation record's corpus pin, and a blake3 self-digest; the loader \
         fail-closes on any corruption. `--check-sample N` re-derives N \
         statement hashes per shard through the independent per-constant scan \
         and fails if the index disagrees.",
    category: Category::Proof,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean mathverse index-build _mathverse-artifacts/mathverse-v1.2.0 \
                  -o /tmp/mathverse-v1.2.0.mvix --check-sample 2 --json",
            what: "index a full release with a 2-constants-per-shard independent spot check",
        },
        Example {
            cmd: "clean mathverse index-build data/mathverse-shards -o /tmp/local-shards.mvix",
            what: "index the local shard directory",
        },
    ],
    see_also: &["mathverse graduate", "mathverse verify"],
    references: &[MATHVERSE_DESIGN_REF, UNIFIED_CLI_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const INDEX_TREE_SCORE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "index-tree-score"],
    summary: "Kernel-confirmed tree-score / uniqueness probe over verified shards (Experimental)",
    description: "Experimental. Over a directory of `stamp-verified` `.mathverse` shards \
         (KernelVerified stamps), computes the KERNEL-CONFIRMED tree-score: each \
         KernelVerified declaration's type is reduced to its defeq tree-signature \
         (Cake `defeq_canonical_digest` — kernel `whnf` β/η/δ/ι/ζ/proj under a \
         fuel bound, then commutative-operand canonicalisation) and bucketed by \
         that signature. Two distinct declarations whose signatures collide but \
         whose structural digests differ are a 'same object, different form' \
         candidate; EVERY such candidate is then CONFIRMED with the kernel \
         `is_def_eq` arbiter (Cake `same_object`) before it is reported. \
         SOUNDNESS: the tree-signature is a one-directional bucketing key, never \
         a sameness claim — only kernel-confirmed pairs are reported as hits, and \
         shards/stamps are never modified. The report also carries the MVBIDX01 \
         stats (name/statement-hash/semantic counts, corpus digest) built over \
         the same shard dir, so the verified corpus's unique-index and \
         kernel-confirmed tree-score land together.",
    category: Category::Proof,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean mathverse index-tree-score /tmp/ws12-stamped \
                  --out reports/ws12-tree-score-index.json --json",
            what: "score a stamp-verified shard dir and write the MVBIDX + kernel-confirmed hits",
        },
        Example {
            cmd: "clean mathverse index-tree-score /tmp/ws12-stamped --fuel 50000 --max-hits 64",
            what: "human-readable tree-score with a custom whnf fuel and hit cap",
        },
    ],
    see_also: &[
        "mathverse index-build",
        "mathverse stamp-verified",
        "mathverse graduate",
    ],
    references: &[MATHVERSE_DESIGN_REF, UNIFIED_CLI_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const GRADUATION_RECORD_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "graduation-record"],
    summary: "Project a full graduation record + shard into the compact git record (Experimental)",
    description: "Experimental. Reads a full `mathverse-graduation-v3.x` `.graduation.json` and \
         its produced `.mathverse` shard and emits the COMPACT \
         `mathverse-graduation-record-v1` JSON — the single ~1-2 KB git artifact \
         in the 3-layer storage model (`designs/2026-06-24-graduation-storage-\
         and-distribution.md`). The compact record preserves every trust-bearing \
         field VERBATIM — per-theorem name, the human-readable statement \
         (reconstructed from the shard's own type encoding, so it is the literal \
         claim the kernel re-checked), universe level params, the transitive \
         axiom closure, and the `expr_canonical_digest`-grade novelty digest plus \
         novelty verdict — alongside the gate verdict (kernel-verified, \
         foundational, cake round-trip, violations), the carried-closure COUNTS \
         (definitions / inductives / theorems — not the multi-MB dumps), \
         provenance, and the shard's blake3 + byte length as the content-address \
         pin of the heavy Layer-2 artifact. It is a PURE PROJECTION: it \
         transcribes the gate's already-decided verdict and recomputes only the \
         shard's blake3 (a content check) — it never re-runs the kernel, the \
         gate, or any proof. Writes to `--out` (creating parent dirs) or to \
         stdout when `--out` is omitted.",
    category: Category::Proof,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean mathverse graduation-record \
                  --from data/graduation/nat-fib-sum-sq/nat-fib-sum-sq-graduated.graduation.json \
                  --shard data/graduation/nat-fib-sum-sq/nat-fib-sum-sq-graduated.mathverse \
                  --out data/graduation/nat-fib-sum-sq/nat-fib-sum-sq.record.json",
            what: "project a full graduation record + shard into the compact git record.json",
        },
        Example {
            cmd: "clean mathverse graduation-record \
                  --from /tmp/graduated/foo-graduated.graduation.json \
                  --shard /tmp/graduated/foo-graduated.mathverse",
            what: "print the compact record to stdout (no --out)",
        },
    ],
    see_also: &["mathverse graduate", "mathverse verify"],
    references: &[MATHVERSE_DESIGN_REF, UNIFIED_CLI_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const AXIOM_AUDIT_RELEASE_CHECK_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "axiom-audit", "release-check"],
    summary: "Non-mutating release-check for the checked-in axiom audit evidence",
    description: "Runs the two axiom-audit invariant lanes (aggregate consistency for \
         `data/axiom_audit.json`, and live row reconciliation + constructive-claim \
         closure) without mutating any reports. Fails closed when aggregates are \
         stale, when per-conjecture rows drift against live kernel output, or when \
         an unsupported `proof_mechanism: constructive` claim appears. On success \
         writes `reports/axiom-audit-launch-evidence.json`; the evidence file is \
         cleared at startup so a failed or interrupted run cannot leave an old \
         passing artifact behind.\n\n\
         Delegates execution to `scripts/axiom_audit_release_check.sh` so the \
         single source of truth for the two-lane gate stays in `scripts/`. The \
         Rust entry point exists so the workflow participates in the unified CLI \
         feature index. Part of the bucket-B script consolidation (Wave 87, see \
         `docs/SCRIPTS_MIGRATION.md`).",
    category: Category::Proof,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse axiom-audit release-check",
        what: "run the two-lane axiom-audit release gate and write evidence JSON",
    }],
    see_also: &["mathverse stats", "kernel verify-constructive-claims"],
    references: &[MATHVERSE_DESIGN_REF, UNIFIED_CLI_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const RATCHET_CHECK_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "ratchet", "check"],
    summary: "Check a stamp-verified summary against the KernelVerified-count ratchet",
    description: "Monotonic-UP guardrail over a saved `clean mathverse stamp-verified \
         --json` summary. SKIPs green (exit 0) when the summary is absent, so dev \
         pushes stay green until an operator stamps the real corpus under the \
         memory governor. When present, fails closed if `heuristic_kernel_verified \
         != 0` (the soundness floor — the heuristic converter must never mint \
         KernelVerified), if the summary is malformed, or if `kernel_verified` / \
         `stored_kernel_verified` regressed below the baseline in \
         `data/mathlib_kv_ratchet.json`. Pure read + integer comparison — never \
         touches the kernel or a shard byte, so it can only turn the gate RED, \
         never promote a constant. Subsumes the retired \
         `scripts/check_kv_ratchet.py`.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse ratchet check --summary data/last_stamp_summary.json --json",
        what: "compare a saved stamp summary against the ratchet baseline (JSON)",
    }],
    see_also: &["mathverse ratchet update", "mathverse stamp-verified"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const RATCHET_UPDATE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "ratchet", "update"],
    summary: "Raise the KernelVerified-count ratchet baseline from a stamp summary",
    description: "Raises `data/mathlib_kv_ratchet.json` from a saved `clean mathverse \
         stamp-verified --json` summary. Unlike `ratchet check`, REQUIRES the \
         summary (fails closed when absent rather than skipping) and re-asserts \
         the same `heuristic_kernel_verified == 0` soundness floor so an unsound \
         run can never be ratcheted. Rewrites the baseline JSON \
         (`kernel_verified_baseline`, `stored_kernel_verified_baseline`, \
         date-only `last_updated`) while preserving the existing operator \
         `notes`. Subsumes `scripts/check_kv_ratchet.py --update`.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse ratchet update --summary data/last_stamp_summary.json",
        what: "raise the ratchet baseline from a real corpus stamp summary",
    }],
    see_also: &["mathverse ratchet check", "mathverse stamp-verified"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const ELISION_GATE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "elision-gate"],
    summary: "Enforce KV(opaque) subset-of KV(opaque-and-theorem) across two manifests",
    description: "Elision soundness gate over two `KernelVerifiedManifest` JSON files \
         produced by stamping the SAME fixed module set under `--closure-elide \
         opaque` and `--closure-elide opaque-and-theorem`. The `opaque-and-theorem` \
         policy is NOT statically sound (theorems can be δ-unfolded), so its only \
         safe contract is that it may ADD KernelVerified constants relative to the \
         statically-sound `opaque` floor — never DROP one. Fails (naming the \
         offenders) if any constant the opaque run kernel-verified is missing from \
         the opaque-and-theorem run. The positional order encodes the soundness \
         direction (opaque first = the floor) and must not be swapped. Fail-closed \
         on a missing/bad manifest. Subsumes the retired \
         `scripts/check_kv_elision_subset.py`.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse elision-gate data/kv_elision_opaque.json data/kv_elision_oat.json",
        what: "fail closed if opaque-and-theorem dropped a KernelVerified constant opaque kept",
    }],
    see_also: &["mathverse stamp-verified", "mathverse fingerprint"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const FINGERPRINT_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "fingerprint"],
    summary: "Print the recorded reproducibility StampEnvFingerprint from a manifest",
    description: "Prints the `env_fingerprint` a `clean mathverse stamp-verified \
         --manifest` run recorded in a `KernelVerifiedManifest`: the \
         verification-env knobs (kernel version, toolchain, heartbeat, \
         elision policy, max-closure-modules ceiling, prelude variant) a \
         KernelVerified verdict is only reproducible against. Pure recorded \
         metadata — nothing in the verify/stamp path reads it back, so printing \
         it can never raise or lower a verdict. Fails closed if the manifest \
         carries no fingerprint (a legacy manifest written before the field \
         existed). Pass `--json` for machine-readable output.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse fingerprint reports/kv-manifest.json --json",
        what: "print a manifest's recorded reproducibility env fingerprint as JSON",
    }],
    see_also: &["mathverse stamp-verified", "mathverse elision-gate"],
    references: &[MATHVERSE_DESIGN_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const PACKAGE_MANAGER_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Mathverse — package manager for math",
    target: "designs/2026-06-13-mathverse-package-manager-for-math.md",
};

const UPLOAD_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "upload"],
    summary: "Publish a local corpus to a release, GCS bucket, or (indirectly) a server",
    description: "Pushes a local `.mathverse` corpus directory to a distribution \
         destination, preserving content-addressing and the blake3 manifest. \
         `--to release:<tag>` packages the corpus into a \
         `mathverse-library-v*.tar.zst` with a fresh manifest and publishes it \
         as a GitHub Release asset (`gh`). `--to gcs:<bucket/path>` writes a \
         fresh manifest then `gcloud storage rsync`s the shards + baseline.mvix \
         + manifest to a bucket. `--to server:<url>` is intentionally indirect — \
         the server holds no signing key and exposes no bulk-ingest endpoint, so \
         it prints how to publish via a release/bucket the server reads. \
         `--version <V>` is required.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse upload data/mathverse-library --to release:mathverse-v1.3.0 --version 1.3.0",
        what: "package the corpus and publish it as a GitHub Release asset",
    }],
    see_also: &["mathverse download", "mathverse release", "mathverse verify"],
    references: &[MATHVERSE_DESIGN_REF, PACKAGE_MANAGER_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const SERVE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "serve"],
    summary: "Turnkey distribution server over a local Mathverse Core",
    description: "Starts the read-only Mathverse distribution server over a located Core. \
         Locates the Core (`--core`, else `$MATHVERSE_CORE_DIR` / \
         `$MATHVERSE_LIBRARY_PATH` / `./data/mathverse-library` / \
         `$HOME/.mathverse/library`), ensures the `baseline.mvix` novelty index \
         exists (building it from the shards if missing), prints a one-line \
         corpus summary plus the local URL, and serves \
         `/stats` `/search` `/shards` `/manifest` `/theorem/{name}` \
         `/download/{shard}`. `--port` selects the bind port; `--download-base` \
         302-redirects shard downloads to a CDN/bucket host. Errors with a \
         download hint when no Core is found.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse serve --core data/mathverse-library --port 8080",
        what: "serve the local Core on http://127.0.0.1:8080",
    }],
    see_also: &["mathverse download", "mathverse stats"],
    references: &[MATHVERSE_DESIGN_REF, PACKAGE_MANAGER_REF, ISSUE_3436],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

/// Static feature descriptor array registered by the top-level `clean` CLI.
///
/// Add new verbs here when extending `MathverseCommands`; the drift tests in
/// `crates/clean-cli/tests/feature_coverage.rs` fail the build if a clap
/// path is missing from this list (or vice versa).
pub const FEATURES: &[FeatureDescriptor] = &[
    SEARCH_DESC,
    INFO_DESC,
    STATS_DESC,
    SYSTEMS_DESC,
    REPLAY_CORPUS_DESC,
    // REPLAY_STRICT_ATTEMPT_DESC is omitted from the registry because the
    // corresponding `MathverseCommands::ReplayStrictAttempt` clap variant has
    // not been wired up. The descriptor remains as documentation of the
    // intended verb; restore this entry once the clap binding lands.
    VALIDATE_REPLAY_REPORT_DESC,
    STAMP_VERIFIED_DESC,
    PER_CONSTANT_VERIFY_DESC,
    ISABELLE_IMPORT_DESC,
    ISABELLE_SLICE_DESC,
    ISABELLE_TARGETS_DESC,
    ISABELLE_INDEX_DESC,
    ISABELLE_CORPUS_DIFF_DESC,
    ISABELLE_VERIFY_ONE_DESC,
    ISABELLE_LEAN_GOAL_DESC,
    ISABELLE_SESSIONS_DESC,
    ISABELLE_CAPTURE_CHAIN_DESC,
    ISABELLE_DOCTOR_DESC,
    ISABELLE_SNAPSHOT_PRESERVE_DESC,
    ISABELLE_FLIP_GATE_DESC,
    TRUST_RECEIPT_BUILD_DESC,
    TRUST_RECEIPT_VERIFY_DESC,
    TRUST_RECEIPT_PROVE_DESC,
    TRUST_RECEIPT_MERGE_DESC,
    TRUST_RECEIPT_CORPUS_DESC,
    TRUST_RECEIPT_FROM_SHARDS_DESC,
    BUILD_CLOSURE_SHARDS_DESC,
    BUILD_LIBRARY_DESC,
    GRADUATE_DESC,
    INDEX_BUILD_DESC,
    INDEX_TREE_SCORE_DESC,
    GRADUATION_RECORD_DESC,
    AXIOM_AUDIT_RELEASE_CHECK_DESC,
    RATCHET_CHECK_DESC,
    RATCHET_UPDATE_DESC,
    ELISION_GATE_DESC,
    FINGERPRINT_DESC,
    UPLOAD_DESC,
    SERVE_DESC,
];

const _REPLAY_STRICT_ATTEMPT_DESC_RESERVED: &FeatureDescriptor = &REPLAY_STRICT_ATTEMPT_DESC;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_every_descriptor_has_an_example() {
        for d in FEATURES {
            assert!(
                !d.examples.is_empty(),
                "descriptor `{}` must have ≥1 example",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_descriptor_paths_are_unique() {
        let mut seen = std::collections::HashSet::new();
        for d in FEATURES {
            let p = d.path_display();
            assert!(seen.insert(p.clone()), "duplicate path `{p}`");
        }
    }

    #[test]
    fn test_every_descriptor_points_to_mathverse_root() {
        for d in FEATURES {
            assert_eq!(
                d.path[0],
                "mathverse",
                "descriptor `{}` must live under `mathverse`",
                d.path_display()
            );
        }
    }
}
