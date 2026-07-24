// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

macro_rules! proof_state_feature {
    ($path:expr, $summary:expr, $example:expr) => {
        FeatureDescriptor {
            path: $path,
            summary: $summary,
            description: "Experimental typed proof-state v2 command surface for math projects. The current CLI implementation exposes honest fail-closed adapters for operations that require persistent server-backed proof-state storage and tactic lifecycle integration.",
            category: Category::Dev,
            stability: Stability::Experimental,
            examples: &[Example {
                cmd: $example,
                what: "parse the proof-state v2 command shape and emit the current adapter report",
            }],
            see_also: &["math obligation open", "server"],
            references: &MATH_REFS,
            domain_root: Some("math"),
            alternative_forms: &[],
            feature_gate: None,
        }
    };
}

macro_rules! proof_state_server_feature {
    ($path:expr, $summary:expr, $example:expr) => {
        FeatureDescriptor {
            path: $path,
            summary: $summary,
            description: "Experimental typed proof-state v2 command surface for math projects. Pass `--server HOST:PORT`, or set `CLEAN_PROOF_STATE_SERVER`/`CLEAN_SERVER`, to route the command to a persistent `clean server` JSON-RPC session; without a server address, the CLI emits the existing fail-closed adapter report.",
            category: Category::Dev,
            stability: Stability::Experimental,
            examples: &[Example {
                cmd: $example,
                what: "use a proof-state id from persistent `open-obligation` against the same server",
            }],
            see_also: &["math proof-state open-obligation", "server"],
            references: &MATH_REFS,
            domain_root: Some("math"),
            alternative_forms: &[],
            feature_gate: None,
        }
    };
}

pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["math", "project", "status"],
        summary: "Print status for a manifest-driven math proof project (Experimental)",
        description: "Loads a strict `clean-math-project-v1` manifest, validates schema, domain profile, theorem-pack paths, obligation sources, artifact formats, and trust policy, then emits deterministic project status for agents and CI. The report includes load diagnostics and project-local replay cache roots, index status, and report status when cache metadata is present.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math project status --project tests/fixtures/math_project/sat_pb/project.json --json",
            what: "validate the SAT/PB pilot project manifest and emit JSON status",
        }],
        see_also: &[
            "math project hygiene",
            "math project dashboard",
            "math issue-plan",
            "factory theorem-index",
        ],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "project", "init"],
        summary: "Write a starter math proof project manifest (Experimental)",
        description: "Creates a strict starter manifest for a built-in domain profile. Use `--layout manifest` to write only the manifest at `--output`, or `--layout full` to create a starter project directory with manifest, theorem-pack, obligation, artifact, and replay-cache subdirectories.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math project init --domain sat-pb --output /tmp/clean-math-project.json --layout manifest --json",
                what: "write a SAT/PB starter manifest",
            },
            Example {
                cmd: "clean math project init --domain nn-verify --output /tmp/clean-math-project --layout full --json",
                what: "scaffold an NN verification project directory layout",
            },
        ],
        see_also: &["math profile inspect", "math project status"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "project", "hygiene"],
        summary: "Run math project hygiene checks (Experimental)",
        description: "Checks manifest validity, trust-policy shape, artifact replay policy, referenced project paths, and project-local replay cache reports. The report uses stable violation codes suitable for filing issues.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math project hygiene --project tests/fixtures/math_project/nn_verify/project.json --json",
            what: "run hygiene checks for the NN verification pilot project",
        }],
        see_also: &["math project status", "math issue-plan"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "project", "dashboard"],
        summary: "Summarize math project obligations, replay, and hygiene (Experimental)",
        description: "Read-only dashboard slice for manifest-driven math projects. It summarizes obligation counts and fingerprints, replay cache roots and statuses, and hygiene blockers without writing reports or mutating the project.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math project dashboard --project tests/fixtures/math_project/sat_pb/project.json --json",
            what: "emit a read-only project dashboard summary for agents and CI",
        }],
        see_also: &["math project status", "math project hygiene", "math artifact replay"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "profile", "inspect"],
        summary: "Inspect a math domain profile (Experimental)",
        description: "Prints the semantic heads, normalizers, tactic recommendations, artifact formats, replay adapter registry descriptors and statuses, certificate extractors, ranking signals, blocker kinds, and the profile-derived tactic/normalizer plan for a built-in or project-local domain profile. Pass `--project` to resolve `domain_profiles/<name>.json` beside a project manifest after built-ins. Replay descriptors are discovery metadata only; descriptors without executable dispatch fail closed and never claim kernel closure.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math profile inspect --domain nn-verify --json",
                what: "inspect the NN verification profile",
            },
            Example {
                cmd: "clean math profile inspect --project path/to/project.json --domain custom-domain --json",
                what: "inspect a project-local profile from domain_profiles/custom-domain.json",
            },
        ],
        see_also: &["math project init"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "theorem-index"],
        summary: "Emit a project-scoped theorem index (Experimental)",
        description: "Reuses the factory theorem-index internals but restricts the scan to theorem packs listed in a math project manifest. The output contains deterministic theorem candidate fingerprints, trust records, and structured per-candidate memory for normal-form heads, side-condition kinds, artifact kinds, and direct import closure.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math theorem-index --project tests/fixtures/math_project/sat_pb/project.json --json",
            what: "index theorem candidates from the SAT/PB pilot theorem pack",
        }],
        see_also: &["factory theorem-index", "math project status"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "obligation", "validate"],
        summary: "Validate a generic math proof obligation (Experimental)",
        description: "Parses `clean-obligation-v1`, validates schema/domain/trust consistency, and computes a canonical SHA-256 fingerprint over the typed obligation envelope.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math obligation validate tests/fixtures/math_project/sat_pb/obligations/subsumption.json --project tests/fixtures/math_project/sat_pb/project.json --json",
            what: "validate a Ay-shaped SAT/PB obligation through the generic ABI",
        }],
        see_also: &["math obligation open", "math proof-state open-obligation"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "obligation", "open"],
        summary: "Open a generic obligation as a proof-state handle (Experimental)",
        description: "Validates a project obligation and returns a deterministic CLI-local proof-state handle. The handle is intentionally marked ephemeral until the server-backed v2 proof-state adapter lands.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math obligation open --project tests/fixtures/math_project/nn_verify/project.json tests/fixtures/math_project/nn_verify/obligations/farkas.json --json",
            what: "open a Gamma-Crown-shaped obligation as an ephemeral proof-state handle",
        }],
        see_also: &["math proof-state open-obligation"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "obligation", "prove"],
        summary: "Attempt proof closure for a generic obligation (Experimental)",
        description: "Validates and fingerprints an obligation. By default it remains fail-closed with `blocked-no-proof-search-v2`; pass `--proof-state` to opt in to an embedded process-local proof-state tactic attempt, which requires serialized kernel expressions and tries a fixed conservative tactic list. The local-assumption provenance gate prevents `assumption` from using producer-supplied locals unless metadata records accepted local provenance under the project trust policy.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math obligation prove --project tests/fixtures/math_project/sat_pb/project.json tests/fixtures/math_project/sat_pb/obligations/prop_serialized_goal.json --proof-state --json",
            what: "try the embedded process-local proof-state tactic path and report tactic attempts",
        }],
        see_also: &["math proof-state apply", "auto premise"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "artifact", "validate"],
        summary: "Validate a proof-artifact-v1 envelope (Experimental)",
        description: "Parses a portable proof-artifact envelope and reports producer, hashes, exact verifier constants, certificate format, and validation status without claiming semantic replay.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math artifact validate tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json --json",
            what: "validate a checked-in Gamma-Crown Farkas artifact envelope",
        }],
        see_also: &["research validate-artifact", "math artifact replay"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "artifact", "replay"],
        summary: "Replay a proof artifact through available adapters (Experimental)",
        description: "Validates a proof-artifact-v1 envelope, gates dispatch through the project domain-profile replay registry, then runs executable replay adapters where available. Gamma-Crown Farkas and linear-entailment fixtures replay through exact-rational certificate checkers; SAT/PB DRAT and LRAT fixtures replay through checked solver artifacts. Unsupported profile/format combinations and registered-but-unwired adapters fail closed with stable replay diagnostics. Pass `--cache` with `--project` to write a project-local replay report and cache index at the default cache root; passing `--cache-dir` selects a project-relative or absolute cache root and also enables the cache write. Cached replay metadata is discoverable by status, hygiene, and dashboard.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math artifact replay --project tests/fixtures/math_project/nn_verify/project.json tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_entailment_valid.json --json",
                what: "replay a Gamma-Crown entailment artifact with project context",
            },
            Example {
                cmd: "clean math artifact replay --project tests/fixtures/math_project/nn_verify/project.json --cache tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json --json",
                what: "replay an artifact and write the project-local replay cache report and index at the default cache root",
            },
        ],
        see_also: &["math certificate extract", "research validate-artifact"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "certificate", "extract"],
        summary: "Extract a consumer-facing math certificate summary (Experimental)",
        description: "Emits the neutral `clean-math-certificate-v1` summary shape with obligation id, optional artifact pointer, direction, trust policy, and synthetic-sorry flag. Pass `--artifact` with a replayed artifact path or hash to attach replay-only evidence; `proof_status: \"closed\"` and `kernel_certified: true` require linked, checked, trust-clean `clean-math-kernel-evidence-v1` from project evidence. Server-produced kernel evidence is emitted only after certificate generation, strict `check_type` success against the proof-state target, and clean trust accounting. Proof-state extraction-shaped evidence and replay-only artifacts are diagnostic only and do not satisfy the checked-kernel-evidence closure gate.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math certificate extract --project tests/fixtures/math_project/sat_pb/project.json --obligation tests/fixtures/math_project/sat_pb/obligations/subsumption.json --json",
                what: "emit the fail-closed certificate summary shape for a SAT/PB obligation",
            },
            Example {
                cmd: "clean math certificate extract --project tests/fixtures/math_project/nn_verify/project.json --obligation tests/fixtures/math_project/nn_verify/obligations/farkas.json --artifact tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json --json",
                what: "attach replay-only artifact evidence to an NN verification certificate summary",
            },
        ],
        see_also: &["math artifact replay", "math obligation validate"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "issue-plan"],
        summary: "Emit issue-ready rows for math proof work (Experimental)",
        description: "Reads the project manifest, obligation sources, hygiene/replay evidence, and optional `clean-math-proof-failure-diagnostic-v1` evidence, then emits phase/workstream grouped rows with deterministic dedupe keys, issue-ready title, body, scope, files, labels, owners, acceptance criteria, dependencies, and verification commands for factory issue filing. Phase 6 rows use artifact replay plus hygiene commands; Phase 7 rows use certificate extraction with a kernel-certified acceptance check. Obligations whose metadata sets `issue_plan` to a non-filing value and `fixture_role` to an explicit smoke role are omitted from filing rows. Pass `--dedupe-open` with an exported GitHub-like issue snapshot to mark rows as new, matched open, or ambiguous without contacting GitHub. Pass `--export-dir` to dry-run deterministic local Markdown/JSON issue files, or add `--write` to create missing files while skipping any existing dedupe keys. The export path is entirely local and makes no live network calls.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math issue-plan --project tests/fixtures/math_project/nn_verify/project.json --json",
                what: "produce issue-plan rows from NN verification obligations",
            },
            Example {
                cmd: "clean math issue-plan --project tests/fixtures/math_project/sat_pb/project.json --dedupe-open open_issues.json --json",
                what: "mark issue-plan rows against an offline open-issue snapshot",
            },
            Example {
                cmd: "clean math issue-plan --project tests/fixtures/math_project/nn_verify/project.json --export-dir .clean/issues --json",
                what: "dry-run deterministic local issue file exports without writing or contacting GitHub",
            },
            Example {
                cmd: "clean math issue-plan --project tests/fixtures/math_project/nn_verify/project.json --export-dir .clean/issues --write --json",
                what: "write missing Markdown/JSON issue files and skip existing dedupe keys",
            },
        ],
        see_also: &["math project hygiene", "factory queue"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "task", "list"],
        summary: "List durable project-local proof tasks (Experimental)",
        description: "Projects the math issue plan into durable local proof-task state stored at `.clean/math-tasks.json` under the project root. The first slice tracks local status, notes, blockers, obligation fingerprints, and issue-plan metadata only; it does not persist live proof-state attempts.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math task list --project tests/fixtures/math_project/sat_pb/project.json --json",
            what: "list durable proof tasks projected from a math project issue plan",
        }],
        see_also: &["math task status", "math task update", "math issue-plan"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "task", "status"],
        summary: "Show one durable project-local proof task (Experimental)",
        description: "Resolves a task by obligation fingerprint, task id, issue key, or obligation JSON path, then prints the durable lifecycle state from `.clean/math-tasks.json` together with its issue-plan projection.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math task status --project tests/fixtures/math_project/sat_pb/project.json --obligation tests/fixtures/math_project/sat_pb/obligations/subsumption.json --json",
            what: "show the local lifecycle state for a proof obligation task",
        }],
        see_also: &["math task list", "math obligation validate"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math", "task", "update"],
        summary: "Update one durable project-local proof task (Experimental)",
        description: "Updates local proof-task status, notes, and blockers in `.clean/math-tasks.json` with an atomic write. This command records only durable lifecycle metadata and intentionally does not persist live proof-state attempts.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math task update --project tests/fixtures/math_project/sat_pb/project.json --obligation tests/fixtures/math_project/sat_pb/obligations/subsumption.json --status in-progress --note started --json",
            what: "mark a proof task in progress and append a local note",
        }],
        see_also: &["math task status", "math proof-state open-obligation"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    proof_state_feature!(
        &["math", "proof-state", "open"],
        "Open a theorem source location as a proof-state v2 handle",
        "clean math proof-state open --project tests/fixtures/math_project/sat_pb/project.json --file tests/fixtures/math_project/sat_pb/theorem_packs/SatPbPilot.lean --theorem sat_pb_subsumption_sound --json"
    ),
    FeatureDescriptor {
        path: &["math", "proof-state", "open-obligation"],
        summary: "Open a generic obligation as a proof-state v2 handle",
        description: "Experimental bridge that opens obligations whose `goal.expr` is serialized `clean_kernel::Expr` JSON by calling `proofState.openObligation`. The request persists structured proof-state metadata including project path/root, obligation fingerprint/source, producer, and artifact references; child proof states and snapshots preserve that metadata. Pass `--server HOST:PORT`, or set `CLEAN_PROOF_STATE_SERVER`/`CLEAN_SERVER`, to persist returned `ps_...` ids in a live `clean server` session for later snapshot/apply/extract commands; without a server address, the embedded process-local cache still expires when the CLI exits. Pretty-only goals and hypotheses fail closed with structured diagnostics.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math proof-state open-obligation --project tests/fixtures/math_project/sat_pb/project.json tests/fixtures/math_project/sat_pb/obligations/prop_serialized_goal.json --json",
            what: "open a serialized kernel goal through server proofState.openObligation",
        }],
        see_also: &["math obligation open", "server"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
    proof_state_server_feature!(
        &["math", "proof-state", "snapshot"],
        "Print a proof-state v2 snapshot",
        "clean math proof-state snapshot --state ps_... --format llm --json"
    ),
    proof_state_server_feature!(
        &["math", "proof-state", "search-theorems"],
        "Search theorem candidates for a proof-state goal",
        "clean math proof-state search-theorems --state ps_... --goal g0 --json"
    ),
    proof_state_server_feature!(
        &["math", "proof-state", "search-tactics"],
        "Search tactic candidates for a proof-state goal",
        "clean math proof-state search-tactics --state ps_... --goal g0 --json"
    ),
    proof_state_server_feature!(
        &["math", "proof-state", "apply"],
        "Apply a tactic script to a proof-state goal",
        "clean math proof-state apply --state ps_... --goal g0 --tactic cert_simp --json"
    ),
    proof_state_server_feature!(
        &["math", "proof-state", "retain"],
        "Retain a proof state in the server lifecycle cache",
        "clean math proof-state retain --state ps_... --json"
    ),
    proof_state_server_feature!(
        &["math", "proof-state", "close"],
        "Close a proof state in the server lifecycle cache",
        "clean math proof-state close --state ps_... --json"
    ),
    proof_state_server_feature!(
        &["math", "proof-state", "explain-failure"],
        "Explain a failed proof-state attempt",
        "clean math proof-state explain-failure --attempt attempt-fixture --json"
    ),
    FeatureDescriptor {
        path: &["math", "proof-state", "extract"],
        summary: "Extract proof material from a proof state",
        description: "Experimental typed proof-state v2 extraction command for math projects. Pass `--server HOST:PORT`, or set `CLEAN_PROOF_STATE_SERVER`/`CLEAN_SERVER`, to route the command to a persistent `clean server` JSON-RPC session; without a server address, the CLI emits the existing fail-closed adapter report. Use `--format kernel_evidence` to emit checked `clean-math-kernel-evidence-v1` from a solved proof state only after certificate generation, strict `check_type` success against the target, clean trust accounting, and structured metadata linkage when available.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean math proof-state extract --state ps_... --format kernel_evidence --json",
            what: "use a proof-state id from persistent `open-obligation` against the same server",
        }],
        see_also: &["math proof-state open-obligation", "server"],
        references: MATH_REFS,
        domain_root: Some("math"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

const MATH_REFS: &[Reference] = &[
    Reference {
        kind: RefKind::Design,
        label: "Math project framework execution plan",
        target: "designs/math-project-framework-execution-plan.tex",
    },
    Reference {
        kind: RefKind::Crate,
        label: "clean-cli",
        target: "clean-cli",
    },
];
