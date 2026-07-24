// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clap types and `FeatureDescriptor` entries for the `clean kernel ...`
//! verb tree introduced in Epic #3436 Phase 3.
//!
//! Split out of `cli.rs` to keep both files under the 500-line limit while
//! preserving a single logical feature surface. The parent `cli.rs` re-exports
//! every public item defined here and concatenates [`KERNEL_VERB_FEATURES`]
//! into the crate-level `FEATURES` constant.

use std::path::PathBuf;

use clap::Subcommand;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

use super::{CRATE_REF, DESIGN_REF};

/// Subcommands under `clean kernel ...`.
///
/// Introduced by Epic #3436 Phase 3 to absorb four orphan kernel binaries
/// into the unified `clean` CLI:
///   - `clean kernel lrat-conform`              ← `lrat_oracle_conformance` (#3443)
///   - `clean kernel soundness-gate`            ← `soundness_gate`          (#3444)
///   - `clean kernel verify-gamma-crown`        ← `verify_gamma_crown`      (#3446)
///   - `clean kernel cert verify|inspect|stats` ← `clean_cert`              (#3447)
///   - `clean kernel generate-lean4-baseline`   ← `generate_lean4_baseline` (#3445)
///   - `clean kernel verify-constructive-claims` ← `verify_constructive_claims` (#3510)
#[derive(Subcommand)]
pub enum KernelCommands {
    /// Run the LRAT oracle-conformance harness against external verifiers.
    ///
    /// Absorbs the `lrat_oracle_conformance` binary (#3443). Compares
    /// clean's native LRAT verifiers against `ay-lrat-check` and/or
    /// `cake_lpr` on a maintained proof corpus and emits a Markdown report.
    LratConform {
        /// Explicit path to the `ay-lrat-check` binary.
        #[arg(long = "ay-lrat-check")]
        ay_lrat_check: Option<PathBuf>,
        /// Explicit path to the `cake_lpr` binary.
        #[arg(long = "cake-lpr")]
        cake_lpr: Option<PathBuf>,
        /// Write the report to `reports/research/issue-936-lrat-oracle-current.md`.
        #[arg(long = "update-report")]
        update_report: bool,
    },
    /// Run the kernel soundness-gate accept/reject lanes against the baseline corpus.
    ///
    /// Absorbs the `soundness_gate` binary (#3444). The gate verifies the
    /// accept lane (well-typed programs accepted), the reject lane (ill-typed
    /// programs rejected), and a battery of trust regressions. The underlying
    /// gate lives inside the `clean-elab` test harness; this entry point
    /// invokes the existing binary so the accept/reject test modules remain
    /// the single source of truth.
    SoundnessGate,
    /// Type-check and classify all 15 gamma-CROWN conjecture environments.
    ///
    /// Absorbs the `verify_gamma_crown` binary (#3446). Emits per-conjecture
    /// kernel type-check results and axiom counts. The conjecture builders
    /// live behind the `math-overlays` feature; without that feature the
    /// handler reports an informative error and exits non-zero.
    VerifyGammaCrown {
        /// Emit a JSON report instead of the default human-readable text.
        #[arg(long, conflicts_with_all = ["csv", "latex"])]
        json: bool,
        /// Emit a CSV report.
        #[arg(long, conflicts_with_all = ["json", "latex"])]
        csv: bool,
        /// Emit a LaTeX report.
        #[arg(long, conflicts_with_all = ["json", "csv"])]
        latex: bool,
    },
    /// Transitive-axiom-closure gate for `constructive: true` claims (#3498).
    ///
    /// Absorbs the `verify_constructive_claims` binary. For a gamma-crown
    /// conjecture, enumerates every `Declaration::Theorem` whose name starts
    /// with the conjecture's declared namespace prefix and classifies each
    /// theorem as `is_constructive` iff its transitive domain-axiom closure
    /// is empty. Emits JSON suitable for the `verify_axiom_audit` Python gate.
    ///
    /// Requires the `math-overlays` feature, which brings in the conjecture
    /// builders used by `init_conjecture`. Without that feature the handler
    /// exits non-zero with an informative message.
    VerifyConstructiveClaims {
        /// Conjecture ID to audit (see `CONJECTURE_IDS`, e.g. `C008`).
        #[arg(long)]
        conjecture: String,
        /// Exit 0 when no theorems are found in the conjecture's namespace.
        #[arg(long = "allow-empty")]
        allow_empty: bool,
    },
    /// Verify, inspect, or summarize `.cleancert` proof-certificate bundles.
    ///
    /// Absorbs the `clean_cert` binary (#3447). Operates on the bundle
    /// format exported by `clean_kernel::cert::bundle::CertBundle`. Unlike
    /// the top-level `clean cert ...` verbs (which take a single `ProofCert`
    /// + `Expr` JSON pair), these verbs take a whole `.cleancert` archive
    ///   containing an environment, a manifest, and many theorems.
    Cert {
        #[command(subcommand)]
        command: KernelCertCommands,
    },
    /// Regenerate the Lean 4 differential-testing baseline JSON.
    ///
    /// Absorbs the `generate_lean4_baseline` binary (#3445). Runs `lean` (Lean 4)
    /// over the test-expressions corpus and captures the normalized inferred
    /// types as a cached JSON baseline used by clean's differential tests.
    /// Requires a Lean 4 toolchain on `PATH` or in `~/.elan/bin`.
    ///
    /// When `--output` is omitted the handler discovers the enclosing `.git`
    /// workspace root and writes to `crates/clean-kernel/tests/differential/
    /// lean4_baseline.json`, matching the original binary's hard-coded path.
    GenerateLean4Baseline {
        /// Explicit path for the generated baseline JSON. Defaults to the
        /// workspace-root-relative `crates/clean-kernel/tests/differential/
        /// lean4_baseline.json` when omitted.
        #[arg(long, value_name = "PATH")]
        output: Option<PathBuf>,
    },
    /// Incremental proof classifier — classify one theorem per-call in <500ms.
    ///
    /// Seeds a kernel `Environment` with the same NN-verify / interval-arith
    /// / CROWN overlay constants that `mathverse_shard build-native` uses, then
    /// runs `env.proof_quality(name)` over each requested declaration and
    /// emits one JSON line per name. Replaces the 90-second
    /// `mathverse_shard build-native` + `grep Constructive` feedback loop with
    /// a sub-500ms per-theorem check suitable for IDE / agent iteration.
    ///
    /// Feature-gated behind `math-overlays` because the env-seeding path
    /// pulls in the overlay constant registrars. See #3598.
    Classify {
        /// One or more fully-qualified theorem names (e.g.
        /// `NNVerify.Rat.max_zero_zero`). Ignored when `--all-constructive`
        /// is set.
        #[arg(value_name = "NAME")]
        names: Vec<String>,
        /// Emit one JSON line for every `ConstantKind::Theorem` in the seeded
        /// env whose `ProofQuality::Constructive` predicate holds. Fast
        /// replacement for the `mathverse_shard build-native | grep Constructive`
        /// pattern.
        #[arg(long = "all-constructive", conflicts_with = "why_rejected")]
        all_constructive: bool,
        /// Print a single human-readable line explaining why the named
        /// theorem was classified `AxiomDependent`: the first non-
        /// foundational axiom in its transitive closure and that axiom's
        /// `ConstantKind`. Conflicts with `--all-constructive`.
        #[arg(long = "why-rejected", value_name = "NAME")]
        why_rejected: Option<String>,
    },
}

/// Subcommands under `clean kernel cert ...`.
///
/// These operate on `.cleancert` bundles (see [`KernelCommands::Cert`]).
#[derive(Subcommand)]
pub enum KernelCertCommands {
    /// Verify every theorem in a `.cleancert` bundle.
    Verify {
        /// Path to the `.cleancert` bundle.
        path: PathBuf,
        /// Emit machine-readable JSON.
        #[arg(long)]
        json: bool,
    },
    /// Inspect the theorem list and per-theorem metadata in a bundle.
    Inspect {
        /// Path to the `.cleancert` bundle.
        path: PathBuf,
        /// Emit machine-readable JSON.
        #[arg(long)]
        json: bool,
    },
    /// Show summary statistics for a bundle (counts, trust breakdown, size).
    Stats {
        /// Path to the `.cleancert` bundle.
        path: PathBuf,
        /// Emit machine-readable JSON.
        #[arg(long)]
        json: bool,
    },
}

/// `FeatureDescriptor` entries for every `clean kernel ...` verb.
///
/// Concatenated into the parent [`super::FEATURES`] constant via
/// `clean-cli`'s registry.
pub const KERNEL_VERB_FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["kernel", "lrat-conform"],
        summary: "Oracle-conformance harness for LRAT proof verifiers",
        description: "\
Runs clean's native LRAT verifiers side-by-side against external oracles \
(`ay-lrat-check` and/or `cake_lpr`) on a maintained proof corpus. Reports \
per-case agreement and flags internal disagreements. Use `--update-report` \
to persist the Markdown report to `reports/research/`.\n\n\
Absorbs the deprecated `lrat_oracle_conformance` standalone binary (#3443).",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean kernel lrat-conform",
                what: "run the oracle-conformance harness with auto-discovered oracles",
            },
            Example {
                cmd: "clean kernel lrat-conform --update-report",
                what: "run the harness and persist the Markdown report under reports/research/",
            },
        ],
        see_also: &["cert verify"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb lrat_oracle_conformance #3443",
                target: "3443",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["kernel", "soundness-gate"],
        summary: "Run the kernel soundness gate (accept/reject + trust regressions)",
        description: "\
Executes the kernel soundness gate: the accept lane (well-typed programs are \
accepted), the reject lane (ill-typed programs are rejected with type-error \
reasons), and a battery of trust regressions that pin `sorry`, explicit \
`sorry`, synthetic `sorry`, and trusted-accept behaviour.\n\n\
Absorbs the deprecated `soundness_gate` standalone binary (#3444). The \
underlying accept/reject test modules remain the single source of truth; this \
entry point shells out to the packaged binary so the gate wiring stays \
identical.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean kernel soundness-gate",
            what: "run the full accept + reject + trust-regression gate",
        }],
        see_also: &["check"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb soundness_gate #3444",
                target: "3444",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["kernel", "verify-gamma-crown"],
        summary: "Type-check and classify all 15 gamma-CROWN conjecture environments",
        description: "\
Initializes all 15 gamma-CROWN conjectures (C001–C012, C028–C030) in fresh \
`Environment`s, runs kernel type-checking over every declaration, and emits a \
per-conjecture report with axiom/trust counts and timing. This command \
classifies the registered environments; it is not a blanket claim that all 15 \
conjectures are constructive, axiom-free NN-verification proofs.\n\n\
The conjecture builders live behind the kernel's `math-overlays` feature, so \
this verb requires the `clean` binary to be compiled with \
`--features math-overlays`. Without that feature the handler exits non-zero \
with an informative message. Absorbs the deprecated `verify_gamma_crown` \
standalone binary (#3446).",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean kernel verify-gamma-crown",
                what: "run all 15 conjectures and emit the human-readable report",
            },
            Example {
                cmd: "clean kernel verify-gamma-crown --json",
                what: "emit the verification report as machine-readable JSON",
            },
        ],
        see_also: &["cert verify"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb verify_gamma_crown #3446",
                target: "3446",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: Some("math-overlays"),
    },
    FeatureDescriptor {
        path: &["kernel", "cert", "verify"],
        summary: "Verify every theorem inside a .cleancert proof bundle",
        description: "\
Loads a `.cleancert` bundle produced by \
`clean_kernel::cert::bundle::CertBundle` and verifies every theorem in it \
against the bundle's serialized environment. Emits per-theorem status plus a \
trust-level summary. Unlike `clean cert verify` (which takes a single \
`ProofCert` + `Expr` JSON pair), this verb targets whole bundles.\n\n\
Absorbs the deprecated `clean_cert verify` standalone binary (#3447).",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean kernel cert verify proof.cleancert",
                what: "verify every theorem in a proof bundle",
            },
            Example {
                cmd: "clean kernel cert verify proof.cleancert --json",
                what: "emit machine-readable JSON for automation",
            },
        ],
        see_also: &["kernel cert inspect", "kernel cert stats", "cert verify"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb clean_cert #3447",
                target: "3447",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["kernel", "cert", "inspect"],
        summary: "List theorem types and readiness details inside a .cleancert bundle",
        description: "\
Prints the manifest of a `.cleancert` bundle: project name, clean version, \
bundle-level trust level, bundle readiness counts, and one line per theorem \
with its trust level, declaration kind, theorem type, and whether the bundle \
contains the certificate + environment proof term needed for replay. Hashes \
remain available when present. Pair with `clean kernel cert stats` for \
aggregate counts.\n\n\
Absorbs the deprecated `clean_cert inspect` standalone binary (#3447).",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean kernel cert inspect proof.cleancert",
            what: "print the theorem list and metadata for a proof bundle",
        }],
        see_also: &["kernel cert verify", "kernel cert stats"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb clean_cert #3447",
                target: "3447",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["kernel", "cert", "stats"],
        summary: "Summary statistics for a .cleancert proof bundle",
        description: "\
Prints a compact summary of a `.cleancert` bundle: theorem count, axiom \
count, sorry count, trust breakdown, bundle size, and env hash. Use `--json` \
for automation integrations.\n\n\
Absorbs the deprecated `clean_cert stats` standalone binary (#3447).",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean kernel cert stats proof.cleancert",
            what: "print size + trust breakdown for a proof bundle",
        }],
        see_also: &["kernel cert verify", "kernel cert inspect"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb clean_cert #3447",
                target: "3447",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["kernel", "generate-lean4-baseline"],
        summary: "Regenerate the Lean 4 differential-testing baseline JSON",
        description: "\
Runs the external `lean` (Lean 4) toolchain over the test-expression corpus at \
`crates/clean-kernel/tests/differential/expressions.txt` and captures the \
normalized inferred types as a cached JSON baseline. The resulting file feeds \
clean's differential parity test (`lean4_parity`), letting CI run without a \
Lean 4 installation while keeping the clean vs Lean4 cross-check honest.\n\n\
Requires a Lean 4 toolchain on `PATH` or in `~/.elan/bin`. Without `--output`, \
the command walks upward looking for `.git` to locate the workspace root and \
writes to the same path the legacy binary used, so pre-existing scripts that \
cd'd to the workspace root still produce byte-identical output.\n\n\
Absorbs the deprecated `generate_lean4_baseline` standalone binary (#3445).",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean kernel generate-lean4-baseline",
                what: "regenerate the baseline at the workspace-relative default path",
            },
            Example {
                cmd: "clean kernel generate-lean4-baseline --output /tmp/baseline.json",
                what: "write the baseline to an explicit location",
            },
        ],
        see_also: &["check"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb generate_lean4_baseline #3445",
                target: "3445",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["kernel", "classify"],
        summary: "Experimental incremental proof classifier — <500ms per-theorem classification",
        description: "\
Seeds a kernel `Environment` with the same NN-verify / interval-arith / CROWN \
overlay constants that `mathverse_shard build-native` uses, then runs the \
kernel's `proof_quality` classifier over each requested declaration and \
emits one JSON line per name.\n\n\
Replaces the 90-second `mathverse_shard build-native | grep Constructive` \
feedback loop with a sub-500ms per-theorem check. JSON schema per line: \
`name`, `kind` (Theorem/Axiom/Opaque/Definition), `classification` \
(Constructive/AxiomDependent/TrustMarkerReached/Unchecked/Unknown/NotFound), \
`axiom_closure`, `trust_markers_reached`.\n\n\
`--all-constructive` iterates every theorem in the seeded env and emits one \
JSON line for each constructive one. `--why-rejected <NAME>` prints a single \
human-readable line explaining which non-foundational axiom blocks the \
named theorem from becoming constructive.\n\n\
Feature-gated behind `math-overlays`. Classifier logic lives in \
`clean_kernel::env::axiom_audit` — no duplication in the CLI layer. See #3598.",
        category: Category::Proof,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean kernel classify NNVerify.Rat.max_zero_zero",
                what: "classify a single theorem (expected: Constructive)",
            },
            Example {
                cmd: "clean kernel classify --all-constructive",
                what: "emit one JSON line per constructive theorem in the seeded env",
            },
            Example {
                cmd: "clean kernel classify --why-rejected NNVerify.C006.monolithic_crown",
                what: "print the first non-foundational axiom blocking the named theorem",
            },
        ],
        see_also: &["kernel verify-constructive-claims"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Incremental classifier CLI #3598",
                target: "3598",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Axiom-dependent reject triage epic #3551",
                target: "3551",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: Some("math-overlays"),
    },
    FeatureDescriptor {
        path: &["kernel", "verify-constructive-claims"],
        summary: "Transitive-axiom-closure gate for gamma_crown constructive claims",
        description: "\
For a given gamma_crown conjecture ID, enumerates every \
`Declaration::Theorem` in the conjecture's namespace, computes the transitive \
domain-axiom closure of each theorem via `env.axiom_deps(name)`, and emits \
JSON suitable for the `verify_axiom_audit` Python audit gate. A theorem is \
`is_constructive` iff its closure is empty (only FOUNDATIONAL_AXIOMS were \
reachable).\n\n\
Exit codes: 0 when every theorem is constructive (or `--allow-empty` with \
no theorems); 1 when at least one theorem has a non-foundational closure; \
2 on usage error; 3 on initialization failure; 4 when no theorems are \
registered in the conjecture's namespace.\n\n\
Requires the `math-overlays` feature (the conjecture builders live behind \
it). Without that feature the handler exits non-zero with an informative \
message. Absorbs the deprecated `verify_constructive_claims` standalone \
binary (#3510).",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean kernel verify-constructive-claims --conjecture C008",
                what: "audit conjecture C008's theorems; exit 0 iff all are constructive",
            },
            Example {
                cmd: "clean kernel verify-constructive-claims --conjecture C010 --allow-empty",
                what: "audit C010, exit 0 even if no theorems are registered yet",
            },
        ],
        see_also: &["kernel verify-gamma-crown"],
        references: &[
            DESIGN_REF,
            Reference {
                kind: RefKind::Issue,
                label: "Absorb verify_constructive_claims #3510",
                target: "3510",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Audit schema + gate #3435",
                target: "3435",
            },
            CRATE_REF,
        ],
        domain_root: Some("kernel"),
        alternative_forms: &["clean verify_constructive_claims"],
        feature_gate: Some("math-overlays"),
    },
];
