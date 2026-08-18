// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors (catalog tail).

use super::*;

pub(crate) const FEATURE_RELEASE_READINESS_SMOKE: FeatureDescriptor = FeatureDescriptor {
        path: &["release", "readiness-smoke"],
        summary: "Run Rust-owned release readiness smoke evidence (Experimental)",
        description: "\
Experimental Rust-owned release readiness smoke surface. The command records \
static release-surface checks and, with `--clean-clone-lite`, runs the detached \
worktree metadata, public-demo, and benchmark lanes. With `--launch`, the \
benchmark publication launch checker is included. The command emits or writes \
machine-readable evidence and fails closed while any release-readiness lane is \
not ready.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean release readiness-smoke --json",
                what: "emit static release readiness smoke evidence",
            },
            Example {
                cmd: "clean release readiness-smoke --clean-clone-lite --launch --evidence /tmp/clean-release.json",
                what: "run the launch-oriented clean-clone-lite smoke gate",
            },
        ],
        see_also: &["replacement status", "replacement release-issue-hygiene"],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "clean full Lean4 ecosystem replacement #3698",
                target: "#3698",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Release readiness checklist",
                target: "docs/RELEASE_READINESS.md",
            },
        ],
        domain_root: Some("release"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_TACTIC_PARITY: FeatureDescriptor = FeatureDescriptor {
        path: &["replacement", "tactic-parity"],
        summary: "Print the tactic parity and strict reconstruction scorecard (Experimental)",
        description: "\
Experimental Rust-owned matrix for Lean4 tactic parity and strict solver \
reconstruction. The report separates registered tactic surface, proof-carrying \
behavior, fail-closed behavior, trusted fallback counts, Lean4 parity status, \
and strict reconstruction gaps. `--json` emits `clean-tactic-parity-report-v1` \
for #3711 and #3712 automation gates.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean replacement tactic-parity",
                what: "print the tactic parity launch blocker matrix",
            },
            Example {
                cmd: "clean replacement tactic-parity --json",
                what: "emit tactic parity and strict reconstruction JSON",
            },
            Example {
                cmd: "clean replacement tactic-parity discover-full-corpus-inputs --json",
                what: "inspect the tactic parity registry and fail closed on missing real full-corpus inputs",
            },
            Example {
                cmd: "clean replacement tactic-parity generate-full-corpus-fixture --output /tmp/tactic-parity-full-corpus.json --json",
                what: "write a schema-valid non-coverage fixture for the future full-corpus tactic artifact",
            },
            Example {
                cmd: "clean replacement tactic-parity validate-full-corpus --report reports/tactic-parity-full-corpus.json --json",
                what: "fail closed unless the full-corpus tactic artifact satisfies the Rust schema validator",
            },
        ],
        see_also: &[
            "replacement status",
            "replacement trust-core-evidence",
            "kernel soundness-gate",
        ],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Lean4 tactic parity matrix and corpus gates #3711",
                target: "#3711",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Strict solver-fragment reconstruction dashboard #3712",
                target: "#3712",
            },
            Reference {
                kind: RefKind::Design,
                label: "Full Lean4 replacement execution plan",
                target: "docs/plans/LEAN4_REPLACEMENT_PLAN.md",
            },
            Reference {
                kind: RefKind::Doc,
                label: "SMT trust boundary",
                target: "docs/SMT_TRUST.md",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_TACTIC_PARITY_DISCOVER_FULL_CORPUS_INPUTS: FeatureDescriptor = FeatureDescriptor {
        path: &[
            "replacement",
            "tactic-parity",
            "discover-full-corpus-inputs",
        ],
        summary: "Inspect tactic parity full-corpus inputs (Experimental)",
        description: "\
Reads the tactic parity eval registry and reports whether real full-corpus \
source manifests and count artifacts are present. The command is intentionally \
fail-closed when the full-corpus inputs are placeholders, so launch reports do \
not confuse a schema fixture with representative tactic coverage.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean replacement tactic-parity discover-full-corpus-inputs --json",
            what: "inspect the tactic parity registry and fail closed on missing real full-corpus inputs",
        }],
        see_also: &[
            "replacement tactic-parity",
            "replacement tactic-parity generate-full-corpus-fixture",
            "replacement tactic-parity validate-full-corpus",
        ],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Lean4 tactic parity matrix and corpus gates #3711",
                target: "#3711",
            },
            Reference {
                kind: RefKind::Design,
                label: "Full Lean4 replacement execution plan",
                target: "docs/plans/LEAN4_REPLACEMENT_PLAN.md",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_TACTIC_PARITY_GENERATE_FULL_CORPUS_FIXTURE: FeatureDescriptor = FeatureDescriptor {
        path: &[
            "replacement",
            "tactic-parity",
            "generate-full-corpus-fixture",
        ],
        summary: "Generate the tactic parity full-corpus schema fixture (Experimental)",
        description: "\
Writes a schema-valid non-coverage fixture for the future full-corpus tactic \
parity artifact. The generated report validates the artifact shape and stable \
blocker vocabulary without claiming Lean4 full-corpus tactic replacement \
coverage.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean replacement tactic-parity generate-full-corpus-fixture --output /tmp/tactic-parity-full-corpus.json --json",
            what: "write a schema-valid non-coverage fixture for the future full-corpus tactic artifact",
        }],
        see_also: &[
            "replacement tactic-parity",
            "replacement tactic-parity discover-full-corpus-inputs",
            "replacement tactic-parity validate-full-corpus",
        ],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Lean4 tactic parity matrix and corpus gates #3711",
                target: "#3711",
            },
            Reference {
                kind: RefKind::Design,
                label: "Full Lean4 replacement execution plan",
                target: "docs/plans/LEAN4_REPLACEMENT_PLAN.md",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_TACTIC_PARITY_VALIDATE_FULL_CORPUS: FeatureDescriptor = FeatureDescriptor {
        path: &["replacement", "tactic-parity", "validate-full-corpus"],
        summary: "Validate tactic parity full-corpus evidence (Experimental)",
        description: "\
Validates the full Lean4 tactic corpus acceptance artifact against the Rust \
schema gate. It remains fail-closed unless the artifact is real full-corpus \
evidence with matching counts, blocker accounting, and reproduction metadata.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean replacement tactic-parity validate-full-corpus --report reports/tactic-parity-full-corpus.json --json",
            what: "fail closed unless the full-corpus tactic artifact satisfies the Rust schema validator",
        }],
        see_also: &[
            "replacement tactic-parity",
            "replacement tactic-parity discover-full-corpus-inputs",
            "replacement tactic-parity generate-full-corpus-fixture",
        ],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Lean4 tactic parity matrix and corpus gates #3711",
                target: "#3711",
            },
            Reference {
                kind: RefKind::Design,
                label: "Full Lean4 replacement execution plan",
                target: "docs/plans/LEAN4_REPLACEMENT_PLAN.md",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_TRUST_CORE_EVIDENCE: FeatureDescriptor = FeatureDescriptor {
    path: &["replacement", "trust-core-evidence"],
    summary: "Print kernel launch, differential, and fallback-denial evidence (Experimental)",
    description: "\
Experimental evidence report for the replacement trust core. The report reads \
checked-in Lean4 differential baseline artifacts, recomputes the expression \
corpus SHA-256, validates the fresh kernel soundness launch evidence artifact, \
and summarizes the DENY_SORRY fallback-denial lanes plus the unchecked-declaration \
ratchet. It also emits the required kernel soundness, DENY_SORRY, and axiom-audit \
gate rows consumed by replacement status. `--json` emits `clean-trust-core-evidence-v1` \
for #3699 and #3705. It is intentionally non-green until fresh kernel, \
differential, and zero-trust closure gates are complete.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean replacement trust-core-evidence",
            what: "print trust-core evidence for kernel and fallback gates",
        },
        Example {
            cmd: "clean replacement trust-core-evidence --json",
            what: "emit kernel launch, differential, and fallback-denial JSON",
        },
    ],
    see_also: &[
        "replacement status",
        "kernel soundness-gate",
        "replacement tactic-parity",
    ],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Proof-system replacement certification and zero-trust gates #3699",
            target: "#3699",
        },
        Reference {
            kind: RefKind::Issue,
            label: "Zero-trust gate forbids sorryAx and trusted fallback constructors #3705",
            target: "#3705",
        },
        Reference {
            kind: RefKind::Doc,
            label: "Kernel soundness launch evidence",
            target: KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH,
        },
        Reference {
            kind: RefKind::Doc,
            label: "Lean4 differential baseline",
            target: "tests/differential/lean4_baseline.json",
        },
        Reference {
            kind: RefKind::Doc,
            label: "Unchecked declaration ratchet",
            target: "data/unchecked_decl_ratchet.json",
        },
    ],
    domain_root: Some("replacement"),
    alternative_forms: &[],
    feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_TRUST_BOUNDARY_AUDIT: FeatureDescriptor = FeatureDescriptor {
        path: &["replacement", "trust-boundary-audit"],
        summary: "Summarize TrustBoundary audit TSV records without Python (Experimental)",
        description: "\
Experimental Rust-owned TrustBoundary audit summarizer for #2875 and #3706. \
The command reads one or more CLEAN_TRUST_BOUNDARY_AUDIT_PATH TSV artifacts, \
loads expected boundary-only test patterns, groups hits deterministically by \
crate, test, lane, tactic, proof kind, and subsystem, and emits JSON or the \
legacy Markdown report shape without `scripts/trust_boundary_audit.py`.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean replacement trust-boundary-audit --input /tmp/clean-2875-auto.tsv --expected scripts/trust_boundary_expected_tests.txt --json",
                what: "emit grouped trust-boundary audit JSON for agents",
            },
            Example {
                cmd: "clean replacement trust-boundary-audit --input /tmp/clean-2875-auto.tsv --input /tmp/clean-2875-elab.tsv --output reports/research/issue-2875-trustboundary-audit-current.md",
                what: "write the Gate 2 Markdown report from TSV audit artifacts",
            },
        ],
        see_also: &["replacement status", "replacement trust-core-evidence"],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Gate 2 TrustBoundary audit #2875",
                target: "#2875",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Migrate replacement-critical Python tests and tooling #3706",
                target: "#3706",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Expected TrustBoundary tests",
                target: TRUST_BOUNDARY_EXPECTED_TESTS_PATH,
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_RUST_FIRST_TOOLING: FeatureDescriptor = FeatureDescriptor {
    path: &["replacement", "rust-first-tooling"],
    summary: "Emit the Rust-first tooling migration inventory and evidence artifact (Experimental)",
    description: "\
Experimental Rust-owned emitter for the rust-first-tooling replacement row. The \
command serializes the same Python-tool migration inventory that backs \
`clean replacement status` (per-lane owner, status, planned Rust surface, and \
removal condition) together with build provenance (`generated_at_commit`). \
`--evidence` writes `reports/rust-first-tooling.json` and is guarded twice: the \
write refuses a binary that is not built at HEAD, and it refuses to mint \
evidence while any replacement-critical lane is not Rust-owned or demoted. The \
artifact records computed state only — it never claims replacement launch \
readiness.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean replacement rust-first-tooling --json",
            what: "print the Rust-first tooling migration inventory as JSON",
        },
        Example {
            cmd: "clean replacement rust-first-tooling --evidence reports/rust-first-tooling.json --json",
            what: "write the rust-first-tooling row evidence artifact from a HEAD-built binary",
        },
    ],
    see_also: &["replacement status", "replacement trust-core-evidence"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Migrate replacement-critical Python tests and tooling #3706",
            target: "#3706",
        },
        Reference {
            kind: RefKind::Doc,
            label: "Lean4 replacement source audit",
            target: "docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md",
        },
    ],
    domain_root: Some("replacement"),
    alternative_forms: &[],
    feature_gate: None,
};
