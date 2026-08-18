// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors (catalog root).

use super::*;

/// Feature catalog for the `clean replacement` command group (also
/// `release readiness-smoke`). Order matches the original single-file array.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FEATURE_REPLACEMENT_STATUS,
    FEATURE_REPLACEMENT_RELEASE_ISSUE_HYGIENE,
    FEATURE_REPLACEMENT_VALIDATE_REPORT,
    FEATURE_REPLACEMENT_AXIOM_AUDIT,
    FEATURE_REPLACEMENT_NATIVE_LIBRARY_COVERAGE_MATRIX,
    FEATURE_REPLACEMENT_NATIVE_LIBRARY_API_SLICE,
    FEATURE_REPLACEMENT_NATIVE_LIBRARY_MATHLIB_API,
    FEATURE_RELEASE_READINESS_SMOKE,
    FEATURE_REPLACEMENT_TACTIC_PARITY,
    FEATURE_REPLACEMENT_TACTIC_PARITY_DISCOVER_FULL_CORPUS_INPUTS,
    FEATURE_REPLACEMENT_TACTIC_PARITY_GENERATE_FULL_CORPUS_FIXTURE,
    FEATURE_REPLACEMENT_TACTIC_PARITY_VALIDATE_FULL_CORPUS,
    FEATURE_REPLACEMENT_TRUST_CORE_EVIDENCE,
    FEATURE_REPLACEMENT_TRUST_BOUNDARY_AUDIT,
    FEATURE_REPLACEMENT_RUST_FIRST_TOOLING,
];

pub(crate) const FEATURE_REPLACEMENT_STATUS: FeatureDescriptor = FeatureDescriptor {
    path: &["replacement", "status"],
    summary: "Print the Lean4 replacement scorecard and launch gate (Experimental)",
    description: "\
Experimental replacement scorecard for the clean + Mathverse Lean4 ecosystem \
replacement program. The command emits every launch-critical row with owner \
slot, issue, gate command, status, blocker, evidence artifact, and structured \
zero-trust gate status for kernel soundness, DENY_SORRY, and axiom audit. \
`--json` is the Rust-owned control-plane surface intended for factory \
dispatch, release readiness, and HN-launch claim gating.\n\n\
The target claim is intentionally aggressive, but the command fails closed at \
the data level: `launch_ready` remains false until every required replacement \
row is green and every required zero-trust gate is passed.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean replacement status",
            what: "print a compact replacement launch scorecard",
        },
        Example {
            cmd: "clean replacement status --json",
            what: "emit structured replacement status for agents and release gates",
        },
    ],
    see_also: &[
        "replacement tactic-parity",
        "replacement trust-core-evidence",
        "research status",
        "kernel soundness-gate",
    ],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "clean full Lean4 ecosystem replacement #3698",
            target: "#3698",
        },
        Reference {
            kind: RefKind::Issue,
            label: "Canonical clean AI-factory execution plan #3691",
            target: "#3691",
        },
        Reference {
            kind: RefKind::Design,
            label: "Full Lean4 replacement execution plan",
            target: "docs/plans/LEAN4_REPLACEMENT_PLAN.md",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("replacement"),
    alternative_forms: &[],
    feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_RELEASE_ISSUE_HYGIENE: FeatureDescriptor = FeatureDescriptor {
    path: &["replacement", "release-issue-hygiene"],
    summary: "Check release issue hygiene live or from an offline snapshot (Experimental)",
    description: "\
Experimental non-mutating release issue hygiene gate. `--fetch` runs read-only \
`gh issue list --state open --limit <N> --json number,title,url,labels,assignees,body,comments`; \
`--input` parses the same local GitHub issue snapshot. Both modes evaluate \
watched labels, owner evidence, `Release decision:`, `non_ready_issues`, \
`missing_fields`, and `suggested_actions`, and fail closed on fetch, parse, or \
hygiene gaps.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd:
                "clean replacement release-issue-hygiene --input /tmp/clean-open-issues.json --json",
            what: "check a local gh issue snapshot without mutating GitHub",
        },
        Example {
            cmd: "clean replacement release-issue-hygiene --fetch --json",
            what: "run the read-only live GitHub issue hygiene gate",
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
            label: "Release issue hygiene Python gate",
            target: "scripts/release_issue_hygiene.py",
        },
    ],
    domain_root: Some("replacement"),
    alternative_forms: &[],
    feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_VALIDATE_REPORT: FeatureDescriptor = FeatureDescriptor {
        path: &["replacement", "validate-report"],
        summary: "Validate replacement evidence reports without Python (Experimental)",
        description: "\
Experimental Rust-owned replacement evidence report validator. The command \
checks the checked-in native-library, mathverse-replay, LSP/infoview, and frontend \
parity report contracts directly from JSON: schema version, scorecard provenance, \
row evidence, non-claims, blockers, launch-readiness non-claims, and \
kind-specific accounting. \
`--json` emits `clean-replacement-report-validation-v1` and fails closed on \
malformed or drifted evidence.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean replacement validate-report --report reports/native-library-replacement.json --kind native-library --json",
                what: "validate the native-library replacement report contract",
            },
            Example {
                cmd: "clean replacement validate-report --report reports/lsp-infoview-parity.json --kind lsp-infoview --json",
                what: "validate the LSP/infoview parity evidence report contract",
            },
            Example {
                cmd: "clean replacement validate-report --report tests/lean4_compat/frontend_replacement_scorecard.json --kind frontend-parity --json",
                what: "validate the frontend replacement scorecard contract",
            },
        ],
        see_also: &["replacement status", "replacement tactic-parity"],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Migrate replacement-critical Python tests and tooling #3706",
                target: "#3706",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Native library replacement report",
                target: "reports/native-library-replacement.json",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Mathverse replay replacement report",
                target: "reports/mathverse-replay-replacement.json",
            },
            Reference {
                kind: RefKind::Doc,
                label: "LSP infoview parity report",
                target: "reports/lsp-infoview-parity.json",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_AXIOM_AUDIT: FeatureDescriptor = FeatureDescriptor {
        path: &["replacement", "axiom-audit"],
        summary: "Verify axiom-audit evidence and emit launch evidence without Python (Experimental)",
        description: "\
Experimental Rust-owned axiom-audit replacement gate. `--verify` reads \
`data/axiom_audit.json`, recomputes aggregate counters, rejects malformed or \
stale aggregate fields, and fails closed unless domain/all axiom debt and \
nonzero conjecture rows are zero. `--evidence` writes \
`reports/axiom-audit-launch-evidence.json` with Rust CLI provenance and source \
hashes for the command implementation plus the audit data file.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean replacement axiom-audit --verify data/axiom_audit.json --json",
                what: "verify the checked-in axiom audit without Python",
            },
            Example {
                cmd: "clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json",
                what: "write Rust-owned axiom-audit launch evidence",
            },
        ],
        see_also: &["replacement trust-core-evidence", "replacement status"],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Proof-system replacement certification #3697",
                target: "#3697",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Axiom audit data",
                target: "data/axiom_audit.json",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Axiom-audit launch evidence",
                target: "reports/axiom-audit-launch-evidence.json",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_NATIVE_LIBRARY_COVERAGE_MATRIX: FeatureDescriptor = FeatureDescriptor {
        path: &["replacement", "native-library", "coverage-matrix"],
        summary: "Generate or check native-library replacement coverage evidence (Experimental)",
        description: "\
Experimental Rust-owned native-library coverage evidence surface. The command \
generates the scoped native reducer coverage matrix, checks the committed \
`reports/native-library-replacement.json` matrix for drift, or updates that \
matrix in place. It intentionally does not claim complete Init, Std, or Mathlib \
API replacement; `--check-report` fails closed when the checked-in report no \
longer matches Rust source discovery.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean replacement native-library coverage-matrix --json",
                what: "emit the Rust-generated native-library coverage matrix",
            },
            Example {
                cmd: "clean replacement native-library coverage-matrix --check-report reports/native-library-replacement.json --json",
                what: "fail closed if the committed native-library report matrix drifted",
            },
        ],
        see_also: &[
            "replacement validate-report",
            "replacement native-library mathlib-api",
        ],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Native Init, Std, and core Mathlib replacement scorecards #3713",
                target: "#3713",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Native library replacement report",
                target: "reports/native-library-replacement.json",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_NATIVE_LIBRARY_API_SLICE: FeatureDescriptor = FeatureDescriptor {
        path: &["replacement", "native-library", "api-slice"],
        summary: "Prove a concrete native-library API slice (Experimental)",
        description: "\
Experimental Rust-owned native API slice scanner. The command fails closed \
unless the named slice is present in native reducer registrations and backed by \
focused Rust reducer tests. The checked-in report gate enumerates scoped native \
API slices, including Nat arithmetic, String, Decidable, Int order Decidable, signed Int Decidable equality alias, heterogeneous operation short-circuit, BEq short-circuit, Decidable decide/combinator, Nat order Decidable, Char, Int, Int8/Int16/Int32/Int64/ISize, UInt/USize, \
BitVec, System.Platform, Float arithmetic/comparison, Float Decidable comparison, \
Float classification, Float numeric function, Float input conversion, Float formatting, and Float output conversion evidence, without claiming \
complete Init, Std, or Mathlib replacement.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean replacement native-library api-slice --slice nat-arithmetic --json",
                what: "fail closed unless the Nat arithmetic/comparison native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice float-core --json",
                what: "fail closed unless the Float arithmetic/comparison native API slice is registered and tested",
            },
            // `float-decidable-comparisons` is documented in the
            // descriptor's prose but the corresponding `--slice` enum
            // variant has not been added to the clap parser. Once that
            // landed, restore the example here.
            Example {
                cmd: "clean replacement native-library api-slice --slice float-classification --json",
                what: "fail closed unless the Float classification native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice float-functions --json",
                what: "fail closed unless the Float numeric function native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice float-input-conversions --json",
                what: "fail closed unless the Float input conversion native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice float-formatting --json",
                what: "fail closed unless the Float formatting native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice float-output-conversions --json",
                what: "fail closed unless the Float output conversion native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice string-transform --json",
                what: "fail closed unless the String extraction/casing/intercalation native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice int-core --json",
                what: "fail closed unless the Int core native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice int-order-decidable --json",
                what: "fail closed unless the Int order Decidable native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice signed-decidable-eq-aliases --json",
                what: "fail closed unless the signed Int Decidable equality alias native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice hetero-ops --json",
                what: "fail closed unless the heterogeneous operation short-circuit native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice beq-shortcircuit --json",
                what: "fail closed unless the BEq.beq short-circuit native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice decidable-combinators --json",
                what: "fail closed unless the Decidable decide/combinator native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice nat-order-decidable --json",
                what: "fail closed unless the Nat order Decidable native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice int8-core --json",
                what: "fail closed unless the Int8 core native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice int16-core --json",
                what: "fail closed unless the Int16 core native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice int32-core --json",
                what: "fail closed unless the Int32 core native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice int64-core --json",
                what: "fail closed unless the Int64 core native API slice is registered and tested",
            },
            Example {
                cmd: "clean replacement native-library api-slice --slice isize-core --json",
                what: "fail closed unless the ISize core native API slice is registered and tested",
            },
        ],
        see_also: &[
            "replacement validate-report",
            "replacement native-library coverage-matrix",
            "replacement native-library mathlib-api",
        ],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Native Init, Std, and core Mathlib replacement scorecards #3713",
                target: "#3713",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Native library replacement report",
                target: "reports/native-library-replacement.json",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
};

pub(crate) const FEATURE_REPLACEMENT_NATIVE_LIBRARY_MATHLIB_API: FeatureDescriptor =
    FeatureDescriptor {
        path: &["replacement", "native-library", "mathlib-api"],
        summary: "Report fail-closed native Mathlib API replacement status (Experimental)",
        description: "\
Experimental fail-closed native Mathlib API replacement gate. The command \
returns structured NOT READY evidence showing that current Mathlib coverage is \
compatibility-only `.olean` evidence and cannot certify full native Mathlib API \
replacement. It exits nonzero until real native Mathlib API replacement evidence \
lands. `--expect-blocked` turns the current NOT READY state into a passing \
validation lane for reports that must prove they are not overclaiming native \
Mathlib replacement.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean replacement native-library mathlib-api --json",
                what: "emit fail-closed native Mathlib API replacement status",
            },
            Example {
                cmd: "clean replacement native-library mathlib-api --expect-blocked --json",
                what: "validate that native Mathlib replacement remains correctly blocked",
            },
        ],
        see_also: &[
            "replacement validate-report",
            "replacement native-library coverage-matrix",
        ],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Native Init, Std, and core Mathlib replacement scorecards #3713",
                target: "#3713",
            },
            Reference {
                kind: RefKind::Doc,
                label: "Native library replacement report",
                target: "reports/native-library-replacement.json",
            },
        ],
        domain_root: Some("replacement"),
        alternative_forms: &[],
        feature_gate: None,
    };
