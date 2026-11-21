// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Static feature descriptor registry for the `clean` CLI.
//!
//! Domain crates register their `FeatureDescriptor` arrays here with one
//! `v.extend(clean_<domain>::cli::FEATURES)` line per crate. The coverage
//! gate in `tests/feature_coverage.rs` asserts that every clap subcommand
//! either has a matching descriptor or is listed in [`META_PATHS`].
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

pub(crate) const EVIDENCE_FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["evidence", "check"],
        summary: "Check recorded evidence figures offline",
        description: "\
Read each named figure's existing record through its adapter, or every registered \
figure with `--all`. A planned figure with no record producer reports its catalog \
absence reason without reading the checkout. Each adapter re-derives the record's counts from its rows and \
compares any W0 scoreboard row or ratchet that restates them. The historical \
planted-`False`, island-gap, elaboration, rule-family and C3 readers recount their \
reports. The historical K3 figures `selfproof.decided_by_compiled_kcheck` and \
`selfproof.accepted_by_kcheck_no_site` validate the K3 coverage receipt and compare \
the exact scoreboard row; the row records a stable absence when the receipt is \
missing or a listed source has moved, and the figure then reads absent. Use \
`clean evidence check-k3-coverage` to check the receipt directly. \
`model.lean.families` checks that `data/cic_l_rule_ratchet.json` names \
exactly the inventory's unspecified families and has not grown against HEAD. \
`tooling.python_minters` reads `data/python_minters_evidence.json` and compares its \
counts and digests with the current Git index and exact gate registry bytes. \
The local gate checks the falling membership rule separately. \
`frontend.native_exec_battery` and `frontend.tactic_parity` first apply the \
`clean replacement` evidence contract; a vacuous artifact reads absent. \
`suite.recorded_targets` checks each `data/suite_state` record's status against its \
exit code and counts. A record with a pinned input digest is fresh or stale; a stale \
record fails. A record without one has unknown freshness, which never passes as \
fresh. Quorum rechecking uses separate evidence. The check uses the current \
directory unless `--repo-root <PATH>` is given. Exit 0 means every check passed or \
the figure is absent. Exit 1 means a record is inconsistent or stale, 2 means \
invalid usage or an unknown figure, and 3 means an input is unavailable here. \
With several figures each prints one line and the worst exit wins.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean evidence check --all --repo-root .",
                what: "check every registered figure in this checkout",
            },
            Example {
                cmd: "clean evidence check selfproof.planted_false.trust --repo-root .",
                what: "check the recorded Trust planted-`False` figure in this checkout",
            },
            Example {
                cmd: "clean evidence check model.lean.families suite.recorded_targets",
                what: "check the rule-family ratchet and the suite records",
            },
            Example {
                cmd: "clean evidence check selfproof.decided_by_compiled_kcheck --repo-root .",
                what: "check the recorded count of declarations decided by the compiled checker",
            },
            Example {
                cmd: "clean evidence check selfproof.accepted_by_kcheck_no_site --repo-root .",
                what: "check the interim acceptance count and its denominators",
            },
        ],
        see_also: &[
            "evidence list",
            "evidence explain",
            "evidence status",
            "evidence check-k3-coverage",
            "evidence check-k3-sources",
            "evidence check-k3-packet-syntax",
            "evidence check-k3-export-syntax",
            "replacement status",
        ],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "meaning-digest"],
        summary: "Compute the canonical meaning digest of one exported package declaration",
        description: "Read the as-written NDJSON export and the original compiled module inventory. \
The module name is a caller-supplied label. The SHA-256 of each compiled part identifies the \
inventory source. Print the package digest and format version, reachable singleton digests, inventory, export hash and \
structural refusals as JSON. A reachable missing, refused or unreplayable declaration prevents a \
digest. Outside-closure refusals are recorded. The structural reading measures identity. Kernel \
type checking and production authority have separate evidence.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean evidence meaning-digest --export subject.ndjson --module KCheck.Token --olean Token.olean --root KCheck.Advice.start",
            what: "measure the original checker definition using its full module inventory",
        }],
        see_also: &["evidence check"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Canonical checker-definition comparison",
            target: "reports/self-proof-w3-advice-start/canonical/README.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "list"],
        summary: "List supported evidence figures and their check inputs",
        description: "\
Print the catalog of figures supported by `clean evidence check`. Each entry names \
its plan unit, lane, producer and local check inputs. The cost class describes the \
check. Each entry identifies headline and historical figures and gives the configured \
ratchet direction. In `--json` output an absent ratchet or producer module is `null`. \
The island-gap and rule-family inventories are manually recorded. \
`selfproof.decided_by_compiled_kcheck` is the historical K3 headline figure. \
`selfproof.accepted_by_kcheck_no_site` is the historical K3 route figure. Both checks \
use the validated coverage receipt and the W0 scoreboard. Planned figures with no \
record producer list their absence reason in the text and in `absent_reason` in JSON. Listing \
works without a Clean checkout or evidence files.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean evidence list",
                what: "browse available figure IDs and check inputs",
            },
            Example {
                cmd: "clean evidence list --json",
                what: "read the catalog and both historical K3 entries as a JSON array",
            },
        ],
        see_also: &["evidence check", "evidence explain"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "explain"],
        summary: "Show the recorded provenance of an evidence figure",
        description: "\
Show the recorded provenance or source paths for an evidence figure. The \
planted-`False` reports supply dates, revisions, toolchains and test-leg commands. \
The island-gap inventory names the measured compiler, subject and probe record. \
The elaboration baseline records the run binary, date and producer commit. The \
rule inventory identifies its upstream Lean pin and specification root. The C3 \
reader lists matching theorem statements and paths from the source scan. For \
`selfproof.decided_by_compiled_kcheck` and `selfproof.accepted_by_kcheck_no_site`, \
the explanation gives the recorded run command, Lean toolchain pin and version, \
and executable digest even when listed sources have moved. For other figures the \
output shows the commit, date, labels, non-claims and freshness of the reading. \
Planned figures with no record producer show their absence reason and plan unit without \
reading the checkout. Missing provenance is shown as unavailable. The output also names the input paths that \
`clean evidence check` uses. Read the report from the current directory or from `--repo-root <PATH>` \
if given. Use `clean evidence check` to compare the measurements with the scoreboard.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean evidence explain selfproof.planted_false.clean --repo-root .",
                what: "show the recorded Clean experiment provenance",
            },
            Example {
                cmd: "clean evidence explain selfproof.planted_false.trust --repo-root .",
                what: "show the Trust revision and Clean pin from the recorded experiment",
            },
            Example {
                cmd: "clean evidence explain selfproof.island_gaps --repo-root .",
                what: "show the recorded island probe and its compiler",
            },
            Example {
                cmd: "clean evidence explain selfproof.accepted_by_kcheck_no_site --repo-root .",
                what: "show the recorded K3 run and its executable digest",
            },
        ],
        see_also: &["evidence check", "evidence list"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "status"],
        summary: "Show the evidence board in design order",
        description: "\
Render the board: rows 1 to 17 in the order of section 4 of the combined Trust \
design, then the other registered figures. A measured row shows the value, the \
denominator with its count, scope and digest, labels and non-claims, the recorded \
commit, the record's age in days and its freshness. Freshness is fresh or stale only \
where the record pins an input digest, and unknown otherwise. Age is shown and never \
decides freshness. A figure that no producer mints yet is shown as absent with the \
reason and the unit that owes it, never as zero. An inconsistent or unavailable row \
gives the reason in place of a value. Use `--json` for a JSON array or `--markdown \
<OUT>` to write a Markdown table. The survey exits 0 when it renders the rows. With \
`--scoreboard`, derive all eight W0 rows directly from their source artifacts and \
print the historical scoreboard format; add `--json` for canonical W0 v1 JSON. The \
render modes read the historical sources directly. Missing source artifacts and \
stale K3 source pins produce explicit absence rows. Invalid source data fails the \
derivation. With `--scoreboard --check`, compare the canonical derivation with the \
exact saved bytes, including line endings and final LF. A match prints \
`SELF_PROOF_SCOREBOARD=ok the record matches its sources` and exits 0. A missing or \
different board or invalid source exits 1. With `--scoreboard --write`, derive and \
atomically publish the canonical bytes to `data/self_proof_scoreboard.json`, then \
print the scoreboard and written path. An existing destination must be a regular \
file. Invalid arguments exit 2. Unavailable inputs or a destination I/O failure exit \
3. `--check` and `--write` require `--scoreboard`. They are mutually exclusive and \
both conflict with `--json`. Use the current directory unless `--repo-root <PATH>` \
is given. Use `clean evidence check` for a process exit code based on the evidence.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean evidence status",
                what: "show the board for this checkout",
            },
            Example {
                cmd: "clean evidence status --json --repo-root .",
                what: "read the board rows as JSON",
            },
            Example {
                cmd: "clean evidence status --markdown board.md",
                what: "write the board as a Markdown table",
            },
            Example {
                cmd: "clean evidence status --scoreboard --json",
                what: "derive canonical W0 JSON from the historical source artifacts",
            },
            Example {
                cmd: "clean evidence status --scoreboard --check --repo-root .",
                what: "check the saved W0 board against freshly derived canonical bytes",
            },
            Example {
                cmd: "clean evidence status --scoreboard --write --repo-root .",
                what: "publish the canonical W0 board in the checkout",
            },
        ],
        see_also: &["evidence check", "evidence explain", "evidence list"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "check-rule-lean-references"],
        summary: "Check Lean rule references and discover unlisted controls",
        description: "\
Read `data/cic_l_rule_inventory.json` and check cited names, declaration kinds \
and rule-carrier constructor coverage with Clean's production parser. Check \
the cited ground control statements and scan the full specification and control \
root scope for unlisted controls. The reverse check compares the constructor, \
theorem name and resolved source file. JSON lists matched references, control \
bindings, unreadable inputs and findings. Parser recovery makes a source \
unreadable. Use the current directory or give `--repo-root <PATH>`. Exit 0 means \
the checks passed, 1 means an invalid reference or inventory, 2 means invalid \
usage and 3 means a required source input was unavailable for a complete check.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean evidence check-rule-lean-references --repo-root .",
            what: "check cited Lean references and the controls found across the source scope",
        }],
        see_also: &["evidence check", "evidence status"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "check-rule-cpp-anchors"],
        summary: "Check pinned C++ rule source files and raw line digests",
        description: "\
Cross-check the Lean kernel C++ source pins against the upstream record and \
Lean toolchain. JSON reports raw and masked file measurements and each \
derived function's name, inclusive line range, raw SHA-256 digest, switch \
arms, nonblank masked line numbers and hardcoded constant occurrences. \
Check that each recorded anchor is inside its named function and matches \
the raw bytes of its inclusive line range. Add `--coverage` to require rows \
for every function, split switch arm and nonblank line, and to check both \
directions of constant ownership. Use the current directory or give \
`--repo-root <PATH>`. Exit 0 means the checks passed, 1 means invalid evidence, \
2 means invalid usage and 3 means a required input was unavailable.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean evidence check-rule-cpp-anchors --repo-root .",
                what: "verify the pinned C++ inputs and recorded raw line digests",
            },
            Example {
                cmd: "clean evidence check-rule-cpp-anchors --coverage --repo-root .",
                what: "also verify coverage by the inventory rows",
            },
        ],
        see_also: &["evidence check-rule-lean-references", "evidence check"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "check-rule-inventory"],
        summary: "Check rule inventory sources, row shape, and incomplete-family status",
        description: "\
Read a single inventory snapshot and check pinned C++ coverage, Lean references \
and ground controls, rule-row shape, and the recorded status of every incomplete \
family. JSON contains the row, C++ and Lean reports and any inputs that could \
not be checked. Give `--require-complete` to require that every family is \
specified after the consistency checks pass. Use the current directory or \
give `--repo-root <PATH>`. Exit 0 means the checks passed, 1 means inconsistent \
evidence or a failed completeness requirement, 2 means invalid usage and 3 \
means a required input was unavailable.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean evidence check-rule-inventory --repo-root .",
            what: "check inventory coverage, references and recorded statuses",
        }],
        see_also: &[
            "evidence check-rule-cpp-anchors",
            "evidence check-rule-lean-references",
        ],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "check-k3-sources"],
        summary: "Check recorded K3 executable sources and digests",
        description: "\
Read the source pins in `data/kcheck_coverage.json`. Reconstruct the K3 executable's \
Lean import closure and Lake build inputs, compare their SHA-256 digests, and check \
the recorded Lean toolchain. This diagnostic covers the source portion of K3. \
Use the current directory or give `--repo-root <PATH>`. Exit 0 means the source \
check passed, 1 means an invalid record or closure, and 3 means stale or unavailable \
inputs. Invalid command arguments exit 2.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean evidence check-k3-sources --repo-root .",
            what: "compare the recorded K3 source closure with this checkout",
        }],
        see_also: &["evidence check-k3-coverage", "evidence check-k3-packet-syntax", "evidence check"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "check-k3-coverage"],
        summary: "Check the canonical K3 coverage receipt",
        description: "\
Read `data/kcheck_coverage.json` and rederive its canonical v1 bytes from the \
validated export, advice and transcript. Verify the listed source digests, the \
executable's Lean import closure and Lake build inputs, and the pinned toolchain. \
The executable digest is recorded run provenance for this offline check. Use the \
current directory or give `--repo-root <PATH>`. Exits are 0 for a matching receipt, \
1 for a refusal, 2 for invalid arguments, and 3 for an absent receipt or stale or \
unavailable source inputs.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean evidence check-k3-coverage --repo-root .",
            what: "check the recorded coverage receipt, packet and source pins",
        }],
        see_also: &["evidence check-k3-sources", "evidence check-k3-packet-syntax", "evidence status"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "check-k3-packet-syntax"],
        summary: "Check K3 advice framing and transcript syntax",
        description: "\
Read the advice and version-1 transcript in `data/kcheck_coverage`. Check minimal \
unsigned LEB128 lengths, transcript headers and rows, and statement placement. \
Add `--check-consistency` to correlate frames, rows and summary and check IOTA \
and K flags. Add `--check-declaration-index` to bind each physical line and kind \
in the transcript to the validated export. Add `--check-non-inductive-bodies` \
to also check definition, theorem, opaque, axiom and quotient fields, earlier \
references and unique names among those bodies. The body check counts inductive \
envelopes separately. Add `--check-declaration-bodies` to also check inductive \
members and rules, constructor order and ownership, and unique names across all \
declarations. Add `--check-declaration-names` to also compare the exact transcript \
name of each export declaration. Add `--check-accepted-statements` to also compare \
the level parameter count, type echo, and value echo of each accepted row with the \
export. Add `--check-base-families` to also compare recognition of the pinned Eq, \
PUnit and Nat inductive blocks with the transcript. Add `--check-fragment-classes` \
to bind every declaration's coarse fragment class to the export. Accepted and \
refused rows both report the inside class. Add `--check-dependency-refusals` to \
check that the run accepted each earlier inside declaration cited by an accepted row \
and that dependency refusals name a cited earlier inside declaration still awaiting \
acceptance. Refused advice payloads remain opaque. Add `--coverage-figures` to run \
the dependency and earlier checks and write canonical coverage figure JSON. This \
flag selects figure JSON even with `--json` or earlier check flags. Use `--json` \
for frame lengths, rows and the reported summary, with decimal fields retained as \
strings. Inputs come from the current directory or `--repo-root <PATH>`. Exits are \
0 for success, 1 for invalid or inconsistent inputs, 2 for invalid arguments, and \
3 for unavailable inputs. Use `clean evidence check-k3-coverage` for the full \
canonical receipt and source check.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean evidence check-k3-packet-syntax --json --repo-root .",
                what: "read the frame lengths, declaration rows, and reported summary",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-consistency",
                what: "check the advice and transcript for agreement",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-declaration-index",
                what: "check the packet and bind declaration lines and kinds to the export",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-non-inductive-bodies",
                what: "also check required fields and earlier references in non-inductive bodies",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-declaration-bodies",
                what: "also check inductive blocks and unique names across all declarations",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-declaration-names",
                what: "also bind every exact transcript declaration name to the export",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-accepted-statements",
                what: "also bind each accepted statement and level parameter count to the export",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-base-families",
                what: "also check that the transcript recognises exactly the pinned base blocks",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-fragment-classes",
                what: "also compare inside, outside and recognised classes with the export",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --check-dependency-refusals",
                what: "also check accepted dependency order and bind dependency refusals to cited declarations",
            },
            Example {
                cmd: "clean evidence check-k3-packet-syntax --coverage-figures",
                what: "derive canonical coverage figure JSON from the checked packet and export",
            },
        ],
        see_also: &["evidence check-k3-coverage", "evidence check-k3-sources", "evidence check-k3-export-syntax"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["evidence", "check-k3-export-syntax"],
        summary: "Check K3 export syntax and the lean4export 3.1.0 header",
        description: "\
Read the tracked gzip-compressed K3 export. Require compact LF-terminated JSON with canonical natural-number tokens \
and an initial meta record with exact lean4export format 3.1.0. Add \
`--check-names` for consecutive IDs and exact name identity, or `--check-levels` for names and \
levels. Add `--check-expressions` for all three tables, including exact \
expression payloads, earlier references and the 1,048,576-node unfolded \
size limit. Read from the current directory or give `--repo-root <PATH>`. \
Exit 0 means the requested checks passed, 1 means invalid inputs, and 3 \
means unavailable input. Invalid command arguments exit 2. K3 coverage \
also requires validating declarations.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean evidence check-k3-export-syntax --repo-root .",
                what: "check the NDJSON syntax of the recorded K3 export",
            },
            Example {
                cmd: "clean evidence check-k3-export-syntax --check-names",
                what: "check the explicit name table",
            },
            Example {
                cmd: "clean evidence check-k3-export-syntax --check-levels",
                what: "check the explicit names and levels and report the maximum unfolded level size",
            },
            Example {
                cmd: "clean evidence check-k3-export-syntax --check-expressions",
                what: "check the name, level, and expression tables and report their sizes",
            },
        ],
        see_also: &["evidence check-k3-packet-syntax", "evidence check-k3-sources"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Combined Trust design, evidence CLI",
            target: "designs/2026-11-16-full-rust-lean-models-combined-trust.md",
        }],
        domain_root: Some("evidence"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// Collect every `FeatureDescriptor` surfaced by the `clean` binary.
///
/// Registration order is stable: one `v.extend(...)` per owning crate, grouped
/// by top-level verb. Phase 3 absorbed `discover` (#3449), `tlaps bench`
/// (#3448), and `mathverse` (#3440) orphan binaries into the unified CLI; the
/// `lake` subcommand tree migrated in #3479.
#[must_use]
pub(crate) fn all_features() -> Vec<&'static FeatureDescriptor> {
    let mut v: Vec<&'static FeatureDescriptor> = Vec::new();
    // Phase 2 — owning-crate migrations
    v.extend(clean_c_sem::cli::FEATURES);
    // #3451: Rust verification verb (Experimental). Nested under
    // `clean verify rust` so future language migrations can drop in.
    v.extend(clean_rust_sem::cli::FEATURES);
    // #3454: Automation entry point (Experimental). Nested under
    // `clean auto prove` so sibling verbs (`auto premise`, `auto smt`, …)
    // can drop in without reshaping the top-level clap tree.
    v.extend(clean_auto::cli::FEATURES);
    // #3452: TLA+ obligation verification verb (Experimental). Nested under
    // `clean verify tla` next to `verify rust`.
    v.extend(clean_tla::cli::FEATURES);
    v.extend(clean_server::cli::FEATURES);
    v.extend(clean_fold::cli::FEATURES);
    // `commit` verbs live in clean-fold's absorbed `commit` module
    // (ex clean-commit; rearch stage 9 facade consolidation).
    v.extend(clean_fold::commit::cli::FEATURES);
    v.extend(clean_kernel::cli::FEATURES);
    // Phase 3 kernel-verb orphan absorptions (Epic #3436: #3443/#3444/#3446/#3447).
    // Published separately to keep `clean-kernel/src/cli/mod.rs` under the
    // 500-line file-size cap.
    v.extend(clean_kernel::cli::KERNEL_VERB_FEATURES);
    v.extend(clean_elab::cli::FEATURES);
    v.extend(clean_lake::cli::FEATURES);
    v.extend(crate::cli::FEATURES);
    // `clean lean` — the `lean`-compatible front door (decision R74).
    v.extend(crate::cmd_lean::FEATURES);
    v.extend(crate::cli::bench::FEATURES);
    v.extend(crate::cli::promote::FEATURES);
    v.extend(crate::cmd_research::FEATURES);
    v.extend(crate::cmd_replacement::FEATURES);
    v.extend(EVIDENCE_FEATURES);
    v.extend(crate::cmd_factory::FEATURES);
    v.extend(crate::cmd_math::FEATURES);
    // `clean math-map ingest` + `clean math-map keys list|verify` — the
    // user-facing entry point for the fail-closed MathMap/Harmonic Lean
    // patch-bundle ingest pipeline in `clean_mathverse::math_map`.
    v.extend(crate::cmd_math_map::FEATURES);
    // `clean drift snapshot|diff` — the user-facing entry point for the
    // statement-preservation snapshot/diff engine in `clean_mathverse::drift`.
    v.extend(crate::cmd_drift::FEATURES);
    // `clean false-controls run|replay-attempt` — the user-facing entry point
    // for the known-bad-input probe engine in
    // `clean_mathverse::false_control_suite`.
    v.extend(crate::cmd_false_controls::FEATURES);
    v.extend(crate::cmd_project::FEATURES);
    v.extend(crate::cmd_attempts::FEATURES);
    // `clean prove run/status/list` — submit a Lean goal to a remote / automated
    // prover backend (Aristotle / ax-prover), retrieve the proof, and re-verify
    // it locally (lake build + #print axioms ⊆ foundational allowlist).
    v.extend(crate::cmd_prove::FEATURES);
    // `clean cake build/graduate/verify` — the Layer-1 CAKE project lifecycle
    // (build → graduate → verify) whose handlers live in `clean-cli`.
    v.extend(crate::cmd_cake::FEATURES);
    // `clean solver index-build/stats/weak/vbs-gap/export-dataset` — Phase-1
    // solver-results-cache tooling over the captured telemetry stream.
    v.extend(crate::cmd_solver::FEATURES);
    // `clean vendor fetch/package/status/clean` — vendored-sources lifecycle for
    // offline/reproducible builds (artifact-based; replaces fetch_vendor.sh).
    v.extend(crate::cmd_vendor::FEATURES);
    // Artifact system v0 (master design v2 §5.6): `clean artifacts
    // list/get/verify/extract` — generic release-artifact logistics with
    // mandatory fail-closed blake3 manifest verification.
    v.extend(crate::cmd_artifacts::FEATURES);
    // `clean audit trust-ledger` — per-declaration recursive trust ledger
    // diagnostic ported from the divergent `consolidation` branch.
    v.extend(crate::cmd_audit::FEATURES);
    // Phase 3 — absorbed orphan binaries
    v.extend(clean_discovery::cli::FEATURES);
    // `tlaps` verbs live in clean-tla's absorbed `bench::cli` module
    // (ex clean-tlaps-bench; rearch stage 9 facade consolidation).
    v.extend(clean_tla::bench::cli::FEATURES);
    v.extend(clean_mathverse::cli::FEATURES);
    // Phase 3.5 (#3512) — browse-oriented mathverse verbs absorbed into the
    // unified `clean mathverse <verb>` tree (list / sample / deps / version).
    // Kept in a separate descriptor module so each file stays under the
    // 500-line cap (see `designs/2026-04-19-epic-3436-orphan-triage.md`).
    v.extend(clean_mathverse::cli::BROWSE_FEATURES);
    // Phase 3.5 (#3512) — the 7 passthrough-absorbed mathverse verbs
    // (find / graph / diff / verify / download / export / release) that
    // regressed between `ae3772027` (original absorption) and
    // `f43429751` (partial re-type) and were re-absorbed via
    // `PassthroughArgs` delegation. See `descriptors_passthrough.rs` for
    // the full rationale on why passthrough (not typed-arg) is the right
    // design for these 7 verbs.
    v.extend(clean_mathverse::cli::PASSTHROUGH_FEATURES);
    // Phase 3.5 (#3513) — descriptor-only surfaces for the standalone
    // `mathverse_convert` and `mathverse_shard` operator binaries. These carry
    // `Category::OperatorTools` and are exempt from the clap-routability
    // drift check because they are intentionally not absorbed into the
    // unified `clean` clap tree (see `designs/2026-04-19-epic-3436-orphan-triage.md`).
    v.extend(clean_mathverse::cli::OPERATOR_TOOLS_FEATURES);
    v.extend(clean_olean::cli::FEATURES);
    v.extend(clean_lsp::cli::FEATURES);
    // Phase 3.5 — `clean verify proof` (#3511).
    #[cfg(feature = "sat-verify")]
    v.extend(clean_verify::cli::FEATURES);
    // Phase 4 — #3453: `clean compile` MVP (Experimental).
    v.extend(clean_compiler::cli::FEATURES);
    v
}

/// Clap subcommand paths that are intentionally _not_ backed by a
/// `FeatureDescriptor`.
///
/// Two categories live here:
///
/// 1. **True meta commands** (`features`, `help`) — these describe or host
///    the feature index itself rather than expose a new domain feature.
/// 2. **Pre-existing paths not yet migrated** — clap subcommands whose owning
///    crate still needs a `cli::FEATURES` array.
///
/// The goal of the gate is to prevent **new** clap paths from being added
/// without a matching descriptor once Phase 2+ lands. Pre-existing paths are
/// grandfathered until migrated.
pub(crate) const META_PATHS: &[&[&str]] = &[
    // --- True meta commands ---
    &["features"],
    &["help"],
];
