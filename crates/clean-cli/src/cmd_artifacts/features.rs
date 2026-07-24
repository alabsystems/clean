// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors for the `clean artifacts` verb family.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const ARTIFACT_SYSTEM_DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Master design v2 §5.6 — the artifact system",
    target: "designs/2026-06-09-master-design-v2.md",
};

const CLEAN_MATHVERSE_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-mathverse (artifacts + release modules)",
    target: "clean-mathverse",
};

const CLEAN_CLI_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

/// Feature descriptors surfaced by `clean artifacts`.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["artifacts", "list"],
        summary: "List release artifacts of a repository (Experimental)",
        description: "\
Experimental v0 of the unified artifact system (master design v2 §5.6). \
Lists the releases of a GitHub repository (default: the clean repo) via a \
`gh release list` shell-out, or — with `--tag <TAG>` — the downloadable \
assets of a single release. `--json` emits a machine-readable index with \
tag names, publication timestamps, the latest marker, and per-asset sizes.\n\n\
Auth and private-repo access are delegated to the `gh` CLI, the same \
mechanism the Mathverse release pipeline uses.",
        category: Category::Build,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean artifacts list --json",
                what: "list recent releases of the clean repo as JSON",
            },
            Example {
                cmd: "clean artifacts list --tag mathverse-v1.2.0 --repo alabsystems/clean",
                what: "show the downloadable assets of one release tag",
            },
        ],
        see_also: &["artifacts get", "artifacts verify", "mathverse release"],
        references: &[
            ARTIFACT_SYSTEM_DESIGN_REF,
            CLEAN_MATHVERSE_CRATE_REF,
            CLEAN_CLI_CRATE_REF,
        ],
        domain_root: Some("artifacts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["artifacts", "get"],
        summary: "Download release assets with fail-closed blake3 verification (Experimental)",
        description: "\
Experimental v0 of the unified artifact system (master design v2 §5.6). \
Downloads assets of a release tag into a temp directory (optionally \
restricted by `--pattern <GLOB>`; a `*manifest.json` asset is always \
fetched in addition when present), verifies every downloaded file that \
appears in the manifest against its blake3 digest, and only then publishes \
the files into `--out`.\n\n\
Verification is mandatory and fail-closed: a checksum mismatch is ALWAYS a \
hard error. When no manifest asset exists, or downloaded files are not \
covered by it, the command refuses to publish unless `--allow-unverified` \
is passed — which emits a loud stderr warning and `\"verified\": false` in \
the `--json` report. `--skip-verify` is rejected outright.\n\n\
Note: corpus releases like `mathverse-v*` publish an archive whose manifest \
describes the *extracted* shard tree, not the archive asset itself — for \
those, pair `get --allow-unverified` with `clean artifacts extract`, which \
verifies the extracted tree against its embedded manifest before \
publishing.",
        category: Category::Build,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean artifacts get mathverse-v1.2.0 --pattern '*.tar.zst' --out downloads --allow-unverified --json",
                what: "download a corpus archive (verified later by `artifacts extract`)",
            },
            Example {
                cmd: "clean artifacts get mathverse-v1.2.0 --out downloads --json",
                what: "download all assets of a tag, fail-closed on manifest coverage",
            },
        ],
        see_also: &["artifacts list", "artifacts extract", "artifacts verify", "mathverse download"],
        references: &[
            ARTIFACT_SYSTEM_DESIGN_REF,
            CLEAN_MATHVERSE_CRATE_REF,
            CLEAN_CLI_CRATE_REF,
        ],
        domain_root: Some("artifacts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["artifacts", "verify"],
        summary: "Verify an artifact directory against its blake3 manifest (Experimental)",
        description: "\
Experimental v0 of the unified artifact system (master design v2 §5.6). \
Re-verifies a directory of artifacts against a blake3 manifest: every \
manifest entry is hashed and compared, missing files are reported, and any \
mismatch makes the command exit non-zero with per-file failure rows. The \
manifest defaults to the first `*manifest.json` found directly inside DIR \
(covering the Mathverse `mathverse-manifest.json` convention) and can be \
overridden with `--manifest <FILE>`. Generic manifests may list entries \
under a `files` key instead of `shards`.\n\n\
Hard guards: zero-entry manifests are rejected (no vacuous passes), and \
manifest entry paths containing `..` or absolute components are a hard \
error (path-traversal guard).",
        category: Category::Build,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean artifacts verify data/mathverse-library --json",
                what: "re-verify an installed corpus directory against its manifest",
            },
            Example {
                cmd: "clean artifacts verify downloads --manifest downloads/artifact-manifest.json",
                what: "verify against an explicitly chosen manifest file",
            },
        ],
        see_also: &["artifacts get", "artifacts extract", "mathverse verify"],
        references: &[
            ARTIFACT_SYSTEM_DESIGN_REF,
            CLEAN_MATHVERSE_CRATE_REF,
            CLEAN_CLI_CRATE_REF,
        ],
        domain_root: Some("artifacts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["artifacts", "extract"],
        summary: "Extract an artifact archive and verify the tree before publishing (Experimental)",
        description: "\
Experimental v0 of the unified artifact system (master design v2 §5.6). \
Extracts a `.tar.zst`, `.tar.gz`, or `.tgz` archive into a temp directory \
(`--strip-components <N>`, default 1), looks for an embedded \
`*manifest.json` in the extracted tree, verifies every manifest entry's \
blake3 digest fail-closed, and only then publishes the tree into `--out`. \
Unsupported archive suffixes are a typed error — extraction never \
guesses.\n\n\
A checksum mismatch or missing manifest entry is ALWAYS a hard error and \
nothing is published. A tree with no embedded manifest requires \
`--allow-unverified` (loud stderr warning, `\"verified\": false` in the \
`--json` report). `--skip-verify` is rejected outright. This is the \
verification step that makes `artifacts get --allow-unverified` of corpus \
archives safe end-to-end.",
        category: Category::Build,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean artifacts extract downloads/mathverse-library-v1.2.0.tar.zst --out data/mathverse-library --json",
                what: "unpack a corpus archive and publish only after blake3 verification",
            },
            Example {
                cmd: "clean artifacts extract bundle.tar.gz --out vendor/bundle --strip-components 0 --allow-unverified",
                what: "unpack a manifest-less archive with the explicit unverified override",
            },
        ],
        see_also: &["artifacts get", "artifacts verify", "mathverse download"],
        references: &[
            ARTIFACT_SYSTEM_DESIGN_REF,
            CLEAN_MATHVERSE_CRATE_REF,
            CLEAN_CLI_CRATE_REF,
        ],
        domain_root: Some("artifacts"),
        alternative_forms: &[],
        feature_gate: None,
    },
];
