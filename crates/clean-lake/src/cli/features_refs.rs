// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared `Reference` values for the lake `FeatureDescriptor` array.
//!
//! Every descriptor in [`super::features`] points at the same design doc,
//! epic, and owning crate, so the references are defined once here and
//! borrowed via [`COMMON_REFS`].

use clean_features::{RefKind, Reference};

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const EPIC_REF: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic #3436 — unified CLI as feature index",
    target: "#3436",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-lake",
    target: "clean-lake",
};

/// References shared by every lake `FeatureDescriptor` — the design doc,
/// the epic issue, and the `clean-lake` crate itself.
pub(super) const COMMON_REFS: &[Reference] = &[DESIGN_REF, EPIC_REF, CRATE_REF];
