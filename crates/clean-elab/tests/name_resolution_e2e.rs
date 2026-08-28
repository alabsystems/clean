// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! B03 gap sweep brick — name-resolution core
//! (docs/plans/GAP_SWEEP_2026-07-09.md §3, rows namespaces_scoping
//! p02/p03/p20/p21/p23).
//!
//! End-to-end (parse → elaborate → kernel re-check) pins for the three B03
//! sub-defects:
//!
//! 1. **Innermost-namespace-first resolution** (`Lean/ResolveName.lean`
//!    `resolveGlobalName`/`resolveUsingNamespace`: candidates from the current
//!    namespace outward win over the root; `_root_.x` forces the root). The
//!    silent-wrong witness SILENT_WRONG_SUSPECT-15 (`p21_shadow_inner_wins`)
//!    is pinned by VALUE: `Bar.useW` must equal the namespace `Bar.w = 2`,
//!    never the root `w = 1`.
//! 2. **No auto-bound implicits in term bodies** (`Lean/Elab/MutualDef.lean`
//!    `elabHeaders` runs under `withAutoBoundImplicit` — headers ONLY;
//!    validity rules in `Lean/Elab/Binders.lean`; an unknown identifier in a
//!    def/theorem VALUE position is a loud `unknown identifier`). OVER_ACCEPT
//!    rows p20 (section-variable leak) and p23 (typo'd body ident) must
//!    REJECT; signature-position auto-implicits stay intact.
//! 3. **Multi-segment qualified names** — Lean resolves `A.B.y` as ONE
//!    identifier via `resolveGlobalName`; clean's parser splits it into a
//!    projection chain, which must be reassembled and resolved through the
//!    namespace chain (declaration forms `namespace A namespace B` and
//!    `namespace A.B`; reference forms `A.B.c`, `B.c` inside `A`, `c` inside
//!    `A.B`) — rows p02/p03.
//!
//! Axiom hygiene: every positive declaration below has an EMPTY transitive
//! axiom closure (the `rfl` pins would fail otherwise; asserted explicitly).
//!
//! The rows live in `name_resolution_e2e/namespaces.rs` (sub-defects 1-2) and
//! `name_resolution_e2e/qualified_names.rs` (sub-defect 3 + the
//! diagnostic-distinction block), over the harness in
//! `name_resolution_e2e/common.rs`; this file binds them into one test binary.

// An integration-test crate ROOT resolves `mod` against `tests/`, not against a
// same-named directory, so each child module names its path explicitly.
#[path = "name_resolution_e2e/common.rs"]
mod common;
#[path = "name_resolution_e2e/namespaces.rs"]
mod namespaces;
#[path = "name_resolution_e2e/qualified_names.rs"]
mod qualified_names;
