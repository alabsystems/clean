// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared mapping from Lean 4 `ConstantKind` variants to shard-level [`DeclKind`].
//!
//! Two `ConstantKind` enums exist in the codebase:
//!
//! - [`clean_olean::module::ConstantKind`] — produced by the pre-type-checked
//!   `.olean` parser. Includes `Inductive`, `Constructor`, `Recursor`, `Quot`
//!   variants in addition to the core `Axiom`/`Definition`/`Theorem`/`Opaque`.
//! - [`clean_kernel::ConstantKind`] — the post-kernel-load representation
//!   attached to a `ConstantInfo` inside an `Environment`. Only four variants:
//!   `Definition`, `Theorem`, `Opaque`, `Axiom`. Inductive machinery and Quot
//!   are stored as separate `Declaration` shapes, not as `ConstantKind`.
//!
//! Both paths emit `MathverseConstantHeader`s and must populate `decl_kind`
//! correctly. Before this helper existed the olean-bridge and env-import
//! writers hardcoded `decl_kind: 0` (= `DeclKind::Theorem`), silently
//! mis-tagging every axiom/definition/inductive/recursor as a theorem
//! (issue #3520). This module is the single source of truth for the
//! mapping; both helpers MUST stay in lock-step.

use crate::types::DeclKind;

/// Map a parsed-`.olean` [`clean_olean::module::ConstantKind`] to a shard-level
/// [`DeclKind`].
///
/// `ConstantKind` is `#[non_exhaustive]` on the olean side; the wildcard arm
/// falls back to `DeclKind::Definition` so a future Lean 4 kind never silently
/// re-enters the `DeclKind::Theorem` trap (discriminant 0).
#[must_use]
pub(crate) fn decl_kind_from_olean(kind: &clean_olean::module::ConstantKind) -> DeclKind {
    use clean_olean::module::ConstantKind as OK;
    match kind {
        OK::Theorem => DeclKind::Theorem,
        OK::Definition => DeclKind::Definition,
        OK::Axiom => DeclKind::Axiom,
        OK::Opaque => DeclKind::Opaque,
        OK::Inductive => DeclKind::Inductive,
        OK::Constructor => DeclKind::Constructor,
        OK::Recursor => DeclKind::Recursor,
        OK::Quot => DeclKind::Quot,
        // `ConstantKind` is `#[non_exhaustive]`; default unknown kinds to
        // `Definition` as a safe, non-`Theorem` fallback. Downstream consumers
        // can still disambiguate via `source_system` + `axiom_profile`.
        _ => DeclKind::Definition,
    }
}

/// Map a kernel [`clean_kernel::ConstantKind`] (attached to a `ConstantInfo`)
/// to a shard-level [`DeclKind`].
///
/// The kernel representation only carries the four core variants; the
/// inductive-family distinctions (`Inductive`, `Constructor`, `Recursor`,
/// `Quot`) live on separate `Declaration` shapes rather than on
/// `ConstantKind`. The env-import writer therefore cannot emit
/// `DeclKind::{Inductive,Constructor,Recursor,Quot}` from `ConstantKind`
/// alone — the caller must layer that on explicitly when the surrounding
/// context (e.g., `Declaration::Inductive`) provides it.
#[must_use]
pub(crate) fn decl_kind_from_kernel(kind: clean_kernel::ConstantKind) -> DeclKind {
    use clean_kernel::ConstantKind as KK;
    match kind {
        KK::Theorem => DeclKind::Theorem,
        KK::Definition => DeclKind::Definition,
        KK::Axiom => DeclKind::Axiom,
        KK::Opaque => DeclKind::Opaque,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn olean_all_variants_map_to_distinct_non_theorem_kinds() {
        use clean_olean::module::ConstantKind as OK;
        assert_eq!(decl_kind_from_olean(&OK::Axiom), DeclKind::Axiom);
        assert_eq!(decl_kind_from_olean(&OK::Definition), DeclKind::Definition);
        assert_eq!(decl_kind_from_olean(&OK::Theorem), DeclKind::Theorem);
        assert_eq!(decl_kind_from_olean(&OK::Opaque), DeclKind::Opaque);
        assert_eq!(decl_kind_from_olean(&OK::Quot), DeclKind::Quot);
        assert_eq!(decl_kind_from_olean(&OK::Inductive), DeclKind::Inductive);
        assert_eq!(
            decl_kind_from_olean(&OK::Constructor),
            DeclKind::Constructor
        );
        assert_eq!(decl_kind_from_olean(&OK::Recursor), DeclKind::Recursor);
    }

    #[test]
    fn kernel_four_variants_map_correctly() {
        use clean_kernel::ConstantKind as KK;
        assert_eq!(decl_kind_from_kernel(KK::Axiom), DeclKind::Axiom);
        assert_eq!(decl_kind_from_kernel(KK::Definition), DeclKind::Definition);
        assert_eq!(decl_kind_from_kernel(KK::Theorem), DeclKind::Theorem);
        assert_eq!(decl_kind_from_kernel(KK::Opaque), DeclKind::Opaque);
    }

    #[test]
    fn olean_axiom_does_not_map_to_theorem_default() {
        use clean_olean::module::ConstantKind as OK;
        // Regression guard for #3520: axioms must not be silently tagged
        // `DeclKind::Theorem` (discriminant 0). Before the fix, `decl_kind: 0`
        // was hardcoded in `lean4_olean_bridge.rs` and `lean4/env_import.rs`
        // and every axiom round-tripped as a theorem.
        assert_ne!(decl_kind_from_olean(&OK::Axiom), DeclKind::Theorem);
        assert_ne!(decl_kind_from_olean(&OK::Definition), DeclKind::Theorem);
        assert_ne!(decl_kind_from_olean(&OK::Inductive), DeclKind::Theorem);
    }

    #[test]
    fn kernel_axiom_does_not_map_to_theorem_default() {
        use clean_kernel::ConstantKind as KK;
        // Regression guard for #3520 on the env-import path.
        assert_ne!(decl_kind_from_kernel(KK::Axiom), DeclKind::Theorem);
        assert_ne!(decl_kind_from_kernel(KK::Definition), DeclKind::Theorem);
        assert_ne!(decl_kind_from_kernel(KK::Opaque), DeclKind::Theorem);
    }
}
