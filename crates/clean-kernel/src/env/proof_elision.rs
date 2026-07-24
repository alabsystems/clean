// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded-memory closure loading: eliding never-unfolded proof VALUES from a
//! TRUSTED IMPORTED closure environment (Mathverse Subsumption Engine WS3).
//!
//! # Why this is sound
//!
//! When an [`Environment`](super::Environment) is loaded purely as the TRUSTED
//! IMPORTED CONTEXT used to type-check a *separate* target module, the kernel
//! needs, for each imported constant:
//!
//! * its TYPE (to type references to it), and
//! * — only for constants that can be δ-unfolded — its VALUE.
//!
//! The kernel's single δ-unfold entry point is
//! [`Environment::unfold_definition`](super::Environment::unfold_definition)
//! (`env/unfold.rs`). That function returns `None` — i.e. refuses to unfold —
//! for any constant whose [`ConstantKind`](super::ConstantKind) is `Opaque`
//! (and for `Axiom`, which has no value). An `Opaque`-kind constant's VALUE is
//! therefore NEVER read during `whnf` / `is_def_eq`, so dropping it cannot
//! change any type-checking verdict.
//!
//! # Why THEOREM values are NOT in the default-safe subset
//!
//! In THIS kernel `unfold_definition` unfolds `Theorem`-kind constants too
//! (it mirrors Lean 4's `has_value(false)`, which is true for definitions AND
//! theorems — `env/unfold.rs:165` and the `lazy_delta` callers in
//! `tc/def_eq/delta.rs`). A theorem head reached during lazy-delta reduction
//! will be unfolded whenever proof irrelevance does not first short-circuit the
//! comparison. Eliding a theorem value would then turn a provable `is_def_eq`
//! into `DefUnknown`, which can change a verdict. Theorem elision is hence
//! gated behind an explicit, non-default policy and must be validated
//! empirically (unchanged kernel-verified count) per corpus before use.
//!
//! # Scope
//!
//! This pass is ONLY ever applied to a closure environment that holds TRUSTED
//! IMPORTED constants. It is never applied to a target module whose own decls
//! are being kernel-checked: those decls are added AFTER this pass, through
//! `add_decl`'s `check_type`, and keep their values. The on-disk `.olean` /
//! `.mathverse` data is never touched — only the resident in-memory env.

use super::ConstantKind;

/// Which never-unfolded proof VALUES to drop from a trusted imported closure
/// environment to bound resident memory.
///
/// The values are set to `None` in place; TYPES and `Definition` values are
/// always retained.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ProofValueElision {
    /// Do not elide anything (the legacy full-resident behavior).
    #[default]
    None,
    /// Elide only `Opaque`-kind values. STATICALLY SOUND: `unfold_definition`
    /// provably never returns an `Opaque` value, so no verdict can change.
    OpaqueOnly,
    /// Elide `Opaque`- AND `Theorem`-kind values. NOT statically sound for this
    /// kernel (theorems CAN be δ-unfolded); use only when the unchanged
    /// kernel-verified-count gate has been confirmed for the target corpus.
    OpaqueAndTheorem,
}

impl ProofValueElision {
    /// Whether a constant of the given `kind` should have its VALUE elided
    /// under this policy. `Definition` and `Axiom` are never elided
    /// (definitions are δ-unfolded; axioms already have no value).
    #[must_use]
    pub fn elides(self, kind: ConstantKind) -> bool {
        match self {
            ProofValueElision::None => false,
            ProofValueElision::OpaqueOnly => kind == ConstantKind::Opaque,
            ProofValueElision::OpaqueAndTheorem => {
                matches!(kind, ConstantKind::Opaque | ConstantKind::Theorem)
            }
        }
    }
}

/// Counts produced by
/// [`Environment::elide_proof_values`](super::Environment::elide_proof_values).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct ProofElisionStats {
    /// Number of `Opaque`-kind values dropped.
    pub opaque_elided: usize,
    /// Number of `Theorem`-kind values dropped (0 unless the policy includes
    /// theorems).
    pub theorem_elided: usize,
    /// Constants left untouched because their value is still reachable by
    /// δ-unfolding (`Definition`) or because they never had a value (`Axiom`),
    /// or simply because the policy did not select their kind.
    pub retained: usize,
}

impl ProofElisionStats {
    /// Total number of VALUES dropped across all elided kinds.
    #[must_use]
    pub fn total_elided(&self) -> usize {
        self.opaque_elided + self.theorem_elided
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantInfo, Environment, Reducibility};
    use crate::expr::Expr;
    use crate::name::Name;

    fn info(name: &str, kind: ConstantKind, has_value: bool) -> ConstantInfo {
        ConstantInfo::new_with_reducibility(
            Name::from_string(name),
            vec![],
            Expr::sort(crate::level::Level::zero()),
            has_value.then(|| Expr::sort(crate::level::Level::zero())),
            Reducibility::Regular(0),
            kind,
        )
    }

    fn seeded_env() -> Environment {
        let mut env = Environment::new();
        env.add_constant_for_test(info("D", ConstantKind::Definition, true));
        env.add_constant_for_test(info("T", ConstantKind::Theorem, true));
        env.add_constant_for_test(info("O", ConstantKind::Opaque, true));
        env.add_constant_for_test(info("A", ConstantKind::Axiom, false));
        env
    }

    #[test]
    fn test_elides_predicate_selects_expected_kinds() {
        assert!(!ProofValueElision::None.elides(ConstantKind::Opaque));
        assert!(ProofValueElision::OpaqueOnly.elides(ConstantKind::Opaque));
        assert!(!ProofValueElision::OpaqueOnly.elides(ConstantKind::Theorem));
        assert!(!ProofValueElision::OpaqueOnly.elides(ConstantKind::Definition));
        assert!(ProofValueElision::OpaqueAndTheorem.elides(ConstantKind::Opaque));
        assert!(ProofValueElision::OpaqueAndTheorem.elides(ConstantKind::Theorem));
        assert!(!ProofValueElision::OpaqueAndTheorem.elides(ConstantKind::Definition));
        assert!(!ProofValueElision::OpaqueAndTheorem.elides(ConstantKind::Axiom));
    }

    #[test]
    fn test_none_policy_is_noop() {
        let mut env = seeded_env();
        let stats = env.elide_proof_values(ProofValueElision::None);
        assert_eq!(stats.total_elided(), 0);
        assert!(env
            .get_const(&Name::from_string("O"))
            .unwrap()
            .value
            .is_some());
        assert!(env
            .get_const(&Name::from_string("T"))
            .unwrap()
            .value
            .is_some());
    }

    #[test]
    fn test_opaque_only_drops_opaque_keeps_definition_theorem_type() {
        let mut env = seeded_env();
        let stats = env.elide_proof_values(ProofValueElision::OpaqueOnly);
        assert_eq!(stats.opaque_elided, 1);
        assert_eq!(stats.theorem_elided, 0);
        // Opaque value dropped, type kept.
        let o = env.get_const(&Name::from_string("O")).unwrap();
        assert!(o.value.is_none(), "opaque value must be elided");
        // Definition + Theorem values preserved (definitions unfold; theorems
        // can unfold in this kernel, so OpaqueOnly must not touch them).
        assert!(env
            .get_const(&Name::from_string("D"))
            .unwrap()
            .value
            .is_some());
        assert!(env
            .get_const(&Name::from_string("T"))
            .unwrap()
            .value
            .is_some());
    }

    #[test]
    fn test_forget_proof_values_for_streams_named_subset() {
        // Streaming counterpart: only the NAMED, policy-selected constants are
        // freed; unnamed ones (even of an elidable kind) are untouched.
        let mut env = seeded_env();
        let names = [Name::from_string("O"), Name::from_string("T")];
        // OpaqueOnly: only O is freed even though T is named.
        let stats = env.forget_proof_values_for(names.iter(), ProofValueElision::OpaqueOnly);
        assert_eq!(stats.opaque_elided, 1);
        assert_eq!(stats.theorem_elided, 0);
        assert!(env
            .get_const(&Name::from_string("O"))
            .unwrap()
            .value
            .is_none());
        assert!(
            env.get_const(&Name::from_string("T"))
                .unwrap()
                .value
                .is_some(),
            "T named but OpaqueOnly must not free a Theorem"
        );
        // Definition never freed.
        assert!(env
            .get_const(&Name::from_string("D"))
            .unwrap()
            .value
            .is_some());
    }

    #[test]
    fn test_forget_proof_values_for_none_is_noop() {
        let mut env = seeded_env();
        let names = [Name::from_string("O"), Name::from_string("T")];
        let stats = env.forget_proof_values_for(names.iter(), ProofValueElision::None);
        assert_eq!(stats.total_elided(), 0);
        assert!(env
            .get_const(&Name::from_string("O"))
            .unwrap()
            .value
            .is_some());
    }

    #[test]
    fn test_opaque_and_theorem_drops_both_keeps_definition() {
        let mut env = seeded_env();
        let stats = env.elide_proof_values(ProofValueElision::OpaqueAndTheorem);
        assert_eq!(stats.opaque_elided, 1);
        assert_eq!(stats.theorem_elided, 1);
        assert!(env
            .get_const(&Name::from_string("O"))
            .unwrap()
            .value
            .is_none());
        assert!(env
            .get_const(&Name::from_string("T"))
            .unwrap()
            .value
            .is_none());
        // Definition value is ALWAYS retained — the kernel δ-unfolds it.
        assert!(
            env.get_const(&Name::from_string("D"))
                .unwrap()
                .value
                .is_some(),
            "definition value must never be elided"
        );
    }
}
