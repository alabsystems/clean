// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Obligation key: a canonical content address for a proof obligation.
//!
//! Phase 0 of the solver-results cache (see
//! `designs/2026-06-24-solver-results-cache-service.md` §2). The key is the
//! alpha-canonical de-Bruijn `blake3` digest of the **goal type** — the same
//! primitive [`expr_canonical_digest`] (clean-mathverse) uses for the novelty
//! gate, recomputed here over `clean_kernel::flat::FlatBuilder` so `clean-auto`
//! does not depend on the downstream `clean-mathverse` crate.
//!
//! [`expr_canonical_digest`]: https://github.com/alabsystems/clean
//!
//! # Soundness
//!
//! The obligation digest is a **soundness bucket**, not an arbiter. A cache hit
//! keyed on this digest returns a stored *proof term*; the caller still
//! re-checks that proof term through the kernel exactly as for a freshly-found
//! proof, so a stale or colliding key is caught by the kernel re-check and never
//! silently trusted. The digest identifies the goal *type* only; per the design
//! the full obligation address extends this with `context_digest` and
//! `env_digest` (the goal ‖ context ‖ env triple) in a later phase.

use crate::solver_cache::SolverCacheError;
use clean_kernel::Expr;

/// Compute the alpha-canonical content address of a proof obligation's goal.
///
/// Returns `blake3:<64hex>` over the deterministic `FlatExpr` byte encoding of
/// `goal`. `FlatExpr` encodes binders by `BinderInfo` + de-Bruijn index with no
/// binder *names*, so the digest is alpha-invariant: alpha-equivalent goals map
/// to the same digest, structurally-distinct goals (including ones differing
/// only in universe level or `BinderInfo`) map to different digests.
///
/// This is the Phase-0 obligation key. Context and environment digests extend it
/// later (design §2.1); the goal-type digest alone is the key for Phase 0.
pub(crate) fn obligation_digest(goal: &Expr) -> Result<String, SolverCacheError> {
    let mut builder = clean_kernel::flat::FlatBuilder::new();
    builder
        .add_kernel_expr(goal)
        .map_err(|e| SolverCacheError::Flatten(e.to_string()))?;
    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .map_err(|e| SolverCacheError::Flatten(e.to_string()))?;
    Ok(format!("blake3:{}", blake3::hash(&bytes).to_hex()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Expr, Level, Name};

    fn type0() -> Expr {
        Expr::sort(Level::zero())
    }

    #[test]
    fn test_obligation_digest_format_is_blake3_64hex() {
        let goal = type0();
        let digest = obligation_digest(&goal).expect("flatten Sort 0");
        assert!(
            digest.starts_with("blake3:"),
            "digest must be blake3-tagged"
        );
        let hex = digest.strip_prefix("blake3:").expect("prefix");
        assert_eq!(hex.len(), 64, "blake3 hex digest is 64 chars");
        assert!(
            hex.chars().all(|c| c.is_ascii_hexdigit()),
            "digest body is hex"
        );
    }

    #[test]
    fn test_obligation_digest_is_stable() {
        let goal = Expr::pi(BinderInfo::Default, type0(), Expr::bvar(0));
        let a = obligation_digest(&goal).expect("flatten");
        let b = obligation_digest(&goal).expect("flatten");
        assert_eq!(a, b, "same goal must produce the same digest");
    }

    #[test]
    fn test_obligation_digest_alpha_invariant() {
        // De-Bruijn encoding is name-free: the kernel `BinderData` carries no
        // binder name, so two goals that are alpha-equivalent (identical up to
        // bound-variable renaming) flatten to the same bytes regardless of how
        // the surrounding constant heads are named. Build `∀ (_ : Sort 0), v 0`
        // two ways — directly, and by substituting a renamed-but-alpha-equal
        // sub-term — and confirm the digest is invariant.
        //
        // `id_pi` is `∀ (x : Sort 0), x` (de-Bruijn `BVar(0)` body). Its
        // alpha-variant `∀ (y : Sort 0), y` has the *same* de-Bruijn form, so it
        // is literally the same `Expr`; the digest must match.
        let id_pi = Expr::pi(BinderInfo::Default, type0(), Expr::bvar(0));
        let id_pi_again = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        );
        assert_eq!(
            obligation_digest(&id_pi).expect("flatten id_pi"),
            obligation_digest(&id_pi_again).expect("flatten id_pi_again"),
            "alpha-equivalent goals must share an obligation digest"
        );

        // Nested binders: `∀ a b, a` vs `∀ a b, a` built from independently
        // constructed Level/Name values. The bound variable reference is
        // de-Bruijn `BVar(1)`, name-free, so the two are byte-identical.
        let const_a = Expr::const_(Name::from_string("C"), Vec::<Level>::new());
        let nested_x = Expr::pi(
            BinderInfo::Default,
            const_a.clone(),
            Expr::pi(BinderInfo::Default, const_a.clone(), Expr::bvar(1)),
        );
        let nested_y = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("C"), Vec::<Level>::new()),
            Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("C"), Vec::<Level>::new()),
                Expr::bvar(1),
            ),
        );
        assert_eq!(
            obligation_digest(&nested_x).expect("flatten nested_x"),
            obligation_digest(&nested_y).expect("flatten nested_y"),
            "nested alpha-equivalent goals must share a digest"
        );
    }

    #[test]
    fn test_obligation_digest_distinguishes_different_goals() {
        let g1 = Expr::pi(BinderInfo::Default, type0(), Expr::bvar(0));
        // Different body: `∀ (_ : Sort 0), Sort 0` is a different proposition.
        let g2 = Expr::pi(BinderInfo::Default, type0(), type0());
        let d1 = obligation_digest(&g1).expect("flatten g1");
        let d2 = obligation_digest(&g2).expect("flatten g2");
        assert_ne!(d1, d2, "structurally-distinct goals must differ");
    }

    #[test]
    fn test_obligation_digest_distinguishes_bound_variable_index() {
        // `BVar(0)` vs `BVar(1)` under two binders are *not* alpha-equivalent;
        // the de-Bruijn index is load-bearing and must change the digest.
        let inner0 = Expr::pi(
            BinderInfo::Default,
            type0(),
            Expr::pi(BinderInfo::Default, type0(), Expr::bvar(0)),
        );
        let inner1 = Expr::pi(
            BinderInfo::Default,
            type0(),
            Expr::pi(BinderInfo::Default, type0(), Expr::bvar(1)),
        );
        assert_ne!(
            obligation_digest(&inner0).expect("flatten inner0"),
            obligation_digest(&inner1).expect("flatten inner1"),
            "distinct de-Bruijn indices must produce distinct digests"
        );
    }

    #[test]
    fn test_obligation_digest_distinguishes_binder_info() {
        // Implicit vs explicit binder is a kernel-distinguished field (#2109):
        // the digest must not merge them.
        let explicit = Expr::pi(BinderInfo::Default, type0(), Expr::bvar(0));
        let implicit = Expr::pi(BinderInfo::Implicit, type0(), Expr::bvar(0));
        let de = obligation_digest(&explicit).expect("flatten explicit");
        let di = obligation_digest(&implicit).expect("flatten implicit");
        assert_ne!(de, di, "binder info must be committed in the digest");
    }
}
