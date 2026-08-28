// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotion of `Nat.lt_succ_iff` from `Declaration::Axiom` to a
//! kernel-checked `Declaration::Theorem`.
//!
//! `Nat.lt_succ_iff : ∀ n m : Nat, Nat.lt n (Nat.succ m) ↔ Nat.le n m` was one
//! of the six ASSERTED PROPOSITIONS the default prelude shipped as axioms (the
//! `debt_proposition` bucket of `data/prelude_axiom_ratchet.json`). It is not a
//! capability gap: both halves of the iff were already constructive theorems in
//! the same `init_nat_succ_lt` block that asserted it.
//!
//! # Proof
//!
//! `Nat.lt` is a *reducible* definition, `Nat.lt n m := Nat.le (Nat.succ n) m`
//! (`order_le_lt.rs`), so the left-hand side beta/delta-reduces to
//! `Nat.le (Nat.succ n) (Nat.succ m)` and the iff is exactly successor
//! injectivity for `Nat.le`:
//!
//! ```text
//! Iff.intro (Nat.lt n (Nat.succ m)) (Nat.le n m)
//!   (fun h => Nat.le_of_succ_le_succ n m h)   -- mp
//!   (fun h => Nat.succ_le_succ    n m h)      -- mpr
//! ```
//!
//! `Nat.le_of_succ_le_succ` is the constructive theorem registered by
//! `nat_le_inversion_proof.rs` (#3599 follow-up) and `Nat.succ_le_succ` the one
//! registered by `nat_top_level_ordering_proof.rs` (#3599). Neither reaches a
//! non-foundational axiom, so `env.axiom_deps("Nat.lt_succ_iff")` is empty and
//! the theorem is a proof in CLAUDE.md's sense.
//!
//! The legacy axiom site in `order_lemmas_succ.rs::add_nat_lt_succ_iff` is now
//! guarded by a `get_const` check, so it is an idempotent no-op once this
//! theorem is present — the same shape as the #3599 / #3604 demotions.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `Nat.lt_succ_iff : ∀ n m : Nat, Nat.lt n (Nat.succ m) ↔ Nat.le n m`
    /// as a kernel-checked theorem.
    ///
    /// Idempotent: a no-op when the name is already present (whether as this
    /// theorem or as the legacy axiom).
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from the dependency initializers or from
    /// `add_decl`'s kernel check of the proof term.
    pub(crate) fn register_nat_lt_succ_iff_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_succ_iff");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_iff()?;
        // `Nat.succ_le_succ` (mpr).
        self.init_nat_top_level_ordering()?;
        // `Nat.le_of_succ_le_succ` (mp).
        self.register_nat_le_of_succ_le_succ_theorem()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let iff = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);
        let le_of_succ_le_succ = Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);
        let succ_le_succ = Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let (m_id, m) = b.fresh_local(nat.clone());

        // `Nat.lt n (Nat.succ m)` and `Nat.le n m` — the two sides, spelled
        // exactly as the retired axiom spelled them.
        let lhs = Expr::apps(lt, [n.clone(), Expr::app(succ, m.clone())]);
        let rhs = Expr::apps(le, [n.clone(), m.clone()]);

        let type_ = {
            let body = Expr::apps(iff, [lhs.clone(), rhs.clone()]);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // mp : Nat.lt n (Nat.succ m) → Nat.le n m
        //
        // `Nat.lt n (Nat.succ m)` delta/beta-reduces to
        // `Nat.le (Nat.succ n) (Nat.succ m)`, which is exactly what
        // `Nat.le_of_succ_le_succ n m` consumes.
        let mp = {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = cb.fresh_local(lhs.clone());
            let body = Expr::apps(le_of_succ_le_succ, [n.clone(), m.clone(), h]);
            let lam = cb.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
            cb.finish_child(lam)
        };

        // mpr : Nat.le n m → Nat.lt n (Nat.succ m)
        let mpr = {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = cb.fresh_local(rhs.clone());
            let body = Expr::apps(succ_le_succ, [n.clone(), m.clone(), h]);
            let lam = cb.mk_lam(h_id, BinderInfo::Default, rhs.clone(), body);
            cb.finish_child(lam)
        };

        let value = {
            let body = Expr::apps(iff_intro, [lhs, rhs, mp, mpr]);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat, e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}
