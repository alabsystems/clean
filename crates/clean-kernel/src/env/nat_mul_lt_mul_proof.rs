// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotion of `Nat.mul_lt_mul_right` and `Nat.mul_lt_mul` from
//! `Declaration::Axiom` to kernel-checked `Declaration::Theorem`s.
//!
//! Both were ASSERTED PROPOSITIONS in the default prelude — two of the six
//! entries in the `debt_proposition` bucket of
//! `data/prelude_axiom_ratchet.json`. Their `Nat.mul_le_*` and
//! `Nat.mul_lt_mul_left` siblings had already been demoted to theorems
//! (`nat_arith_order_proof.rs`, #3604); these two were simply never finished.
//!
//! Both types are reproduced EXACTLY as `order_arith.rs` asserted them, so no
//! downstream term changes meaning — only the declaration's kind and its axiom
//! closure change.
//!
//! # Proofs
//!
//! **`Nat.mul_lt_mul_right : ∀ a b c, 0 < c → a < b → a*c < b*c`** — the
//! already-constructive `Nat.mul_lt_mul_left a b c h₁ h₂ : c*a < c*b`
//! transported along commutativity, twice:
//!
//! ```text
//! Eq.subst.{1} Nat (fun y => Nat.lt (a*c) y)   (c*b) (b*c) (Nat.mul_comm c b)
//!  (Eq.subst.{1} Nat (fun x => Nat.lt x (c*b)) (c*a) (a*c) (Nat.mul_comm c a)
//!    (Nat.mul_lt_mul_left a b c h₁ h₂))
//! ```
//!
//! **`Nat.mul_lt_mul : ∀ a b c d, a < b → c < d → 0 < c → a*c < b*d`** —
//! `Nat.lt x y` is the *reducible* definition `Nat.le (Nat.succ x) y`
//! (`order_le_lt.rs`), so `a*c < b*d` is `Nat.succ (a*c) ≤ b*d` and the proof is
//! one transitivity step through `b*c`:
//!
//! ```text
//! Nat.le_trans (Nat.succ (a*c)) (b*c) (b*d)
//!   (Nat.mul_lt_mul_right a b c h₃ h₁)                  -- succ (a*c) ≤ b*c
//!   (Nat.mul_le_mul_left c d b (Nat.le_of_lt c d h₂))   -- b*c ≤ b*d
//! ```
//!
//! `Nat.le_trans` and `Nat.le_of_lt` are stated with the `LE.le`/`LT.lt`
//! typeclass spellings; those are reducible projections of `instLENat` /
//! `instLTNat` onto `Nat.le` / `Nat.lt`, so every hypothesis and the conclusion
//! match definitionally and the kernel accepts the term without any coercion
//! lemma.
//!
//! Support lemmas used: `Nat.mul_lt_mul_left`, `Nat.mul_comm`,
//! `Nat.mul_le_mul_left`, `Nat.le_of_lt`, `Nat.le_trans`, `Eq.subst` — all
//! `Declaration::Theorem`s with empty non-foundational closures, so
//! `env.axiom_deps` is empty for both new theorems.
//!
//! The legacy axiom sites in `order_arith.rs::init_nat_mul_ord` are now guarded
//! by `get_const`, exactly like the #3604 demotions beside them, so they are
//! idempotent no-ops once these theorems are present.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The constants both proofs share.
struct MulLtConsts {
    nat: Expr,
    succ: Expr,
    zero: Expr,
    lt: Expr,
    mul: Expr,
}

impl MulLtConsts {
    fn new() -> Self {
        MulLtConsts {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
        }
    }

    fn lt_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.lt.clone(), [lhs, rhs])
    }

    fn mul_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [lhs, rhs])
    }

    /// `Nat.lt Nat.zero c` — the positivity hypothesis, spelled as the retired
    /// axioms spelled it.
    fn pos(&self, c: Expr) -> Expr {
        self.lt_of(self.zero.clone(), c)
    }
}

impl Environment {
    /// Register the constructive `Nat.mul_lt_mul_right` and `Nat.mul_lt_mul`
    /// theorems, retiring the two `order_arith.rs` axiom stubs.
    ///
    /// Idempotent, and safe to call from any init path: each half is guarded by
    /// its own `get_const`.
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from the dependency initializers or from
    /// `add_decl`'s kernel check of a proof term.
    pub(crate) fn register_nat_mul_lt_mul_proofs(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS / FIDELITY: import-mode gate, byte-identical to the one
        // guarding `register_nat_arith_order_proofs` and the two legacy axiom
        // sites in `order_arith.rs`. Under `suppress_lossy_structure_stubs` the
        // whole Clean-native `Nat.mul_lt_*` family is withheld so the genuine
        // Lean-core constants (whose `mul_lt_mul_right` is an IFF, not this
        // implication) import in its place. Nothing about the import lane
        // changes: `Nat.mul_lt_mul_right` stays withheld and `Nat.mul_lt_mul`
        // stays the axiom `init_nat_mul_ord` registers there today. This gate is
        // also load-bearing for termination: the support lemma
        // `Nat.mul_lt_mul_left` is itself withheld in import mode, so the proofs
        // below have no premise to build on there.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_nat_mul_lt_mul_right_theorem()?;
        self.register_nat_mul_lt_mul_theorem()
    }

    /// `Nat.mul_lt_mul_right : ∀ a b c, Nat.lt Nat.zero c → Nat.lt a b →
    /// Nat.lt (Nat.mul a c) (Nat.mul b c)`.
    fn register_nat_mul_lt_mul_right_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_lt_mul_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.mul_lt_prerequisites()?;

        let c = MulLtConsts::new();
        // `Eq.subst.{u}` at `α := Nat : Sort 1`.
        let eq_subst = Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        );
        let mul_comm = Expr::const_(Name::from_string("Nat.mul_comm"), vec![]);
        let mul_lt_mul_left = Expr::const_(Name::from_string("Nat.mul_lt_mul_left"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (b_id, bv) = b.fresh_local(c.nat.clone());
        let (c_id, cv) = b.fresh_local(c.nat.clone());
        let pos_c = c.pos(cv.clone());
        let lt_a_b = c.lt_of(a.clone(), bv.clone());
        let (h1_id, h1) = b.fresh_local(pos_c.clone());
        let (h2_id, h2) = b.fresh_local(lt_a_b.clone());

        let conclusion = c.lt_of(
            c.mul_of(a.clone(), cv.clone()),
            c.mul_of(bv.clone(), cv.clone()),
        );

        let type_ = {
            let e = b.mk_pi(h2_id, BinderInfo::Default, lt_a_b.clone(), conclusion);
            let e = b.mk_pi(h1_id, BinderInfo::Default, pos_c.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // `Nat.mul_lt_mul_left a b c h₁ h₂ : Nat.lt (c*a) (c*b)`
        let left_form = Expr::apps(mul_lt_mul_left, [a.clone(), bv.clone(), cv.clone(), h1, h2]);

        // Transport the LEFT factor: `c*a  ↦  a*c`.
        let after_left = {
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = mb.fresh_local(c.nat.clone());
                let body = c.lt_of(x, c.mul_of(cv.clone(), bv.clone()));
                let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };
            Expr::apps(
                eq_subst.clone(),
                [
                    c.nat.clone(),
                    motive,
                    c.mul_of(cv.clone(), a.clone()),
                    c.mul_of(a.clone(), cv.clone()),
                    Expr::apps(mul_comm.clone(), [cv.clone(), a.clone()]),
                    left_form,
                ],
            )
        };

        // Transport the RIGHT factor: `c*b  ↦  b*c`.
        let value = {
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = mb.fresh_local(c.nat.clone());
                let body = c.lt_of(c.mul_of(a.clone(), cv.clone()), y);
                let lam = mb.mk_lam(y_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };
            let body = Expr::apps(
                eq_subst,
                [
                    c.nat.clone(),
                    motive,
                    c.mul_of(cv.clone(), bv.clone()),
                    c.mul_of(bv.clone(), cv.clone()),
                    Expr::apps(mul_comm, [cv.clone(), bv.clone()]),
                    after_left,
                ],
            );
            let e = b.mk_lam(h2_id, BinderInfo::Default, lt_a_b, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, pos_c, e);
            let e = b.mk_lam(c_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(b_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.mul_lt_mul : ∀ a b c d, Nat.lt a b → Nat.lt c d → Nat.lt Nat.zero c →
    /// Nat.lt (Nat.mul a c) (Nat.mul b d)`.
    fn register_nat_mul_lt_mul_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_lt_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.mul_lt_prerequisites()?;
        self.register_nat_mul_lt_mul_right_theorem()?;

        let c = MulLtConsts::new();
        let le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let le_of_lt = Expr::const_(Name::from_string("Nat.le_of_lt"), vec![]);
        let mul_le_mul_left = Expr::const_(Name::from_string("Nat.mul_le_mul_left"), vec![]);
        let mul_lt_mul_right = Expr::const_(Name::from_string("Nat.mul_lt_mul_right"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (b_id, bv) = b.fresh_local(c.nat.clone());
        let (c_id, cv) = b.fresh_local(c.nat.clone());
        let (d_id, dv) = b.fresh_local(c.nat.clone());
        let lt_a_b = c.lt_of(a.clone(), bv.clone());
        let lt_c_d = c.lt_of(cv.clone(), dv.clone());
        let pos_c = c.pos(cv.clone());
        let (h1_id, h1) = b.fresh_local(lt_a_b.clone());
        let (h2_id, h2) = b.fresh_local(lt_c_d.clone());
        let (h3_id, h3) = b.fresh_local(pos_c.clone());

        let a_c = c.mul_of(a.clone(), cv.clone());
        let b_c = c.mul_of(bv.clone(), cv.clone());
        let b_d = c.mul_of(bv.clone(), dv.clone());

        let type_ = {
            let conclusion = c.lt_of(a_c.clone(), b_d.clone());
            let e = b.mk_pi(h3_id, BinderInfo::Default, pos_c.clone(), conclusion);
            let e = b.mk_pi(h2_id, BinderInfo::Default, lt_c_d.clone(), e);
            let e = b.mk_pi(h1_id, BinderInfo::Default, lt_a_b.clone(), e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // `Nat.succ (a*c) ≤ b*c` — definitionally `Nat.lt (a*c) (b*c)`.
        let step_left = Expr::apps(
            mul_lt_mul_right,
            [a.clone(), bv.clone(), cv.clone(), h3, h1],
        );
        // `b*c ≤ b*d` from `c ≤ d`.
        let step_right = Expr::apps(
            mul_le_mul_left,
            [
                cv.clone(),
                dv.clone(),
                bv.clone(),
                Expr::apps(le_of_lt, [cv.clone(), dv.clone(), h2]),
            ],
        );

        let value = {
            let body = Expr::apps(
                le_trans,
                [
                    Expr::app(c.succ.clone(), a_c),
                    b_c,
                    b_d,
                    step_left,
                    step_right,
                ],
            );
            let e = b.mk_lam(h3_id, BinderInfo::Default, pos_c, body);
            let e = b.mk_lam(h2_id, BinderInfo::Default, lt_c_d, e);
            let e = b.mk_lam(h1_id, BinderInfo::Default, lt_a_b, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(c_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(b_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Everything both proofs need in scope before their terms are built.
    ///
    /// Every callee is idempotent and none of them re-enters
    /// `init_nat_mul_ord` (the caller), so this cannot recurse.
    fn mul_lt_prerequisites(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        // `Nat.le_of_lt`, `Nat.succ_le_succ`.
        self.init_nat_top_level_ordering()?;
        // `Nat.le_trans`.
        self.register_nat_le_trans_proof()?;
        // `Nat.mul_comm`.
        self.register_nat_mul_comm_proof()?;
        // `Nat.mul_le_mul_left`.
        self.register_nat_mul_le_mul_left_proof()?;
        // `Nat.mul_lt_mul_left` (the `lt` cluster of #3604).
        self.register_nat_arith_order_proofs()?;
        Ok(())
    }
}
