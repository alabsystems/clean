// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat arithmetic ordering lemmas for Environment
//!
//! Split from order.rs (#307). Contains:
//! - Addition ordering lemmas (add_lt_add, add_le_add variants)
//! - Multiplication ordering lemmas (mul_lt_mul, mul_le_mul variants)
//! - Subtraction ordering lemmas (sub_le, sub_lt, sub_self, sub_zero)
//! - Power ordering lemmas (pow_le_pow, pow_lt_pow, pow_zero, pow_one, one_pow)
//! - FATE-X order stubs (WithBot, WithTop, Top, Bot, ValuationRing, etc.)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Nat addition ordering lemmas
    ///
    /// This adds:
    /// - Nat.add_lt_add_left : axiom ∀ a b : Nat, Nat.lt a b → ∀ c : Nat, Nat.lt (Nat.add c a) (Nat.add c b)
    /// - Nat.add_lt_add_right : axiom ∀ a b : Nat, Nat.lt a b → ∀ c : Nat, Nat.lt (Nat.add a c) (Nat.add b c)
    /// - Nat.add_le_add_left : axiom ∀ a b : Nat, Nat.le a b → ∀ c : Nat, Nat.le (Nat.add c a) (Nat.add c b)
    /// - Nat.add_le_add_right : axiom ∀ a b : Nat, Nat.le a b → ∀ c : Nat, Nat.le (Nat.add a c) (Nat.add b c)
    /// - Nat.add_lt_add : axiom ∀ a b c d : Nat, Nat.lt a b → Nat.lt c d → Nat.lt (Nat.add a c) (Nat.add b d)
    /// - Nat.add_le_add : axiom ∀ a b c d : Nat, Nat.le a b → Nat.le c d → Nat.le (Nat.add a c) (Nat.add b d)
    ///
    /// These are fundamental ordering lemmas for addition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_add_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_add_ord(&mut self) -> Result<(), EnvError> {
        if self.nat_add_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?; // Provides Nat, Nat.add, Nat.mul
        self.init_le()?; // Provides LE typeclass
        self.init_lt()?; // Provides LT typeclass
        self.init_nat_linear_order()?; // Provides Nat.le and Nat.lt

        // #3604: Demote the `Nat.add_le_add*` family to constructive
        // `Declaration::Theorem`s. Registered *before* the legacy Axiom block
        // so the Theorem form wins; each `Nat.add_le_add*` Axiom `add_decl`
        // below is guarded by `is_theorem` and becomes a no-op once the
        // Theorem is present. See `nat_arith_order_proof.rs`.
        self.register_nat_arith_order_proofs()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let add_const = Expr::const_(Name::from_string("Nat.add"), vec![]);

        // Built with EnvDeclBuilder (#1444).
        // Nat.add_lt_add_left : ∀ a b : Nat, Nat.lt a b → ∀ c : Nat, Nat.lt (Nat.add c a) (Nat.add c b)
        let add_lt_add_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let lt_a_b = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(lt_a_b.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    lt_const.clone(),
                    Expr::app(Expr::app(add_const.clone(), c.clone()), a.clone()),
                ),
                Expr::app(Expr::app(add_const.clone(), c.clone()), bv.clone()),
            );
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(h_id, BinderInfo::Default, lt_a_b, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604 (lt cluster): Guarded — skipped when the constructive Theorem
        // form is present (registered by `register_nat_arith_order_proofs`).
        if self
            .get_const(&Name::from_string("Nat.add_lt_add_left"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.add_lt_add_left"),
                level_params: vec![],
                type_: add_lt_add_left_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.add_lt_add_right : ∀ a b : Nat, Nat.lt a b → ∀ c : Nat, Nat.lt (Nat.add a c) (Nat.add b c)
        let add_lt_add_right_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let lt_a_b = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(lt_a_b.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    lt_const.clone(),
                    Expr::app(Expr::app(add_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(add_const.clone(), bv.clone()), c.clone()),
            );
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(h_id, BinderInfo::Default, lt_a_b, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604 (lt cluster): Guarded — skipped when the constructive Theorem
        // form is present.
        if self
            .get_const(&Name::from_string("Nat.add_lt_add_right"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.add_lt_add_right"),
                level_params: vec![],
                type_: add_lt_add_right_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.add_le_add_left : ∀ a b : Nat, Nat.le a b → ∀ c : Nat, Nat.le (Nat.add c a) (Nat.add c b)
        let add_le_add_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let le_a_b = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(le_a_b.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(add_const.clone(), c.clone()), a.clone()),
                ),
                Expr::app(Expr::app(add_const.clone(), c.clone()), bv.clone()),
            );
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(h_id, BinderInfo::Default, le_a_b, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when `register_nat_arith_order_proofs`
        // has already registered the constructive Theorem form (above).
        if self
            .get_const(&Name::from_string("Nat.add_le_add_left"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.add_le_add_left"),
                level_params: vec![],
                type_: add_le_add_left_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.add_le_add_right : ∀ a b : Nat, Nat.le a b → ∀ c : Nat, Nat.le (Nat.add a c) (Nat.add b c)
        let add_le_add_right_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let le_a_b = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(le_a_b.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(add_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(add_const.clone(), bv.clone()), c.clone()),
            );
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(h_id, BinderInfo::Default, le_a_b, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when the constructive Theorem form is present.
        if self
            .get_const(&Name::from_string("Nat.add_le_add_right"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.add_le_add_right"),
                level_params: vec![],
                type_: add_le_add_right_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.add_lt_add : ∀ a b c d : Nat, Nat.lt a b → Nat.lt c d → Nat.lt (Nat.add a c) (Nat.add b d)
        let add_lt_add_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let (d_id, d) = b.fresh_local(nat_const.clone());
            let lt_a_b = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
            let lt_c_d = Expr::app(Expr::app(lt_const.clone(), c.clone()), d.clone());
            let (h1_id, _h1) = b.fresh_local(lt_a_b.clone());
            let (h2_id, _h2) = b.fresh_local(lt_c_d.clone());
            let body = Expr::app(
                Expr::app(
                    lt_const.clone(),
                    Expr::app(Expr::app(add_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(add_const.clone(), bv.clone()), d.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, lt_c_d, body);
            let e = b.mk_pi(h1_id, BinderInfo::Default, lt_a_b, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604 (lt cluster): Guarded — skipped when the constructive Theorem
        // form is present.
        if self
            .get_const(&Name::from_string("Nat.add_lt_add"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.add_lt_add"),
                level_params: vec![],
                type_: add_lt_add_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.add_le_add : ∀ a b c d : Nat, Nat.le a b → Nat.le c d → Nat.le (Nat.add a c) (Nat.add b d)
        let add_le_add_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let (d_id, d) = b.fresh_local(nat_const.clone());
            let le_a_b = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let le_c_d = Expr::app(Expr::app(le_const.clone(), c.clone()), d.clone());
            let (h1_id, _h1) = b.fresh_local(le_a_b.clone());
            let (h2_id, _h2) = b.fresh_local(le_c_d.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(add_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(add_const.clone(), bv.clone()), d.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, le_c_d, body);
            let e = b.mk_pi(h1_id, BinderInfo::Default, le_a_b, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when the constructive Theorem form is present.
        if self
            .get_const(&Name::from_string("Nat.add_le_add"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.add_le_add"),
                level_params: vec![],
                type_: add_le_add_type,
            })?;
        }

        self.nat_add_ord_init = true;
        Ok(())
    }

    /// Check if Nat addition ordering lemmas have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_add_ord_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_add_ord(&self) -> bool {
        self.nat_add_ord_init
    }

    /// Initialize Nat multiplication ordering lemmas
    ///
    /// This adds:
    /// - Nat.mul_lt_mul_left : axiom ∀ a b c : Nat, Nat.lt Nat.zero c → Nat.lt a b → Nat.lt (Nat.mul c a) (Nat.mul c b)
    /// - Nat.mul_lt_mul_right : axiom ∀ a b c : Nat, Nat.lt Nat.zero c → Nat.lt a b → Nat.lt (Nat.mul a c) (Nat.mul b c)
    /// - Nat.mul_le_mul_left : axiom ∀ a b c : Nat, Nat.le a b → Nat.le (Nat.mul c a) (Nat.mul c b)
    /// - Nat.mul_le_mul_right : axiom ∀ a b c : Nat, Nat.le a b → Nat.le (Nat.mul a c) (Nat.mul b c)
    /// - Nat.mul_lt_mul : axiom ∀ a b c d : Nat, Nat.lt a b → Nat.lt c d → Nat.lt Nat.zero c → Nat.lt (Nat.mul a c) (Nat.mul b d)
    /// - Nat.mul_le_mul : axiom ∀ a b c d : Nat, Nat.le a b → Nat.le c d → Nat.le (Nat.mul a c) (Nat.mul b d)
    ///
    /// These are fundamental ordering lemmas for multiplication.
    /// Note: mul_lt_mul_left and mul_lt_mul_right require positivity of the multiplier (0 < c).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_mul_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_mul_ord(&mut self) -> Result<(), EnvError> {
        if self.nat_mul_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?; // Provides Nat, Nat.add, Nat.mul
        self.init_le()?; // Provides LE typeclass
        self.init_lt()?; // Provides LT typeclass
        self.init_nat_linear_order()?; // Provides Nat.le and Nat.lt

        // #3604: Demote `Nat.mul_le_mul_left` to a constructive
        // `Declaration::Theorem`. Registered *before* the legacy Axiom block so
        // the Theorem form wins; the Axiom `add_decl` below is guarded by
        // `get_const` and becomes a no-op once the Theorem is present. See
        // `algebra_nat_mul_cancel_proof.rs`.
        self.register_nat_mul_le_mul_left_proof()?;

        // #3604: Demote `Nat.mul_le_mul_right` and `Nat.mul_le_mul` (plus the
        // `Nat.add_le_add*` family) to constructive `Declaration::Theorem`s.
        // Order-independent: idempotent, and also invoked from
        // `init_nat_add_ord`. See `nat_arith_order_proof.rs`. The legacy mul
        // Axiom `add_decl`s below are guarded by `get_const`.
        self.register_nat_arith_order_proofs()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let mul_const = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);

        // Built with EnvDeclBuilder (#1444).
        // Nat.mul_lt_mul_left : ∀ a b c : Nat, 0 < c → a < b → c * a < c * b
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — see the
        // matching gate in `register_nat_mul_lt_mul_left`. The genuine Lean
        // `Nat.mul_lt_mul_left` is an IFF, not this implication; the stub would
        // shadow the real Iff on import. `register_nat_arith_order_proofs` (run
        // above) also suppresses the Theorem form in import mode, so without this
        // guard the fallback Axiom below would re-introduce the wrong stub.
        if !self.suppress_lossy_structure_stubs {
            let mul_lt_mul_left_type = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat_const.clone());
                let (b_id, bv) = b.fresh_local(nat_const.clone());
                let (c_id, c) = b.fresh_local(nat_const.clone());
                let lt_zero_c =
                    Expr::app(Expr::app(lt_const.clone(), zero_const.clone()), c.clone());
                let lt_a_b = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
                let (h1_id, _h1) = b.fresh_local(lt_zero_c.clone());
                let (h2_id, _h2) = b.fresh_local(lt_a_b.clone());
                let body = Expr::app(
                    Expr::app(
                        lt_const.clone(),
                        Expr::app(Expr::app(mul_const.clone(), c.clone()), a.clone()),
                    ),
                    Expr::app(Expr::app(mul_const.clone(), c.clone()), bv.clone()),
                );
                let e = b.mk_pi(h2_id, BinderInfo::Default, lt_a_b, body);
                let e = b.mk_pi(h1_id, BinderInfo::Default, lt_zero_c, e);
                let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
                let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
                b.finish(e)
            };

            // #3604 (lt cluster): Guarded — skipped when the constructive Theorem
            // form is present (registered by `register_nat_arith_order_proofs`).
            if self
                .get_const(&Name::from_string("Nat.mul_lt_mul_left"))
                .is_none()
            {
                self.add_decl(Declaration::Axiom {
                    name: Name::from_string("Nat.mul_lt_mul_left"),
                    level_params: vec![],
                    type_: mul_lt_mul_left_type,
                })?;
            }
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.mul_lt_mul_right : ∀ a b c : Nat, 0 < c → a < b → a * c < b * c
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): WITHHOLD this stub. It
        // is the IMPLICATION `∀ a b c, 0 < c → a < b → a*c < b*c`, but Lean core's
        // genuine `Nat.mul_lt_mul_right` is an IFF:
        // `∀ {a b c}, 0 < a → (b*a < c*a ↔ b < c)`. As an Axiom with the wrong
        // implication type it SHADOWS the real Iff on import, so every Mathlib
        // proof that rewrites with / applies the Iff (e.g.
        // `Nat.mul_lt_mul_pow_succ`) fails `check_type` with a spurious
        // TypeMismatch. Withholding it lets the genuine kernel-checked Iff-form
        // import register in its place (the real lemma lives in Lean's `Init` and
        // is in every Mathlib import closure). Mirrors the
        // `Nat.mul_lt_mul_left` gate in `register_nat_mul_lt_mul_left`.
        //
        // SOUNDNESS: suppression only lets the genuine Mathlib/Init constant
        // import in the overlay's place; nothing here touches
        // `is_def_eq`/`check_type`/`whnf`. The NON-import lane keeps the
        // implication stub UNCHANGED. No production prelude declaration consumes
        // `Nat.mul_lt_mul_right`.
        if !self.suppress_lossy_structure_stubs {
            let mul_lt_mul_right_type = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat_const.clone());
                let (b_id, bv) = b.fresh_local(nat_const.clone());
                let (c_id, c) = b.fresh_local(nat_const.clone());
                let lt_zero_c =
                    Expr::app(Expr::app(lt_const.clone(), zero_const.clone()), c.clone());
                let lt_a_b = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
                let (h1_id, _h1) = b.fresh_local(lt_zero_c.clone());
                let (h2_id, _h2) = b.fresh_local(lt_a_b.clone());
                let body = Expr::app(
                    Expr::app(
                        lt_const.clone(),
                        Expr::app(Expr::app(mul_const.clone(), a.clone()), c.clone()),
                    ),
                    Expr::app(Expr::app(mul_const.clone(), bv.clone()), c.clone()),
                );
                let e = b.mk_pi(h2_id, BinderInfo::Default, lt_a_b, body);
                let e = b.mk_pi(h1_id, BinderInfo::Default, lt_zero_c, e);
                let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
                let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
                b.finish(e)
            };

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.mul_lt_mul_right"),
                level_params: vec![],
                type_: mul_lt_mul_right_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.mul_le_mul_left : ∀ a b c : Nat, a ≤ b → c * a ≤ c * b
        let mul_le_mul_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let le_a_b = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(le_a_b.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(mul_const.clone(), c.clone()), a.clone()),
                ),
                Expr::app(Expr::app(mul_const.clone(), c.clone()), bv.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_a_b, body);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when `register_nat_mul_le_mul_left_proof`
        // has already registered the constructive Theorem form (above).
        if self
            .get_const(&Name::from_string("Nat.mul_le_mul_left"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.mul_le_mul_left"),
                level_params: vec![],
                type_: mul_le_mul_left_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.mul_le_mul_right : ∀ a b c : Nat, a ≤ b → a * c ≤ b * c
        let mul_le_mul_right_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let le_a_b = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(le_a_b.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(mul_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(mul_const.clone(), bv.clone()), c.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_a_b, body);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when `register_nat_arith_order_proofs`
        // has already registered the constructive Theorem form (above).
        if self
            .get_const(&Name::from_string("Nat.mul_le_mul_right"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.mul_le_mul_right"),
                level_params: vec![],
                type_: mul_le_mul_right_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.mul_lt_mul : ∀ a b c d : Nat, a < b → c < d → 0 < c → a * c < b * d
        let mul_lt_mul_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let (d_id, d) = b.fresh_local(nat_const.clone());
            let lt_a_b = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
            let lt_c_d = Expr::app(Expr::app(lt_const.clone(), c.clone()), d.clone());
            let lt_zero_c = Expr::app(Expr::app(lt_const.clone(), zero_const.clone()), c.clone());
            let (h1_id, _h1) = b.fresh_local(lt_a_b.clone());
            let (h2_id, _h2) = b.fresh_local(lt_c_d.clone());
            let (h3_id, _h3) = b.fresh_local(lt_zero_c.clone());
            let body = Expr::app(
                Expr::app(
                    lt_const.clone(),
                    Expr::app(Expr::app(mul_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(mul_const.clone(), bv.clone()), d.clone()),
            );
            let e = b.mk_pi(h3_id, BinderInfo::Default, lt_zero_c, body);
            let e = b.mk_pi(h2_id, BinderInfo::Default, lt_c_d, e);
            let e = b.mk_pi(h1_id, BinderInfo::Default, lt_a_b, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.mul_lt_mul"),
            level_params: vec![],
            type_: mul_lt_mul_type,
        })?;

        // Built with EnvDeclBuilder (#1444).
        // FIDELITY: match Lean core's real `Nat.mul_le_mul` signature —
        //   ∀ {n₁ m₁ n₂ m₂ : Nat}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁*m₁ ≤ n₂*m₂
        // (the hypotheses pair 1st-with-3rd and 2nd-with-4th, and the result
        // multiplies adjacent binders). This axiom is only registered as a
        // fallback when the constructive Theorem form is absent, but its type
        // must still be Lean-faithful. See
        // `nat_arith_order_proof::register_nat_mul_le_mul`.
        let mul_le_mul_type = {
            let mut b = EnvDeclBuilder::new();
            let (n1_id, n1) = b.fresh_local(nat_const.clone());
            let (m1_id, m1) = b.fresh_local(nat_const.clone());
            let (n2_id, n2) = b.fresh_local(nat_const.clone());
            let (m2_id, m2) = b.fresh_local(nat_const.clone());
            let le_h1 = Expr::app(Expr::app(le_const.clone(), n1.clone()), n2.clone());
            let le_h2 = Expr::app(Expr::app(le_const.clone(), m1.clone()), m2.clone());
            let (h1_id, _h1) = b.fresh_local(le_h1.clone());
            let (h2_id, _h2) = b.fresh_local(le_h2.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(mul_const.clone(), n1.clone()), m1.clone()),
                ),
                Expr::app(Expr::app(mul_const.clone(), n2.clone()), m2.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, le_h2, body);
            let e = b.mk_pi(h1_id, BinderInfo::Default, le_h1, e);
            let e = b.mk_pi(m2_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_pi(n2_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_pi(m1_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_pi(n1_id, BinderInfo::Implicit, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when the constructive Theorem form is present.
        if self
            .get_const(&Name::from_string("Nat.mul_le_mul"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.mul_le_mul"),
                level_params: vec![],
                type_: mul_le_mul_type,
            })?;
        }

        self.nat_mul_ord_init = true;
        Ok(())
    }

    /// Check if Nat multiplication ordering lemmas have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_mul_ord_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_mul_ord(&self) -> bool {
        self.nat_mul_ord_init
    }

    /// Initialize Nat subtraction ordering lemmas
    ///
    /// Adds axioms for subtraction ordering properties:
    /// - Nat.sub_le : ∀ a b : Nat, Nat.le (Nat.sub a b) a
    /// - Nat.sub_lt : ∀ a b : Nat, Nat.lt Nat.zero a → Nat.lt Nat.zero b → Nat.lt (Nat.sub a b) a
    /// - Nat.sub_le_sub_left : ∀ a b c : Nat, Nat.le b c → Nat.le (Nat.sub a c) (Nat.sub a b)
    /// - Nat.sub_le_sub_right : ∀ a b c : Nat, Nat.le a b → Nat.le (Nat.sub a c) (Nat.sub b c)
    /// - Nat.sub_self : ∀ a : Nat, Eq (Nat.sub a a) Nat.zero
    /// - Nat.sub_zero : ∀ a : Nat, Eq (Nat.sub a Nat.zero) a
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_sub_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_nat_sub_ord(&mut self) -> Result<(), EnvError> {
        if self.nat_sub_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?; // Provides Nat, Nat.sub
        self.init_le()?; // Provides LE typeclass
        self.init_lt()?; // Provides LT typeclass
        self.init_nat_linear_order()?; // Provides Nat.le and Nat.lt
        self.init_eq()?; // Provides Eq

        // #3604 (lt cluster): Demote `Nat.sub_le` to a constructive
        // `Declaration::Theorem`. Registered *before* the legacy Axiom block so
        // the Theorem form wins; the `Nat.sub_le` Axiom `add_decl` below is
        // guarded by `get_const` and becomes a no-op once the Theorem is
        // present. See `nat_arith_order_proof.rs`.
        self.register_nat_arith_order_proofs()?;

        // #3604: Demote the remaining `Nat.sub` order family
        // (`Nat.sub_self`, `Nat.sub_lt`, `Nat.sub_le_sub_left`,
        // `Nat.sub_le_sub_right`) to constructive `Declaration::Theorem`s.
        // Registered *before* the legacy Axiom blocks so the Theorem form
        // wins; each legacy `add_decl` below is guarded by `get_const` and
        // becomes a no-op once the Theorem is present. See
        // `nat_sub_order_remaining_proof.rs`.
        self.register_nat_sub_order_remaining_proofs()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let sub_const = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);

        // Built with EnvDeclBuilder (#1444).
        // Nat.sub_le : ∀ a b : Nat, Nat.le (Nat.sub a b) a
        let sub_le_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(sub_const.clone(), a.clone()), bv.clone()),
                ),
                a.clone(),
            );
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604 (lt cluster): Guarded — skipped when the constructive Theorem
        // form is present (registered by `register_nat_arith_order_proofs`).
        if self.get_const(&Name::from_string("Nat.sub_le")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.sub_le"),
                level_params: vec![],
                type_: sub_le_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.sub_lt : ∀ a b : Nat, 0 < a → 0 < b → (a - b) < a
        let sub_lt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let lt_zero_a = Expr::app(Expr::app(lt_const.clone(), zero_const.clone()), a.clone());
            let lt_zero_b = Expr::app(Expr::app(lt_const.clone(), zero_const.clone()), bv.clone());
            let (h1_id, _h1) = b.fresh_local(lt_zero_a.clone());
            let (h2_id, _h2) = b.fresh_local(lt_zero_b.clone());
            let body = Expr::app(
                Expr::app(
                    lt_const.clone(),
                    Expr::app(Expr::app(sub_const.clone(), a.clone()), bv.clone()),
                ),
                a.clone(),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, lt_zero_b, body);
            let e = b.mk_pi(h1_id, BinderInfo::Default, lt_zero_a, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when the constructive Theorem form is
        // present (registered by `register_nat_sub_order_remaining_proofs`).
        if self.get_const(&Name::from_string("Nat.sub_lt")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.sub_lt"),
                level_params: vec![],
                type_: sub_lt_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.sub_le_sub_left : ∀ a b c : Nat, b ≤ c → (a - c) ≤ (a - b)
        let sub_le_sub_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let le_b_c = Expr::app(Expr::app(le_const.clone(), bv.clone()), c.clone());
            let (h_id, _h) = b.fresh_local(le_b_c.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(sub_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(sub_const.clone(), a.clone()), bv.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_b_c, body);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when the constructive Theorem form is
        // present (registered by `register_nat_sub_order_remaining_proofs`).
        // IMPORT MODE (v4.31 retarget): transposed-binder drift — Clean puts
        // `(k : Nat)` before `h : a ≤ b` with explicit bounds and raw Nat.le;
        // v4.31 is `{n m} → h → (k)` in LE.le form. Import-suppressed so the
        // genuine olean lemma imports (closure-checked).
        if !self.suppress_lossy_structure_stubs
            && self
                .get_const(&Name::from_string("Nat.sub_le_sub_left"))
                .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.sub_le_sub_left"),
                level_params: vec![],
                type_: sub_le_sub_left_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.sub_le_sub_right : ∀ a b c : Nat, a ≤ b → (a - c) ≤ (b - c)
        let sub_le_sub_right_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let (c_id, c) = b.fresh_local(nat_const.clone());
            let le_a_b = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(le_a_b.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(sub_const.clone(), a.clone()), c.clone()),
                ),
                Expr::app(Expr::app(sub_const.clone(), bv.clone()), c.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_a_b, body);
            let e = b.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // #3604: Guarded — skipped when the constructive Theorem form is
        // present (registered by `register_nat_sub_order_remaining_proofs`).
        // IMPORT MODE (v4.31 retarget): transposed-binder drift — Clean puts
        // `(k : Nat)` before `h : a ≤ b` with explicit bounds and raw Nat.le;
        // v4.31 is `{n m} → h → (k)` in LE.le form. Import-suppressed so the
        // genuine olean lemma imports (closure-checked).
        if !self.suppress_lossy_structure_stubs
            && self
                .get_const(&Name::from_string("Nat.sub_le_sub_right"))
                .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.sub_le_sub_right"),
                level_params: vec![],
                type_: sub_le_sub_right_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.sub_self : ∀ a : Nat, Eq (Nat.sub a a) Nat.zero
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let sub_self_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), nat_const.clone()),
                    Expr::app(Expr::app(sub_const.clone(), a.clone()), a.clone()),
                ),
                zero_const.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        // #3604: Guarded — skipped when the constructive Theorem form is
        // present (registered by `register_nat_sub_order_remaining_proofs`).
        if self.get_const(&Name::from_string("Nat.sub_self")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.sub_self"),
                level_params: vec![],
                type_: sub_self_type,
            })?;
        }

        // Nat.sub_zero : ∀ a : Nat, Eq (Nat.sub a Nat.zero) a
        //
        // SOUNDNESS (#3604 kernel-soundness Tier 6): Converted from
        // Declaration::Axiom to Declaration::Theorem. Pure
        // `@Eq.refl.{1} Nat a`; the kernel reduces `Nat.sub a Nat.zero` to
        // `a` by iota on `Nat.rec` (zero case) + delta on the reducible
        // `Nat.sub` definition. See `algebra_nat_sub_zero_proof.rs`. Empty
        // domain-axiom closure.
        self.register_nat_sub_zero_proof()?;

        self.nat_sub_ord_init = true;
        Ok(())
    }

    /// Check if Nat subtraction ordering lemmas have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_sub_ord_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_sub_ord(&self) -> bool {
        self.nat_sub_ord_init
    }

    /// Initialize Nat power ordering lemmas
    ///
    /// Adds axioms for power ordering properties:
    /// - Nat.pow_le_pow_left : ∀ a b n : Nat, a ≤ b → Nat.pow a n ≤ Nat.pow b n
    /// - Nat.pow_lt_pow_left : ∀ a b n : Nat, a < b → 0 < n → Nat.pow a n < Nat.pow b n
    /// - Nat.pow_le_pow_right : ∀ a m n : Nat, 1 ≤ a → m ≤ n → Nat.pow a m ≤ Nat.pow a n
    /// - Nat.pow_zero : ∀ a : Nat, Eq (Nat.pow a Nat.zero) (Nat.succ Nat.zero)
    /// - Nat.pow_one : ∀ a : Nat, Eq (Nat.pow a (Nat.succ Nat.zero)) a
    /// - Nat.one_pow : ∀ n : Nat, Eq (Nat.pow (Nat.succ Nat.zero) n) (Nat.succ Nat.zero)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_pow_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_nat_pow_ord(&mut self) -> Result<(), EnvError> {
        if self.nat_pow_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat()?; // Provides Nat, Nat.pow
        self.init_le()?; // Provides LE typeclass
        self.init_lt()?; // Provides LT typeclass
        self.init_nat_linear_order()?; // Provides Nat.le and Nat.lt
        self.init_eq()?; // Provides Eq

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let pow_const = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one_const = Expr::app(succ_const.clone(), zero_const.clone());

        // Built with EnvDeclBuilder (#1444).
        // Nat.pow_le_pow_left : ∀ a b n : Nat, a ≤ b → Nat.pow a n ≤ Nat.pow b n
        let pow_le_pow_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let le_a_b = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
            let (h_id, _h) = b.fresh_local(le_a_b.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(pow_const.clone(), a.clone()), n.clone()),
                ),
                Expr::app(Expr::app(pow_const.clone(), bv.clone()), n.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_a_b, body);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Nat.pow_le_pow_left : ∀ a b n : Nat, a ≤ b → a^n ≤ b^n
        //
        // SOUNDNESS (#3604 kernel-soundness arithmetic-ordering vein): Converted
        // from Declaration::Axiom to Declaration::Theorem. Induction on `n` via
        // `@Nat.rec.{0}`: base `Nat.le.refl 1` (both powers reduce to `1` at the
        // zero iota-case of `Nat.pow`), step `Nat.mul_le_mul (a^k) (b^k) a b ih h`
        // after the kernel reduces `Nat.pow x (succ k)` to `Nat.mul (Nat.pow x k) x`.
        // See `algebra_nat_pow_le_pow_left_proof.rs`. Empty domain-axiom closure.
        // The legacy axiom below is guarded so the Theorem form wins.
        self.register_nat_pow_le_pow_left_proof()?;
        if self
            .get_const(&Name::from_string("Nat.pow_le_pow_left"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.pow_le_pow_left"),
                level_params: vec![],
                type_: pow_le_pow_left_type,
            })?;
        }

        // Built with EnvDeclBuilder (#1444).
        // Nat.pow_lt_pow_left : ∀ a b n : Nat, a < b → 0 < n → a^n < b^n
        let pow_lt_pow_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bv_id, bv) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let lt_a_b = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
            let lt_zero_n = Expr::app(Expr::app(lt_const.clone(), zero_const.clone()), n.clone());
            let (h1_id, _h1) = b.fresh_local(lt_a_b.clone());
            let (h2_id, _h2) = b.fresh_local(lt_zero_n.clone());
            let body = Expr::app(
                Expr::app(
                    lt_const.clone(),
                    Expr::app(Expr::app(pow_const.clone(), a.clone()), n.clone()),
                ),
                Expr::app(Expr::app(pow_const.clone(), bv.clone()), n.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, lt_zero_n, body);
            let e = b.mk_pi(h1_id, BinderInfo::Default, lt_a_b, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.pow_lt_pow_left"),
            level_params: vec![],
            type_: pow_lt_pow_left_type,
        })?;

        // Built with EnvDeclBuilder (#1444).
        // Nat.pow_le_pow_right : ∀ a m n : Nat, 1 ≤ a → m ≤ n → a^m ≤ a^n
        let pow_le_pow_right_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (m_id, m) = b.fresh_local(nat_const.clone());
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let le_one_a = Expr::app(Expr::app(le_const.clone(), one_const.clone()), a.clone());
            let le_m_n = Expr::app(Expr::app(le_const.clone(), m.clone()), n.clone());
            let (h1_id, _h1) = b.fresh_local(le_one_a.clone());
            let (h2_id, _h2) = b.fresh_local(le_m_n.clone());
            let body = Expr::app(
                Expr::app(
                    le_const.clone(),
                    Expr::app(Expr::app(pow_const.clone(), a.clone()), m.clone()),
                ),
                Expr::app(Expr::app(pow_const.clone(), a.clone()), n.clone()),
            );
            let e = b.mk_pi(h2_id, BinderInfo::Default, le_m_n, body);
            let e = b.mk_pi(h1_id, BinderInfo::Default, le_one_a, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Nat.pow_le_pow_right : ∀ a m n : Nat, 1 ≤ a → m ≤ n → a^m ≤ a^n
        //
        // SOUNDNESS (#3604 kernel-soundness arithmetic-ordering vein): Converted
        // from Declaration::Axiom to Declaration::Theorem. Induction on the
        // `Nat.le m n` witness via `@Nat.le.rec`: refl `Nat.le.refl (a^m)`, step
        // chains the IH with `Nat.le (a^t) ((a^t)*a)` (transport of
        // `Nat.mul_le_mul_left 1 a (a^t) h1` along `Nat.mul_one (a^t)`) through
        // `Nat.le_trans`, with the kernel reducing `Nat.pow a (succ t)` to
        // `Nat.mul (Nat.pow a t) a`. See `algebra_nat_pow_le_pow_right_proof.rs`.
        // Empty domain-axiom closure. The legacy axiom below is guarded so the
        // Theorem form wins.
        self.register_nat_pow_le_pow_right_proof()?;
        if self
            .get_const(&Name::from_string("Nat.pow_le_pow_right"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.pow_le_pow_right"),
                level_params: vec![],
                type_: pow_le_pow_right_type,
            })?;
        }

        // Nat.pow_zero : ∀ a : Nat, Eq (Nat.pow a 0) 1
        //
        // SOUNDNESS (#3604 kernel-soundness Tier 6): Converted from
        // Declaration::Axiom to Declaration::Theorem. Pure
        // `@Eq.refl.{1} Nat (Nat.succ Nat.zero)`; the kernel reduces
        // `Nat.pow a Nat.zero` to `Nat.succ Nat.zero` by iota on `Nat.rec`
        // (zero case) + delta on the reducible `Nat.pow` definition. See
        // `algebra_nat_pow_zero_proof.rs`. Empty domain-axiom closure.
        self.register_nat_pow_zero_proof()?;

        // Nat.pow_one : ∀ a : Nat, Eq (Nat.pow a 1) a
        //
        // SOUNDNESS (#3604 kernel-soundness Tier 6): Converted from
        // Declaration::Axiom to Declaration::Theorem. Body
        // `λ a => Nat.one_mul a`; the kernel reduces
        // `Nat.pow a (Nat.succ Nat.zero)` to `Nat.mul (Nat.succ Nat.zero) a`
        // (iota + delta), so the constructive `Nat.one_mul` is defeq to the
        // goal. See `algebra_nat_pow_one_proof.rs`. Empty domain-axiom
        // closure.
        self.register_nat_pow_one_proof()?;

        // Nat.one_pow : ∀ n : Nat, Eq (Nat.pow 1 n) 1
        //
        // SOUNDNESS (#3604 kernel-soundness Tier 6): Converted from
        // Declaration::Axiom to Declaration::Theorem. Induction on `n` via
        // `@Nat.rec.{0}`: base `@Eq.refl.{1}` (zero iota-case of `Nat.pow`),
        // step `Eq.trans (Nat.mul_one (Nat.pow 1 k)) ih` after the kernel
        // reduces `Nat.pow 1 (succ k)` to `Nat.mul (Nat.pow 1 k) 1`. See
        // `algebra_nat_one_pow_proof.rs`. Empty domain-axiom closure.
        self.register_nat_one_pow_proof()?;

        // Nat.pow_add : ∀ a m n, Eq (Nat.pow a (Nat.add m n))
        //                           (Nat.mul (Nat.pow a m) (Nat.pow a n))
        //
        // SOUNDNESS: Constructive `Declaration::Theorem`. Induction on `n` via
        // `@Nat.rec.{0}`: base `Eq.symm (Nat.mul_one (Nat.pow a m))`, step
        // `Eq.trans (congrArg (λ z => Nat.mul z a) ih)
        //           (Nat.mul_assoc (Nat.pow a m) (Nat.pow a k) a)`. See
        // `algebra_nat_pow_add_proof.rs`. Empty domain-axiom closure.
        self.register_nat_pow_add_proof()?;

        // Nat.pow_mul : ∀ a m n, Eq (Nat.pow a (Nat.mul m n))
        //                           (Nat.pow (Nat.pow a m) n)
        //
        // SOUNDNESS: Constructive `Declaration::Theorem`. Induction on `n` via
        // `@Nat.rec.{0}`: base `@Eq.refl.{1} Nat 1`, step
        // `Eq.trans (Nat.pow_add a (Nat.mul m k) m)
        //           (congrArg (λ z => Nat.mul z (Nat.pow a m)) ih)`. See
        // `algebra_nat_pow_mul_proof.rs`. Empty domain-axiom closure.
        self.register_nat_pow_mul_proof()?;

        self.nat_pow_ord_init = true;
        Ok(())
    }

    /// Check if Nat power ordering lemmas have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_pow_ord_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_pow_ord(&self) -> bool {
        self.nat_pow_ord_init
    }

    /// Initialize FATE-X order theory stubs
    ///
    /// Additional order-theoretic types and predicates needed for FATE-X elaboration:
    /// - WithBot: Type with bottom element adjoined
    /// - WithTop: Type with top element adjoined
    /// - Top.top: Top element typeclass
    /// - Bot.bot: Bottom element typeclass
    /// - ValuationRing: Ring where all elements are comparable by divisibility
    /// - Set.range: Range of a function as a set
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fate_x_order_stubs_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_fate_x_order_stubs(&mut self) -> Result<(), EnvError> {
        if self.fate_x_order_stubs_init {
            return Ok(());
        }

        self.init_eq()?;
        // ValuationRing references Ring; Set.range references Set (#1444).
        self.init_ring()?;
        self.init_set()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::sort(Level::zero()); // Prop = Sort 0

        // WithBot : Type u → Type u
        let with_bot_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("WithBot"),
            level_params: vec![u.clone()],
            type_: with_bot_type,
        })?;

        // WithTop : Type u → Type u
        let with_top_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("WithTop"),
            level_params: vec![u.clone()],
            type_: with_top_type,
        })?;

        // Top : Type u → Type u (typeclass)
        let top_class_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Top"),
            level_params: vec![u.clone()],
            type_: top_class_type,
        })?;

        // Built with EnvDeclBuilder (#1444).
        // Top.top : {α : Type u} → [Top α] → α
        let top_top_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let top_alpha = Expr::app(
                Expr::const_(Name::from_string("Top"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(top_alpha.clone());
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, top_alpha, alpha.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Top.top"),
            level_params: vec![u.clone()],
            type_: top_top_type,
        })?;

        // Bot : Type u → Type u (typeclass)
        let bot_class_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Bot"),
            level_params: vec![u.clone()],
            type_: bot_class_type,
        })?;

        // Built with EnvDeclBuilder (#1444).
        // Bot.bot : {α : Type u} → [Bot α] → α
        let bot_bot_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let bot_alpha = Expr::app(
                Expr::const_(Name::from_string("Bot"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(bot_alpha.clone());
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, bot_alpha, alpha.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Bot.bot"),
            level_params: vec![u.clone()],
            type_: bot_bot_type,
        })?;

        // Built with EnvDeclBuilder (#1444).
        // ValuationRing : {α : Type u} → [Ring α] → Prop
        let ring_const = |lvl: Level| Expr::const_(Name::from_string("Ring"), vec![lvl]);
        let valuation_ring_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ring_alpha = Expr::app(ring_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(ring_alpha.clone());
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ring_alpha, prop.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ValuationRing"),
            level_params: vec![u.clone()],
            type_: valuation_ring_type,
        })?;

        // Built with EnvDeclBuilder (#1444).
        // Set.range : {α : Type u} → {β : Type v} → (α → β) → Set β
        let v = Name::from_string("v");
        let v_level = Level::param(v.clone());
        let type_v = Expr::sort(Level::succ(v_level.clone()));

        let set_range_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let fn_type = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (f_id, _f) = b.fresh_local(fn_type.clone());
            let body = Expr::app(
                Expr::const_(Name::from_string("Set"), vec![v_level.clone()]),
                beta.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, fn_type, body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Set.range"),
            level_params: vec![u.clone(), v.clone()],
            type_: set_range_type,
        })?;

        // Ring.jacobson references Ideal; declare it if not already present.
        // Ideal : Type u → Type u (Lean 4: Ideal R = Submodule R R)
        self.add_init_axiom_if_absent("Ideal", std::slice::from_ref(&u), || {
            Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone())
        })?;

        // Built with EnvDeclBuilder (#1444).
        // Ring.jacobson : {R : Type u} → [Ring R] → Ideal R
        let jacobson_type = {
            let mut b = EnvDeclBuilder::new();
            let (r_id, r) = b.fresh_local(type_u.clone());
            let ring_r = Expr::app(ring_const(u_level.clone()), r.clone());
            let (inst_id, _inst) = b.fresh_local(ring_r.clone());
            let body = Expr::app(
                Expr::const_(Name::from_string("Ideal"), vec![u_level.clone()]),
                r.clone(),
            );
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ring_r, body);
            let e = b.mk_pi(r_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Ring.jacobson"),
            level_params: vec![u.clone()],
            type_: jacobson_type,
        })?;

        // CategoryTheory.Skeleton : Type u → Type u
        let skeleton_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("CategoryTheory.Skeleton"),
            level_params: vec![u.clone()],
            type_: skeleton_type,
        })?;

        // Module.Projective : {R : Type u} → {M : Type v} → Prop
        let projective_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(BinderInfo::Implicit, type_v.clone(), prop.clone()),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Module.Projective"),
            level_params: vec![u.clone(), v.clone()],
            type_: projective_type,
        })?;

        // NoZeroSMulDivisors : (R : Type u) → (M : Type v) → Prop
        let no_zero_smul_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),
            Expr::pi(BinderInfo::Default, type_v, prop),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NoZeroSMulDivisors"),
            level_params: vec![u, v],
            type_: no_zero_smul_type,
        })?;

        self.fate_x_order_stubs_init = true;
        Ok(())
    }

    /// Check if FATE-X order stubs have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.fate_x_order_stubs_init == true`
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn has_fate_x_order_stubs(&self) -> bool {
        self.fate_x_order_stubs_init
    }
}
