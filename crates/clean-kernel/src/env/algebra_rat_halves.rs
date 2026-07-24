// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the `Rat` halving sub-build (`Rat.add_halves`).
//!
//! # Why this module exists
//!
//! `NNReal.CauSeq.Equiv.trans` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B) needs the ε/2
//! split: combining `vf < vg + ε` and `vg < vh + ε` with a single shared `ε`
//! only lands at `vf < vh + 2ε`; to land at `ε` you instantiate both hypotheses
//! at `ε/2` and recombine via `ε/2 + ε/2 = ε`. That identity is the gate to a
//! genuine setoid, and everything below `trans` (`add`, `le`, `sqrt`) depends on
//! it.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.two : Rat`  := `Rat.add Rat.one Rat.one`  (reducible)
//! - `Rat.two_ne_zero : @Eq Rat Rat.two Rat.zero → False`
//! - `Rat.add_halves : ∀ ε : Rat,
//!       @Eq Rat (Rat.add (Rat.div ε Rat.two) (Rat.div ε Rat.two)) ε`
//!
//! Every declaration is a checked `Definition`/`Theorem` through `self.add_decl`;
//! every theorem's transitive admitted-axiom closure is empty (foundational
//! only). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof sketch
//!
//! `Rat.div ε Rat.two` reduces (it is reducible) to `Rat.mul ε (Rat.inv two)`.
//! Write `inv2 := Rat.inv two`. The proof is two `Eq.trans` chains:
//!
//! 1. `inv2 + inv2 = one`:
//!    `inv2 + inv2 = (one·inv2) + (one·inv2)`   (`congrArg (·+·) (one_mul inv2)⁻¹`)
//!                 `= (one+one)·inv2`            (`right_distrib one one inv2 ⁻¹`)
//!                 `= two·inv2`                  (defeq: `two ≡ one+one`)
//!                 `= one`                       (`mul_inv_cancel two two_ne_zero`).
//! 2. main:
//!    `(ε·inv2) + (ε·inv2) = ε·(inv2+inv2)`     (`left_distrib ε inv2 inv2 ⁻¹`)
//!                         `= ε·one`            (`congrArg (ε··) step1`)
//!                         `= ε`                (`mul_one ε`).
//!
//! `Rat.two_ne_zero`: `0 < 1` (`Rat.zero_lt_one`) and `1 < two` (from
//! `Rat.add_lt_add_left 0 1 1 zero_lt_one : 1+0 < 1+1` transported along
//! `Rat.add_zero 1`) give `0 < two` (`Rat.lt_trans`). If `two = 0`, substituting
//! turns `0 < two` into `0 < 0`; `Rat.lt_iff_le_not_le 0 0` then yields
//! `And (0≤0) (¬0≤0)`, and `And.right · (And.left ·)` produces `False`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles + smart-constructors for the `Rat` halving
/// lemmas. All operate on the live `Rat` field surface.
pub(crate) struct RatHalvesConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    // Field/order lemmas (live `Rat`, each a kernel-checked Theorem).
    rat_left_distrib: Expr,
    rat_right_distrib: Expr,
    rat_one_mul: Expr,
    rat_mul_one: Expr,
    rat_mul_inv_cancel: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_trans: Expr,
    rat_zero_lt_one: Expr,
    rat_lt_iff_le_not_le: Expr,
    // Eq / logic machinery at level 1 (Rat : Type 0 = Sort 1).
    eq_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    iff_mp: Expr,
    and_c: Expr,
    and_left: Expr,
    and_right: Expr,
    not_c: Expr,
    false_c: Expr,
}

impl RatHalvesConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_left_distrib: k("Rat.left_distrib"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_one_mul: k("Rat.one_mul"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_trans: k("Rat.lt_trans"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
            iff_mp: k("Iff.mp"),
            and_c: k("And"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            not_c: k("Not"),
            false_c: k("False"),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    /// `Rat.two := Rat.add Rat.one Rat.one`.
    fn two(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.two"), vec![])
    }
    /// `@Eq Rat a b`.
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }

    // ── proof constructors ──────────────────────────────────────────────────

    /// `@Eq.symm Rat a b h : Eq Rat b a` (h : Eq Rat a b).
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.trans Rat a b cc hab hbc : Eq Rat a cc`.
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a) (f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn eq_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Rat.left_distrib a b c : Eq Rat (a·(b+c)) ((a·b)+(a·c))`.
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_left_distrib.clone(), [a, b, cc])
    }
    /// `Rat.right_distrib a b c : Eq Rat ((a+b)·c) ((a·c)+(b·c))`.
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_right_distrib.clone(), [a, b, cc])
    }
    /// `Rat.one_mul a : Eq Rat (one·a) a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    /// `Rat.mul_one a : Eq Rat (a·one) a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `Rat.mul_inv_cancel a h : Eq Rat (a·(inv a)) one`  (h : a = 0 → False).
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.add_zero a : Eq Rat (a+0) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `Rat.add_lt_add_left a b c h : Rat.lt (c+a) (c+b)`  (h : a<b).
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.lt_trans a b c hab hbc : Rat.lt a c`.
    fn lt_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_trans.clone(), [a, b, cc, hab, hbc])
    }
}

impl Environment {
    /// Register the `Rat` halving sub-build: `Rat.two`, `Rat.two_ne_zero`,
    /// `Rat.add_halves`. Idempotent. Pulls in the live `Rat` field surface
    /// (`init_rat_field_inst` — distrib/one_mul/mul_one/mul_inv_cancel) plus the
    /// linear order and strict-add monotonicity it needs.
    pub fn init_algebra_rat_halves(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_true_false()?;
        // Live `Rat` field lemmas: left_distrib, right_distrib, one_mul, mul_one,
        // mul_inv_cancel, add_zero (all kernel-checked quotient Theorems).
        self.init_rat_field_inst()?;
        // Rat.lt, Rat.lt_trans, Rat.zero_lt_one, Rat.lt_iff_le_not_le.
        self.init_rat_linear_order()?;
        self.register_rat_lt_trans()?;
        // Rat.add_lt_add_left (constructive strict-add monotonicity).
        self.register_rat_add_lt_add_left()?;

        let c = RatHalvesConsts::new();
        self.register_rat_two(&c)?;
        self.register_rat_two_ne_zero(&c)?;
        self.register_rat_add_halves(&c)?;
        Ok(())
    }

    /// `Rat.two : Rat := Rat.add Rat.one Rat.one` (reducible).
    fn register_rat_two(&mut self, c: &RatHalvesConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.two")).is_some() {
            return Ok(());
        }
        let value = c.add(c.rat_one.clone(), c.rat_one.clone());
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.two"),
            level_params: vec![],
            type_: c.rat.clone(),
            value,
            is_reducible: true,
        })
    }

    /// `Rat.two_ne_zero : @Eq Rat Rat.two Rat.zero → False`.
    fn register_rat_two_ne_zero(&mut self, c: &RatHalvesConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.two_ne_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two = c.two();
        let eq_two_zero = c.eq_ty(two.clone(), c.rat_zero.clone());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, _h) = b.fresh_local(eq_two_zero.clone());
            let e = b.mk_pi(
                h_id,
                BinderInfo::Default,
                eq_two_zero.clone(),
                c.false_c.clone(),
            );
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(eq_two_zero.clone());

            // h_one_lt_two : Rat.lt 1 two.
            //   add_lt_add_left 0 1 1 zero_lt_one : Rat.lt (1+0) (1+1) = (1+0) < two.
            //   transport along (add_zero 1 : 1+0 = 1):  motive t := Rat.lt t two.
            let one = c.rat_one.clone();
            let zero = c.rat_zero.clone();
            let one_plus_zero = c.add(one.clone(), zero.clone());
            let step = c.add_lt_add_left(
                zero.clone(),
                one.clone(),
                one.clone(),
                c.rat_zero_lt_one.clone(),
            );
            let motive_lt = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.lt(t, two.clone());
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let h_one_lt_two = c.eq_subst(
                motive_lt,
                one_plus_zero,
                one.clone(),
                c.add_zero(one.clone()),
                step,
            );

            // h_zero_lt_two : Rat.lt 0 two  := lt_trans 0 1 two zero_lt_one one_lt_two.
            let h_zero_lt_two = c.lt_trans(
                zero.clone(),
                one.clone(),
                two.clone(),
                c.rat_zero_lt_one.clone(),
                h_one_lt_two,
            );

            // Substitute two := 0 (via h : two = 0):  motive t := Rat.lt 0 t.
            //   h_zero_lt_zero : Rat.lt 0 0.
            let motive_zero_lt = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.lt(zero.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let h_zero_lt_zero =
                c.eq_subst(motive_zero_lt, two.clone(), zero.clone(), h, h_zero_lt_two);

            // Iff.mp (lt_iff_le_not_le 0 0) h_zero_lt_zero : And (0≤0) (Not (0≤0)).
            let le_00 = c.le(zero.clone(), zero.clone());
            let not_le_00 = Expr::app(c.not_c.clone(), le_00.clone());
            let lt_00 = c.lt(zero.clone(), zero.clone());
            let and_body = Expr::apps(c.and_c.clone(), [le_00.clone(), not_le_00.clone()]);
            let iff_lt = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [zero.clone(), zero.clone()]);
            let conj = Expr::apps(c.iff_mp.clone(), [lt_00, and_body, iff_lt, h_zero_lt_zero]);
            // And.right (0≤0)(¬0≤0) conj : Not (0≤0) ; applied to And.left … : False.
            let hr = Expr::apps(
                c.and_right.clone(),
                [le_00.clone(), not_le_00.clone(), conj.clone()],
            );
            let hl = Expr::apps(c.and_left.clone(), [le_00, not_le_00, conj]);
            let false_proof = Expr::app(hr, hl);

            let e = b.mk_lam(h_id, BinderInfo::Default, eq_two_zero, false_proof);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_halves : ∀ ε : Rat,
    ///     @Eq Rat (Rat.add (Rat.div ε Rat.two) (Rat.div ε Rat.two)) ε`.
    fn register_rat_add_halves(&mut self, c: &RatHalvesConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_halves");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two = c.two();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let half = c.div(eps.clone(), two.clone());
            let lhs = c.add(half.clone(), half);
            let concl = c.eq_ty(lhs, eps.clone());
            let e = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), concl);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let one = c.rat_one.clone();
            let inv2 = c.inv(two.clone());
            let one_mul_inv2 = c.mul(one.clone(), inv2.clone());

            // ── Step A: inv2 + inv2 = one ──────────────────────────────────
            // s1 : inv2 = one·inv2   (= Eq.symm (one_mul inv2)).
            let s1 = c.eq_symm(one_mul_inv2.clone(), inv2.clone(), c.one_mul(inv2.clone()));
            // s2 : (inv2 + inv2) = (one·inv2 + one·inv2)  via congrArg (fun t => t + t).
            let add_diag = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = fb.fresh_local(c.rat.clone());
                let body = c.add(t.clone(), t);
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let s2 = c.congr_arg(inv2.clone(), one_mul_inv2.clone(), add_diag, s1);
            // s3 : (one·inv2 + one·inv2) = (one+one)·inv2  (= Eq.symm right_distrib).
            let one_plus_one = c.add(one.clone(), one.clone());
            let two_mul_inv2 = c.mul(one_plus_one.clone(), inv2.clone()); // ≡ two·inv2 (defeq)
            let lhs_pair = c.add(one_mul_inv2.clone(), one_mul_inv2.clone());
            let rd = c.right_distrib(one.clone(), one.clone(), inv2.clone());
            let s3 = c.eq_symm(two_mul_inv2.clone(), lhs_pair.clone(), rd);
            // mic : two·inv2 = one  (= mul_inv_cancel two two_ne_zero).
            // Note Rat.two ≡ one+one (reducible) and inv2 = inv two, so
            // mul_inv_cancel two _ : (two · inv two) = one is defeq to (one+one)·inv2.
            let two_ne_zero = Expr::const_(Name::from_string("Rat.two_ne_zero"), vec![]);
            let mic = c.mul_inv_cancel(two.clone(), two_ne_zero);
            // chain: (inv2+inv2) → (one·inv2 + one·inv2) → (one+one)·inv2 → one.
            let inv2_pair = c.add(inv2.clone(), inv2.clone());
            let t1 = c.eq_trans(
                inv2_pair.clone(),
                lhs_pair.clone(),
                two_mul_inv2.clone(),
                s2,
                s3,
            );
            let step_a = c.eq_trans(inv2_pair.clone(), two_mul_inv2, one.clone(), t1, mic);

            // ── Step B: (ε·inv2) + (ε·inv2) = ε ────────────────────────────
            let e_inv2 = c.mul(eps.clone(), inv2.clone());
            let e_inv2_pair = c.add(e_inv2.clone(), e_inv2.clone());
            // b1 : (ε·inv2 + ε·inv2) = ε·(inv2+inv2)  (= Eq.symm left_distrib).
            let e_times_pair = c.mul(eps.clone(), inv2_pair.clone());
            let ld = c.left_distrib(eps.clone(), inv2.clone(), inv2.clone());
            let b1 = c.eq_symm(e_times_pair.clone(), e_inv2_pair.clone(), ld);
            // b2 : ε·(inv2+inv2) = ε·one  via congrArg (fun t => ε·t) step_a.
            let mul_eps_fn = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = fb.fresh_local(c.rat.clone());
                let body = c.mul(eps.clone(), t);
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let e_times_one = c.mul(eps.clone(), one.clone());
            let b2 = c.congr_arg(inv2_pair.clone(), one.clone(), mul_eps_fn, step_a);
            // mo : ε·one = ε  (= mul_one ε).
            let mo = c.mul_one(eps.clone());
            // chain: (ε·inv2+ε·inv2) → ε·(inv2+inv2) → ε·one → ε.
            let c1 = c.eq_trans(
                e_inv2_pair.clone(),
                e_times_pair,
                e_times_one.clone(),
                b1,
                b2,
            );
            let final_eq = c.eq_trans(e_inv2_pair, e_times_one, eps.clone(), c1, mo);

            let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), final_eq);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["Rat.two"];
    const THEOREMS: &[&str] = &["Rat.two_ne_zero", "Rat.add_halves"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_halves()
            .expect("init_algebra_rat_halves");
        env.init_algebra_rat_halves().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_halves_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_rat_halves_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
