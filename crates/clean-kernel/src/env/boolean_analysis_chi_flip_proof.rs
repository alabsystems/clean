// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Step 2/4 toward `influence_fourier`: the spectral action of a coordinate flip
//! on the parity character `χ_S`.
//!
//! `BoolAnalysis.chi_flip_spectral : ∀ (n : Nat) (S x : HCPoint n) (i : Fin n),
//!     @Eq Rat (chi n S (hcFlip n x i))
//!             (Rat.mul (flipSign (S i)) (chi n S x))`
//!
//! where `flipSign : Bool → Rat`, `flipSign false = 1`, `flipSign true = -1`,
//! pulls the sign change of the single flipped coordinate out of the cube
//! product. Built from:
//!
//! - `flipSign` — the {+1 / −1} sign of "does this coordinate contribute a flip?".
//! - `pm_not : pm (¬b) = Rat.neg (pm b)` — flipping a bit negates its ±1 value
//!   (`Bool.rec`, ground Rat numerals).
//! - `Nat.beq_eq_false_of_ne` — the contrapositive of `Nat.eq_of_beq_eq_true`,
//!   needed to know the `hcFlip` gate is `false` off the flipped coordinate.
//! - `chi_flip_factor` — the per-coordinate identity
//!   `factor (S j) ((hcFlip n x i) j) = factor (S j) (x j) · signFactor i S j`
//!   where `signFactor i S j = if (Nat.beq (val j)(val i)) then flipSign (S i)
//!   else 1`.
//! - `Fin.prod_mul` to split the rewritten product, then `Fin.prod_single`
//!   (Step 1) to collapse the sign product to `flipSign (S i)`.
//!
//! All pieces axiom-free / `ProofQuality::Constructive`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `BoolAnalysis.flipSign : Bool → Rat` — `false ↦ 1`, `true ↦ -1`.
    /// `@Bool.rec (fun _ => Rat) Rat.one (Rat.neg Rat.one) b`. Reducible.
    pub(crate) fn register_flip_sign(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.flipSign");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );

        let ty = Expr::pi(BinderInfo::Default, bool_c.clone(), rat.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (b_id, bval) = b.fresh_local(bool_c.clone());
            // motive : fun (_ : Bool) => Rat
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, _t) = m.fresh_local(bool_c.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, bool_c.clone(), rat.clone()))
            };
            let neg_one = Expr::app(rat_neg.clone(), rat_one.clone());
            let body = Expr::apps(bool_rec.clone(), [motive, rat_one.clone(), neg_one, bval]);
            let e = b.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), body);
            b.finish(e)
        };
        // `init_boolean_analysis` may re-enter the influence assembly and register
        // this name already; re-check before re-declaring (idempotent).
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.pm_not : ∀ (b : Bool), pm (Bool.not b) = Rat.neg (pm b)`.
    /// `Bool.rec` on `b`, both leaves close by `Eq.refl` (ground Rat numerals:
    /// `pm (¬false)=pm true=-1=Rat.neg 1`, `pm (¬true)=pm false=1=Rat.neg(-1)`).
    pub(crate) fn register_pm_not(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.pm_not");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let one = Level::succ(Level::zero());
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let eq_rat_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        // lhs(b) = pm (Bool.not b);  rhs(b) = Rat.neg (pm b)
        let lhs = |bb: Expr| Expr::app(pm.clone(), Expr::app(bool_not.clone(), bb));
        let rhs = |bb: Expr| Expr::app(rat_neg.clone(), Expr::app(pm.clone(), bb));
        let eqn = |l: Expr, r: Expr| Expr::apps(eq_rat_c.clone(), [rat.clone(), l, r]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            let concl = eqn(lhs(bv.clone()), rhs(bv.clone()));
            b.finish(b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            // motive : fun (b' : Bool) => lhs b' = rhs b'
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (bp_id, bp) = m.fresh_local(bool_c.clone());
                let body = eqn(lhs(bp.clone()), rhs(bp.clone()));
                m.finish_child(m.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
            };
            let leaf = |bv: Expr| Expr::apps(eq_refl.clone(), [rat.clone(), lhs(bv)]);
            let f_case = leaf(bfalse.clone());
            let t_case = leaf(btrue.clone());
            let rec = Expr::apps(bool_rec0.clone(), [motive, f_case, t_case, bv.clone()]);
            b.finish(b.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec))
        };

        // Re-entrancy guard: `init_boolean_analysis` may register this name.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.flip_coeff_absorb : ∀ (b : Bool),
    ///   Rat.sub Rat.one (flipSign b) = Rat.mul (Rat.mk (Int.ofNat 2) 1) (ind b)`
    ///
    /// The modified-coefficient absorption for the influence energy identity:
    /// `1 − flipSign(S i) = 2·ind(S i)`. When the flip-difference
    /// `pm(f x) − pm(f(hcFlip n x i))` is expanded spectrally (via Fourier
    /// inversion + `chi_flip_spectral`), the `S`-coefficient `f̂(S)` is scaled by
    /// `1 − flipSign(S i)`, and this lemma rewrites that to `2·ind(S i)·f̂(S)` — the
    /// "absorbed" modified coefficient. `Bool.rec` on `b`, two ground Rat-numeral
    /// leaves (`1 − 1 = 0 = 2·0`; `1 − (−1) = 2 = 2·1`) closed by `Eq.refl`.
    /// Axiom-free.
    pub(crate) fn register_flip_coeff_absorb(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.flip_coeff_absorb");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_flip_sign()?;

        let one = Level::succ(Level::zero());
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let flip_sign = Expr::const_(Name::from_string("BoolAnalysis.flipSign"), vec![]);
        let eq_rat_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let nat_two = Expr::app(nat_succ.clone(), nat_one.clone());
        let rat_two = Expr::apps(
            rat_mk.clone(),
            [Expr::app(int_of_nat.clone(), nat_two), nat_one.clone()],
        );

        // lhs(b) = Rat.sub 1 (flipSign b); rhs(b) = Rat.mul 2 (ind b)
        let lhs = |bb: Expr| {
            Expr::apps(
                rat_sub.clone(),
                [rat_one.clone(), Expr::app(flip_sign.clone(), bb)],
            )
        };
        let rhs = |bb: Expr| {
            Expr::apps(
                rat_mul.clone(),
                [rat_two.clone(), Expr::app(ind.clone(), bb)],
            )
        };
        let eqn = |l: Expr, r: Expr| Expr::apps(eq_rat_c.clone(), [rat.clone(), l, r]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            let concl = eqn(lhs(bv.clone()), rhs(bv.clone()));
            b.finish(b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (bp_id, bp) = m.fresh_local(bool_c.clone());
                let body = eqn(lhs(bp.clone()), rhs(bp.clone()));
                m.finish_child(m.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
            };
            let leaf = |bv: Expr| Expr::apps(eq_refl.clone(), [rat.clone(), lhs(bv)]);
            let f_case = leaf(bfalse.clone());
            let t_case = leaf(btrue.clone());
            let rec = Expr::apps(bool_rec0.clone(), [motive, f_case, t_case, bv.clone()]);
            b.finish(b.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec))
        };

        // Re-entrancy guard: `init_boolean_analysis` may register this name.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.beq_eq_false_of_ne : ∀ (a b : Nat), (a = b → False) → Nat.beq a b = false`
    ///
    /// The contrapositive of `Nat.eq_of_beq_eq_true`. "Remember the discriminant"
    /// `Bool.rec` on `Nat.beq a b` with motive
    /// `fun z => (Nat.beq a b = z) → (Nat.beq a b = false)`, applied to
    /// `Eq.refl (Nat.beq a b)`:
    ///   * `z = false`: `fun h => h`.
    ///   * `z = true`: `fun h => False.elim (hne (Nat.eq_of_beq_eq_true a b h))`.
    ///
    /// Axiom-free.
    pub(crate) fn register_nat_beq_eq_false_of_ne(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.beq_eq_false_of_ne");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_nat_cmp()?; // Nat.beq
        self.register_nat_eq_of_beq_eq_true()?;

        let one = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let eq_bool_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_nat_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let eq_of_beq = Expr::const_(Name::from_string("Nat.eq_of_beq_eq_true"), vec![]);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
        // Bool.rec at the Prop motive level (the goal is an Eq : Prop).
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        let beq = |a: Expr, b: Expr| Expr::apps(nat_beq.clone(), [a, b]);
        let eq_bool = |l: Expr, r: Expr| Expr::apps(eq_bool_c.clone(), [bool_c.clone(), l, r]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eq_nat_c.clone(), [nat.clone(), l, r]);
        let ne_ty = |a: Expr, b: Expr| Expr::pi(BinderInfo::Default, eq_nat(a, b), false_c.clone());

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());
            let hne = ne_ty(a.clone(), bv.clone());
            let (h_id, _h) = b.fresh_local(hne.clone());
            let concl = eq_bool(beq(a.clone(), bv.clone()), bfalse.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hne, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());
            let hne = ne_ty(a.clone(), bv.clone());
            let (h_id, hh) = b.fresh_local(hne.clone());
            let g = beq(a.clone(), bv.clone());

            // motive P : fun (z : Bool) => (Nat.beq a b = z) → (Nat.beq a b = false)
            let p_motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = m.fresh_local(bool_c.clone());
                let prem = eq_bool(g.clone(), z.clone());
                let concl = eq_bool(g.clone(), bfalse.clone());
                let body = Expr::arrow(prem, concl);
                m.finish_child(m.mk_lam(z_id, BinderInfo::Default, bool_c.clone(), body))
            };
            // false case: fun (h : g = false) => h
            let false_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let prem = eq_bool(g.clone(), bfalse.clone());
                let (hf_id, hf) = d.fresh_local(prem.clone());
                d.finish_child(d.mk_lam(hf_id, BinderInfo::Default, prem, hf))
            };
            // true case: fun (h : g = true) =>
            //   False.elim (hne (Nat.eq_of_beq_eq_true a b h))
            let true_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let prem = eq_bool(g.clone(), btrue.clone());
                let (ht_id, ht) = d.fresh_local(prem.clone());
                let ab_eq = Expr::apps(eq_of_beq.clone(), [a.clone(), bv.clone(), ht]);
                let absurd = Expr::app(hh.clone(), ab_eq);
                let goal = eq_bool(g.clone(), bfalse.clone());
                let body = Expr::apps(false_elim.clone(), [goal, absurd]);
                d.finish_child(d.mk_lam(ht_id, BinderInfo::Default, prem, body))
            };
            let rec = Expr::apps(
                bool_rec0.clone(),
                [p_motive, false_case, true_case, g.clone()],
            );
            // apply to Eq.refl Bool g
            let refl_g = Expr::apps(eq_refl.clone(), [bool_c.clone(), g.clone()]);
            let proof = Expr::app(rec, refl_g);

            let e = b.mk_lam(h_id, BinderInfo::Default, hne, proof);
            let e = b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e))
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.chi_factor_neg : ∀ (sb xb : Bool),
    ///   factor sb (Bool.not xb) = Rat.mul (factor sb xb) (flipSign sb)`
    ///
    /// where `factor sb xb = @Bool.rec (fun _ => Rat) Rat.one (1 - 2·⟦xb⟧) sb` is
    /// the per-coordinate `chi` factor (byte-for-byte `register_chi`'s inner
    /// lambda). The multiplicative heart of `chi_flip_spectral`: negating the bit
    /// at a coordinate multiplies that coordinate's chi factor by `flipSign sb`
    /// (`-1` if the coordinate is in `S`, else `1`). `Bool.rec` on `sb` then `xb`
    /// — all four leaves are ground Rat-numeral identities closed by `Eq.refl`.
    pub(crate) fn register_chi_factor_neg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_factor_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_flip_sign()?;

        let one = Level::succ(Level::zero());
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let flip_sign = Expr::const_(Name::from_string("BoolAnalysis.flipSign"), vec![]);
        let eq_rat_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let bool_rec1 = Expr::const_(Name::from_string("Bool.rec"), vec![one.clone()]);
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        // `2 : Rat` = Rat.mk (Int.ofNat 2) 1
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let nat_two = Expr::app(nat_succ.clone(), nat_one.clone());
        let rat_two = Expr::apps(
            rat_mk.clone(),
            [Expr::app(int_of_nat.clone(), nat_two), nat_one.clone()],
        );
        // `fun (_ : Bool) => Rat`
        let bool_to_rat = || Expr::lam(BinderInfo::Default, bool_c.clone(), rat.clone());

        // factor(sb, xb) = @Bool.rec (fun _ => Rat) 1 (1 - 2·⟦xb⟧) sb
        let factor = |sb: Expr, xb: Expr| {
            let embed = Expr::apps(
                bool_rec1.clone(),
                [bool_to_rat(), rat_zero.clone(), rat_one.clone(), xb],
            );
            let two_embed = Expr::apps(rat_mul.clone(), [rat_two.clone(), embed]);
            let signed = Expr::apps(rat_sub.clone(), [rat_one.clone(), two_embed]);
            Expr::apps(
                bool_rec1.clone(),
                [bool_to_rat(), rat_one.clone(), signed, sb],
            )
        };
        // lhs(sb,xb) = factor sb (Bool.not xb)
        let lhs = |sb: Expr, xb: Expr| factor(sb, Expr::app(bool_not.clone(), xb));
        // rhs(sb,xb) = Rat.mul (factor sb xb) (flipSign sb)
        let rhs = |sb: Expr, xb: Expr| {
            Expr::apps(
                rat_mul.clone(),
                [factor(sb.clone(), xb), Expr::app(flip_sign.clone(), sb)],
            )
        };
        let eqn = |l: Expr, r: Expr| Expr::apps(eq_rat_c.clone(), [rat.clone(), l, r]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(bool_c.clone());
            let (x_id, x) = b.fresh_local(bool_c.clone());
            let concl = eqn(lhs(s.clone(), x.clone()), rhs(s.clone(), x.clone()));
            let e = b.mk_pi(x_id, BinderInfo::Default, bool_c.clone(), concl);
            b.finish(b.mk_pi(s_id, BinderInfo::Default, bool_c.clone(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(bool_c.clone());
            let (x_id, x) = b.fresh_local(bool_c.clone());
            // motive_s : fun (s' : Bool) => lhs s' x = rhs s' x
            let motive_s = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (sp_id, sp) = m.fresh_local(bool_c.clone());
                let body = eqn(lhs(sp.clone(), x.clone()), rhs(sp.clone(), x.clone()));
                m.finish_child(m.mk_lam(sp_id, BinderInfo::Default, bool_c.clone(), body))
            };
            // For a concrete sv: split on x, Eq.refl leaves.
            let inner = |sv: Expr, parent: &EnvDeclBuilder| {
                let mut d = EnvDeclBuilder::child_of(parent);
                let motive_x = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (xp_id, xp) = e.fresh_local(bool_c.clone());
                    let body = eqn(lhs(sv.clone(), xp.clone()), rhs(sv.clone(), xp.clone()));
                    e.finish_child(e.mk_lam(xp_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let leaf =
                    |xv: Expr| Expr::apps(eq_refl.clone(), [rat.clone(), lhs(sv.clone(), xv)]);
                let x_false = leaf(bfalse.clone());
                let x_true = leaf(btrue.clone());
                let e = Expr::apps(bool_rec0.clone(), [motive_x, x_false, x_true, x.clone()]);
                d.finish_child(e)
            };
            let s_false = inner(bfalse.clone(), &b);
            let s_true = inner(btrue.clone(), &b);
            let rec_s = Expr::apps(bool_rec0.clone(), [motive_s, s_false, s_true, s.clone()]);
            let e = b.mk_lam(x_id, BinderInfo::Default, bool_c.clone(), rec_s);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, bool_c.clone(), e))
        };

        // Re-entrancy guard: `init_boolean_analysis` may register this name.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.chi_flip_factor : ∀ (n)(S x : HCPoint n)(i j : Fin n),
    ///   @Eq Rat
    ///     (factor (S j) ((hcFlip n x i) j))
    ///     (Rat.mul (factor (S j) (x j))
    ///              (@ite Rat (@Eq (Fin n) j i) (instDecidableEqFin n j i)
    ///                        (flipSign (S i)) Rat.one))`
    ///
    /// The per-coordinate chi-factor action of an `i`-flip: at the flipped
    /// coordinate (`j = i`) the factor picks up `flipSign (S i)`, elsewhere it is
    /// unchanged. `Decidable.rec` on `instDecidableEqFin n j i`:
    ///   * isTrue `heq : j = i`: `ite ↦ flipSign (S i)` (`if_pos`); transport the
    ///     `M i` instance (where `(hcFlip n x i) i ≡ ¬(x i)` since the gate
    ///     `Nat.beq (val i)(val i)` reduces to `true` after `Nat.beq_refl`) back
    ///     to `M j` along `heq.symm`; `M i` is `chi_factor_neg (S i)(x i)`.
    ///   * isFalse `hne`: `ite ↦ 1` (`if_neg`); the gate `Nat.beq (val j)(val i)`
    ///     is `false` (`Nat.beq_eq_false_of_ne` ∘ `Fin.eq_of_val_eq`), so
    ///     `(hcFlip n x i) j ≡ x j` and the goal is `Rat.mul_one`-symm.
    ///
    /// Axiom-free.
    pub(crate) fn register_chi_flip_factor(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_flip_factor");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat_cmp()?;
        self.init_ite()?;
        self.init_decidable_eq()?;
        self.register_fin_dec_eq_proof()?;
        self.register_ite_pos_neg_lemmas()?;
        self.register_nat_beq_lemmas()?; // Nat.beq_refl
        self.register_nat_beq_eq_false_of_ne()?;
        self.register_flip_sign()?;
        self.register_chi_factor_neg()?;

        let l0 = Level::zero();
        let one = Level::succ(l0.clone());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let rat_mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let nat_beq_refl = Expr::const_(Name::from_string("Nat.beq_refl"), vec![]);
        let nat_beq_false = Expr::const_(Name::from_string("Nat.beq_eq_false_of_ne"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_eq_of_val = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
        let hc_flip = Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]);
        let flip_sign = Expr::const_(Name::from_string("BoolAnalysis.flipSign"), vec![]);
        let chi_factor_neg = Expr::const_(Name::from_string("BoolAnalysis.chi_factor_neg"), vec![]);
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let inst_dec = Expr::const_(Name::from_string("instDecidableEqFin"), vec![]);
        let ite = Expr::const_(Name::from_string("ite"), vec![one.clone()]);
        let if_pos = Expr::const_(Name::from_string("if_pos"), vec![one.clone()]);
        let if_neg = Expr::const_(Name::from_string("if_neg"), vec![one.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![l0.clone()]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]);
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]);
        let eq_ndrec = Expr::const_(Name::from_string("Eq.ndrec"), vec![l0.clone(), one.clone()]);
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![one.clone(), one.clone()],
        );
        let bool_rec1 = Expr::const_(Name::from_string("Bool.rec"), vec![one.clone()]);

        // `2 : Rat`
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let nat_two = Expr::app(nat_succ.clone(), nat_one.clone());
        let rat_two = Expr::apps(
            rat_mk.clone(),
            [Expr::app(int_of_nat.clone(), nat_two), nat_one.clone()],
        );
        let bool_to_rat = || Expr::lam(BinderInfo::Default, bool_c.clone(), rat.clone());
        let bool_to_bool = || Expr::lam(BinderInfo::Default, bool_c.clone(), bool_c.clone());

        let fin_n = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let hcp = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
        let val = |n: &Expr, j: &Expr| Expr::apps(fin_val.clone(), [n.clone(), j.clone()]);
        let beq = |a: Expr, b: Expr| Expr::apps(nat_beq.clone(), [a, b]);
        let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [rat.clone(), l, r]);
        let eq_bool = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [bool_c.clone(), l, r]);
        let eq_fin = |n: &Expr, l: Expr, r: Expr| Expr::apps(eq1.clone(), [fin_n(n), l, r]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [nat.clone(), l, r]);
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        // factor(sb, xb)
        let factor = |sb: Expr, xb: Expr| {
            let embed = Expr::apps(
                bool_rec1.clone(),
                [bool_to_rat(), rat_zero.clone(), rat_one.clone(), xb],
            );
            let two_embed = mul(rat_two.clone(), embed);
            let signed = Expr::apps(rat_sub.clone(), [rat_one.clone(), two_embed]);
            Expr::apps(
                bool_rec1.clone(),
                [bool_to_rat(), rat_one.clone(), signed, sb],
            )
        };
        // the hcFlip gate for coordinate j: @Bool.rec (fun _ => Bool)(x j)(¬(x j)) g
        let flip_bit = |xj: Expr, g: Expr| {
            Expr::apps(
                bool_rec1.clone(),
                [
                    bool_to_bool(),
                    xj.clone(),
                    Expr::app(bool_not.clone(), xj),
                    g,
                ],
            )
        };
        // instDecidableEqFin n j i
        let inst = |n: &Expr, j: &Expr, i: &Expr| {
            Expr::apps(inst_dec.clone(), [n.clone(), j.clone(), i.clone()])
        };
        // @ite Rat (Eq (Fin n) j i) (inst n j i) c 1
        let kron_ite = |n: &Expr, j: &Expr, i: &Expr, c: Expr| {
            Expr::apps(
                ite.clone(),
                [
                    rat.clone(),
                    eq_fin(n, j.clone(), i.clone()),
                    inst(n, j, i),
                    c,
                    rat_one.clone(),
                ],
            )
        };

        // ── Type ──
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (s_id, s) = b.fresh_local(hcp(&n));
            let (x_id, x) = b.fresh_local(hcp(&n));
            let (i_id, i) = b.fresh_local(fin_n(&n));
            let (j_id, j) = b.fresh_local(fin_n(&n));
            let s_j = Expr::app(s.clone(), j.clone());
            let x_j = Expr::app(x.clone(), j.clone());
            let flip_j = Expr::app(
                Expr::apps(hc_flip.clone(), [n.clone(), x.clone(), i.clone()]),
                j.clone(),
            );
            let lhs = factor(s_j.clone(), flip_j);
            let sgn = kron_ite(
                &n,
                &j,
                &i,
                Expr::app(flip_sign.clone(), Expr::app(s.clone(), i.clone())),
            );
            let rhs = mul(factor(s_j, x_j), sgn);
            let concl = eq_rat(lhs, rhs);
            let e = b.mk_pi(j_id, BinderInfo::Default, fin_n(&n), concl);
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_n(&n), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, hcp(&n), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp(&n), e);
            b.finish(b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e))
        };

        // ── Value ──
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (s_id, s) = b.fresh_local(hcp(&n));
            let (x_id, x) = b.fresh_local(hcp(&n));
            let (i_id, i) = b.fresh_local(fin_n(&n));
            let (j_id, j) = b.fresh_local(fin_n(&n));

            let s_i = Expr::app(s.clone(), i.clone());
            let s_j = Expr::app(s.clone(), j.clone());
            let x_i = Expr::app(x.clone(), i.clone());
            let x_j = Expr::app(x.clone(), j.clone());
            let flip_app = |w: &Expr| {
                Expr::app(
                    Expr::apps(hc_flip.clone(), [n.clone(), x.clone(), i.clone()]),
                    w.clone(),
                )
            };
            let flip_sign_si = Expr::app(flip_sign.clone(), s_i.clone());
            let cond = eq_fin(&n, j.clone(), i.clone());
            let inst_ji = inst(&n, &j, &i);

            // M w := @Eq Rat (factor (S w) ((hcFlip n x i) w))
            //                (Rat.mul (factor (S w) (x w)) (flipSign (S i)))
            // (the goal with the ite already replaced by flipSign(S i); used only
            //  in the isTrue branch via transport along heq.)
            let m_at = |w: &Expr| {
                let s_w = Expr::app(s.clone(), w.clone());
                let x_w = Expr::app(x.clone(), w.clone());
                let lhs = factor(s_w.clone(), flip_app(w));
                let rhs = mul(factor(s_w, x_w), flip_sign_si.clone());
                eq_rat(lhs, rhs)
            };

            // dmotive : (d : Decidable cond) → Prop
            //   := fun d => factor (S j)((hcFlip..) j)
            //              = Rat.mul (factor (S j)(x j)) (@ite Rat cond d (flipSign(S i)) 1)
            let dmotive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let dec_c = Expr::app(dec.clone(), cond.clone());
                let (dd_id, dd) = d.fresh_local(dec_c.clone());
                let ite_d = Expr::apps(
                    ite.clone(),
                    [
                        rat.clone(),
                        cond.clone(),
                        dd,
                        flip_sign_si.clone(),
                        rat_one.clone(),
                    ],
                );
                let lhs = factor(s_j.clone(), flip_app(&j));
                let rhs = mul(factor(s_j.clone(), x_j.clone()), ite_d);
                let body = eq_rat(lhs, rhs);
                d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_c, body))
            };

            // ── isFalse minor: fun (hne : cond → False) => proof : LHS = RHS_with_1 ──
            // RHS_with_1 = Rat.mul (factor (S j)(x j)) (@ite Rat cond (isFalse hne) .. 1)
            //   if_neg collapses ite to 1; goal reduces (def-eq) to
            //   factor(S j)((hcFlip) j) = Rat.mul (factor(S j)(x j)) 1.
            // (hcFlip) j = flip_bit (x j) (Nat.beq (val j)(val i)); beq = false ⇒ = x j.
            let false_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let not_c = Expr::pi(BinderInfo::Default, cond.clone(), false_c.clone());
                let (hne_id, hne) = d.fresh_local(not_c.clone());

                // hne_val : (val j = val i) → False := fun (e) => hne (Fin.eq_of_val_eq n j i e)
                let hne_val = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let prem = eq_nat(val(&n, &j), val(&n, &i));
                    let (e_id, e) = g.fresh_local(prem.clone());
                    let lifted =
                        Expr::apps(fin_eq_of_val.clone(), [n.clone(), j.clone(), i.clone(), e]);
                    let body = Expr::app(hne.clone(), lifted);
                    g.finish_child(g.mk_lam(e_id, BinderInfo::Default, prem, body))
                };
                // hbeq : Nat.beq (val j)(val i) = false
                let hbeq = Expr::apps(nat_beq_false.clone(), [val(&n, &j), val(&n, &i), hne_val]);
                // flip_j_eq_xj : (hcFlip) j = x j
                //   congrArg (fun g => @Bool.rec (fun _ => Bool)(x j)(¬(x j)) g) hbeq
                //   : flip_bit (x j) (Nat.beq..) = flip_bit (x j) false   (≡ x j)
                let bit_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (gg_id, gg) = g.fresh_local(bool_c.clone());
                    let body = flip_bit(x_j.clone(), gg);
                    g.finish_child(g.mk_lam(gg_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let flip_j_eq_xj = Expr::apps(
                    congr_arg.clone(),
                    [
                        bool_c.clone(),
                        bool_c.clone(),
                        beq(val(&n, &j), val(&n, &i)),
                        bfalse.clone(),
                        bit_fn,
                        hbeq,
                    ],
                );
                // factor congr: factor (S j)((hcFlip) j) = factor (S j)(x j)
                //   congrArg (fun (y:Bool) => factor (S j) y) flip_j_eq_xj
                let factor_fn = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = g.fresh_local(bool_c.clone());
                    let body = factor(s_j.clone(), y);
                    g.finish_child(g.mk_lam(y_id, BinderInfo::Default, bool_c.clone(), body))
                };
                // The hcFlip-applied bit, in explicit Bool.rec form, for congr endpoints.
                let flip_bit_j = flip_bit(x_j.clone(), beq(val(&n, &j), val(&n, &i)));
                let hfac = Expr::apps(
                    congr_arg.clone(),
                    [
                        bool_c.clone(),
                        rat.clone(),
                        flip_bit_j.clone(),
                        x_j.clone(),
                        factor_fn,
                        flip_j_eq_xj,
                    ],
                );
                // h_one : Rat.mul (factor(S j)(x j)) 1 = factor (S j)(x j)
                //   Rat.mul_one (factor (S j)(x j))
                let fac_xj = factor(s_j.clone(), x_j.clone());
                let h_one = Expr::app(rat_mul_one.clone(), fac_xj.clone());
                // Need : factor(S j)((hcFlip) j) = Rat.mul (factor(S j)(x j)) 1
                //   = Eq.trans hfac (Eq.symm h_one)
                let h_one_symm = Expr::apps(
                    eq_symm.clone(),
                    [
                        rat.clone(),
                        mul(fac_xj.clone(), rat_one.clone()),
                        fac_xj.clone(),
                        h_one,
                    ],
                );
                // factor(S j)((hcFlip) j) — LHS, in Bool.rec form for the trans endpoints
                let lhs_fac = factor(s_j.clone(), flip_bit_j);
                let core = Expr::apps(
                    eq_trans.clone(),
                    [
                        rat.clone(),
                        lhs_fac.clone(),
                        fac_xj.clone(),
                        mul(fac_xj.clone(), rat_one.clone()),
                        hfac,
                        h_one_symm,
                    ],
                );
                d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_c, core))
            };

            // ── isTrue minor: fun (heq : cond) => proof ──
            // goal: factor(S j)((hcFlip) j) = Rat.mul (factor(S j)(x j)) (ite cond (isTrue heq) (flipSign(S i)) 1)
            //   if_pos ⇒ ite = flipSign(S i); so goal def-eq to M j.
            //   M j obtained from M i by Eq.ndrec transport along heq : j = i.
            let true_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (heq_id, heq) = d.fresh_local(cond.clone());

                // M i, where (hcFlip n x i) i ≡ flip_bit (x i)(Nat.beq (val i)(val i))
                //   and Nat.beq (val i)(val i) = true (Nat.beq_refl), so it reduces to ¬(x i).
                // hbeq_ii : Nat.beq (val i)(val i) = true
                let hbeq_ii = Expr::app(nat_beq_refl.clone(), val(&n, &i));
                // flip_i_eq_noti : (hcFlip) i = ¬(x i)
                //   congrArg (fun g => flip_bit (x i) g) hbeq_ii
                let bit_fn_i = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (gg_id, gg) = g.fresh_local(bool_c.clone());
                    let body = flip_bit(x_i.clone(), gg);
                    g.finish_child(g.mk_lam(gg_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let flip_bit_i = flip_bit(x_i.clone(), beq(val(&n, &i), val(&n, &i)));
                let not_xi = Expr::app(bool_not.clone(), x_i.clone());
                let flip_i_eq_noti = Expr::apps(
                    congr_arg.clone(),
                    [
                        bool_c.clone(),
                        bool_c.clone(),
                        beq(val(&n, &i), val(&n, &i)),
                        btrue.clone(),
                        bit_fn_i,
                        hbeq_ii,
                    ],
                );
                // factor congr to LHS of M i:
                //   factor (S i)((hcFlip) i) = factor (S i)(¬(x i))
                let factor_fn_i = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = g.fresh_local(bool_c.clone());
                    let body = factor(s_i.clone(), y);
                    g.finish_child(g.mk_lam(y_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let hfac_i = Expr::apps(
                    congr_arg.clone(),
                    [
                        bool_c.clone(),
                        rat.clone(),
                        flip_bit_i.clone(),
                        not_xi.clone(),
                        factor_fn_i,
                        flip_i_eq_noti,
                    ],
                );
                // chi_factor_neg (S i)(x i) : factor (S i)(¬(x i)) = Rat.mul (factor (S i)(x i)) (flipSign (S i))
                let cfn_i = Expr::apps(chi_factor_neg.clone(), [s_i.clone(), x_i.clone()]);
                // m_i : factor (S i)((hcFlip) i) = Rat.mul (factor (S i)(x i)) (flipSign (S i))
                //   = Eq.trans hfac_i cfn_i
                let lhs_mi = factor(s_i.clone(), flip_bit_i);
                let fac_notxi = factor(s_i.clone(), not_xi.clone());
                let rhs_mi = mul(factor(s_i.clone(), x_i.clone()), flip_sign_si.clone());
                let m_i = Expr::apps(
                    eq_trans.clone(),
                    [rat.clone(), lhs_mi, fac_notxi, rhs_mi, hfac_i, cfn_i],
                );

                // Transport M i to M j along heq.symm : i = j.
                //   @Eq.ndrec (Fin n) i (fun w => M w) m_i j (Eq.symm heq)
                let m_motive = {
                    let mut g = EnvDeclBuilder::child_of(&d);
                    let (w_id, w) = g.fresh_local(fin_n(&n));
                    let body = m_at(&w);
                    g.finish_child(g.mk_lam(w_id, BinderInfo::Default, fin_n(&n), body))
                };
                let heq_symm = Expr::apps(
                    eq_symm.clone(),
                    [fin_n(&n), j.clone(), i.clone(), heq.clone()],
                );
                // @Eq.ndrec {A} {a} {motive} (h_a) {b} (heq_ab) : motive b
                // Eq.ndrec.{l0,1} : {A : Sort 1} {a : A} {motive : A → Sort l0}
                //   → motive a → {b : A} → a = b → motive b
                let m_j = Expr::apps(
                    eq_ndrec.clone(),
                    [
                        fin_n(&n), // A
                        i.clone(), // a
                        m_motive,  // motive
                        m_i,       // motive a
                        j.clone(), // b
                        heq_symm,  // a = b  (i = j)
                    ],
                );
                d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, cond.clone(), m_j))
            };

            // @Decidable.rec.{0} cond dmotive false_minor true_minor (inst n j i)
            //   : dmotive (inst n j i) = goal.
            let rec_app = Expr::apps(
                dec_rec.clone(),
                [cond.clone(), dmotive, false_minor, true_minor, inst_ji],
            );

            let e = b.mk_lam(j_id, BinderInfo::Default, fin_n(&n), rec_app);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n(&n), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, hcp(&n), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp(&n), e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e))
        };

        // Re-entrancy guard: `init_boolean_analysis` may register this name.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.chi_flip_spectral : ∀ (n)(S x : HCPoint n)(i : Fin n),
    ///   @Eq Rat (chi n S (hcFlip n x i)) (Rat.mul (flipSign (S i)) (chi n S x))`
    ///
    /// The spectral action of a coordinate flip. `chi n S (hcFlip n x i)` δ-unfolds
    /// to `Fin.prod n (factor_fn S (hcFlip n x i))`; `Fin.prod_congr` +
    /// `chi_flip_factor` rewrites the integrand to `factor_fn S x j · sgn j` with
    /// `sgn j = ite (j = i) (flipSign (S i)) 1`; `Fin.prod_mul` splits the product
    /// into `(Fin.prod n (factor_fn S x)) · (Fin.prod n sgn)`; the first factor is
    /// `chi n S x` (def-eq) and the second collapses to `flipSign (S i)` by
    /// `Fin.prod_single` (Step 1); `Rat.mul_comm` reorders to the stated form.
    /// Axiom-free.
    pub(crate) fn register_chi_flip_spectral(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_flip_spectral");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_nat_cmp()?;
        self.init_ite()?;
        self.init_decidable_eq()?;
        self.init_fin_sum()?; // Fin.isLt etc.
        self.register_fin_dec_eq_proof()?;
        self.register_fin_prod_mul_theorem()?;
        self.register_fin_prod_one_theorems()?; // Fin.prod_congr
        self.register_flip_sign()?;
        self.register_chi_flip_factor()?;
        {
            let c = super::nn_verify_fin_sum::FinSumConsts::new();
            self.register_fin_prod_single_theorem(&c)?;
        }
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm

        let l0 = Level::zero();
        let one = Level::succ(l0.clone());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let rat_mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let fin_prod = Expr::const_(Name::from_string("Fin.prod"), vec![]);
        let fin_prod_mul = Expr::const_(Name::from_string("Fin.prod_mul"), vec![]);
        let fin_prod_congr = Expr::const_(Name::from_string("Fin.prod_congr"), vec![]);
        let fin_prod_single = Expr::const_(Name::from_string("Fin.prod_single"), vec![]);
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
        let hc_flip = Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]);
        let chi = Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]);
        let flip_sign = Expr::const_(Name::from_string("BoolAnalysis.flipSign"), vec![]);
        let chi_flip_factor =
            Expr::const_(Name::from_string("BoolAnalysis.chi_flip_factor"), vec![]);
        let bool_rec1 = Expr::const_(Name::from_string("Bool.rec"), vec![one.clone()]);
        let inst_dec = Expr::const_(Name::from_string("instDecidableEqFin"), vec![]);
        let ite = Expr::const_(Name::from_string("ite"), vec![one.clone()]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]);

        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let nat_two = Expr::app(nat_succ.clone(), nat_one.clone());
        let rat_two = Expr::apps(
            rat_mk.clone(),
            [Expr::app(int_of_nat.clone(), nat_two), nat_one.clone()],
        );
        let bool_to_rat = || Expr::lam(BinderInfo::Default, bool_c.clone(), rat.clone());
        let fin_n = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let hcp = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
        let val = |n: &Expr, j: &Expr| Expr::apps(fin_val.clone(), [n.clone(), j.clone()]);
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let prod = |n: &Expr, g: Expr| Expr::apps(fin_prod.clone(), [n.clone(), g]);
        let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [rat.clone(), l, r]);
        let eq_fin = |n: &Expr, l: Expr, r: Expr| Expr::apps(eq1.clone(), [fin_n(n), l, r]);
        let factor = |sb: Expr, xb: Expr| {
            let embed = Expr::apps(
                bool_rec1.clone(),
                [bool_to_rat(), rat_zero.clone(), rat_one.clone(), xb],
            );
            let two_embed = mul(rat_two.clone(), embed);
            let signed = Expr::apps(rat_sub.clone(), [rat_one.clone(), two_embed]);
            Expr::apps(
                bool_rec1.clone(),
                [bool_to_rat(), rat_one.clone(), signed, sb],
            )
        };
        // chi integrand: fun (j : Fin n) => factor (S j) (p j)
        let factor_fn = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr, p: Expr| -> Expr {
            let mut g = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = g.fresh_local(fin_n(n));
            let s_j = Expr::app(s.clone(), j.clone());
            let p_j = Expr::app(p.clone(), j.clone());
            g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(n), factor(s_j, p_j)))
        };
        // sgn function: fun (j : Fin n) => @ite Rat (Eq (Fin n) j i)(inst n j i)(flipSign(S i)) 1
        let sgn_fn = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr, i: &Expr| -> Expr {
            let mut g = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = g.fresh_local(fin_n(n));
            let s_i = Expr::app(s.clone(), i.clone());
            let body = Expr::apps(
                ite.clone(),
                [
                    rat.clone(),
                    eq_fin(n, j.clone(), i.clone()),
                    Expr::apps(inst_dec.clone(), [n.clone(), j.clone(), i.clone()]),
                    Expr::app(flip_sign.clone(), s_i),
                    rat_one.clone(),
                ],
            );
            g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(n), body))
        };
        // congr target integrand: fun (j : Fin n) => Rat.mul (factor (S j)(x j)) (sgn j)
        let mixed_fn = |parent: &EnvDeclBuilder, n: &Expr, s: &Expr, x: &Expr, i: &Expr| -> Expr {
            let mut g = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = g.fresh_local(fin_n(n));
            let s_j = Expr::app(s.clone(), j.clone());
            let x_j = Expr::app(x.clone(), j.clone());
            let s_i = Expr::app(s.clone(), i.clone());
            let sgn = Expr::apps(
                ite.clone(),
                [
                    rat.clone(),
                    eq_fin(n, j.clone(), i.clone()),
                    Expr::apps(inst_dec.clone(), [n.clone(), j.clone(), i.clone()]),
                    Expr::app(flip_sign.clone(), s_i),
                    rat_one.clone(),
                ],
            );
            let body = mul(factor(s_j, x_j), sgn);
            g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(n), body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (s_id, s) = b.fresh_local(hcp(&n));
            let (x_id, x) = b.fresh_local(hcp(&n));
            let (i_id, i) = b.fresh_local(fin_n(&n));
            let flipped = Expr::apps(hc_flip.clone(), [n.clone(), x.clone(), i.clone()]);
            let lhs = Expr::apps(chi.clone(), [n.clone(), s.clone(), flipped]);
            let s_i = Expr::app(s.clone(), i.clone());
            let chi_sx = Expr::apps(chi.clone(), [n.clone(), s.clone(), x.clone()]);
            let rhs = mul(Expr::app(flip_sign.clone(), s_i), chi_sx);
            let concl = eq_rat(lhs, rhs);
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_n(&n), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, hcp(&n), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp(&n), e);
            b.finish(b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (s_id, s) = b.fresh_local(hcp(&n));
            let (x_id, x) = b.fresh_local(hcp(&n));
            let (i_id, i) = b.fresh_local(fin_n(&n));
            let flipped = Expr::apps(hc_flip.clone(), [n.clone(), x.clone(), i.clone()]);
            let s_i = Expr::app(s.clone(), i.clone());
            let flip_sign_si = Expr::app(flip_sign.clone(), s_i.clone());

            // integrands
            let ff_flip = factor_fn(&b, &n, &s, flipped.clone()); // chi n S (hcFlip) integrand
            let ff_x = factor_fn(&b, &n, &s, x.clone()); // chi n S x integrand
            let sgn = sgn_fn(&b, &n, &s, &i);
            let mixed = mixed_fn(&b, &n, &s, &x, &i);

            // H : ∀ j, ff_flip j = mixed j  := fun j => chi_flip_factor n S x i j
            let h_pointwise = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (j_id, j) = g.fresh_local(fin_n(&n));
                let body = Expr::apps(
                    chi_flip_factor.clone(),
                    [n.clone(), s.clone(), x.clone(), i.clone(), j.clone()],
                );
                g.finish_child(g.mk_lam(j_id, BinderInfo::Default, fin_n(&n), body))
            };
            // step1 : Fin.prod n ff_flip = Fin.prod n mixed
            let step1 = Expr::apps(
                fin_prod_congr.clone(),
                [n.clone(), ff_flip.clone(), mixed.clone(), h_pointwise],
            );
            // step2 : Fin.prod n mixed = Rat.mul (Fin.prod n ff_x) (Fin.prod n sgn)
            //   Fin.prod_mul n ff_x sgn  (mixed ≡ fun j => Rat.mul (ff_x j)(sgn j))
            let step2 = Expr::apps(fin_prod_mul.clone(), [n.clone(), ff_x.clone(), sgn.clone()]);
            // step3 : Fin.prod n sgn = flipSign (S i)
            //   Fin.prod_single n i (flipSign (S i)) (Fin.isLt n i)
            let islt = Expr::apps(fin_islt.clone(), [n.clone(), i.clone()]);
            let step3 = Expr::apps(
                fin_prod_single.clone(),
                [n.clone(), i.clone(), flip_sign_si.clone(), islt],
            );
            // congrArg (fun z => Rat.mul (Fin.prod n ff_x) z) step3
            //   : Rat.mul (Fin.prod n ff_x)(Fin.prod n sgn) = Rat.mul (Fin.prod n ff_x)(flipSign(S i))
            let prod_ffx = prod(&n, ff_x.clone());
            let prod_sgn = prod(&n, sgn.clone());
            let mul_left_fn = {
                let mut g = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = g.fresh_local(rat.clone());
                let body = mul(prod_ffx.clone(), z);
                g.finish_child(g.mk_lam(z_id, BinderInfo::Default, rat.clone(), body))
            };
            let congr_arg = Expr::const_(
                Name::from_string("congrArg"),
                vec![one.clone(), one.clone()],
            );
            let step4 = Expr::apps(
                congr_arg.clone(),
                [
                    rat.clone(),
                    rat.clone(),
                    prod_sgn.clone(),
                    flip_sign_si.clone(),
                    mul_left_fn,
                    step3,
                ],
            );
            // step5 : Rat.mul (Fin.prod n ff_x)(flipSign(S i)) = Rat.mul (flipSign(S i))(Fin.prod n ff_x)
            //   Rat.mul_comm (Fin.prod n ff_x)(flipSign(S i))
            let step5 = Expr::apps(
                rat_mul_comm.clone(),
                [prod_ffx.clone(), flip_sign_si.clone()],
            );

            // Chain everything. Endpoints:
            //   A = Fin.prod n ff_flip        (≡ chi n S (hcFlip n x i))
            //   B = Fin.prod n mixed
            //   C = Rat.mul (Fin.prod n ff_x)(Fin.prod n sgn)
            //   D = Rat.mul (Fin.prod n ff_x)(flipSign(S i))
            //   E = Rat.mul (flipSign(S i))(Fin.prod n ff_x)   (≡ rhs, since Fin.prod n ff_x ≡ chi n S x)
            let a = prod(&n, ff_flip.clone());
            let bb = prod(&n, mixed.clone());
            let cc = mul(prod_ffx.clone(), prod_sgn.clone());
            let dd = mul(prod_ffx.clone(), flip_sign_si.clone());
            let ee = mul(flip_sign_si.clone(), prod_ffx.clone());
            let trans = |x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr| {
                Expr::apps(eq_trans.clone(), [rat.clone(), x, y, z, h1, h2])
            };
            // A=B, B=C, C=D, D=E
            let ab_c = trans(a.clone(), bb.clone(), cc.clone(), step1, step2);
            let ab_cd = trans(a.clone(), cc.clone(), dd.clone(), ab_c, step4);
            let proof = trans(a, dd, ee, ab_cd, step5);

            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n(&n), proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, hcp(&n), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp(&n), e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e))
        };

        // Re-entrancy guard: `init_boolean_analysis` may register this name.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
    use crate::tc::TypeChecker;

    #[test]
    fn test_flip_sign_and_pm_not() {
        let mut env = Environment::new();
        env.register_flip_sign().expect("flipSign");
        env.register_flip_sign().expect("idempotent");
        env.register_pm_not().expect("pm_not");
        env.register_pm_not().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for nm in ["BoolAnalysis.flipSign", "BoolAnalysis.pm_not"] {
            let n = Name::from_string(nm);
            let info = env.get_const(&n).expect("registered");
            tc.check_type(&info.value.clone().expect("val"), &info.type_)
                .unwrap_or_else(|e| panic!("{nm} must type-check: {e:?}"));
        }
        let pm_not = Name::from_string("BoolAnalysis.pm_not");
        assert!(
            env.axiom_deps(&pm_not).expect("deps").is_empty(),
            "pm_not must be axiom-free, got {:?}",
            env.axiom_deps(&pm_not)
        );
    }

    #[test]
    fn test_nat_beq_eq_false_of_ne_axiom_free() {
        let mut env = Environment::new();
        env.register_nat_beq_eq_false_of_ne().expect("beq_false");
        env.register_nat_beq_eq_false_of_ne().expect("idempotent");
        let n = Name::from_string("Nat.beq_eq_false_of_ne");
        let info = env.get_const(&n).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("val"), &info.type_)
            .expect("Nat.beq_eq_false_of_ne must type-check");
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "Nat.beq_eq_false_of_ne must be axiom-free, got {:?}",
            env.axiom_deps(&n)
        );
    }

    #[test]
    fn test_flip_coeff_absorb_axiom_free() {
        let mut env = Environment::new();
        env.register_flip_coeff_absorb().expect("flip_coeff_absorb");
        env.register_flip_coeff_absorb().expect("idempotent");
        let n = Name::from_string("BoolAnalysis.flip_coeff_absorb");
        let info = env.get_const(&n).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("val"), &info.type_)
            .expect("flip_coeff_absorb must type-check");
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "flip_coeff_absorb must be axiom-free, got {:?}",
            env.axiom_deps(&n)
        );
    }

    #[test]
    fn test_chi_flip_spectral_axiom_free() {
        let mut env = Environment::new();
        env.register_chi_flip_spectral().expect("chi_flip_spectral");
        env.register_chi_flip_spectral().expect("idempotent");
        let n = Name::from_string("BoolAnalysis.chi_flip_spectral");
        let info = env.get_const(&n).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("val"), &info.type_)
            .expect("chi_flip_spectral must type-check");
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "chi_flip_spectral must be axiom-free, got {:?}",
            env.axiom_deps(&n)
        );
    }

    #[test]
    fn test_chi_flip_factor_axiom_free() {
        let mut env = Environment::new();
        env.register_chi_flip_factor().expect("chi_flip_factor");
        env.register_chi_flip_factor().expect("idempotent");
        let n = Name::from_string("BoolAnalysis.chi_flip_factor");
        let info = env.get_const(&n).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("val"), &info.type_)
            .expect("chi_flip_factor must type-check");
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "chi_flip_factor must be axiom-free, got {:?}",
            env.axiom_deps(&n)
        );
    }

    #[test]
    fn test_chi_factor_neg_axiom_free() {
        let mut env = Environment::new();
        env.register_chi_factor_neg().expect("chi_factor_neg");
        env.register_chi_factor_neg().expect("idempotent");
        let n = Name::from_string("BoolAnalysis.chi_factor_neg");
        let info = env.get_const(&n).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("val"), &info.type_)
            .expect("chi_factor_neg must type-check");
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "chi_factor_neg must be axiom-free, got {:?}",
            env.axiom_deps(&n)
        );
    }
}
