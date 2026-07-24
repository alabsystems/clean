// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the de-cube keystone `NNReal.le_of_cube_le_cube`
//! (`mul (mul a a) a ≤ mul (mul b b) b → a ≤ b`), plus the two pure-`Rat` bricks
//! it stands on. One cubic degree up from the de-square keystone
//! `NNReal.le_of_sq_le_sq` (`algebra_nnreal_reverse_square_sq.rs`), reusing the
//! landed pure-`Rat` cube lemmas (`Rat.add_cube`, `Rat.le_of_cube_le_cube`,
//! `Rat.cube_lt_cube_of_lt_of_nonneg`).
//!
//! # Why this module exists (the cube-reflects-order brick)
//!
//! The `(4/3,4)` two-point Hölder base raises a `cbrtGen`/`pow43Gen` lower bound
//! to the third power; pushing a value bound THROUGH a cube needs cube
//! monotonicity on `NNReal`. The cleanest reusable form is the REFLECTION
//! `a³ ≤ b³ → a ≤ b` (and, downstream, its forward partner). This module lands
//! the reflection at `NNReal` via the same pointwise CauSeq argument the square
//! keystone uses — NO boundedness, NO limits.
//!
//! # The keystone (fully constructive, boundedness-free, POINTWISE)
//!
//! ```text
//!   NNReal.le_of_cube_le_cube : ∀ a b : NNReal,
//!     NNReal.le (NNReal.mul (NNReal.mul a a) a)(NNReal.mul (NNReal.mul b b) b)
//!       → NNReal.le a b
//! ```
//!
//! At the representative level the CauSeq core is pointwise: given
//! `CauSeq.le (mul (mul f f) f)(mul (mul g g) g)` (i.e. `∀ε∃N∀n≥N,
//! (vf n)³ < (vg n)³ + ε`) and a goal tolerance `ε`, instantiate the hypothesis
//! at `ε³` (`> 0` by two `Rat.mul_pos`); at each `n ≥ N` we have
//! `(vf n)³ < (vg n)³ + ε³`, and since `(vg n)³ + ε³ ≤ (vg n + ε)³`
//! (`Rat.cube_add_le_add_cube`), `(vf n)³ < (vg n + ε)³`, whence
//! `vf n < vg n + ε` (`Rat.lt_of_cube_lt_cube`). The cubed `+ε³` slack is exactly
//! the additive `+ε` slack after the cube root — the cross terms `3y²ε + 3yε²`
//! of `(y+ε)³` are `≥ 0`, so they only widen the bound. The two new `Rat` bricks
//! make this rigorous:
//!
//! - `Rat.cube_add_le_add_cube : ∀ y d, 0≤y → 0≤d →
//!     Rat.le ((y·y)·y + (d·d)·d) (((y+d)·(y+d))·(y+d))`
//!   (`(y+d)³ = (y³+d³) + (3y²d + 3yd²)` via `Rat.add_cube` + a 4-term reassoc,
//!   then `+ nonneg` cross terms).
//! - `Rat.lt_of_cube_lt_cube : ∀ x z, 0≤x → 0≤z → (x·x)·x < (z·z)·z → Rat.lt x z`
//!   (`le_of_cube_le_cube` gives `x ≤ z`; `x = z` forces `x³ = z³`, contradicting
//!   strictness, so `x < z` via the `lt_iff` engine).
//!
//! `NNReal.le_of_cube_le_cube` is the nested `Quot.ind`² lift reducing each leaf
//! to `NNReal.CauSeq.le_of_cube_le_cube`. The CauSeq `seq` of a `mul` is
//! definitionally `NNRat.mul` of the factor `seq`s, and `NNRat.val (NNRat.mul p
//! q) ≡ Rat.mul (val p)(val q)` by `Eq.refl` (the `Subtype.val`/`mk` projection),
//! so `vseq (mul (mul f f) f) m ≡ ((vf m)·(vf m))·(vf m)` definitionally — the
//! cube core consumes the hypothesis at the cube form with no transport.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the de-cube keystone.
/// Self-contained (mirrors `SqConsts` one degree up).
pub(crate) struct CubeReflConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    nnrat_val: Expr,
    nnrat_mul: Expr,
    nnrat_property: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_mul: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // Rat lemmas.
    rat_add_cube: Expr,
    rat_le_of_cube_le_cube: Expr,
    rat_cube_lt_cube: Expr,
    rat_mul_comm: Expr,
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
    rat_le_refl: Expr,
    rat_add_le_add: Expr,
    rat_mul_nonneg: Expr,
    rat_mul_pos: Expr,
    rat_le_add_of_nonneg_right: Expr,
    rat_le_antisymm: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_lt_of_lt_of_le: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    eq_rat: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

impl CubeReflConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            nnrat_val: k("NNRat.val"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_property: k("NNRat.property"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_add_cube: k("Rat.add_cube"),
            rat_le_of_cube_le_cube: k("Rat.le_of_cube_le_cube"),
            rat_cube_lt_cube: k("Rat.cube_lt_cube_of_lt_of_nonneg"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_comm: k("Rat.add_comm"),
            rat_le_refl: k("Rat.le_refl"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_mul_pos: k("Rat.mul_pos"),
            rat_le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            rat_le_antisymm: k("Rat.le_antisymm"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1]),
        }
    }

    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.rle(self.rat_zero.clone(), a)
    }
    /// `(a·a)·a` — the left-nested cube matching `Rat.add_cube`/the NNReal lift.
    fn cube(&self, a: &Expr) -> Expr {
        self.rmul(self.rmul(a.clone(), a.clone()), a.clone())
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_val.clone(), seq)
    }
    fn property_seq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_property.clone(), seq)
    }
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    fn cau_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    /// `NNReal.CauSeq.mul (mul f f) f` — the CauSeq cube.
    fn cau_cube(&self, f: &Expr) -> Expr {
        self.cau_mul(self.cau_mul(f.clone(), f.clone()), f.clone())
    }
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
    }
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, b, ha, hb])
    }
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_pos.clone(), [a, b, ha, hb])
    }
    fn le_add_of_nonneg_right(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_add_of_nonneg_right.clone(), [a, b, h])
    }
    /// `Rat.add_cube a b : ((a+b)·(a+b))·(a+b) = a³ + (3·a²b + (3·ab² + b³))`.
    fn add_cube(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_cube.clone(), [a, b])
    }
    /// `Rat.le_of_cube_le_cube a b (0≤a)(0≤b)(a³≤b³) : a ≤ b`.
    fn le_of_cube_le_cube(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_of_cube_le_cube.clone(), [a, b, ha, hb, h])
    }
    /// `Rat.cube_lt_cube_of_lt_of_nonneg a b (0≤b)(b<a) : b³ < a³`.
    fn cube_lt_cube(&self, a: Expr, b: Expr, hb: Expr, hlt: Expr) -> Expr {
        Expr::apps(self.rat_cube_lt_cube.clone(), [a, b, hb, hlt])
    }
    fn le_antisymm(&self, a: Expr, b: Expr, hab: Expr, hba: Expr) -> Expr {
        Expr::apps(self.rat_le_antisymm.clone(), [a, b, hab, hba])
    }
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, cc, h1, h2])
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `Rat.le a b` from `hlt : Rat.lt a b` via `lt_iff_le_not_le` + `And.left`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.rlt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }
    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, cap) = bn.fresh_local(self.nat.clone());
        let inner = self.pred_n_at(&bn, a, b, eps, &cap);
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    fn pred_n_at(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        eps: &Expr,
        cap: &Expr,
    ) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let hle = self.nat_le(cap.clone(), m.clone());
        let (hle_id, _h) = bn.fresh_local(hle.clone());
        let concl = self.rlt(self.vseq(a, &m), self.radd(self.vseq(b, &m), eps.clone()));
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }
}

impl Environment {
    /// Register the two `Rat` bricks, the `CauSeq` core, and the `NNReal`
    /// de-cube keystone `NNReal.le_of_cube_le_cube`. Idempotent.
    pub fn init_algebra_nnreal_reverse_cube(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul, NNRat.*
        self.init_algebra_nnreal_le()?; // CauSeq.le, NNReal.le
        self.init_algebra_nnreal_nnrat()?; // NNRat.property/mul/val
        self.init_algebra_rat_cube_identity()?; // Rat.add_cube, le_of_cube_le_cube, cube_lt_cube
        self.init_rat_field_inst()?; // add_assoc, add_comm
        self.init_rat_linear_order()?; // le_antisymm, lt_iff_le_not_le
        self.register_rat_order_proofs()?; // Rat.mul_pos, le_refl, mul_nonneg
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_lt_of_le
        self.init_iff()?;
        self.init_and()?;
        self.init_exists()?;

        let c = CubeReflConsts::new();
        self.register_rat_cube_add_le_add_cube(&c)?;
        self.register_rat_lt_of_cube_lt_cube(&c)?;
        self.register_causeq_le_of_cube_le_cube(&c)?;
        self.register_nnreal_le_of_cube_le_cube(&c)?;
        Ok(())
    }

    /// `Rat.cube_add_le_add_cube : ∀ y d, 0≤y → 0≤d →
    ///     Rat.le ((y·y)·y + (d·d)·d) (((y+d)·(y+d))·(y+d))`.
    fn register_rat_cube_add_le_add_cube(&mut self, c: &CubeReflConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cube_add_le_add_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let (d_id, d) = b.fresh_local(c.rat.clone());
            let h0y_ty = c.nonneg(y.clone());
            let (h0y_id, _h) = b.fresh_local(h0y_ty.clone());
            let h0d_ty = c.nonneg(d.clone());
            let (h0d_id, _h2) = b.fresh_local(h0d_ty.clone());
            let lhs = c.radd(c.cube(&y), c.cube(&d));
            let yd = c.radd(y.clone(), d.clone());
            let rhs = c.cube(&yd);
            let concl = c.rle(lhs, rhs);
            let e = b.mk_pi(h0d_id, BinderInfo::Default, h0d_ty, concl);
            let e = b.mk_pi(h0y_id, BinderInfo::Default, h0y_ty, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_cube_add_le_add_cube(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_of_cube_lt_cube : ∀ x z, 0≤x → 0≤z → (x·x)·x < (z·z)·z → Rat.lt x z`.
    fn register_rat_lt_of_cube_lt_cube(&mut self, c: &CubeReflConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_of_cube_lt_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (z_id, z) = b.fresh_local(c.rat.clone());
            let h0x_ty = c.nonneg(x.clone());
            let (h0x_id, _h) = b.fresh_local(h0x_ty.clone());
            let h0z_ty = c.nonneg(z.clone());
            let (h0z_id, _h2) = b.fresh_local(h0z_ty.clone());
            let hcb_ty = c.rlt(c.cube(&x), c.cube(&z));
            let (hcb_id, _h3) = b.fresh_local(hcb_ty.clone());
            let concl = c.rlt(x.clone(), z.clone());
            let e = b.mk_pi(hcb_id, BinderInfo::Default, hcb_ty, concl);
            let e = b.mk_pi(h0z_id, BinderInfo::Default, h0z_ty, e);
            let e = b.mk_pi(h0x_id, BinderInfo::Default, h0x_ty, e);
            let e = b.mk_pi(z_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_lt_of_cube_lt_cube(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.le_of_cube_le_cube : ∀ f g,
    ///     CauSeq.le (cube f)(cube g) → CauSeq.le f g`.
    fn register_causeq_le_of_cube_le_cube(&mut self, c: &CubeReflConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.le_of_cube_le_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let hyp = c.causeq_le(c.cau_cube(&f), c.cau_cube(&g));
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = c.causeq_le(f.clone(), g.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_le_of_cube_le_cube(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_of_cube_le_cube : ∀ a b,
    ///     NNReal.le (mul (mul a a) a)(mul (mul b b) b) → NNReal.le a b`.
    fn register_nnreal_le_of_cube_le_cube(&mut self, c: &CubeReflConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_of_cube_le_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
        let nncube = |x: &Expr| -> Expr {
            let sq = Expr::apps(nnmul.clone(), [x.clone(), x.clone()]);
            Expr::apps(nnmul.clone(), [sq, x.clone()])
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let hyp = Expr::apps(nnle.clone(), [nncube(&a), nncube(&bv)]);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = Expr::apps(nnle.clone(), [a.clone(), bv.clone()]);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_le_of_cube_le_cube(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `Rat.cube_add_le_add_cube`: `(y³ + d³) ≤ (y+d)³`.
///
/// `E : (y+d)³ = (y³+d³) + (3y²d + 3yd²)` from `Rat.add_cube` + a reassoc of the
/// trailing four summands; then `le_add_of_nonneg_right (y³+d³)(3y²d+3yd²)(0≤…)`
/// gives `(y³+d³) ≤ (y³+d³)+(3y²d+3yd²)`; subst RHS back along `E`.
fn build_cube_add_le_add_cube(c: &CubeReflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let h0y_ty = c.nonneg(y.clone());
    let (h0y_id, h0y) = b.fresh_local(h0y_ty.clone());
    let h0d_ty = c.nonneg(d.clone());
    let (h0d_id, h0d) = b.fresh_local(h0d_ty.clone());

    let y3 = c.cube(&y);
    let d3 = c.cube(&d);
    let y3_d3 = c.radd(y3.clone(), d3.clone()); // y³ + d³
    let yd = c.radd(y.clone(), d.clone()); // y+d
    let prod = c.cube(&yd); // (y+d)³

    // The cross terms `3·y²d` and `3·yd²` as the `add_cube` RHS builds them.
    let three = three(c);
    let y2b = c.rmul(c.rmul(y.clone(), y.clone()), d.clone()); // (y·y)·d  = y²d
    let yb2 = c.rmul(c.rmul(y.clone(), d.clone()), d.clone()); // (y·d)·d  = yd²
    let three_y2b = c.rmul(three.clone(), y2b.clone()); // 3·y²d
    let three_yb2 = c.rmul(three.clone(), yb2.clone()); // 3·yd²
    let cross = c.radd(three_y2b.clone(), three_yb2.clone()); // 3y²d + 3yd²

    // E : (y+d)³ = (y³ + d³) + (3y²d + 3yd²).
    let e_eq = build_cube_expand_eq(c, &b, &y, &d);

    // 0 ≤ 3y²d + 3yd².
    let h0cross = {
        let h0three = three_nonneg(c);
        let h0y2 = c.mul_nonneg(y.clone(), y.clone(), h0y.clone(), h0y.clone());
        let h0y2b = c.mul_nonneg(c.rmul(y.clone(), y.clone()), d.clone(), h0y2, h0d.clone());
        let h0yb = c.mul_nonneg(y.clone(), d.clone(), h0y.clone(), h0d.clone());
        let h0yb2 = c.mul_nonneg(c.rmul(y.clone(), d.clone()), d.clone(), h0yb, h0d.clone());
        let h0_3y2b = c.mul_nonneg(three.clone(), y2b.clone(), h0three.clone(), h0y2b);
        let h0_3yb2 = c.mul_nonneg(three.clone(), yb2.clone(), h0three, h0yb2);
        // 0 ≤ (3y²d)+(3yd²) : add_le_add 0 (3y²d) 0 (3yd²) → 0+0 ≤ …; subst 0+0→0.
        let step = add_le_add(
            c,
            c.rat_zero.clone(),
            three_y2b.clone(),
            c.rat_zero.clone(),
            three_yb2.clone(),
            h0_3y2b,
            h0_3yb2,
        );
        let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
        let add_zero0 = Expr::app(
            Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            c.rat_zero.clone(),
        );
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rle(t, cross.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(motive, zz, c.rat_zero.clone(), add_zero0, step)
    };

    // le_step : (y³+d³) ≤ (y³+d³) + (3y²d+3yd²).
    let le_step = c.le_add_of_nonneg_right(y3_d3.clone(), cross.clone(), h0cross);
    // subst RHS (y³+d³)+(3y²d+3yd²) → (y+d)³ along symm E.
    let rhs_expanded = c.radd(y3_d3.clone(), cross.clone());
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rle(y3_d3.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_symm = c.eq_symm(prod.clone(), rhs_expanded.clone(), e_eq);
    let proof = c.subst(motive, rhs_expanded, prod, e_symm, le_step);

    let e = b.mk_lam(h0d_id, BinderInfo::Default, h0d_ty, proof);
    let e = b.mk_lam(h0y_id, BinderInfo::Default, h0y_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `E : (y+d)³ = (y³ + d³) + (3·y²d + 3·yd²)`.
///
/// `Rat.add_cube y d` gives `(y+d)³ = y³ + (3y²d + (3yd² + d³))`. The remaining
/// step reassociates the four-term tail
/// `y³ + (3y²d + (3yd² + d³))  →  (y³ + d³) + (3y²d + 3yd²)`
/// via `add_assoc`/`add_comm`, mirroring `build_sq_expand_eq` one degree up.
fn build_cube_expand_eq(c: &CubeReflConsts, parent: &EnvDeclBuilder, y: &Expr, d: &Expr) -> Expr {
    let y3 = c.cube(y);
    let d3 = c.cube(d);
    let yd = c.radd(y.clone(), d.clone());
    let prod = c.cube(&yd);

    let three = three(c);
    let y2b = c.rmul(c.rmul(y.clone(), y.clone()), d.clone()); // y²d
    let yb2 = c.rmul(c.rmul(y.clone(), d.clone()), d.clone()); // yd²
    let p = c.rmul(three.clone(), y2b.clone()); // 3y²d  (= P)
    let q = c.rmul(three.clone(), yb2.clone()); // 3yd²  (= Q)

    // add_cube RHS: y³ + (P + (Q + d³)).
    let q_d3 = c.radd(q.clone(), d3.clone()); // Q + d³
    let p_qd3 = c.radd(p.clone(), q_d3.clone()); // P + (Q + d³)
    let ac_rhs = c.radd(y3.clone(), p_qd3.clone()); // y³ + (P + (Q + d³))
    let s0 = c.add_cube(y.clone(), d.clone()); // prod = ac_rhs

    // Target: (y³ + d³) + (P + Q).
    let pq = c.radd(p.clone(), q.clone()); // P + Q
    let final_rhs = c.radd(c.radd(y3.clone(), d3.clone()), pq.clone());

    // congr helpers.
    let add_left_fn = |t: &Expr| -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (v_id, v) = fb.fresh_local(c.rat.clone());
        let body = c.radd(t.clone(), v);
        fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let add_right_fn = |t: &Expr| -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (v_id, v) = fb.fresh_local(c.rat.clone());
        let body = c.radd(v, t.clone());
        fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
    };

    // We rewrite the tail `P + (Q + d³)` to `d³ + (P + Q)`, all under `y³ + ·`.
    //   P + (Q + d³)
    //   = P + (d³ + Q)            [congr (P+·)(add_comm Q d³)]
    //   = (P + d³) + Q            [symm (add_assoc P d³ Q)]
    //   = (d³ + P) + Q            [congr (·+Q)(add_comm P d³)]
    //   = d³ + (P + Q)            [add_assoc d³ P Q]
    let d3_q = c.radd(d3.clone(), q.clone()); // d³ + Q
    let p_d3q = c.radd(p.clone(), d3_q.clone()); // P + (d³ + Q)
    let p_d3 = c.radd(p.clone(), d3.clone()); // P + d³
    let p_d3_q = c.radd(p_d3.clone(), q.clone()); // (P + d³) + Q
    let d3_p = c.radd(d3.clone(), p.clone()); // d³ + P
    let d3_p_q = c.radd(d3_p.clone(), q.clone()); // (d³ + P) + Q
    let d3_pq = c.radd(d3.clone(), pq.clone()); // d³ + (P + Q)

    // Running-LHS chain on `p_qd3 = P+(Q+d³)`:
    //   P+(Q+d³) = P+(d³+Q) = (P+d³)+Q = (d³+P)+Q = d³+(P+Q).
    let t1 = c.congr_arg(
        q_d3.clone(),
        d3_q.clone(),
        add_left_fn(&p),
        c.add_comm(q.clone(), d3.clone()),
    ); // p_qd3 = P+(d³+Q)
    let t2 = c.eq_symm(
        p_d3_q.clone(),
        p_d3q.clone(),
        c.add_assoc(p.clone(), d3.clone(), q.clone()),
    ); // P+(d³+Q) = (P+d³)+Q
    let t3 = c.congr_arg(
        p_d3.clone(),
        d3_p.clone(),
        add_right_fn(&q),
        c.add_comm(p.clone(), d3.clone()),
    ); // (P+d³)+Q = (d³+P)+Q
    let t4 = c.add_assoc(d3.clone(), p.clone(), q.clone()); // (d³+P)+Q = d³+(P+Q)

    let chain_tail = c.eq_trans(p_qd3.clone(), p_d3q.clone(), p_d3_q.clone(), t1, t2);
    let chain_tail = c.eq_trans(
        p_qd3.clone(),
        p_d3_q.clone(),
        d3_p_q.clone(),
        chain_tail,
        t3,
    );
    let chain_tail = c.eq_trans(p_qd3.clone(), d3_p_q.clone(), d3_pq.clone(), chain_tail, t4);
    // chain_tail : P+(Q+d³) = d³+(P+Q).

    // Lift under `y³ + ·` : y³+(P+(Q+d³)) = y³+(d³+(P+Q)).
    let lift = c.congr_arg(p_qd3.clone(), d3_pq.clone(), add_left_fn(&y3), chain_tail);
    let y3_d3pq = c.radd(y3.clone(), d3_pq.clone()); // y³ + (d³ + (P+Q))

    // y³+(d³+(P+Q)) = (y³+d³)+(P+Q)  [symm add_assoc y³ d³ (P+Q)].
    let assoc_final = c.add_assoc(y3.clone(), d3.clone(), pq.clone()); // (y³+d³)+(P+Q) = y³+(d³+(P+Q))
    let close = c.eq_symm(final_rhs.clone(), y3_d3pq.clone(), assoc_final); // y³+(d³+(P+Q)) = (y³+d³)+(P+Q)

    // Full chain: prod =s0= ac_rhs =lift= y³+(d³+(P+Q)) =close= (y³+d³)+(P+Q).
    let ch = c.eq_trans(prod.clone(), ac_rhs.clone(), y3_d3pq.clone(), s0, lift);
    c.eq_trans(prod, y3_d3pq, final_rhs, ch, close)
}

/// `Rat.lt_of_cube_lt_cube`: `x < z` from `x³ < z³` (nonneg `x,z`).
///
/// `le_of_cube_le_cube x z (0≤x)(0≤z)(le_of_lt x³<z³) : x ≤ z`. For the strict
/// part, `¬(z ≤ x)`: from `z ≤ x` derive `x = z` (antisymm), transport `x³ < z³`
/// to `z³ < z³` (congr cube on `x = z`), contradiction via `lt_iff` + `le_refl`.
fn build_lt_of_cube_lt_cube(c: &CubeReflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(c.rat.clone());
    let h0x_ty = c.nonneg(x.clone());
    let (h0x_id, h0x) = b.fresh_local(h0x_ty.clone());
    let h0z_ty = c.nonneg(z.clone());
    let (h0z_id, h0z) = b.fresh_local(h0z_ty.clone());
    let x3 = c.cube(&x);
    let z3 = c.cube(&z);
    let hcb_ty = c.rlt(x3.clone(), z3.clone());
    let (hcb_id, hcb) = b.fresh_local(hcb_ty.clone());

    // h_le : x ≤ z := le_of_cube_le_cube x z h0x h0z (le_of_lt x³<z³).
    let hcb_le = c.le_of_lt(x3.clone(), z3.clone(), hcb.clone());
    let h_le = c.le_of_cube_le_cube(x.clone(), z.clone(), h0x.clone(), h0z.clone(), hcb_le);

    // not_zx : ¬ (z ≤ x).
    let not_zx = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let hzx_ty = c.rle(z.clone(), x.clone());
        let (hzx_id, hzx) = nb.fresh_local(hzx_ty.clone());
        // x = z via antisymm x z h_le hzx.
        let x_eq_z = c.le_antisymm(x.clone(), z.clone(), h_le.clone(), hzx);
        // x³ = z³ : congrArg cube x_eq_z. cube := fun t => (t·t)·t.
        let cube_fn = {
            let mut fb = EnvDeclBuilder::child_of(&nb);
            let (v_id, v) = fb.fresh_local(c.rat.clone());
            let body = c.cube(&v);
            fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let x3_eq_z3 = c.congr_arg(x.clone(), z.clone(), cube_fn, x_eq_z); // x³ = z³
                                                                           // subst hcb : x³ < z³ along x3_eq_z3 → z³ < z³.
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&nb);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rlt(t, z3.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let z3_lt_z3 = c.subst(motive, x3.clone(), z3.clone(), x3_eq_z3, hcb.clone());
        // ¬(z³ ≤ z³) := And.right (Iff.mp (lt_iff z³ z³) z3_lt_z3).
        let le_zz = c.rle(z3.clone(), z3.clone());
        let not_le_zz = Expr::app(c.not_c.clone(), le_zz.clone());
        let and_zz = Expr::apps(c.and_c.clone(), [le_zz.clone(), not_le_zz.clone()]);
        let lt_zz_ty = c.rlt(z3.clone(), z3.clone());
        let iff_zz = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [z3.clone(), z3.clone()]);
        let mp_zz = Expr::apps(c.iff_mp.clone(), [lt_zz_ty, and_zz, iff_zz, z3_lt_z3]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let not_le_zz_pf = Expr::apps(and_right, [le_zz.clone(), not_le_zz, mp_zz]);
        // apply to le_refl (z³) : False.
        let le_refl_zz = Expr::app(c.rat_le_refl.clone(), z3.clone());
        let false_pf = Expr::app(not_le_zz_pf, le_refl_zz);
        nb.finish_child(nb.mk_lam(hzx_id, BinderInfo::Default, hzx_ty, false_pf))
    };

    // x < z := Iff.mpr (lt_iff x z) (And.intro (x≤z) ¬(z≤x) h_le not_zx).
    let le_xz = c.rle(x.clone(), z.clone());
    let not_le_zx = Expr::app(c.not_c.clone(), c.rle(z.clone(), x.clone()));
    let and_pf = Expr::apps(
        c.and_intro.clone(),
        [le_xz.clone(), not_le_zx.clone(), h_le, not_zx],
    );
    let and_ty = Expr::apps(c.and_c.clone(), [le_xz, not_le_zx]);
    let lt_xz_ty = c.rlt(x.clone(), z.clone());
    let iff_xz = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [x.clone(), z.clone()]);
    let proof = Expr::apps(c.iff_mpr.clone(), [lt_xz_ty, and_ty, iff_xz, and_pf]);

    let e = b.mk_lam(hcb_id, BinderInfo::Default, hcb_ty, proof);
    let e = b.mk_lam(h0z_id, BinderInfo::Default, h0z_ty, e);
    let e = b.mk_lam(h0x_id, BinderInfo::Default, h0x_ty, e);
    let e = b.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNReal.CauSeq.le_of_cube_le_cube` proof value (the pointwise core).
fn build_causeq_le_of_cube_le_cube(c: &CubeReflConsts) -> Expr {
    let lt_of_cube = Expr::const_(Name::from_string("Rat.lt_of_cube_lt_cube"), vec![]);
    let cube_add = Expr::const_(Name::from_string("Rat.cube_add_le_add_cube"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let fff = c.cau_cube(&f);
    let ggg = c.cau_cube(&g);
    let hyp_ty = c.causeq_le(fff.clone(), ggg.clone());
    let (hyp_id, hyp) = b.fresh_local(hyp_ty.clone());

    // goal: CauSeq.le f g = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vf n < vg n + ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // ε³ > 0 (mul_pos (ε·ε) ε (mul_pos ε ε) hpos).
    let eps_sq = c.rmul(eps.clone(), eps.clone());
    let eps_cube = c.cube(&eps);
    let h_eps_sq_pos = c.mul_pos(eps.clone(), eps.clone(), hpos.clone(), hpos.clone());
    let h_eps_cube_pos = c.mul_pos(eps_sq.clone(), eps.clone(), h_eps_sq_pos, hpos.clone());

    // hyp (ε³) (>0) : ∃ N, ∀ n, N≤n → vseq(cube f) n < vseq(cube g) n + ε³.
    let exists_src = Expr::apps(hyp.clone(), [eps_cube.clone(), h_eps_cube_pos]);
    let pred_src = c.pred_n(&b, &fff, &ggg, &eps_cube);
    let goal_exists = c.exists_pred(&b, &f, &g, &eps);

    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = be.fresh_local(c.nat.clone());
        let hn_ty = c.pred_n_at(&be, &fff, &ggg, &eps_cube, &cap);
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        let witness = {
            let mut bw = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bw.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), m.clone());
            let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

            // base : vseq(cube f) m < vseq(cube g) m + ε³ := hn m hle.
            // vseq(cube f) m ≡ (vf·vf)·vf = cube vf  (val_mul defeq, twice).
            let base = Expr::apps(hn.clone(), [m.clone(), hle]);
            let vf = c.vseq(&f, &m);
            let vg = c.vseq(&g, &m);
            let vf_cube = c.cube(&vf);
            let vg_cube = c.cube(&vg);

            // 0≤vf, 0≤vg (property); 0≤ε from hpos (for cube_add d=ε).
            let h0vf = c.property_seq(&f, &m);
            let h0vg = c.property_seq(&g, &m);
            let h0eps = c.le_of_lt(c.rat_zero.clone(), eps.clone(), hpos.clone());

            // cube_add vg ε (0≤vg)(0≤ε) : vg³ + ε³ ≤ (vg+ε)³.
            let h_cubeadd = Expr::apps(
                cube_add.clone(),
                [vg.clone(), eps.clone(), h0vg.clone(), h0eps],
            );

            // base : vf³ < vg³ + ε³ (defeq). lt_of_lt_of_le → vf³ < (vg+ε)³.
            let vgg_eps = c.radd(vg_cube.clone(), eps_cube.clone()); // vg³ + ε³
            let vg_eps = c.radd(vg.clone(), eps.clone());
            let vg_eps_cube = c.cube(&vg_eps);
            let vf_cube_lt_prod = c.lt_of_lt_of_le(
                vf_cube.clone(),
                vgg_eps.clone(),
                vg_eps_cube.clone(),
                base,
                h_cubeadd,
            );
            let _ = vf_cube;

            // 0 ≤ vg+ε := add_le_add 0 vg 0 ε → 0+0≤vg+ε; subst 0+0→0.
            let h0vgeps = {
                let step = add_le_add(
                    c,
                    c.rat_zero.clone(),
                    vg.clone(),
                    c.rat_zero.clone(),
                    eps.clone(),
                    h0vg.clone(),
                    c.le_of_lt(c.rat_zero.clone(), eps.clone(), hpos.clone()),
                );
                let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
                let add_zero0 = Expr::app(
                    Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
                    c.rat_zero.clone(),
                );
                let motive = {
                    let mut m2 = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = m2.fresh_local(c.rat.clone());
                    let body = c.rle(t, vg_eps.clone());
                    m2.finish_child(m2.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.subst(motive, zz, c.rat_zero.clone(), add_zero0, step)
            };

            // lt_of_cube_lt_cube vf (vg+ε) (0≤vf)(0≤vg+ε)(vf³ < (vg+ε)³) : vf < vg+ε.
            let proof = Expr::apps(
                lt_of_cube.clone(),
                [vf.clone(), vg_eps.clone(), h0vf, h0vgeps, vf_cube_lt_prod],
            );

            let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
            let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            bw.finish_child(e)
        };

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [
                c.nat.clone(),
                c.pred_n(&be, &f, &g, &eps),
                cap.clone(),
                witness,
            ],
        );
        let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
        let e = be.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_src, goal_exists, exists_src, elim_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hyp_id, BinderInfo::Default, hyp_ty, e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// `NNReal.le_of_cube_le_cube` via nested `Quot.ind` reducing the leaf to core.
fn build_nnreal_le_of_cube_le_cube(c: &CubeReflConsts, nnreal: &Expr) -> Expr {
    let core = Expr::const_(
        Name::from_string("NNReal.CauSeq.le_of_cube_le_cube"),
        vec![],
    );
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let nncube = |x: &Expr| -> Expr {
        let sq = Expr::apps(nnmul.clone(), [x.clone(), x.clone()]);
        Expr::apps(nnmul.clone(), [sq, x.clone()])
    };

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let hyp_ty = Expr::apps(nnle.clone(), [nncube(&a), nncube(&bv)]);
    let (hyp_id, hyp) = b.fresh_local(hyp_ty.clone());

    // motive over a: P a := nnle (cube a)(cube bv) → nnle a bv.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let h = Expr::apps(nnle.clone(), [nncube(&x), nncube(&bv)]);
        let concl = Expr::apps(nnle.clone(), [x.clone(), bv.clone()]);
        let imp = Expr::pi(BinderInfo::Default, h, concl);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        // descend on bv.
        let motive_b = {
            let mut mb = EnvDeclBuilder::child_of(&mf);
            let (y_id, y) = mb.fresh_local(nnreal.clone());
            let h = Expr::apps(nnle.clone(), [nncube(&mkf), nncube(&y)]);
            let concl = Expr::apps(nnle.clone(), [mkf.clone(), y.clone()]);
            let imp = Expr::pi(BinderInfo::Default, h, concl);
            mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), imp))
        };
        let minor_b = {
            let mut mg = EnvDeclBuilder::child_of(&mf);
            let (g_id, g) = mg.fresh_local(c.causeq.clone());
            // leaf: hyp reduces to CauSeq.le (cube f)(cube g); goal to CauSeq.le f g.
            let h_ty = c.causeq_le(c.cau_cube(&f), c.cau_cube(&g));
            let (h_id, h) = mg.fresh_local(h_ty.clone());
            let body = Expr::apps(core.clone(), [f.clone(), g.clone(), h]);
            let e = mg.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e))
        };
        let ind_b = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_b,
                minor_b,
                bv.clone(),
            ],
        );
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), ind_b))
    };
    let ind_a = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    let applied = Expr::apps(ind_a, [hyp.clone()]);

    let e = b.mk_lam(hyp_id, BinderInfo::Default, hyp_ty, applied);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// `1+1+1` as `(1+1)+1` (the `Rat.add_cube` coefficient shape).
fn three(c: &CubeReflConsts) -> Expr {
    let one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    c.radd(c.radd(one.clone(), one.clone()), one)
}

/// `0 ≤ 1+1+1`, built from `0 ≤ 1` (`Rat.zero_le_one`) by `add_le_add`s and
/// `Rat.add_zero`-transport.
fn three_nonneg(c: &CubeReflConsts) -> Expr {
    let one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let zero = c.rat_zero.clone();
    let h01 = Expr::const_(Name::from_string("Rat.zero_le_one"), vec![]); // 0 ≤ 1
                                                                          // 0 ≤ 1+1 : add_le_add 0 1 0 1 h01 h01 → 0+0 ≤ 1+1; subst 0+0→0.
    let two = c.radd(one.clone(), one.clone());
    let step2 = add_le_add(
        c,
        zero.clone(),
        one.clone(),
        zero.clone(),
        one.clone(),
        h01.clone(),
        h01.clone(),
    );
    let zz = c.radd(zero.clone(), zero.clone());
    let add_zero0 = Expr::app(
        Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
        zero.clone(),
    );
    let h02 = {
        let motive_e = motive_le_right(c, &two);
        c.subst(motive_e, zz.clone(), zero.clone(), add_zero0.clone(), step2)
    };
    // 0 ≤ (1+1)+1 : add_le_add 0 (1+1) 0 1 h02 h01 → 0+0 ≤ (1+1)+1; subst 0+0→0.
    let three_v = c.radd(two.clone(), one.clone());
    let step3 = add_le_add(
        c,
        zero.clone(),
        two.clone(),
        zero.clone(),
        one.clone(),
        h02,
        h01,
    );
    let motive_e = motive_le_right(c, &three_v);
    c.subst(motive_e, zz, zero, add_zero0, step3)
}

/// `fun t => Rat.le t rhs` — a one-place motive for transporting the LHS of a `≤`.
fn motive_le_right(c: &CubeReflConsts, rhs: &Expr) -> Expr {
    let mut m = EnvDeclBuilder::new();
    let (t_id, t) = m.fresh_local(c.rat.clone());
    let body = c.rle(t, rhs.clone());
    m.finish(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
}

/// `Rat.add_le_add a b c d (a≤b)(c≤d) : (a+c) ≤ (b+d)`.
fn add_le_add(
    c: &CubeReflConsts,
    a: Expr,
    bb: Expr,
    cc: Expr,
    d: Expr,
    h1: Expr,
    h2: Expr,
) -> Expr {
    Expr::apps(c.rat_add_le_add.clone(), [a, bb, cc, d, h1, h2])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Rat.cube_add_le_add_cube",
        "Rat.lt_of_cube_lt_cube",
        "NNReal.CauSeq.le_of_cube_le_cube",
        "NNReal.le_of_cube_le_cube",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_reverse_cube()
            .expect("init_algebra_nnreal_reverse_cube");
        env.init_algebra_nnreal_reverse_cube().expect("idempotent");
        env
    }

    #[test]
    fn test_reverse_cube_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
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
    fn test_reverse_cube_constructive_empty_closure() {
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
