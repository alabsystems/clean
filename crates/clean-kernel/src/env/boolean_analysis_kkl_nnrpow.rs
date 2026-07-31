// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL fractional-power carrier — the faithful `3/2`-power relation `IsRpow32`.
//!
//! ## Why this carrier exists
//!
//! The sharp-KKL retirement (`designs/2026-06-18-kkl-root-free-obstruction.md`)
//! is walled by a non-rational `Inf_i^{3/2}` hypercontractive step. The
//! root-free squared route is conclusively dead (a fatal Cauchy–Schwarz `√n`).
//! Andrew authorized option (a): a faithful fractional-power carrier carrying
//! the handful of facts the argument needs. `√(Inf_i)` is IRRATIONAL for general
//! rational `Inf_i`, so a `Rat`-VALUED total `nnRpow` cannot equal the real
//! value. The consumers use only ORDER + the squaring relation, so we model
//! `x^{3/2}` by its **graph relation**, never by a (non-existent) rational value:
//!
//! ```text
//! BoolAnalysis.IsRpow32 (x r : Rat) : Prop :=
//!   And (Rat.le Rat.zero r) (Eq (Rat.mul r r) (Rat.mul (Rat.mul x x) x))
//! ```
//!
//! "`r` is THE 3/2-power of `x`": a nonnegative rational whose square is `x³`.
//! It is a reducible `Declaration::Definition` of a `Prop`, built ENTIRELY from
//! the existing constructive `Rat` surface — **it introduces NO axiom**, so it
//! does NOT relocate trust. It is a partial spec: for a given `x` the relation
//! may hold for no rational `r` (when `x³` is not a perfect rational square).
//! This is SOUND — the carrier never asserts existence and so cannot prove
//! `False`; the facts below quantify over a supplied witness `r`, so they are
//! vacuously safe when no witness exists and exact when one does.
//!
//! ## The facts (all constructive Theorems, empty domain-axiom closure)
//!
//! ```text
//! (i)  rpow32_sq :                                              -- defining relation
//!   ∀ x r, IsRpow32 x r → Rat.mul r r = Rat.mul (Rat.mul x x) x
//!
//! (ii') rpow32_sq_le_eps_mul_sq :                              -- squared form (witness-free)
//!   ∀ x ε r, Rat.le 0 x → Rat.le x ε → IsRpow32 x r
//!          → Rat.le (Rat.mul r r) (Rat.mul ε (Rat.mul x x))
//!
//! (ii) rpow32_le_sqrt_eps_mul :                                -- value form x^{3/2} ≤ √ε·x
//!   ∀ x ε s r, Rat.le 0 x → Rat.le x ε → Rat.le 0 s → Rat.mul s s = ε
//!            → IsRpow32 x r → Rat.le r (Rat.mul s x)
//!
//! (iii) rpow32_mono :                                          -- monotonicity
//!   ∀ x y rx ry, Rat.le 0 x → Rat.le 0 y → Rat.le 0 rx → Rat.le 0 ry
//!              → Rat.le x y → IsRpow32 x rx → IsRpow32 y ry → Rat.le rx ry
//! ```
//!
//! ## Proofs (constructive, empty admitted-axiom closure)
//!
//! Cornerstone `Rat.le_of_sq_le_sq : ∀ a b, 0≤a → 0≤b → a·a ≤ b·b → a ≤ b` is a
//! LANDED constructive Theorem (`boolean_analysis_order_toolkit_b1d.rs`; routes
//! through `Classical.em`, whose closure ⊆ FOUNDATIONAL, so empty domain
//! closure). All other leaves (`Rat.mul_le_mul_of_nonneg_{left,right}`,
//! `Rat.mul_nonneg`, `Rat.mul_comm`, `Rat.mul_mul_mul_comm`,
//! `Eq.refl/symm/trans/subst`, `And.*`) are `Constructive` with empty closure,
//! so every fact here is too.
//!
//! - **(i)** `And.right` of the unfolded relation.
//! - **(ii')** `r·r = (x·x)·x ≤ (x·x)·ε = ε·(x·x)`: `Eq.subst` the relation,
//!   `mul_le_mul_of_nonneg_left (x·x)` consumes `x ≤ ε` (`0 ≤ x·x` from
//!   `sq_nonneg`), `mul_comm` lands `ε·(x·x)`.
//! - **(ii)** square it: `r·r ≤ ε·(x·x) = (s·s)·(x·x) = (s·x)·(s·x)`
//!   (uses `s·s = ε`, `mul_mul_mul_comm`), then `Rat.le_of_sq_le_sq r (s·x)`.
//! - **(iii)** `rx·rx = x³ ≤ y³ = ry·ry` (cube-monotone for `0≤x≤y`, built from
//!   `mul_le_mul` thrice), `Eq.subst` both relations, then
//!   `Rat.le_of_sq_le_sq rx ry`.
//!
//! Refute-checked: each fact's type returns `None` from `refute_conjecture`
//! (TRUE conditional statements), and the carrier `IsRpow32` does not prove
//! `False`. See `designs/2026-06-18-nnrpow-carrier-build.md`.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the `IsRpow32` carrier and its facts.
struct NnRpowConsts {
    order: OrderConsts,
    rat: Expr,
    and_: Expr,
    and_left: Expr,
    and_right: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    mul_comm: Expr,
    mul_mul_mul_comm: Expr,
    mul_le_left: Expr,
    mul_le_right: Expr,
    le_trans: Expr,
    le_of_sq_le_sq: Expr,
    is_rpow32: Expr,
    nat: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_le: Expr,
    fin_sum_smul: Expr,
    bool_fn: Expr,
    influence: Expr,
    total_influence: Expr,
}

impl NnRpowConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            rat: k("Rat"),
            and_: k("And"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            mul_comm: k("Rat.mul_comm"),
            mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            le_trans: k("Rat.le_trans"),
            le_of_sq_le_sq: k("Rat.le_of_sq_le_sq"),
            is_rpow32: k("BoolAnalysis.IsRpow32"),
            nat: k("Nat"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_le: k("Fin.sum_le"),
            fin_sum_smul: k("Fin.sum_smul"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            influence: k("BoolAnalysis.Influence"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    /// `Fin.sum n h`.
    fn sum(&self, n: &Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), h])
    }
    /// `Influence n f i`.
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `TotalInfluence n f`.
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }

    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.zero(), a)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    /// `(x·x)·x`.
    fn cube(&self, x: &Expr) -> Expr {
        self.mul(self.mul(x.clone(), x.clone()), x.clone())
    }
    /// `IsRpow32 x r`.
    fn is_rpow32_of(&self, x: &Expr, r: &Expr) -> Expr {
        Expr::apps(self.is_rpow32.clone(), [x.clone(), r.clone()])
    }
    /// The `And (0≤r) (r·r = x³)` body `IsRpow32 x r` unfolds to — used to spell
    /// the `And.left`/`And.right` propositions.
    fn rpow32_parts(&self, x: &Expr, r: &Expr) -> (Expr, Expr) {
        let nn = self.le0(r.clone());
        let rel = self.eq(self.mul(r.clone(), r.clone()), self.cube(x));
        (nn, rel)
    }
    /// `And P Q`.
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_.clone(), [p, q])
    }
    /// `@And.left P Q h : P`.
    fn and_left_of(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [p, q, h])
    }
    /// `@And.right P Q h : Q`.
    fn and_right_of(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [p, q, h])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg_of(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Rat.mul_nonneg a b h0a h0b : 0 ≤ a·b`.
    fn mul_nonneg_of(&self, a: Expr, b: Expr, h0a: Expr, h0b: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, h0a, h0b])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mul_mul_mul_comm_of(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_0a : a·b ≤ a·c`.
    fn mul_le_left_of(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, h_bc, h_0a])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c h_bc h_0a : b·a ≤ c·a`.
    fn mul_le_right_of(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h_bc, h_0a])
    }
    /// `Rat.le_trans a b c h_ab h_bc : a ≤ c`.
    fn le_trans_of(&self, a: Expr, b: Expr, cc: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h_ab, h_bc])
    }
    /// `Rat.le_of_sq_le_sq a b h0a h0b h_sq : a ≤ b`.
    fn le_of_sq_le_sq_of(&self, a: Expr, b: Expr, h0a: Expr, h0b: Expr, h_sq: Expr) -> Expr {
        Expr::apps(self.le_of_sq_le_sq.clone(), [a, b, h0a, h0b, h_sq])
    }
    /// `Eq.subst.{1} @Rat motive @a @b h_eq h_motive_a : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_motive_a)
    }
    /// `Eq.symm.{1} @Rat @a @b h : Eq b a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
}

impl Environment {
    /// Register the `IsRpow32` carrier + its facts. Idempotent.
    pub fn init_boolean_analysis_kkl_nnrpow(&mut self) -> Result<(), EnvError> {
        self.register_is_rpow32()?;
        self.register_rpow32_sq()?;
        self.register_rpow32_sq_le_eps_mul_sq()?;
        self.register_rpow32_le_sqrt_eps_mul()?;
        self.register_rpow32_mono()?;
        self.register_sum_rpow32_le_sqrt_eps_mul_sum()?;
        self.register_kkl_sum_rpow32_influence_le()?;
        Ok(())
    }

    /// `BoolAnalysis.IsRpow32 (x r : Rat) : Prop` — the faithful `3/2`-power
    /// graph relation `And (0 ≤ r) (r·r = (x·x)·x)`. Reducible `Definition` of a
    /// `Prop`, NO axiom. Idempotent.
    pub fn register_is_rpow32(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.IsRpow32");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat order surface

        let c = NnRpowConsts::new();
        let prop = Expr::prop();

        // type: Rat → Rat → Prop
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(c.rat.clone());
            let (r_id, _r) = b.fresh_local(c.rat.clone());
            let e = b.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), prop.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        // value: fun (x r : Rat) => And (0 ≤ r) (r·r = (x·x)·x)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let (nn, rel) = c.rpow32_parts(&x, &r);
            let body = c.and(nn, rel);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// (i) `BoolAnalysis.rpow32_sq : ∀ x r, IsRpow32 x r → r·r = (x·x)·x`.
    /// Proof: `And.right` of the (reducibly unfolded) relation. Constructive,
    /// empty closure.
    pub fn register_rpow32_sq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.rpow32_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_is_rpow32()?;
        let c = NnRpowConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let hyp = c.is_rpow32_of(&x, &r);
            let (_nn, rel) = c.rpow32_parts(&x, &r);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, rel);
            let e = b.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let hyp = c.is_rpow32_of(&x, &r);
            let (nn, rel) = c.rpow32_parts(&x, &r);
            let (h_id, h) = b.fresh_local(hyp.clone());
            // And.right (0≤r) (r·r = x³) h : r·r = x³.  `h : IsRpow32 x r` is
            // def-eq (reducible δ) to `And (0≤r) (r·r=x³)`, so this type-checks.
            let body = c.and_right_of(nn, rel, h);
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// (ii') `BoolAnalysis.rpow32_sq_le_eps_mul_sq :
    ///   ∀ x ε r, 0≤x → x≤ε → IsRpow32 x r → r·r ≤ ε·(x·x)`.
    /// Squared form, witness-free. Constructive, empty closure.
    pub fn register_rpow32_sq_le_eps_mul_sq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.rpow32_sq_le_eps_mul_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rpow32_sq()?;
        self.register_rat_le_trans_proof()?; // Rat.le_trans (defensive; reused elsewhere)
        let c = NnRpowConsts::new();

        // Shared telescope builder for both type and value.
        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let h0x = c.le0(x.clone());
            let hxe = c.le(x.clone(), eps.clone());
            let hrp = c.is_rpow32_of(&x, &r);

            let xx = c.mul(x.clone(), x.clone());
            let rr = c.mul(r.clone(), r.clone());
            let cube = c.cube(&x);
            let eps_xx = c.mul(eps.clone(), xx.clone());
            let concl = c.le(rr.clone(), eps_xx.clone());

            let (h0x_id, _h0x_v) = b.fresh_local(h0x.clone());
            let (hxe_id, hxe_v) = b.fresh_local(hxe.clone());
            let (hrp_id, hrp_v) = b.fresh_local(hrp.clone());

            let tail = if for_value {
                // h_rel : r·r = (x·x)·x
                let rpow32_sq = Expr::const_(Name::from_string("BoolAnalysis.rpow32_sq"), vec![]);
                let h_rel = Expr::apps(rpow32_sq, [x.clone(), r.clone(), hrp_v]);
                // h_0xx : 0 ≤ x·x
                let h_0xx = c.sq_nonneg_of(x.clone());
                // h_cube_le : (x·x)·x ≤ (x·x)·ε
                let h_cube_le = c.mul_le_left_of(xx.clone(), x.clone(), eps.clone(), hxe_v, h_0xx);
                // h_comm : (x·x)·ε = ε·(x·x)
                let h_comm = c.mul_comm_of(xx.clone(), eps.clone());
                // transport (x·x)·ε → ε·(x·x): motive fun t => (x·x)·x ≤ t
                let motive_comm = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(cube.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // h_cube_le2 : (x·x)·x ≤ ε·(x·x)
                let h_cube_le2 = c.subst(
                    motive_comm,
                    c.mul(xx.clone(), eps.clone()),
                    eps_xx.clone(),
                    h_comm,
                    h_cube_le,
                );
                // transport (x·x)·x → r·r on the LHS via h_rel.symm : (x·x)·x = r·r
                let h_rel_sym = c.symm(rr.clone(), cube.clone(), h_rel);
                let motive_lhs = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(t, eps_xx.clone());
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // r·r ≤ ε·(x·x)
                c.subst(motive_lhs, cube.clone(), rr.clone(), h_rel_sym, h_cube_le2)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, bi, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = bind(&b, hrp_id, BinderInfo::Default, hrp, tail);
            let e = bind(&b, hxe_id, BinderInfo::Default, hxe, e);
            let e = bind(&b, h0x_id, BinderInfo::Default, h0x, e);
            let e = bind(&b, r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// (ii) `BoolAnalysis.rpow32_le_sqrt_eps_mul :
    ///   ∀ x ε s r, 0≤x → x≤ε → 0≤s → s·s = ε → IsRpow32 x r → r ≤ s·x`.
    /// Value form `x^{3/2} ≤ √ε·x` with `s` a SUPPLIED `√ε` witness. Constructive,
    /// empty closure.
    pub fn register_rpow32_le_sqrt_eps_mul(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.rpow32_le_sqrt_eps_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rpow32_sq_le_eps_mul_sq()?;
        self.init_boolean_analysis_order_toolkit_b1d()?; // Rat.le_of_sq_le_sq
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm
        let c = NnRpowConsts::new();

        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let h0x = c.le0(x.clone());
            let hxe = c.le(x.clone(), eps.clone());
            let h0s = c.le0(s.clone());
            let hse = c.eq(c.mul(s.clone(), s.clone()), eps.clone());
            let hrp = c.is_rpow32_of(&x, &r);

            let xx = c.mul(x.clone(), x.clone());
            let rr = c.mul(r.clone(), r.clone());
            let sx = c.mul(s.clone(), x.clone());
            let concl = c.le(r.clone(), sx.clone());

            let (h0x_id, h0x_v) = b.fresh_local(h0x.clone());
            let (hxe_id, hxe_v) = b.fresh_local(hxe.clone());
            let (h0s_id, h0s_v) = b.fresh_local(h0s.clone());
            let (hse_id, hse_v) = b.fresh_local(hse.clone());
            let (hrp_id, hrp_v) = b.fresh_local(hrp.clone());

            let tail = if for_value {
                let ss = c.mul(s.clone(), s.clone());
                let ss_xx = c.mul(ss.clone(), xx.clone());
                let sx_sx = c.mul(sx.clone(), sx.clone());
                let _eps_xx = c.mul(eps.clone(), xx.clone());

                // h_sq_le : r·r ≤ ε·(x·x)
                let sq_le = Expr::const_(
                    Name::from_string("BoolAnalysis.rpow32_sq_le_eps_mul_sq"),
                    vec![],
                );
                let h_sq_le = Expr::apps(
                    sq_le,
                    [
                        x.clone(),
                        eps.clone(),
                        r.clone(),
                        h0x_v.clone(),
                        hxe_v,
                        hrp_v.clone(),
                    ],
                );
                // rewrite ε → s·s : hse.symm : ε = s·s.  motive fun t => r·r ≤ t·(x·x)
                let hse_sym = c.symm(ss.clone(), eps.clone(), hse_v);
                let motive1 = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(rr.clone(), c.mul(t, xx.clone()));
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // h_le_ssxx : r·r ≤ (s·s)·(x·x)
                let h_le_ssxx = c.subst(motive1, eps.clone(), ss.clone(), hse_sym, h_sq_le);

                // ring: (s·s)·(x·x) = (s·x)·(s·x)
                let h_ring = c.mul_mul_mul_comm_of(s.clone(), s.clone(), x.clone(), x.clone());
                let motive2 = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(rr.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // h_le_sxsx : r·r ≤ (s·x)·(s·x)
                let h_le_sxsx = c.subst(motive2, ss_xx.clone(), sx_sx.clone(), h_ring, h_le_ssxx);

                // 0 ≤ r  (And.left of hrp, def-eq unfold)
                let (nn, rel) = c.rpow32_parts(&x, &r);
                let h_0r = c.and_left_of(nn, rel, hrp_v);
                // 0 ≤ s·x  (mul_nonneg s x h0s h0x)
                let h_0sx = c.mul_nonneg_of(s.clone(), x.clone(), h0s_v, h0x_v);

                // le_of_sq_le_sq r (s·x) (0≤r) (0≤s·x) (r·r ≤ (s·x)·(s·x)) : r ≤ s·x
                c.le_of_sq_le_sq_of(r.clone(), sx.clone(), h_0r, h_0sx, h_le_sxsx)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, bi, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = bind(&b, hrp_id, BinderInfo::Default, hrp, tail);
            let e = bind(&b, hse_id, BinderInfo::Default, hse, e);
            let e = bind(&b, h0s_id, BinderInfo::Default, h0s, e);
            let e = bind(&b, hxe_id, BinderInfo::Default, hxe, e);
            let e = bind(&b, h0x_id, BinderInfo::Default, h0x, e);
            let e = bind(&b, r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, s_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// (iii) `BoolAnalysis.rpow32_mono :
    ///   ∀ x y rx ry, 0≤x → 0≤y → 0≤rx → 0≤ry → x≤y → IsRpow32 x rx → IsRpow32 y ry
    ///              → rx ≤ ry`. Constructive, empty closure.
    pub fn register_rpow32_mono(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.rpow32_mono");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rpow32_sq()?;
        self.init_boolean_analysis_order_toolkit_b1d()?; // Rat.le_of_sq_le_sq
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        let c = NnRpowConsts::new();

        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let (rx_id, rx) = b.fresh_local(c.rat.clone());
            let (ry_id, ry) = b.fresh_local(c.rat.clone());
            let h0x = c.le0(x.clone());
            let h0y = c.le0(y.clone());
            let h0rx = c.le0(rx.clone());
            let h0ry = c.le0(ry.clone());
            let hxy = c.le(x.clone(), y.clone());
            let hrpx = c.is_rpow32_of(&x, &rx);
            let hrpy = c.is_rpow32_of(&y, &ry);
            let concl = c.le(rx.clone(), ry.clone());

            let (h0x_id, h0x_v) = b.fresh_local(h0x.clone());
            let (h0y_id, h0y_v) = b.fresh_local(h0y.clone());
            let (h0rx_id, h0rx_v) = b.fresh_local(h0rx.clone());
            let (h0ry_id, h0ry_v) = b.fresh_local(h0ry.clone());
            let (hxy_id, hxy_v) = b.fresh_local(hxy.clone());
            let (hrpx_id, hrpx_v) = b.fresh_local(hrpx.clone());
            let (hrpy_id, hrpy_v) = b.fresh_local(hrpy.clone());

            let tail = if for_value {
                let xx = c.mul(x.clone(), x.clone());
                let yy = c.mul(y.clone(), y.clone());
                let cube_x = c.cube(&x);
                let cube_y = c.cube(&y);
                let rxrx = c.mul(rx.clone(), rx.clone());
                let ryry = c.mul(ry.clone(), ry.clone());

                // cube-monotone: x³ ≤ y³ for 0≤x≤y.
                //   step A: x·x ≤ x·y    (mul_le_left x x y hxy h0x)
                //   step B: x·y ≤ y·y    (mul_le_right y x y hxy h0y)
                //   ⇒ x·x ≤ y·y          (le_trans)
                let h_xx_xy = c.mul_le_left_of(
                    x.clone(),
                    x.clone(),
                    y.clone(),
                    hxy_v.clone(),
                    h0x_v.clone(),
                );
                let h_xy_yy = c.mul_le_right_of(
                    y.clone(),
                    x.clone(),
                    y.clone(),
                    hxy_v.clone(),
                    h0y_v.clone(),
                );
                let xy = c.mul(x.clone(), y.clone());
                let h_xx_yy = c.le_trans_of(xx.clone(), xy.clone(), yy.clone(), h_xx_xy, h_xy_yy);
                //   step C: (x·x)·x ≤ (y·y)·x  (mul_le_right x (x·x) (y·y) h_xx_yy h0x)
                let h_cxx =
                    c.mul_le_right_of(x.clone(), xx.clone(), yy.clone(), h_xx_yy, h0x_v.clone());
                //   step D: (y·y)·x ≤ (y·y)·y  (mul_le_left (y·y) x y hxy h0yy)
                let h0yy = c.sq_nonneg_of(y.clone());
                let yy_x = c.mul(yy.clone(), x.clone());
                let h_cyy = c.mul_le_left_of(yy.clone(), x.clone(), y.clone(), hxy_v, h0yy);
                //   ⇒ (x·x)·x ≤ (y·y)·y  (le_trans)  i.e. x³ ≤ y³
                let h_cube_le =
                    c.le_trans_of(cube_x.clone(), yy_x.clone(), cube_y.clone(), h_cxx, h_cyy);

                // h_relx : rx·rx = x³ ;  h_rely : ry·ry = y³
                let rpow32_sq = Expr::const_(Name::from_string("BoolAnalysis.rpow32_sq"), vec![]);
                let h_relx = Expr::apps(rpow32_sq.clone(), [x.clone(), rx.clone(), hrpx_v]);
                let h_rely = Expr::apps(rpow32_sq, [y.clone(), ry.clone(), hrpy_v]);

                // transport x³ → rx·rx on the LHS: h_relx.symm : x³ = rx·rx
                let h_relx_sym = c.symm(rxrx.clone(), cube_x.clone(), h_relx);
                let motive_l = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(t, cube_y.clone());
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // h1 : rx·rx ≤ y³
                let h1 = c.subst(
                    motive_l,
                    cube_x.clone(),
                    rxrx.clone(),
                    h_relx_sym,
                    h_cube_le,
                );
                // transport y³ → ry·ry on the RHS: h_rely.symm : y³ = ry·ry
                let h_rely_sym = c.symm(ryry.clone(), cube_y.clone(), h_rely);
                let motive_r = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(rxrx.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // h2 : rx·rx ≤ ry·ry
                let h2 = c.subst(motive_r, cube_y.clone(), ryry.clone(), h_rely_sym, h1);

                // le_of_sq_le_sq rx ry (0≤rx) (0≤ry) (rx·rx ≤ ry·ry) : rx ≤ ry
                c.le_of_sq_le_sq_of(rx.clone(), ry.clone(), h0rx_v, h0ry_v, h2)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, bi, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = bind(&b, hrpy_id, BinderInfo::Default, hrpy, tail);
            let e = bind(&b, hrpx_id, BinderInfo::Default, hrpx, e);
            let e = bind(&b, hxy_id, BinderInfo::Default, hxy, e);
            let e = bind(&b, h0ry_id, BinderInfo::Default, h0ry, e);
            let e = bind(&b, h0rx_id, BinderInfo::Default, h0rx, e);
            let e = bind(&b, h0y_id, BinderInfo::Default, h0y, e);
            let e = bind(&b, h0x_id, BinderInfo::Default, h0x, e);
            let e = bind(&b, ry_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, rx_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `BoolAnalysis.sum_rpow32_le_sqrt_eps_mul_sum` — the abstract n-FREE charge
    /// `Σ_i r_i ≤ √ε·Σ_i g_i` whenever `0≤g_i≤ε`, `s·s=ε` (`0≤s`), and each
    /// `r_i` is THE `3/2`-power of `g_i` (`IsRpow32 (g i) (r i)`).
    ///
    /// This is the genuine `n`-free sharp charge the obstruction report
    /// (`2026-06-18-kkl-root-free-obstruction.md` §3) shows the root-free squared
    /// route CANNOT reach (its Cauchy–Schwarz `√n` is fatal). Here the carrier
    /// makes it statable and provable: fact (ii) `rpow32_le_sqrt_eps_mul` gives
    /// `r_i ≤ s·g_i` per coordinate, then `Fin.sum_le` + `Fin.sum_smul` sum it
    /// LINEARLY (no Cauchy–Schwarz, no `√n`). Constructive, empty closure.
    ///
    /// Proof:
    /// 1. per `i`: `rpow32_le_sqrt_eps_mul (g i) ε s (r i) (h_nn i) (h_le i) h0s
    ///    hse (h_rp i) : r i ≤ s·(g i)`.
    /// 2. `Fin.sum_le n r (fun i => s·g i) (per) : Σ r ≤ Σ (s·g)`.
    /// 3. `Fin.sum_smul n s g : Σ (s·g) = s·Σ g`.
    /// 4. `Eq.subst` transports (2) along (3) to `Σ r ≤ s·Σ g`.
    pub fn register_sum_rpow32_le_sqrt_eps_mul_sum(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.sum_rpow32_le_sqrt_eps_mul_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rpow32_le_sqrt_eps_mul()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_le, Fin.sum_smul
        let c = NnRpowConsts::new();

        // hypotheses parameterised over (n, g, eps, s, r):
        //   h_nn  : ∀ i, 0 ≤ g i
        //   h_le  : ∀ i, g i ≤ eps
        //   h0s   : 0 ≤ s
        //   hse   : s·s = eps
        //   h_rp  : ∀ i, IsRpow32 (g i) (r i)
        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let g_ty = c.fin_to_rat(&n);
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let r_ty = c.fin_to_rat(&n);
            let (r_id, r) = b.fresh_local(r_ty.clone());

            let nn_hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let body = c.le0(Expr::app(g.clone(), i));
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
            };
            let le_hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let body = c.le(Expr::app(g.clone(), i), eps.clone());
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
            };
            let h0s = c.le0(s.clone());
            let hse = c.eq(c.mul(s.clone(), s.clone()), eps.clone());
            let rp_hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let gi = Expr::app(g.clone(), i.clone());
                let ri = Expr::app(r.clone(), i);
                let body = c.is_rpow32_of(&gi, &ri);
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
            };

            // integrand `fun i => s · g i`
            let scaled_fn = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let body = c.mul(s.clone(), Expr::app(g.clone(), i));
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

            let lhs = c.sum(&n, r.clone());
            let rhs = c.mul(s.clone(), c.sum(&n, g.clone()));
            let concl = c.le(lhs.clone(), rhs);

            let (hnn_id, hnn_v) = b.fresh_local(nn_hyp.clone());
            let (hle_id, hle_v) = b.fresh_local(le_hyp.clone());
            let (h0s_id, h0s_v) = b.fresh_local(h0s.clone());
            let (hse_id, hse_v) = b.fresh_local(hse.clone());
            let (hrp_id, hrp_v) = b.fresh_local(rp_hyp.clone());

            let tail = if for_value {
                let rpow32_le = Expr::const_(
                    Name::from_string("BoolAnalysis.rpow32_le_sqrt_eps_mul"),
                    vec![],
                );
                // per i : r i ≤ s · g i
                let per = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let fin_n = c.fin_of(&n);
                    let (i_id, i) = d.fresh_local(fin_n.clone());
                    let gi = Expr::app(g.clone(), i.clone());
                    let ri = Expr::app(r.clone(), i.clone());
                    let h_nn_i = Expr::app(hnn_v.clone(), i.clone());
                    let h_le_i = Expr::app(hle_v.clone(), i.clone());
                    let h_rp_i = Expr::app(hrp_v.clone(), i);
                    // rpow32_le_sqrt_eps_mul (g i) eps s (r i) h_nn_i h_le_i h0s hse h_rp_i
                    let body = Expr::apps(
                        rpow32_le.clone(),
                        [
                            gi,
                            eps.clone(),
                            s.clone(),
                            ri,
                            h_nn_i,
                            h_le_i,
                            h0s_v.clone(),
                            hse_v.clone(),
                            h_rp_i,
                        ],
                    );
                    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
                };
                // h_sumle : Σ r ≤ Σ (s·g)
                let h_sumle = Expr::apps(
                    c.fin_sum_le.clone(),
                    [n.clone(), r.clone(), scaled_fn.clone(), per],
                );
                // h_smul : Σ (s·g) = s·Σ g
                let h_smul = Expr::apps(c.fin_sum_smul.clone(), [n.clone(), s.clone(), g.clone()]);
                // motive fun t => Σ r ≤ t
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(lhs.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let a = c.sum(&n, scaled_fn); // Σ (s·g)
                let bb = c.mul(s.clone(), c.sum(&n, g.clone())); // s·Σ g
                c.subst(motive, a, bb, h_smul, h_sumle)
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, bi, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = bind(&b, hrp_id, BinderInfo::Default, rp_hyp, tail);
            let e = bind(&b, hse_id, BinderInfo::Default, hse, e);
            let e = bind(&b, h0s_id, BinderInfo::Default, h0s, e);
            let e = bind(&b, hle_id, BinderInfo::Default, le_hyp, e);
            let e = bind(&b, hnn_id, BinderInfo::Default, nn_hyp, e);
            let e = bind(&b, r_id, BinderInfo::Default, r_ty, e);
            let e = bind(&b, s_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, g_id, BinderInfo::Default, g_ty, e);
            let e = bind(&b, n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `BoolAnalysis.kkl_sum_rpow32_influence_le` — the KKL instance of the
    /// n-free charge: `Σ_i r_i ≤ √ε·I[f]` where `r_i = Inf_i^{3/2}`
    /// (`IsRpow32 (Influence n f i) (r i)`), under `0≤Inf_i≤ε`, `s·s=ε`, `0≤s`.
    ///
    /// Apply `sum_rpow32_le_sqrt_eps_mul_sum n (fun i => Influence n f i) …`; its
    /// RHS `s·Σ_i Influence n f i` is def-eq (δ on the reducible `TotalInfluence`
    /// + η) to `s·TotalInfluence n f`. Constructive, empty closure.
    ///
    /// This is the sharp `n`-free charge `Σ_i Inf_i^{3/2} ≤ √ε·I[f]` — the exact
    /// brick the squared route could not reach. It is the highest carrier-side
    /// rung reachable; the rungs ABOVE it (the dual HC bound
    /// `‖T_{1/3}D_i f‖₂² ≤ 4·Inf_i^{3/2}`, the low-band extraction, the
    /// derivative link) remain unbuilt — see the module/design honesty record.
    pub fn register_kkl_sum_rpow32_influence_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_sum_rpow32_influence_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_sum_rpow32_le_sqrt_eps_mul_sum()?;
        self.init_boolean_analysis()?; // Influence, TotalInfluence (reducible defs)
        let c = NnRpowConsts::new();

        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let r_ty = c.fin_to_rat(&n);
            let (r_id, r) = b.fresh_local(r_ty.clone());

            // `fun i => Influence n f i`
            let infl_fn = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let body = c.influence_of(&n, &f, &i);
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

            let nn_hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let body = c.le0(c.influence_of(&n, &f, &i));
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
            };
            let le_hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let body = c.le(c.influence_of(&n, &f, &i), eps.clone());
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
            };
            let h0s = c.le0(s.clone());
            let hse = c.eq(c.mul(s.clone(), s.clone()), eps.clone());
            let rp_hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let infl = c.influence_of(&n, &f, &i);
                let ri = Expr::app(r.clone(), i);
                let body = c.is_rpow32_of(&infl, &ri);
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
            };

            let lhs = c.sum(&n, r.clone());
            let rhs = c.mul(s.clone(), c.total_influence_of(&n, &f));
            let concl = c.le(lhs, rhs);

            let (hnn_id, hnn_v) = b.fresh_local(nn_hyp.clone());
            let (hle_id, hle_v) = b.fresh_local(le_hyp.clone());
            let (h0s_id, h0s_v) = b.fresh_local(h0s.clone());
            let (hse_id, hse_v) = b.fresh_local(hse.clone());
            let (hrp_id, hrp_v) = b.fresh_local(rp_hyp.clone());

            let tail = if for_value {
                let core = Expr::const_(
                    Name::from_string("BoolAnalysis.sum_rpow32_le_sqrt_eps_mul_sum"),
                    vec![],
                );
                // core n (fun i => Influence n f i) eps s r hnn hle h0s hse hrp
                // : Σ r ≤ s·(Σ (fun i => Influence n f i))  ≡  s·TotalInfluence n f
                Expr::apps(
                    core,
                    [
                        n.clone(),
                        infl_fn,
                        eps.clone(),
                        s.clone(),
                        r.clone(),
                        hnn_v,
                        hle_v,
                        h0s_v,
                        hse_v,
                        hrp_v,
                    ],
                )
            } else {
                concl
            };

            let bind = |b: &EnvDeclBuilder, id, bi, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, bi, ty, body)
                } else {
                    b.mk_pi(id, bi, ty, body)
                }
            };
            let e = bind(&b, hrp_id, BinderInfo::Default, rp_hyp, tail);
            let e = bind(&b, hse_id, BinderInfo::Default, hse, e);
            let e = bind(&b, h0s_id, BinderInfo::Default, h0s, e);
            let e = bind(&b, hle_id, BinderInfo::Default, le_hyp, e);
            let e = bind(&b, hnn_id, BinderInfo::Default, nn_hyp, e);
            let e = bind(&b, r_id, BinderInfo::Default, r_ty, e);
            let e = bind(&b, s_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bind(&b, f_id, BinderInfo::Default, bool_fn_n, e);
            let e = bind(&b, n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }
}

// Recovered (kkl-dualhc-rational): STEP-3 spectral-bridge scaling lemma
// `register_rpow32_scale` (`BoolAnalysis.rpow32_scale`). Shares this module's
// `NnRpowConsts` + imports via textual include, as designed.
include!("boolean_analysis_kkl_nnrpow_scale.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.rpow32_sq",
        "BoolAnalysis.rpow32_sq_le_eps_mul_sq",
        "BoolAnalysis.rpow32_le_sqrt_eps_mul",
        "BoolAnalysis.rpow32_mono",
        "BoolAnalysis.sum_rpow32_le_sqrt_eps_mul_sum",
        "BoolAnalysis.kkl_sum_rpow32_influence_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_nnrpow()
            .expect("init_boolean_analysis_kkl_nnrpow");
        env.init_boolean_analysis_kkl_nnrpow().expect("idempotent");
        env
    }

    /// The carrier `IsRpow32` is a reducible Definition (NOT an Axiom): the
    /// faithful `3/2`-power graph relation. No relocated trust.
    #[test]
    fn test_is_rpow32_is_reducible_definition() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.IsRpow32"))
            .expect("IsRpow32 registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "IsRpow32 must be a Definition, not an Axiom (no relocated trust)"
        );
        assert!(info.value.is_some(), "IsRpow32 must retain its body");
    }

    #[test]
    fn test_nnrpow_facts_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} domain-axiom closure must be empty (no relocated trust)"
            );
        }
    }

    /// The carrier facts are TRUE conditional statements; `refute_conjecture`
    /// must NOT refute any of them on the dictator/parity/constant battery.
    /// (As with the cubecharge bricks, the battery bails at the higher-order /
    /// `IsRpow32`-conditioned binders and returns `None` — the correct verdict.)
    #[test]
    fn test_nnrpow_facts_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            assert_eq!(
                refute_conjecture(&tc, &info.type_),
                None,
                "{name} is a TRUE conditional fact; it must NOT refute"
            );
        }
    }

    /// The carrier itself does not prove `False`: `IsRpow32 x r` for a generic
    /// `x` is a genuine `And` of two refutation-safe atoms; `refute_conjecture`
    /// on `∀ x r, IsRpow32 x r → IsRpow32 x r` (a tautology) is `None`.
    #[test]
    fn test_is_rpow32_carrier_sound() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let c = NnRpowConsts::new();
        // ∀ x r, IsRpow32 x r → IsRpow32 x r  (must not refute).
        let taut = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let hyp = c.is_rpow32_of(&x, &r);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp.clone(), hyp);
            let e = b.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        assert_eq!(
            refute_conjecture(&tc, &taut),
            None,
            "the IsRpow32 carrier tautology must not refute (carrier is sound)"
        );
    }
}
