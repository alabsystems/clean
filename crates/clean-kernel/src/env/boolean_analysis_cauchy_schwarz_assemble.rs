// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — assembly of the finite Cauchy-Schwarz inequality
//! from the per-term Lagrange identity (`Rat.lagrange_term`) and the supporting
//! sum-of-squares nonneg fact (`Fin.sum_cauchy_rhs_nonneg`).
//!
//! This module lands, in dependency order:
//!
//! 1. `Fin.sum_neg : ∀ n f, Fin.sum n (fun i => Rat.neg (f i)) = Rat.neg (Fin.sum n f)`
//!    — the neg-of-sum linearity lemma the cross leg needs (no `Fin.sum_neg`
//!    existed in the kernel; built via the `Σ(0 − f)` route from `Fin.sum_sub`,
//!    `Fin.sum_zero_fn`, `Rat.zero_add`).
//! 2. `Fin.sum_lagrange_identity : ∀ n a b,
//!       Rat.add X X = Fin.sum n (fun i => Fin.sum n (fun j => (aᵢbⱼ − aⱼbᵢ)²))`,
//!    where `X := (Σaᵢ²)·(Σbᵢ²) − (Σaᵢbᵢ)²`. The classical Lagrange identity,
//!    lifted through the double sum: `Fin.sum_congr` rewrites the integrand
//!    pointwise via `Rat.lagrange_term`, `Fin.sum_add` splits the three legs,
//!    `Fin.sum_mul_sum` (×3, one through `Fin.sum_swap`) converts the squared-
//!    factor legs, and the cross leg uses `Fin.sum_smul` + `Fin.sum_neg`.
//! 3. `Fin.sum_cauchy_schwarz : ∀ n a b,
//!       (Σ aᵢbᵢ)² ≤ (Σ aᵢ²)·(Σ bᵢ²)`  — THE finite Cauchy-Schwarz inequality.
//!    Closes by `Rat.nonneg_of_add_self_nonneg` (lifting `0 ≤ X + X` from the
//!    Lagrange RHS being `≥ 0`) followed by `Rat.le_of_sub_nonneg`.
//!
//! Every piece is a kernel-checked `Declaration::Theorem` with empty
//! domain-axiom closure ⇒ `ProofQuality::Constructive`.

use super::boolean_analysis_cauchy_schwarz::CauchyConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the assembly: wraps `CauchyConsts` (which itself wraps
/// `OrderConsts`) and names the extra Fin.sum / Rat lemmas the assembly cites.
struct AssembleConsts {
    c: CauchyConsts,
    fin_sum_sub: Expr,
    fin_sum_zero_fn: Expr,
    fin_sum_add: Expr,
    fin_sum_smul: Expr,
    fin_sum_congr: Expr,
    fin_sum_mul_sum: Expr,
    fin_sum_mul: Expr,
    fin_sum_swap: Expr,
    fin_sum_neg: Expr,
    fin_sum: Expr,
    fin: Expr,
    nat: Expr,
    rat_zero_add: Expr,
    lagrange_term: Expr,
    nonneg_of_add_self: Expr,
    le_of_sub_nonneg: Expr,
    rhs_nonneg: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    two: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl AssembleConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            c: CauchyConsts::new(),
            fin_sum_sub: Expr::const_(Name::from_string("Fin.sum_sub"), vec![]),
            fin_sum_zero_fn: Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]),
            fin_sum_add: Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            fin_sum_smul: Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            fin_sum_mul_sum: Expr::const_(Name::from_string("Fin.sum_mul_sum"), vec![]),
            fin_sum_mul: Expr::const_(Name::from_string("Fin.sum_mul"), vec![]),
            fin_sum_swap: Expr::const_(Name::from_string("Fin.sum_swap"), vec![]),
            fin_sum_neg: Expr::const_(Name::from_string("Fin.sum_neg"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat_zero_add: Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
            lagrange_term: Expr::const_(Name::from_string("Rat.lagrange_term"), vec![]),
            nonneg_of_add_self: Expr::const_(
                Name::from_string("Rat.nonneg_of_add_self_nonneg"),
                vec![],
            ),
            le_of_sub_nonneg: Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]),
            rhs_nonneg: Expr::const_(Name::from_string("Fin.sum_cauchy_rhs_nonneg"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            // (1 + 1) : Rat — the doubling constant `RingConsts::two` produces.
            two: {
                let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
                let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
                Expr::apps(rat_add, [rat_one.clone(), rat_one])
            },
        }
    }

    fn rat(&self) -> Expr {
        self.c.o.rat.clone()
    }
    fn nat(&self) -> Expr {
        self.nat.clone()
    }
    fn zero(&self) -> Expr {
        self.c.o.rat_zero.clone()
    }
    /// `Fin n`.
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `Fin.sum n f`.
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    /// `Fin n → Rat`.
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat())
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.c.o.add(a, b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.c.o.mul(a, b)
    }
    fn neg(&self, a: Expr) -> Expr {
        self.c.o.neg(a)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.c.o.sub(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.c.o.rat_le(a, b)
    }

    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat(), a, b, h])
    }
    /// `congrArg.{1,1} Rat Rat a b g h : g a = g b`.
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, g, h])
    }

    /// `Rat.zero_add a : Rat.add Rat.zero a = a`.
    fn zero_add(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_add.clone(), a)
    }
    /// `fun (i : Fin n) => Rat.neg (f i)` — the neg integrand.
    fn neg_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = self.neg(Expr::app(f.clone(), i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (i : Fin n) => Rat.sub Rat.zero (f i)` — the `0 − f` integrand.
    fn zero_sub_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = self.sub(self.zero(), Expr::app(f.clone(), i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (_ : Fin n) => Rat.zero` — the constant-zero integrand.
    fn zero_const_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = d.fresh_local(fin_n.clone());
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, self.zero()))
    }

    // ── Lagrange-identity integrand pieces (delegate cross/prod to CauchyConsts
    //    so the RHS double-sum is byte-identical to Fin.sum_cauchy_rhs_nonneg's). ──

    /// `2·(−t)` — the doubled-negated leg shape.
    fn two_neg(&self, t: Expr) -> Expr {
        self.mul(self.two.clone(), self.neg(t))
    }
    /// `aₖ·aₗ` (the `prod_fn a a` value at indices `k,l`).
    #[cfg(test)]
    fn aa(&self, a: &Expr, k: &Expr) -> Expr {
        self.mul(
            Expr::app(a.clone(), k.clone()),
            Expr::app(a.clone(), k.clone()),
        )
    }
    /// `aₖ·bₖ` (the `prod_fn a b` value).
    #[cfg(test)]
    fn ab_at(&self, a: &Expr, b: &Expr, k: &Expr) -> Expr {
        self.mul(
            Expr::app(a.clone(), k.clone()),
            Expr::app(b.clone(), k.clone()),
        )
    }
    /// leg A at `(i,j)` := `(aᵢ·aᵢ)·(bⱼ·bⱼ)`.
    fn leg_a(&self, a: &Expr, b: &Expr, i: &Expr, j: &Expr) -> Expr {
        self.mul(
            self.mul(
                Expr::app(a.clone(), i.clone()),
                Expr::app(a.clone(), i.clone()),
            ),
            self.mul(
                Expr::app(b.clone(), j.clone()),
                Expr::app(b.clone(), j.clone()),
            ),
        )
    }
    /// leg B at `(i,j)` := `(aⱼ·aⱼ)·(bᵢ·bᵢ)`.
    fn leg_b(&self, a: &Expr, b: &Expr, i: &Expr, j: &Expr) -> Expr {
        self.mul(
            self.mul(
                Expr::app(a.clone(), j.clone()),
                Expr::app(a.clone(), j.clone()),
            ),
            self.mul(
                Expr::app(b.clone(), i.clone()),
                Expr::app(b.clone(), i.clone()),
            ),
        )
    }
    /// leg C at `(i,j)` := `2·(−((aᵢ·bᵢ)·(aⱼ·bⱼ)))`.
    fn leg_c(&self, a: &Expr, b: &Expr, i: &Expr, j: &Expr) -> Expr {
        let ai_bi = self.mul(
            Expr::app(a.clone(), i.clone()),
            Expr::app(b.clone(), i.clone()),
        );
        let aj_bj = self.mul(
            Expr::app(a.clone(), j.clone()),
            Expr::app(b.clone(), j.clone()),
        );
        self.two_neg(self.mul(ai_bi, aj_bj))
    }
    /// Lagrange-expanded integrand at `(i,j)`:
    /// `((legA i j + legC i j) + legB i j)` — `Rat.lagrange_term`'s RHS shape.
    fn lag(&self, a: &Expr, b: &Expr, i: &Expr, j: &Expr) -> Expr {
        self.add(
            self.add(self.leg_a(a, b, i, j), self.leg_c(a, b, i, j)),
            self.leg_b(a, b, i, j),
        )
    }

    /// `fun (j : Fin n) => integrand(i, j)`, abstracting the inner index.
    /// `fun (j : Fin n) => body_of(d, j)` — the closure receives the child
    /// builder `d` so nested inner lambdas can be `child_of(d)` (correct scope).
    fn inner_fn_of<F: Fn(&EnvDeclBuilder, &Expr) -> Expr>(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        body_of: F,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (j_id, j) = d.fresh_local(fin_n.clone());
        let body = body_of(&d, &j);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (i : Fin n) => body_of(d, i)` — `d` is the child builder of this
    /// lambda, so nested inner functions nest under it.
    fn outer_fn_of<F: Fn(&EnvDeclBuilder, &Expr) -> Expr>(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        body_of: F,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = body_of(&d, &i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `Fin.sum_mul_sum n n F G : (Σ F)·(Σ G) = Σᵢ Σⱼ (F i · G j)`.
    fn sum_mul_sum(&self, n: &Expr, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum_mul_sum.clone(), [n.clone(), n.clone(), f, g])
    }
    /// `Fin.sum_mul n f c : Σᵢ (f i · c) = (Σ f)·c`.
    fn sum_mul(&self, n: &Expr, f: Expr, cc: Expr) -> Expr {
        Expr::apps(self.fin_sum_mul.clone(), [n.clone(), f, cc])
    }
    /// `Fin.sum_smul n c f : Σᵢ (c · f i) = c·(Σ f)`.
    fn sum_smul(&self, n: &Expr, cc: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum_smul.clone(), [n.clone(), cc, f])
    }
    /// `Fin.sum_neg n f : Σᵢ (−f i) = −(Σ f)`.
    fn sum_neg(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum_neg.clone(), [n.clone(), f])
    }
    /// `Fin.sum_add n f g : Σᵢ (f i + g i) = (Σ f) + (Σ g)`.
    fn sum_add(&self, n: &Expr, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum_add.clone(), [n.clone(), f, g])
    }
    /// `Fin.sum_congr n f g h : Σ f = Σ g`  (`h : ∀ i, f i = g i`).
    fn sum_congr(&self, n: &Expr, f: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_congr.clone(), [n.clone(), f, g, h])
    }
    /// `Fin.sum_swap n n F : Σᵢ Σⱼ F i j = Σⱼ Σᵢ F i j`.
    fn sum_swap(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum_swap.clone(), [n.clone(), n.clone(), f])
    }
    /// `@Eq.refl.{1} Rat t : Eq Rat t t` — also inhabits `Eq Rat t' t` for any
    /// `t'` def-eq to `t` (used to bridge β-redex vs expanded leaf terms).
    fn eq_refl(&self, t: Expr) -> Expr {
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_refl, [self.rat(), t])
    }
}

impl Environment {
    /// `Fin.sum_neg : ∀ (n : Nat) (f : Fin n → Rat),
    ///     Fin.sum n (fun i => Rat.neg (f i)) = Rat.neg (Fin.sum n f)`.
    ///
    /// The neg-of-sum linearity lemma (no `Fin.sum_neg` existed in the kernel).
    /// Built via the `Σ(0 − f)` route — `Rat.sub a b ≡ Rat.add a (Rat.neg b)`
    /// is definitional, so (a) `Fin.sum_congr` rewrites `−(f i) → Rat.sub 0 (f i)`
    /// pointwise (`Eq.symm (Rat.zero_add (−(f i)))` — `0 − x ≡ 0 + (−x)`);
    /// (b) `Fin.sum_sub n (fun _ => 0) f` : `Σ(0 − f) = (Σ0) − (Σf)`;
    /// (c) `congrArg (· − Σf) (Fin.sum_zero_fn n)` : `(Σ0) − (Σf) = 0 − (Σf)`;
    /// (d) `Rat.zero_add (−Σf)` : `0 − (Σf) ≡ 0 + (−Σf) = −(Σf)`.
    ///
    /// Kernel-checked, constructive (empty domain-axiom closure). Idempotent.
    pub(crate) fn register_fin_sum_neg_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_sub, Fin.sum_zero_fn, Fin.sum_congr
        self.init_rat_field_inst()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.zero_add
        }

        let c = AssembleConsts::new();
        let (ty, value) = build_sum_neg(&c);
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
}

/// Build the type + proof of `Fin.sum_neg`.
fn build_sum_neg(c: &AssembleConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let f_ty = c.fin_to_rat(&n);
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let lhs = c.sum(n.clone(), c.neg_fn(&b, &n, &f));
        let rhs = c.neg(c.sum(n.clone(), f.clone()));
        let concl = c.eq_rat(lhs, rhs);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let f_ty = c.fin_to_rat(&n);
        let (f_id, f) = b.fresh_local(f_ty.clone());

        let neg_fn = c.neg_fn(&b, &n, &f);
        let zero_sub_fn = c.zero_sub_fn(&b, &n, &f);
        let zero_const_fn = c.zero_const_fn(&b, &n);

        let sum_neg = c.sum(n.clone(), neg_fn.clone());
        let sum_zero_sub = c.sum(n.clone(), zero_sub_fn.clone());
        let sum_zero = c.sum(n.clone(), zero_const_fn.clone());
        let sum_f = c.sum(n.clone(), f.clone());
        let sub_sum0_sumf = c.sub(sum_zero.clone(), sum_f.clone());
        let sub_zero_sumf = c.sub(c.zero(), sum_f.clone());
        let neg_sumf = c.neg(sum_f.clone());

        // step1 : Σ(−f) = Σ(0 − f)   via Fin.sum_congr + pointwise zero_add-symm.
        let h_congr = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(c.fin_of(&n));
            let neg_fi = c.neg(Expr::app(f.clone(), i.clone()));
            // Rat.zero_add (−f i) : 0 + (−f i) = −f i ; symm → −f i = 0 + (−f i)
            //   and 0 + (−f i) ≡ Rat.sub 0 (f i) defeq, so the symm term also
            //   inhabits  −f i = Rat.sub 0 (f i).
            let zero_plus = c.add(c.zero(), neg_fi.clone());
            let h_i = c.symm(zero_plus, neg_fi.clone(), c.zero_add(neg_fi));
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), h_i))
        };
        let step1 = Expr::apps(
            c.fin_sum_congr.clone(),
            [n.clone(), neg_fn.clone(), zero_sub_fn.clone(), h_congr],
        );

        // step2 : Σ(0 − f) = (Σ0) − (Σf)   via Fin.sum_sub n (fun _ => 0) f.
        let step2 = Expr::apps(
            c.fin_sum_sub.clone(),
            [n.clone(), zero_const_fn.clone(), f.clone()],
        );

        // step3 : (Σ0) − (Σf) = 0 − (Σf)   via congrArg (· − Σf) (Fin.sum_zero_fn n).
        let sub_left_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.sub(z, sum_f.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        };
        let sum_zero_fn_eq = Expr::app(c.fin_sum_zero_fn.clone(), n.clone());
        let step3 = c.congr(sum_zero.clone(), c.zero(), sub_left_fn, sum_zero_fn_eq);

        // step4 : 0 − (Σf) = −(Σf)   via Rat.zero_add (−Σf) (0 − x ≡ 0 + (−x)).
        let step4 = c.zero_add(neg_sumf.clone());

        // chain: Σ(−f) = Σ(0−f) = (Σ0)−(Σf) = 0−(Σf) = −(Σf)
        let t12 = c.trans(
            sum_neg.clone(),
            sum_zero_sub.clone(),
            sub_sum0_sumf.clone(),
            step1,
            step2,
        );
        let t123 = c.trans(
            sum_neg.clone(),
            sub_sum0_sumf.clone(),
            sub_zero_sumf.clone(),
            t12,
            step3,
        );
        let proof = c.trans(sum_neg, sub_zero_sumf, neg_sumf, t123, step4);

        let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    (ty, value)
}

impl Environment {
    /// `Fin.sum_lagrange_identity : ∀ (n : Nat) (a b : Fin n → Rat),
    ///   Fin.sum n (fun i => Fin.sum n (fun j => (aᵢbⱼ − aⱼbᵢ)²))
    ///     = Rat.add X X`,  where `X := (Σ aᵢ²)·(Σ bᵢ²) − (Σ aᵢbᵢ)²`.
    ///
    /// The classical finite Lagrange identity. The double-sum-of-squares (LHS,
    /// byte-identical to `Fin.sum_cauchy_rhs_nonneg`'s subject) equals the doubled
    /// Cauchy-Schwarz defect `X`. Proof: `Fin.sum_congr` (×2) rewrites each
    /// `(cross i j)²` to the per-term `Rat.lagrange_term` RHS, `Fin.sum_add`
    /// splits the three legs, `Fin.sum_mul_sum` (×2, one through `Fin.sum_swap`)
    /// converts the squared-factor legs, the cross leg uses `Fin.sum_smul`/
    /// `Fin.sum_mul`/`Fin.sum_neg`, and a closed Rat regroup finishes.
    /// Kernel-checked, constructive (empty domain-axiom closure). Idempotent.
    pub(crate) fn register_fin_sum_lagrange_identity_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_lagrange_identity");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_rat_field_inst()?;
        self.register_fin_sum_neg_theorem()?;
        self.register_fin_sum_mul_theorem()?;
        self.register_fin_sum_mul_sum_theorem()?;
        self.register_fin_sum_swap_theorem()?;
        self.register_rat_lagrange_term()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }

        let c = AssembleConsts::new();
        let (ty, value) = build_lagrange_identity(&c);
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
}

/// Build the type + proof of `Fin.sum_lagrange_identity`.
fn build_lagrange_identity(c: &AssembleConsts) -> (Expr, Expr) {
    let f_g_ty = |b: &EnvDeclBuilder, n: &Expr| {
        let _ = b;
        c.fin_to_rat(n)
    };

    // The doubled Cauchy-Schwarz defect `X := (Σa²)·(Σb²) − (Σab)²`, at fixed a,b.
    let x_of = |b: &EnvDeclBuilder, n: &Expr, a: &Expr, bv: &Expr| -> Expr {
        let sa2 = c.c.sum(n.clone(), c.c.prod_fn(b, n, a, a));
        let sb2 = c.c.sum(n.clone(), c.c.prod_fn(b, n, bv, bv));
        let sab = c.c.sum(n.clone(), c.c.prod_fn(b, n, a, bv));
        c.sub(c.mul(sa2, sb2), c.mul(sab.clone(), sab))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let fty = f_g_ty(&b, &n);
        let (a_id, a) = b.fresh_local(fty.clone());
        let (bb_id, bv) = b.fresh_local(fty.clone());
        let lhs = c.c.sum(n.clone(), c.c.outer_cross_fn(&b, &n, &a, &bv));
        let x = x_of(&b, &n, &a, &bv);
        let rhs = c.add(x.clone(), x);
        let concl = c.eq_rat(lhs, rhs);
        let e = b.mk_pi(bb_id, BinderInfo::Default, fty.clone(), concl);
        let e = b.mk_pi(a_id, BinderInfo::Default, fty, e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let fty = f_g_ty(&b, &n);
        let (a_id, a) = b.fresh_local(fty.clone());
        let (bb_id, bv) = b.fresh_local(fty.clone());
        let proof = lagrange_proof(c, &b, &n, &a, &bv, &x_of);
        let e = b.mk_lam(bb_id, BinderInfo::Default, fty.clone(), proof);
        let e = b.mk_lam(a_id, BinderInfo::Default, fty, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    (ty, value)
}

impl Environment {
    /// `Fin.sum_cauchy_schwarz : ∀ (n : Nat) (a b : Fin n → Rat),
    ///   Rat.le (Rat.mul (Σ aᵢbᵢ) (Σ aᵢbᵢ)) (Rat.mul (Σ aᵢ²) (Σ bᵢ²))`
    ///
    /// i.e. `(Σ aᵢbᵢ)² ≤ (Σ aᵢ²)·(Σ bᵢ²)` — THE finite Cauchy-Schwarz inequality,
    /// the last missing classical inequality. Assembled from:
    /// (a) `Fin.sum_cauchy_rhs_nonneg` : `0 ≤ R` (R = Σᵢ Σⱼ (cross)²);
    /// (b) `Fin.sum_lagrange_identity` : `R = X + X` (X = (Σa²)(Σb²) − (Σab)²);
    /// (c) `Eq.subst` transports (a) along (b) ⇒ `0 ≤ X + X`;
    /// (d) `Rat.nonneg_of_add_self_nonneg X` ⇒ `0 ≤ X`;
    /// (e) `Rat.le_of_sub_nonneg (Σab)² ((Σa²)(Σb²))` ⇒ the stated inequality.
    ///
    /// Kernel-checked, constructive (empty domain-axiom closure). Idempotent.
    pub(crate) fn register_fin_sum_cauchy_schwarz_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_cauchy_schwarz");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.register_fin_sum_cauchy_rhs_nonneg()?;
        self.register_fin_sum_lagrange_identity_theorem()?;
        self.register_rat_nonneg_of_add_self_nonneg()?;
        // `Rat.le_of_sub_nonneg` lives in the nn_verify Rat ordering layer.
        self.init_nn_verify_rat_ordering()?;

        let c = AssembleConsts::new();
        let (ty, value) = build_cauchy_schwarz(&c);
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
}

/// Build the type + proof of `Fin.sum_cauchy_schwarz`.
fn build_cauchy_schwarz(c: &AssembleConsts) -> (Expr, Expr) {
    let fty = |n: &Expr| c.fin_to_rat(n);

    // Helper closures producing the three sums at fixed builder/a/b.
    let sums = |b: &EnvDeclBuilder, n: &Expr, a: &Expr, bv: &Expr| -> (Expr, Expr, Expr) {
        let sa2 = c.c.sum(n.clone(), c.c.prod_fn(b, n, a, a));
        let sb2 = c.c.sum(n.clone(), c.c.prod_fn(b, n, bv, bv));
        let sab = c.c.sum(n.clone(), c.c.prod_fn(b, n, a, bv));
        (sa2, sb2, sab)
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let (a_id, a) = b.fresh_local(fty(&n));
        let (bb_id, bv) = b.fresh_local(fty(&n));
        let (sa2, sb2, sab) = sums(&b, &n, &a, &bv);
        let lhs = c.mul(sab.clone(), sab);
        let rhs = c.mul(sa2, sb2);
        let concl = c.le(lhs, rhs);
        let e = b.mk_pi(bb_id, BinderInfo::Default, fty(&n), concl);
        let e = b.mk_pi(a_id, BinderInfo::Default, fty(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let (a_id, a) = b.fresh_local(fty(&n));
        let (bb_id, bv) = b.fresh_local(fty(&n));
        let (sa2, sb2, sab) = sums(&b, &n, &a, &bv);
        let big_a = c.mul(sa2.clone(), sb2.clone());
        let big_p = c.mul(sab.clone(), sab.clone());
        let x = c.sub(big_a.clone(), big_p.clone());

        // R := Σᵢ Σⱼ (cross)²  (the rhs-nonneg subject = lagrange LHS).
        let r = c.c.sum(n.clone(), c.c.outer_cross_fn(&b, &n, &a, &bv));

        // h_nonneg : 0 ≤ R
        let h_nonneg = Expr::apps(c.rhs_nonneg.clone(), [n.clone(), a.clone(), bv.clone()]);
        // h_lag : R = X + X
        let h_lag = Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_lagrange_identity"), vec![]),
            [n.clone(), a.clone(), bv.clone()],
        );
        // motive : fun z => Rat.le 0 z
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.le(c.zero(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        };
        // h_xx : 0 ≤ X + X   via Eq.subst motive R (X+X) h_lag h_nonneg
        let xx = c.add(x.clone(), x.clone());
        let h_xx = c.c.o.subst(motive, r, xx, h_lag, h_nonneg);
        // h_x : 0 ≤ X   via Rat.nonneg_of_add_self_nonneg X h_xx
        let h_x = Expr::apps(c.nonneg_of_add_self.clone(), [x.clone(), h_xx]);
        // Rat.le_of_sub_nonneg (Σab)² ((Σa²)(Σb²)) h_x : (Σab)² ≤ (Σa²)(Σb²)
        //   (X ≡ (Σa²)(Σb²) − (Σab)² is le_of_sub_nonneg's `b − a` at a=(Σab)², b=A.)
        let proof = Expr::apps(c.le_of_sub_nonneg.clone(), [big_p, big_a, h_x]);

        let e = b.mk_lam(bb_id, BinderInfo::Default, fty(&n), proof);
        let e = b.mk_lam(a_id, BinderInfo::Default, fty(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    (ty, value)
}

/// The core proof of `Fin.sum_lagrange_identity` at free `n, a, b`.
///
/// Names: `A := Σa²·Σb²`, `P := Σab·Σab`, `X := A − P`. We chain
///   `R = Σᵢ Σⱼ (cross i j)²`                                  (subject)
///     = Σᵢ Σⱼ ((legA i j + legC i j) + legB i j)              [lagrange_term]
///     = (Σᵢ Σⱼ legA + Σᵢ Σⱼ legC) + Σᵢ Σⱼ legB                [Fin.sum_add ×3]
///     = (A + 2·(−P)) + A                                      [leg conversions]
///     = X + X                                                 [closed Rat regroup]
fn lagrange_proof<F>(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    bv: &Expr,
    x_of: &F,
) -> Expr
where
    F: Fn(&EnvDeclBuilder, &Expr, &Expr, &Expr) -> Expr,
{
    // Inner integrand functions, parameterized by the builder of the enclosing
    // outer lambda (`d`) and the outer index `i`. Each `Σⱼ leg i j`.
    let lega_inner = |d: &EnvDeclBuilder, i: &Expr| {
        let i = i.clone();
        c.inner_fn_of(d, n, move |_e, j| c.leg_a(a, bv, &i, j))
    };
    let legb_inner = |d: &EnvDeclBuilder, i: &Expr| {
        let i = i.clone();
        c.inner_fn_of(d, n, move |_e, j| c.leg_b(a, bv, &i, j))
    };
    let legc_inner = |d: &EnvDeclBuilder, i: &Expr| {
        let i = i.clone();
        c.inner_fn_of(d, n, move |_e, j| c.leg_c(a, bv, &i, j))
    };
    let lag_inner = |d: &EnvDeclBuilder, i: &Expr| {
        let i = i.clone();
        c.inner_fn_of(d, n, move |_e, j| c.lag(a, bv, &i, j))
    };

    let sum_inner = |f: Expr| c.c.sum(n.clone(), f);

    // Outer integrand functions.
    let outer_lag = c.outer_fn_of(b, n, |d, i| sum_inner(lag_inner(d, i)));
    let outer_lega = c.outer_fn_of(b, n, |d, i| sum_inner(lega_inner(d, i)));
    let outer_legb = c.outer_fn_of(b, n, |d, i| sum_inner(legb_inner(d, i)));
    let outer_legc = c.outer_fn_of(b, n, |d, i| sum_inner(legc_inner(d, i)));
    // `fun i => (Σⱼ legA + Σⱼ legC)` and `fun i => ((Σⱼ legA + Σⱼ legC) + Σⱼ legB)`.
    let outer_ac = c.outer_fn_of(b, n, |d, i| {
        c.add(sum_inner(lega_inner(d, i)), sum_inner(legc_inner(d, i)))
    });
    let outer_acb = c.outer_fn_of(b, n, |d, i| {
        c.add(
            c.add(sum_inner(lega_inner(d, i)), sum_inner(legc_inner(d, i))),
            sum_inner(legb_inner(d, i)),
        )
    });

    let cross_outer = c.c.outer_cross_fn(b, n, a, bv);
    let r = c.c.sum(n.clone(), cross_outer.clone());

    // ── S1 : R = Σᵢ Σⱼ lag   via outer Fin.sum_congr (inner = per-term lagrange) ──
    let h_outer_lag = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (i_id, i) = d.fresh_local(c.fin_of(n));
        // inner congr: Σⱼ cross_sq i j = Σⱼ lag i j
        let cross_inner = c.c.inner_cross_fn(&d, n, a, bv, &i);
        let lag_inner_i = lag_inner(&d, &i);
        let h_inner = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (j_id, j) = e.fresh_local(c.fin_of(n));
            // Rat.lagrange_term aᵢ aⱼ bᵢ bⱼ : cross_sq i j = lag i j
            let term = Expr::apps(
                c.lagrange_term.clone(),
                [
                    Expr::app(a.clone(), i.clone()),
                    Expr::app(a.clone(), j.clone()),
                    Expr::app(bv.clone(), i.clone()),
                    Expr::app(bv.clone(), j.clone()),
                ],
            );
            e.finish_child(e.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), term))
        };
        let h_i = c.sum_congr(n, cross_inner, lag_inner_i, h_inner);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), h_i))
    };
    let s1 = c.sum_congr(n, cross_outer, outer_lag.clone(), h_outer_lag);
    let sum_outer_lag = c.c.sum(n.clone(), outer_lag);

    // ── S2 : Σᵢ Σⱼ lag = Σᵢ ((Σⱼ legA + Σⱼ legC) + Σⱼ legB)
    //         via outer Fin.sum_congr; per-i inner is two Fin.sum_add. ──
    let h_outer_split = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (i_id, i) = d.fresh_local(c.fin_of(n));
        // Σⱼ lag i j = Σⱼ ((legA+legC) + legB) j
        //   = (Σⱼ (legA+legC) j) + (Σⱼ legB j)        [Fin.sum_add]
        //   = ((Σⱼ legA) + (Σⱼ legC)) + (Σⱼ legB)     [Fin.sum_add on the head]
        let ac_inner = c.inner_fn_of(&d, n, {
            let i = i.clone();
            move |_e, j| c.add(c.leg_a(a, bv, &i, j), c.leg_c(a, bv, &i, j))
        });
        // step a: Σⱼ lag = (Σⱼ (legA+legC)) + (Σⱼ legB)
        let split1 = c.sum_add(n, ac_inner.clone(), legb_inner(&d, &i));
        // step b: Σⱼ (legA+legC) = (Σⱼ legA) + (Σⱼ legC)
        let split2 = c.sum_add(n, lega_inner(&d, &i), legc_inner(&d, &i));
        // congr: lift split2 over `(· + Σⱼ legB)`
        let sum_ac = sum_inner(ac_inner);
        let sum_lega = sum_inner(lega_inner(&d, &i));
        let sum_legc = sum_inner(legc_inner(&d, &i));
        let sum_legb = sum_inner(legb_inner(&d, &i));
        let add_legb_fn = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (z_id, z) = e.fresh_local(c.rat());
            let body = c.add(z, sum_legb.clone());
            e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        };
        let split2_lifted = c.congr(
            sum_ac.clone(),
            c.add(sum_lega.clone(), sum_legc.clone()),
            add_legb_fn,
            split2,
        );
        // chain: Σⱼ lag = (Σⱼ ac) + Σⱼ legB = ((Σⱼ legA)+(Σⱼ legC)) + Σⱼ legB
        let lhs_i = sum_inner(lag_inner(&d, &i));
        let mid_i = c.add(sum_ac, sum_legb.clone());
        let rhs_i = c.add(c.add(sum_lega, sum_legc), sum_legb);
        let h_i = c.trans(lhs_i, mid_i, rhs_i, split1, split2_lifted);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), h_i))
    };
    let s2 = c.sum_congr(
        n,
        c.outer_fn_of(b, n, |d, i| sum_inner(lag_inner(d, i))),
        outer_acb.clone(),
        h_outer_split,
    );
    let sum_outer_acb = c.c.sum(n.clone(), outer_acb);

    // ── S3 : Σᵢ ((Σⱼ legA + Σⱼ legC) + Σⱼ legB)
    //         = (Σᵢ (Σⱼ legA + Σⱼ legC)) + (Σᵢ Σⱼ legB)        [Fin.sum_add]
    //         = ((Σᵢ Σⱼ legA) + (Σᵢ Σⱼ legC)) + (Σᵢ Σⱼ legB)   [Fin.sum_add + congr] ──
    let sum_outer_ac = c.c.sum(n.clone(), outer_ac.clone());
    let sum_outer_lega = c.c.sum(n.clone(), outer_lega.clone());
    let sum_outer_legc = c.c.sum(n.clone(), outer_legc.clone());
    let sum_outer_legb = c.c.sum(n.clone(), outer_legb.clone());
    let s3a = c.sum_add(n, outer_ac.clone(), outer_legb.clone());
    let s3b = c.sum_add(n, outer_lega.clone(), outer_legc.clone());
    let add_outer_legb_fn = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.add(z, sum_outer_legb.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let s3b_lifted = c.congr(
        sum_outer_ac.clone(),
        c.add(sum_outer_lega.clone(), sum_outer_legc.clone()),
        add_outer_legb_fn,
        s3b,
    );
    let split_mid = c.add(sum_outer_ac, sum_outer_legb.clone());
    let split_rhs = c.add(
        c.add(sum_outer_lega.clone(), sum_outer_legc.clone()),
        sum_outer_legb.clone(),
    );
    let s3 = c.trans(
        sum_outer_acb.clone(),
        split_mid,
        split_rhs.clone(),
        s3a,
        s3b_lifted,
    );

    // ── S4 : convert each double-leg. ──
    let aa_fn = c.c.prod_fn(b, n, a, a);
    let bb_fn = c.c.prod_fn(b, n, bv, bv);
    let ab_fn = c.c.prod_fn(b, n, a, bv);
    let sa2 = c.c.sum(n.clone(), aa_fn.clone());
    let sb2 = c.c.sum(n.clone(), bb_fn.clone());
    let sab = c.c.sum(n.clone(), ab_fn.clone());
    let big_a = c.mul(sa2.clone(), sb2.clone());
    let big_p = c.mul(sab.clone(), sab.clone());

    let h_lega = leg_a_eq(c, b, n, a, bv, &outer_lega, &big_a);
    let h_legb = leg_b_eq(c, b, n, a, bv, &outer_legb, &big_a);
    let h_legc = leg_c_eq(c, b, n, a, bv, &outer_legc, &big_p);

    // (Σlega + Σlegc) + Σlegb  =  (A + 2·(−P)) + A
    let two_neg_p = c.two_neg(big_p.clone());
    // congr left: (Σlega + Σlegc) = (A + 2·(−P))   [congr both addends via h_lega, h_legc]
    let head_via_a = c.add(big_a.clone(), sum_outer_legc.clone());
    let cong_lega = c.congr(
        sum_outer_lega.clone(),
        big_a.clone(),
        {
            let mut d = EnvDeclBuilder::child_of(b);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.add(z, sum_outer_legc.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        },
        h_lega,
    );
    let cong_legc = c.congr(
        sum_outer_legc.clone(),
        two_neg_p.clone(),
        {
            let mut d = EnvDeclBuilder::child_of(b);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.add(big_a.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        },
        h_legc,
    );
    let head_via_ac = c.add(big_a.clone(), two_neg_p.clone());
    let cong_head = c.trans(
        c.add(sum_outer_lega.clone(), sum_outer_legc.clone()),
        head_via_a,
        head_via_ac.clone(),
        cong_lega,
        cong_legc,
    );
    // lift cong_head over (· + Σlegb), then congr the legb tail via h_legb.
    let cong_head_lifted = c.congr(
        c.add(sum_outer_lega.clone(), sum_outer_legc.clone()),
        head_via_ac.clone(),
        {
            let mut d = EnvDeclBuilder::child_of(b);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.add(z, sum_outer_legb.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        },
        cong_head,
    );
    let e_mid = c.add(head_via_ac.clone(), sum_outer_legb.clone());
    let cong_legb_tail = c.congr(
        sum_outer_legb.clone(),
        big_a.clone(),
        {
            let mut d = EnvDeclBuilder::child_of(b);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.add(head_via_ac.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        },
        h_legb,
    );
    let e_final = c.add(head_via_ac.clone(), big_a.clone());
    let s4 = c.trans(
        split_rhs.clone(),
        e_mid,
        e_final.clone(),
        cong_head_lifted,
        cong_legb_tail,
    );

    // ── S5 : (A + 2·(−P)) + A = X + X   [closed Rat regroup, X = A − P ≡ A + (−P)] ──
    let x = x_of(b, n, a, bv);
    let s5 = rat_regroup(c, b, &big_a, &big_p, &x);

    // chain: R = sum_outer_lag = sum_outer_acb = split_rhs = e_final = X+X
    let t1 = c.trans(
        r.clone(),
        sum_outer_lag.clone(),
        sum_outer_acb.clone(),
        s1,
        s2,
    );
    let t2 = c.trans(r.clone(), sum_outer_acb.clone(), split_rhs.clone(), t1, s3);
    let t3 = c.trans(r.clone(), split_rhs, e_final.clone(), t2, s4);
    c.trans(r, e_final, c.add(x.clone(), x), t3, s5)
}

/// `Σᵢ Σⱼ legA = A`  where `legA i j = (aᵢaᵢ)(bⱼbⱼ)`, `A = (Σ aa)·(Σ bb)`.
/// `Fin.sum_mul_sum n n aa bb : A = Σᵢ Σⱼ (aa i · bb j)`, and `aa i · bb j = legA`,
/// `outer_lega = fun i => Σⱼ (aa i · bb j)` byte-identically, so `symm` of mul_sum.
fn leg_a_eq(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    bv: &Expr,
    outer_lega: &Expr,
    big_a: &Expr,
) -> Expr {
    let aa_fn = c.c.prod_fn(b, n, a, a);
    let bb_fn = c.c.prod_fn(b, n, bv, bv);
    // mul_sum : big_a = Σᵢ Σⱼ (aa i · bb j)   [applied prod_fn form]
    let mul_sum = c.sum_mul_sum(n, aa_fn.clone(), bb_fn.clone());
    let applied_outer = applied_mul_outer(c, b, n, &aa_fn, &bb_fn, false);
    let applied_sum = c.c.sum(n.clone(), applied_outer);
    let sum_outer = c.c.sum(n.clone(), outer_lega.clone());
    // bridge : Σᵢ Σⱼ (aa i·bb j) = Σ outer_lega  (β-defeq leaf rewrite, Eq.refl)
    let bridge = beta_bridge_a(c, b, n, a, bv, &aa_fn, &bb_fn);
    // chain: Σ outer_lega =(symm bridge)= applied_sum =(symm mul_sum)= big_a
    let symm_bridge = c.symm(applied_sum.clone(), sum_outer.clone(), bridge);
    let symm_mul = c.symm(big_a.clone(), applied_sum.clone(), mul_sum);
    c.trans(sum_outer, applied_sum, big_a.clone(), symm_bridge, symm_mul)
}

/// `fun i => Σⱼ (F i · G j)` (or `fun j => Σᵢ (F i · G j)` when `swap`) — the
/// applied-product outer integrand `Fin.sum_mul_sum`'s RHS is built from.
fn applied_mul_outer(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    g: &Expr,
    swap: bool,
) -> Expr {
    c.outer_fn_of(b, n, |d, p| {
        let p = p.clone();
        let inner = c.inner_fn_of(d, n, move |_e, q| {
            if swap {
                c.mul(
                    Expr::app(f.clone(), q.clone()),
                    Expr::app(g.clone(), p.clone()),
                )
            } else {
                c.mul(
                    Expr::app(f.clone(), p.clone()),
                    Expr::app(g.clone(), q.clone()),
                )
            }
        });
        c.c.sum(n.clone(), inner)
    })
}

/// `Σᵢ Σⱼ (aa i·bb j) = Σᵢ Σⱼ legA(i,j)` — both sides β-defeq leaf-wise, bridged
/// by nested `Fin.sum_congr` with `Eq.refl` (the kernel reduces the leaf Rat, not
/// the symbolic sum).
fn beta_bridge_a(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    bv: &Expr,
    aa_fn: &Expr,
    bb_fn: &Expr,
) -> Expr {
    let applied_outer = applied_mul_outer(c, b, n, aa_fn, bb_fn, false);
    let expanded_outer = c.outer_fn_of(b, n, |d, i| {
        let i = i.clone();
        let inner = c.inner_fn_of(d, n, move |_e, j| c.leg_a(a, bv, &i, j));
        c.c.sum(n.clone(), inner)
    });
    // h_outer : ∀ i, Σⱼ (aa i·bb j) = Σⱼ legA(i,j)
    let h_outer = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (i_id, i) = d.fresh_local(c.fin_of(n));
        let applied_inner = c.inner_fn_of(&d, n, {
            let i = i.clone();
            move |_e, j| {
                c.mul(
                    Expr::app(aa_fn.clone(), i.clone()),
                    Expr::app(bb_fn.clone(), j.clone()),
                )
            }
        });
        let expanded_inner = c.inner_fn_of(&d, n, {
            let i = i.clone();
            move |_e, j| c.leg_a(a, bv, &i, j)
        });
        let h_inner = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (j_id, j) = e.fresh_local(c.fin_of(n));
            // Eq.refl (legA i j) : legA i j = legA i j, used as (aa i·bb j)=legA (β).
            let refl = c.eq_refl(c.leg_a(a, bv, &i, &j));
            e.finish_child(e.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), refl))
        };
        let h_i = c.sum_congr(n, applied_inner, expanded_inner, h_inner);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), h_i))
    };
    c.sum_congr(n, applied_outer, expanded_outer, h_outer)
}

/// `Σᵢ Σⱼ legB = A`  where `legB i j = (aⱼaⱼ)(bᵢbᵢ)`.
/// `Fin.sum_swap` turns `Σᵢ Σⱼ (aa j · bb i)` into `Σⱼ Σᵢ (aa j · bb i)`, which is
/// `Fin.sum_mul_sum`'s RHS for `(aa, bb)` ⇒ `= A`.
fn leg_b_eq(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    bv: &Expr,
    outer_legb: &Expr,
    big_a: &Expr,
) -> Expr {
    let aa_fn = c.c.prod_fn(b, n, a, a);
    let bb_fn = c.c.prod_fn(b, n, bv, bv);
    let sum_outer_legb = c.c.sum(n.clone(), outer_legb.clone());

    // F i j := legB i j = (aⱼaⱼ)(bᵢbᵢ)  (expanded, the two-arg integrand swap takes).
    let f2 = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (i_id, i) = d.fresh_local(c.fin_of(n));
        let inner = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (j_id, j) = e.fresh_local(c.fin_of(n));
            let body = c.leg_b(a, bv, &i, &j);
            e.finish_child(e.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), body))
        };
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), inner))
    };
    // swap : Σᵢ Σⱼ legB(i,j) = Σⱼ Σᵢ legB(i,j)   [both expanded]
    let swap = c.sum_swap(n, f2);
    // swapped (expanded): Σⱼ Σᵢ legB(i,j)
    let swapped_outer = c.outer_fn_of(b, n, |d, j| {
        let j = j.clone();
        let inner = c.inner_fn_of(d, n, move |_e, i| c.leg_b(a, bv, i, &j));
        c.c.sum(n.clone(), inner)
    });
    let swapped_sum = c.c.sum(n.clone(), swapped_outer);
    // mul_sum : big_a = Σ_p Σ_q (aa p · bb q)   [applied]
    let mul_sum = c.sum_mul_sum(n, aa_fn.clone(), bb_fn.clone());
    let applied_outer = applied_mul_outer(c, b, n, &aa_fn, &bb_fn, false);
    let applied_sum = c.c.sum(n.clone(), applied_outer);
    // bridge_b : Σⱼ Σᵢ legB(i,j) = Σ_p Σ_q (aa p · bb q)   [β-defeq leaf, Eq.refl]
    let bridge_b = beta_bridge_b(c, b, n, a, bv, &aa_fn, &bb_fn);
    // chain: Σᵢ Σⱼ legB =(swap)= swapped_sum =(bridge_b)= applied_sum =(symm mul_sum)= big_a
    let symm_mul = c.symm(big_a.clone(), applied_sum.clone(), mul_sum);
    let t1 = c.trans(
        sum_outer_legb.clone(),
        swapped_sum.clone(),
        applied_sum.clone(),
        swap,
        bridge_b,
    );
    c.trans(sum_outer_legb, applied_sum, big_a.clone(), t1, symm_mul)
}

/// `Σⱼ Σᵢ legB(i,j) = Σ_p Σ_q (aa p · bb q)` — the swapped expanded legB equals the
/// applied product double-sum (β-defeq leaf-wise), bridged by nested `Fin.sum_congr`
/// + `Eq.refl`. With outer `p=j`, inner `q=i`: `(aa j)·(bb i)` β= `(aⱼaⱼ)(bᵢbᵢ)` = legB.
fn beta_bridge_b(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    bv: &Expr,
    aa_fn: &Expr,
    bb_fn: &Expr,
) -> Expr {
    // LHS outer: fun j => Σᵢ legB(i,j) ;  RHS outer: fun p => Σ_q (aa p·bb q).
    let swapped_outer = c.outer_fn_of(b, n, |d, j| {
        let j = j.clone();
        let inner = c.inner_fn_of(d, n, move |_e, i| c.leg_b(a, bv, i, &j));
        c.c.sum(n.clone(), inner)
    });
    let applied_outer = applied_mul_outer(c, b, n, aa_fn, bb_fn, false);
    let h_outer = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (j_id, j) = d.fresh_local(c.fin_of(n));
        let swapped_inner = c.inner_fn_of(&d, n, {
            let j = j.clone();
            move |_e, i| c.leg_b(a, bv, i, &j)
        });
        let applied_inner = c.inner_fn_of(&d, n, {
            let j = j.clone();
            move |_e, i| {
                c.mul(
                    Expr::app(aa_fn.clone(), j.clone()),
                    Expr::app(bb_fn.clone(), i.clone()),
                )
            }
        });
        let h_inner = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (i_id, i) = e.fresh_local(c.fin_of(n));
            let refl = c.eq_refl(c.leg_b(a, bv, &i, &j));
            e.finish_child(e.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), refl))
        };
        // h_j : Σᵢ legB(i,j) = Σ_q (aa j · bb q)
        let h_j = c.sum_congr(n, swapped_inner, applied_inner, h_inner);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), h_j))
    };
    c.sum_congr(n, swapped_outer, applied_outer, h_outer)
}

/// `Σᵢ Σⱼ legC = 2·(−P)`  where `legC i j = 2·(−((aᵢbᵢ)(aⱼbⱼ)))`, `P = (Σab)²`.
/// Inner: `Σⱼ 2·(−(ab i·ab j)) = 2·(−(ab i·Σab))` via smul/neg/smul.
/// Outer: `Σᵢ 2·(−(ab i·Σab)) = 2·(−(Σab·Σab))` via smul/neg/mul.
fn leg_c_eq(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    bv: &Expr,
    outer_legc: &Expr,
    big_p: &Expr,
) -> Expr {
    let ab_fn = c.c.prod_fn(b, n, a, bv);
    let sab = c.c.sum(n.clone(), ab_fn.clone());
    let sum_outer_legc = c.c.sum(n.clone(), outer_legc.clone());

    // ── B0 : bridge outer_legc (expanded) → applied form, leaf-wise Eq.refl. ──
    // outer_app i := Σⱼ 2·(−(ab_app i · ab_app j))  [applied].
    let outer_app = c.outer_fn_of(b, n, |d, i| {
        let i = i.clone();
        let ab_fn = ab_fn.clone();
        let inner = c.inner_fn_of(d, n, {
            let i = i.clone();
            move |_e, j| c.two_neg(c.mul(ab_app_of(&ab_fn, &i), ab_app_of(&ab_fn, j)))
        });
        c.c.sum(n.clone(), inner)
    });
    let sum_outer_app = c.c.sum(n.clone(), outer_app);
    let bridge0 = {
        let h_outer = {
            let mut d = EnvDeclBuilder::child_of(b);
            let (i_id, i) = d.fresh_local(c.fin_of(n));
            let exp_inner = c.inner_fn_of(&d, n, {
                let i = i.clone();
                move |_e, j| c.leg_c(a, bv, &i, j)
            });
            let app_inner = c.inner_fn_of(&d, n, {
                let i = i.clone();
                let ab_fn = ab_fn.clone();
                move |_e, j| c.two_neg(c.mul(ab_app_of(&ab_fn, &i), ab_app_of(&ab_fn, j)))
            });
            let h_inner = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (j_id, j) = e.fresh_local(c.fin_of(n));
                // applied = expanded β; Eq.refl on the applied leaf inhabits both.
                let refl =
                    c.eq_refl(c.two_neg(c.mul(ab_app_of(&ab_fn, &i), ab_app_of(&ab_fn, &j))));
                e.finish_child(e.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), refl))
            };
            let h_i = c.sum_congr(n, exp_inner, app_inner, h_inner);
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), h_i))
        };
        // outer_legc (expanded) = outer_app (applied).
        let outer_app2 = c.outer_fn_of(b, n, |d, i| {
            let i = i.clone();
            let inner = c.inner_fn_of(d, n, {
                let i = i.clone();
                let ab_fn = ab_fn.clone();
                move |_e, j| c.two_neg(c.mul(ab_app_of(&ab_fn, &i), ab_app_of(&ab_fn, j)))
            });
            c.c.sum(n.clone(), inner)
        });
        c.sum_congr(n, outer_legc.clone(), outer_app2, h_outer)
    };

    // ── per-i inner reduction (applied):  Σⱼ 2·(−(ab i·ab j)) = 2·(−(ab i·Σab)) ──
    // `bd` MUST be the builder of the enclosing outer lambda (next_fvar past `i`),
    // so the inner `j` does not collide with `i`'s FVarId.
    let inner_eq = |bd: &EnvDeclBuilder, i: &Expr| -> Expr {
        let i = i.clone();
        let abi = ab_app_of(&ab_fn, &i);
        // g j := −(ab i · ab j)
        let g_fn = c.inner_fn_of(bd, n, {
            let abi = abi.clone();
            let ab_fn = ab_fn.clone();
            move |_e, j| c.neg(c.mul(abi.clone(), ab_app_of(&ab_fn, j)))
        });
        let smul = c.sum_smul(n, c.two.clone(), g_fn.clone());
        let prod_fn = c.inner_fn_of(bd, n, {
            let abi = abi.clone();
            let ab_fn = ab_fn.clone();
            move |_e, j| c.mul(abi.clone(), ab_app_of(&ab_fn, j))
        });
        let neg_eq = c.sum_neg(n, prod_fn.clone());
        let smul_inner = c.sum_smul(n, abi.clone(), ab_fn.clone());

        let sum_g = c.c.sum(n.clone(), g_fn);
        let sum_prod = c.c.sum(n.clone(), prod_fn);
        let two_sum_g = c.mul(c.two.clone(), sum_g.clone());
        let neg_sum_prod = c.neg(sum_prod.clone());
        let two_neg_sum_prod = c.mul(c.two.clone(), neg_sum_prod.clone());
        let abi_sab = c.mul(abi.clone(), sab.clone());
        let two_neg_abi_sab = c.two_neg(abi_sab.clone());
        // lhs := Σⱼ (2·(−(ab i·ab j)))  [byte-identical to Fin.sum_smul's LHS]
        let lhs = c.c.sum(
            n.clone(),
            c.inner_fn_of(bd, n, {
                let abi = abi.clone();
                let ab_fn = ab_fn.clone();
                move |_e, j| c.two_neg(c.mul(abi.clone(), ab_app_of(&ab_fn, j)))
            }),
        );

        let two_fn = {
            let mut d = EnvDeclBuilder::child_of(bd);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.mul(c.two.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        };
        let step2 = c.congr(sum_g.clone(), neg_sum_prod.clone(), two_fn, neg_eq);
        let two_neg_fn = {
            let mut d = EnvDeclBuilder::child_of(bd);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.mul(c.two.clone(), c.neg(z));
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        };
        let step3 = c.congr(sum_prod.clone(), abi_sab.clone(), two_neg_fn, smul_inner);

        let tt = c.trans(
            lhs.clone(),
            two_sum_g,
            two_neg_sum_prod.clone(),
            smul,
            step2,
        );
        c.trans(lhs, two_neg_sum_prod, two_neg_abi_sab, tt, step3)
    };

    // ── outer congr: outer_app → outer_target (= fun i => 2·(−(ab i·Σab))) ──
    let outer_target = c.outer_fn_of(b, n, |_d, i| {
        let i = i.clone();
        c.two_neg(c.mul(ab_app_of(&ab_fn, &i), sab.clone()))
    });
    let outer_app3 = c.outer_fn_of(b, n, |d, i| {
        let i = i.clone();
        let inner = c.inner_fn_of(d, n, {
            let i = i.clone();
            let ab_fn = ab_fn.clone();
            move |_e, j| c.two_neg(c.mul(ab_app_of(&ab_fn, &i), ab_app_of(&ab_fn, j)))
        });
        c.c.sum(n.clone(), inner)
    });
    let h_congr_outer = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (i_id, i) = d.fresh_local(c.fin_of(n));
        let body = inner_eq(&d, &i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), body))
    };
    let congr_outer = c.sum_congr(n, outer_app3, outer_target.clone(), h_congr_outer);
    let sum_outer_target = c.c.sum(n.clone(), outer_target);

    // ── outer reduction:  Σᵢ 2·(−(ab i·Σab)) = 2·(−(Σab·Σab)) = 2·(−P) ──
    let h_fn = c.outer_fn_of(b, n, |_d, i| {
        let i = i.clone();
        c.neg(c.mul(ab_app_of(&ab_fn, &i), sab.clone()))
    });
    let smul_o = c.sum_smul(n, c.two.clone(), h_fn.clone());
    let prod_o_fn = c.outer_fn_of(b, n, |_d, i| {
        let i = i.clone();
        c.mul(ab_app_of(&ab_fn, &i), sab.clone())
    });
    let neg_o = c.sum_neg(n, prod_o_fn.clone());
    let mul_o = c.sum_mul(n, ab_fn.clone(), sab.clone());

    let sum_h = c.c.sum(n.clone(), h_fn);
    let sum_prod_o = c.c.sum(n.clone(), prod_o_fn);
    let two_sum_h = c.mul(c.two.clone(), sum_h.clone());
    let neg_sum_prod_o = c.neg(sum_prod_o.clone());
    let two_neg_sum_prod_o = c.mul(c.two.clone(), neg_sum_prod_o.clone());
    let two_neg_p = c.two_neg(big_p.clone());

    let two_fn_o = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(c.two.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let step2_o = c.congr(sum_h.clone(), neg_sum_prod_o.clone(), two_fn_o, neg_o);
    let two_neg_fn_o = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.mul(c.two.clone(), c.neg(z));
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let step3_o = c.congr(sum_prod_o.clone(), big_p.clone(), two_neg_fn_o, mul_o);

    let tt_o = c.trans(
        sum_outer_target.clone(),
        two_sum_h,
        two_neg_sum_prod_o.clone(),
        smul_o,
        step2_o,
    );
    let outer_red = c.trans(
        sum_outer_target.clone(),
        two_neg_sum_prod_o,
        two_neg_p.clone(),
        tt_o,
        step3_o,
    );

    // chain: Σ outer_legc =(bridge0)= Σ outer_app =(congr_outer)= sum_outer_target
    //        =(outer_red)= 2·(−P)
    let t0 = c.trans(
        sum_outer_legc,
        sum_outer_app.clone(),
        sum_outer_target.clone(),
        bridge0,
        congr_outer,
    );
    c.trans(
        c.c.sum(n.clone(), outer_legc.clone()),
        sum_outer_target,
        two_neg_p,
        t0,
        outer_red,
    )
}

/// `App(ab_fn, k)` — free helper so closures can build the applied product.
fn ab_app_of(ab_fn: &Expr, k: &Expr) -> Expr {
    Expr::app(ab_fn.clone(), k.clone())
}

/// `(A + 2·(−P)) + A = X + X`  where `X := A − P ≡ A + (−P)`.
///
/// A closed Rat identity. With `q := −P` and `X ≡ A + q` (def-eq, `Rat.sub` is
/// `Rat.add _ (Rat.neg _)`):
///   (A + 2·q) + A
///     = (A + (q + q)) + A     [congr·`Rat.two_mul q`]
///     = ((A + q) + q) + A     [congr·`Eq.symm (Rat.add_assoc A q q)`]
///     = (A + q) + (q + A)     [`Rat.add_assoc (A+q) q A`]
///     = (A + q) + (A + q)     [congr·`Rat.add_comm q A`]  ≡  X + X.
fn rat_regroup(
    c: &AssembleConsts,
    b: &EnvDeclBuilder,
    big_a: &Expr,
    big_p: &Expr,
    x: &Expr,
) -> Expr {
    use super::boolean_analysis_ring_identities_proofs::RingConsts;
    let rc = RingConsts::new();
    let _ = x; // X ≡ A + q def-eq; the chain lands on (A+q)+(A+q).
    let q = c.neg(big_p.clone());
    let a = big_a.clone();
    let two_q = c.mul(c.two.clone(), q.clone());
    let q_plus_q = c.add(q.clone(), q.clone());
    let a_plus_q = c.add(a.clone(), q.clone());

    // lhs := (A + 2·q) + A
    let lhs = c.add(c.add(a.clone(), two_q.clone()), a.clone());
    // m1 := (A + (q+q)) + A
    let m1 = c.add(c.add(a.clone(), q_plus_q.clone()), a.clone());
    // m2 := ((A+q)+q) + A
    let m2 = c.add(c.add(a_plus_q.clone(), q.clone()), a.clone());
    // m3 := (A+q) + (q+A)
    let q_plus_a = c.add(q.clone(), a.clone());
    let m3 = c.add(a_plus_q.clone(), q_plus_a.clone());
    // rhs := (A+q) + (A+q)  (≡ X + X)
    let rhs = c.add(a_plus_q.clone(), a_plus_q.clone());

    // step1: 2·q = q+q ; lift over `(A + ·) + A`.
    let two_mul_q = rc.two_mul(b, q.clone());
    let lift1 = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.add(c.add(a.clone(), z), a.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let s1 = c.congr(two_q.clone(), q_plus_q.clone(), lift1, two_mul_q);

    // step2: A+(q+q) = (A+q)+q  via symm(add_assoc A q q); lift over `· + A`.
    let assoc_aqq = rc.aassoc(a.clone(), q.clone(), q.clone()); // (A+q)+q = A+(q+q)
    let symm_assoc = c.symm(
        c.add(a_plus_q.clone(), q.clone()),
        c.add(a.clone(), q_plus_q.clone()),
        assoc_aqq,
    );
    let lift2 = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.add(z, a.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let s2 = c.congr(
        c.add(a.clone(), q_plus_q.clone()),
        c.add(a_plus_q.clone(), q.clone()),
        lift2,
        symm_assoc,
    );

    // step3: ((A+q)+q)+A = (A+q)+(q+A)  via add_assoc (A+q) q A.
    let s3 = rc.aassoc(a_plus_q.clone(), q.clone(), a.clone());

    // step4: q+A = A+q ; lift over `(A+q) + ·`.
    let comm_qa = rc.acomm(q.clone(), a.clone());
    let lift4 = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat());
        let body = c.add(a_plus_q.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
    };
    let s4 = c.congr(q_plus_a.clone(), a_plus_q.clone(), lift4, comm_qa);

    // chain: lhs = m1 = m2 = m3 = rhs
    let t1 = c.trans(lhs.clone(), m1.clone(), m2.clone(), s1, s2);
    let t2 = c.trans(lhs.clone(), m2, m3.clone(), t1, s3);
    c.trans(lhs, m3, rhs, t2, s4)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let n = Name::from_string(name);
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check against its type: {e:?}"));
        let deps = env.axiom_deps(&n).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
    }

    #[test]
    fn test_fin_sum_neg_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_sum_neg_theorem()
            .expect("register_fin_sum_neg_theorem");
        assert_constructive_theorem(&env, "Fin.sum_neg");
        // sanity: it type-infers as a standalone const too.
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Fin.sum_neg"), vec![]))
            .expect("Fin.sum_neg should type-check");
    }

    #[test]
    fn test_fin_sum_lagrange_identity_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_sum_lagrange_identity_theorem()
            .expect("register_fin_sum_lagrange_identity_theorem");
        assert_constructive_theorem(&env, "Fin.sum_lagrange_identity");
    }

    #[test]
    fn test_fin_sum_cauchy_schwarz_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_sum_cauchy_schwarz_theorem()
            .expect("register_fin_sum_cauchy_schwarz_theorem");
        assert_constructive_theorem(&env, "Fin.sum_cauchy_schwarz");
    }
}
