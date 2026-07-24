// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parseval RUNG 1 — the product-of-two-sums expansion.
//!
//! Two kernel-checked, constructive theorems on the road to retiring
//! `parseval_identity`:
//!
//! - `Fin.sum_mul : ∀ (n : Nat) (f : Fin n → Rat) (c : Rat),
//!       Fin.sum n (fun i => Rat.mul (f i) c) = Rat.mul (Fin.sum n f) c`
//!   — the RIGHT scalar homogeneity of finite sums (the mirror of the existing
//!   left-homogeneous `Fin.sum_smul`). `Nat.rec` over the faithful `Fin.sum`
//!   carrier: base `n=0` closes by `Eq.symm (Rat.zero_mul c)`; step folds the
//!   prefix with the IH and refactors via `Rat.right_distrib`.
//!
//! - `Fin.sum_mul_sum : ∀ (m n : Nat) (F : Fin m → Rat) (G : Fin n → Rat),
//!       Rat.mul (Fin.sum m F) (Fin.sum n G)
//!         = Fin.sum m (fun i => Fin.sum n (fun j => Rat.mul (F i) (G j)))`
//!   — the double-sum expansion of a product. Composed from the two
//!   homogeneity lemmas: the inner `Fin.sum n (fun j => F i · G j)` collapses
//!   to `F i · (Fin.sum n G)` by `Fin.sum_smul`, lifting the RHS (via
//!   `Fin.sum_congr`) to `Fin.sum m (fun i => F i · (Σ G))`, which `Fin.sum_mul`
//!   (with `c = Σ G`) folds back to `(Σ F) · (Σ G)`.
//!
//! Closure ⊆ `Nat.rec`, `Fin.castSucc`, `Fin.last`, `Rat.add`/`Rat.mul`,
//! `Rat.zero_mul`/`Rat.right_distrib`, `Fin.sum_smul`/`Fin.sum_congr`, and the
//! `Eq` built-ins — no domain axiom, so any statement over these stays
//! `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct Rung1Consts {
    base: FinSumConsts,
    nat_zero: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    rat_zero_mul: Expr,
    rat_right_distrib: Expr,
    fin_sum_smul: Expr,
    fin_sum_congr: Expr,
}

impl Rung1Consts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            base: FinSumConsts::new(),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            rat_zero_mul: Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            rat_right_distrib: Expr::const_(Name::from_string("Rat.right_distrib"), vec![]),
            fin_sum_smul: Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.base.rat.clone()
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.base.fin.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.base.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.base.rat_add.clone(), [a, b])
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.base.fin_sum.clone(), [n, f])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.base.rat_eq(l, r)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat(), a, b, h])
    }
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, g, h])
    }
}

// ── Fin.sum_mul : Σ (f i · c) = (Σ f) · c ──────────────────────────────────

/// `fun (i : Fin n) => Rat.mul (f i) c` — the right-scaled summand.
fn rscaled_fn(c: &Rung1Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, cc: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.mul(Expr::app(f.clone(), i), cc.clone());
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

/// `fun (i : Fin k) => f (Fin.castSucc k i)`.
fn cast_fn(c: &Rung1Consts, parent: &EnvDeclBuilder, k: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_k = c.fin_of(k);
    let (i_id, i) = b.fresh_local(fin_k.clone());
    let cast_i = Expr::apps(c.fin_cast_succ.clone(), [k.clone(), i]);
    let body = Expr::app(f.clone(), cast_i);
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_k, body))
}

/// `fun (x : Rat) => Rat.add x right`.
fn add_left_fn(c: &Rung1Consts, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.rat());
    let body = c.add(x, right.clone());
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.rat(), body))
}

fn sum_mul_type(c: &Rung1Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_ty = c.base.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (c_id, cc) = b.fresh_local(c.rat());
    let lhs = c.sum(n.clone(), rscaled_fn(c, &b, &n, &f, &cc));
    let rhs = c.mul(c.sum(n.clone(), f.clone()), cc.clone());
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(c_id, BinderInfo::Default, c.rat(), concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_ty, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), ty);
    b.finish(ty)
}

fn sum_mul_motive(c: &Rung1Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let f_ty = c.base.fin_to_rat(k.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (c_id, cc) = b.fresh_local(c.rat());
    let lhs = c.sum(k.clone(), rscaled_fn(c, &b, &k, &f, &cc));
    let rhs = c.mul(c.sum(k.clone(), f.clone()), cc.clone());
    let body = c.eq_rat(lhs, rhs);
    let pi_c = b.mk_pi(c_id, BinderInfo::Default, c.rat(), body);
    let pi_f = b.mk_pi(f_id, BinderInfo::Default, f_ty, pi_c);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), pi_f);
    b.finish(lam)
}

fn sum_mul_base(c: &Rung1Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let f_ty = c.base.fin_to_rat(c.nat_zero.clone());
    let (f_id, _f) = b.fresh_local(f_ty.clone());
    let (c_id, cc) = b.fresh_local(c.rat());
    // Goal: Rat.zero = Rat.mul Rat.zero c    (LHS Fin.sum 0 _ ≡ 0; RHS (Fin.sum 0 f)·c ≡ 0·c)
    // Rat.zero_mul c : Rat.mul Rat.zero c = Rat.zero
    let zero_mul = c.mul(c.base.rat_zero.clone(), cc.clone());
    let h = Expr::app(c.rat_zero_mul.clone(), cc.clone());
    let proof = c.symm(zero_mul, c.base.rat_zero.clone(), h);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.rat(), proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, val);
    b.finish(val)
}

fn sum_mul_step(c: &Rung1Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());

    // IH : ∀ (f : Fin k → Rat) (c : Rat), Σ_k (f i · c) = (Σ_k f) · c
    let ih_ty = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let f_ty = c.base.fin_to_rat(k.clone());
        let (f_id, f) = bb.fresh_local(f_ty.clone());
        let (c_id, cc) = bb.fresh_local(c.rat());
        let lhs = c.sum(k.clone(), rscaled_fn(c, &bb, &k, &f, &cc));
        let rhs = c.mul(c.sum(k.clone(), f.clone()), cc.clone());
        let body = c.eq_rat(lhs, rhs);
        let pi_c = bb.mk_pi(c_id, BinderInfo::Default, c.rat(), body);
        let pi_f = bb.mk_pi(f_id, BinderInfo::Default, f_ty, pi_c);
        bb.finish_child(pi_f)
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let sk = c.succ(&k);
    let f_ty = c.base.fin_to_rat(sk.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (c_id, cc) = b.fresh_local(c.rat());

    let f_cast = cast_fn(c, &b, &k, &f);
    let prefix = c.sum(k.clone(), f_cast.clone());
    let last_val = Expr::app(f.clone(), Expr::app(c.fin_last.clone(), k.clone()));

    // LHS (ι on Fin.sum_succ): Σ_k ((rscaled f c)∘castSucc) + (rscaled f c)(last)
    //   ≡ Σ_k (rscaled f_cast c) + (f(last) · c)
    let scaled_prefix = c.sum(k.clone(), rscaled_fn(c, &b, &k, &f_cast, &cc));
    let last_mul = c.mul(last_val.clone(), cc.clone());
    let lhs = c.add(scaled_prefix.clone(), last_mul.clone());

    // mid = (P · c) + (last · c)  after IH on the prefix
    let prefix_mul = c.mul(prefix.clone(), cc.clone());
    let mid = c.add(prefix_mul.clone(), last_mul.clone());

    // RHS = (Σ_{k+1} f) · c ≡ (P + last) · c
    let p_plus_l = c.add(prefix.clone(), last_val.clone());
    let rhs = c.mul(p_plus_l.clone(), cc.clone());

    // step1 : lhs = mid    via congrArg (· + last·c) (IH f_cast c)
    let ih_app = Expr::app(Expr::app(ih.clone(), f_cast.clone()), cc.clone());
    let step1_fn = add_left_fn(c, &b, &last_mul);
    let step1 = c.congr(scaled_prefix, prefix_mul, step1_fn, ih_app);

    // step2 : mid = rhs    via Eq.symm (Rat.right_distrib P last c)
    //   right_distrib P last c : (P + last) · c = P·c + last·c
    let distrib = Expr::apps(
        c.rat_right_distrib.clone(),
        [prefix.clone(), last_val.clone(), cc.clone()],
    );
    let step2 = c.symm(rhs.clone(), mid.clone(), distrib);

    let proof = c.trans(lhs, mid, rhs, step1, step2);

    let val = b.mk_lam(c_id, BinderInfo::Default, c.rat(), proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), val);
    b.finish(val)
}

fn sum_mul_value(c: &Rung1Consts) -> Expr {
    let motive = sum_mul_motive(c);
    let base = sum_mul_base(c);
    let step = sum_mul_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), body))
}

// ── Fin.sum_mul_sum : (Σ F)·(Σ G) = Σ_i Σ_j (F i · G j) ────────────────────

/// `fun (j : Fin n) => Rat.mul (F i) (G j)` — the inner integrand at fixed `i`.
fn inner_fn(c: &Rung1Consts, parent: &EnvDeclBuilder, n: &Expr, fi: &Expr, g: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j_id, j) = b.fresh_local(fin_n.clone());
    let body = c.mul(fi.clone(), Expr::app(g.clone(), j));
    b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_n, body))
}

/// `fun (i : Fin m) => Fin.sum n (fun j => F i · G j)` — the RHS outer integrand.
fn outer_fn(
    c: &Rung1Consts,
    parent: &EnvDeclBuilder,
    m: &Expr,
    n: &Expr,
    f: &Expr,
    g: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_m = c.fin_of(m);
    let (i_id, i) = b.fresh_local(fin_m.clone());
    let fi = Expr::app(f.clone(), i);
    let body = c.sum(n.clone(), inner_fn(c, &b, n, &fi, g));
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, body))
}

/// `fun (i : Fin m) => Rat.mul (F i) (Fin.sum n G)` — the mid outer integrand.
fn mid_fn(c: &Rung1Consts, parent: &EnvDeclBuilder, m: &Expr, sumg: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_m = c.fin_of(m);
    let (i_id, i) = b.fresh_local(fin_m.clone());
    let body = c.mul(Expr::app(f.clone(), i), sumg.clone());
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, body))
}

fn sum_mul_sum_type(c: &Rung1Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_ty = c.base.fin_to_rat(m.clone());
    let g_ty = c.base.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let lhs = c.mul(c.sum(m.clone(), f.clone()), c.sum(n.clone(), g.clone()));
    let rhs = c.sum(m.clone(), outer_fn(c, &b, &m, &n, &f, &g));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_ty, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), ty);
    let ty = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), ty);
    b.finish(ty)
}

fn sum_mul_sum_value(c: &Rung1Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_ty = c.base.fin_to_rat(m.clone());
    let g_ty = c.base.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (g_id, g) = b.fresh_local(g_ty.clone());

    let sum_f = c.sum(m.clone(), f.clone());
    let sum_g = c.sum(n.clone(), g.clone());
    let lhs = c.mul(sum_f.clone(), sum_g.clone());
    let mid = c.sum(m.clone(), mid_fn(c, &b, &m, &sum_g, &f));
    let rhs = c.sum(m.clone(), outer_fn(c, &b, &m, &n, &f, &g));

    // legA : lhs = mid     via Eq.symm (Fin.sum_mul m F (Σ G))
    //   Fin.sum_mul m F (Σ G) : Σ_m (F i · Σ G) = (Σ_m F)·(Σ G) = lhs
    let sum_mul = Expr::const_(Name::from_string("Fin.sum_mul"), vec![]);
    let sum_mul_app = Expr::apps(sum_mul, [m.clone(), f.clone(), sum_g.clone()]);
    let leg_a = c.symm(mid.clone(), lhs.clone(), sum_mul_app);

    // legB : mid = rhs     via Fin.sum_congr m (mid integrand) (outer integrand) H
    //   H : ∀ (i : Fin m), F i · (Σ G) = Σ_n (fun j => F i · G j)
    //       = Eq.symm (Fin.sum_smul n (F i) G)
    let h_fn = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let fin_m = c.fin_of(&m);
        let (i_id, i) = hb.fresh_local(fin_m.clone());
        let fi = Expr::app(f.clone(), i.clone());
        let mid_term = c.mul(fi.clone(), sum_g.clone());
        let inner_sum = c.sum(n.clone(), inner_fn(c, &hb, &n, &fi, &g));
        // Fin.sum_smul n (F i) G : Σ_n (F i · G j) = (F i) · (Σ G)
        //   (i.e. inner_sum = mid_term); symm flips it to mid_term = inner_sum.
        let smul_app = Expr::apps(c.fin_sum_smul.clone(), [n.clone(), fi.clone(), g.clone()]);
        let h_i = c.symm(inner_sum, mid_term, smul_app);
        hb.finish_child(hb.mk_lam(i_id, BinderInfo::Default, fin_m, h_i))
    };
    let mid_integrand = mid_fn(c, &b, &m, &sum_g, &f);
    let outer_integrand = outer_fn(c, &b, &m, &n, &f, &g);
    let leg_b = Expr::apps(
        c.fin_sum_congr.clone(),
        [m.clone(), mid_integrand, outer_integrand, h_fn],
    );

    let proof = c.trans(lhs, mid, rhs, leg_a, leg_b);

    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), val);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.sum_mul : ∀ n f c, Σ_n (f i · c) = (Σ_n f) · c` as a
    /// kernel-checked, constructive theorem (RIGHT scalar homogeneity).
    /// Idempotent.
    pub(crate) fn register_fin_sum_mul_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_rat_field_inst()?;

        let c = Rung1Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sum_mul_type(&c),
            value: sum_mul_value(&c),
        })
    }

    /// Register `Fin.sum_mul_sum : ∀ m n F G,
    ///   (Σ_m F)·(Σ_n G) = Σ_m (fun i => Σ_n (fun j => F i · G j))` as a
    /// kernel-checked, constructive theorem. Idempotent.
    pub(crate) fn register_fin_sum_mul_sum_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_mul_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_rat_field_inst()?;
        self.register_fin_sum_mul_theorem()?;
        // Fin.sum_smul / Fin.sum_congr live in the Fin.sum overlay (init_fin_sum).

        let c = Rung1Consts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sum_mul_sum_type(&c),
            value: sum_mul_sum_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn axiom_free(env: &Environment, name: &str) {
        let n = Name::from_string(name);
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ty = tc
            .infer_type(&Expr::const_(n, vec![]))
            .unwrap_or_else(|_| panic!("{name} should type-check"));
    }

    #[test]
    fn test_fin_sum_mul_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_sum_mul_theorem()
            .expect("register_fin_sum_mul_theorem");
        axiom_free(&env, "Fin.sum_mul");
    }

    #[test]
    fn test_fin_sum_mul_sum_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_sum_mul_sum_theorem()
            .expect("register_fin_sum_mul_sum_theorem");
        axiom_free(&env, "Fin.sum_mul");
        axiom_free(&env, "Fin.sum_mul_sum");
    }
}
