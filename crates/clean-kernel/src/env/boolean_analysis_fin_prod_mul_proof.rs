// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.prod_mul` — multiplicativity of `Fin.prod`.
//!
//! `Fin.prod_mul : ∀ (n : Nat) (a b : Fin n → Rat),`
//! `  Fin.prod n (fun i => Rat.mul (a i) (b i)) = Rat.mul (Fin.prod n a) (Fin.prod n b)`
//!
//! The multiplicative twin of the constructive `Fin.sum_add`
//! (`nn_verify_fin_sum_add_proof.rs`). Same `Nat.rec` induction over the faithful
//! `Fin.prod` carrier (identity `Rat.one`, fold `Rat.mul`):
//!
//! - BASE (`n = 0`): both sides reduce to `Rat.one`; `Fin.prod 0 _ ≡ Rat.one`, so
//!   the goal `Rat.one = Rat.mul Rat.one Rat.one` is `Eq.symm (Rat.mul_one
//!   Rat.one)`.
//! - STEP (`n = k+1`): the IH rewrites the `Fin k` prefix product, then a
//!   four-factor rearrange `(A·B)·(x·d) = (A·x)·(B·d)` (checked `Rat.mul_assoc` /
//!   `Rat.mul_comm`) lines up the last-coordinate factors with the per-function
//!   products. `Rat.mul_one` / `Rat.mul_assoc` / `Rat.mul_comm` are landed
//!   constructive `Declaration::Theorem`s, so the closure stays empty.
//!
//! This is the first reusable building block of the character-orthonormality /
//! Parseval machinery (the cube-tensor Fubini factorization merges
//! `chi n S x · chi n T x` into a single `Fin.prod` of per-coordinate products,
//! which `Fin.prod_mul` then splits). Kernel-checked, `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FinProdMulConsts {
    base: FinSumConsts,
    fin_prod: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    rat_one: Expr,
    rat_mul_one: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
}

impl FinProdMulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            base: FinSumConsts::new(),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            rat_mul_assoc: Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            rat_mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
        }
    }

    fn mul_rat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.base.rat_mul.clone(), lhs), rhs)
    }

    fn prod(&self, n: Expr, f: Expr) -> Expr {
        Expr::app(Expr::app(self.fin_prod.clone(), n), f)
    }

    fn eq_rat(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.base.rat_eq(lhs, rhs)
    }

    fn fin_to_rat(&self, n: Expr) -> Expr {
        self.base.fin_to_rat(n)
    }
}

/// `fun (i : Fin n) => Rat.mul (f i) (g i)`.
fn pointwise_mul(c: &FinProdMulConsts, parent: &EnvDeclBuilder, n: Expr, f: Expr, g: Expr) -> Expr {
    let fin_n = Expr::app(c.base.fin.clone(), n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.mul_rat(Expr::app(f, i.clone()), Expr::app(g, i));
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// `fun (i : Fin k) => f (Fin.castSucc k i)`.
fn cast_succ_fn(c: &FinProdMulConsts, parent: &EnvDeclBuilder, k: Expr, f: Expr) -> Expr {
    let fin_k = Expr::app(c.base.fin.clone(), k.clone());
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_k.clone());
    let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), k), i);
    let body = Expr::app(f, cast_i);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_k, body);
    b.finish_child(lam)
}

/// `fun (x : Rat) => Rat.mul x right`.
fn mul_right_fn(c: &FinProdMulConsts, parent: &EnvDeclBuilder, right: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.base.rat.clone());
    let body = c.mul_rat(x, right);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.base.rat.clone(), body);
    b.finish_child(lam)
}

/// `fun (x : Rat) => Rat.mul (Rat.mul left x) right`.
fn mul_left_then_outer_right_fn(
    c: &FinProdMulConsts,
    parent: &EnvDeclBuilder,
    left: Expr,
    right: Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.base.rat.clone());
    let body = c.mul_rat(c.mul_rat(left, x), right);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.base.rat.clone(), body);
    b.finish_child(lam)
}

fn build_type(c: &FinProdMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let lhs = c.prod(
        n.clone(),
        pointwise_mul(c, &b, n.clone(), f.clone(), g.clone()),
    );
    let rhs = c.mul_rat(c.prod(n.clone(), f), c.prod(n, g));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_type, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), ty);
    b.finish(ty)
}

fn build_motive(c: &FinProdMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(k.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let lhs = c.prod(
        k.clone(),
        pointwise_mul(c, &b, k.clone(), f.clone(), g.clone()),
    );
    let rhs = c.mul_rat(c.prod(k.clone(), f), c.prod(k, g));
    let body = c.eq_rat(lhs, rhs);
    let pi_g = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), body);
    let pi_f = b.mk_pi(f_id, BinderInfo::Default, f_type, pi_g);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), pi_f);
    b.finish(lam)
}

/// BASE (`n = 0`): `Fin.prod 0 (a·b) ≡ Rat.one` and `Fin.prod 0 a ≡ Fin.prod 0 b
/// ≡ Rat.one`, so the goal is `Rat.one = Rat.mul Rat.one Rat.one`. Discharged by
/// `Eq.symm (Rat.mul_one Rat.one : Rat.mul Rat.one Rat.one = Rat.one)`.
fn build_base(c: &FinProdMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let f_type = c.fin_to_rat(c.nat_zero.clone());
    let (f_id, _f) = b.fresh_local(f_type.clone());
    let (g_id, _g) = b.fresh_local(f_type.clone());
    let mul_one_one = c.mul_rat(c.rat_one.clone(), c.rat_one.clone());
    // Rat.mul_one Rat.one : Rat.mul Rat.one Rat.one = Rat.one
    let h = Expr::app(c.rat_mul_one.clone(), c.rat_one.clone());
    let proof = Expr::apps(
        c.eq_symm.clone(),
        [c.base.rat.clone(), mul_one_one, c.rat_one.clone(), h],
    );
    let val = b.mk_lam(g_id, BinderInfo::Default, f_type.clone(), proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type, val);
    b.finish(val)
}

fn congr_rat(c: &FinProdMulConsts, alpha: Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
    Expr::apps(c.congr_arg.clone(), [alpha, c.base.rat.clone(), a, b, f, h])
}

fn eq_trans(c: &FinProdMulConsts, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(c.eq_trans.clone(), [c.base.rat.clone(), a, b, d, h1, h2])
}

fn eq_symm(c: &FinProdMulConsts, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c.eq_symm.clone(), [c.base.rat.clone(), a, b, h])
}

/// Prove `(A·B)·(x·d) = (A·x)·(B·d)` for Rats, using `Rat.mul_assoc` /
/// `Rat.mul_comm` only. A direct port of `build_four_add_rearrange` in
/// `nn_verify_fin_sum_add_proof.rs` with `+`↦`*`. The chain:
///   (A·B)·(x·d)
///   = ((A·B)·x)·d         [assoc⁻¹ on (A·B), x, d]
///   = (A·(B·x))·d         [congr (·d) on assoc A B x]
///   = (A·(x·B))·d         [congr (A·_·d) on comm B x]
///   = (A·x)·B·d           [congr (·d) on assoc⁻¹ A x B]
///   = (A·x)·(B·d)         [assoc on (A·x), B, d]
fn build_four_mul_rearrange(
    c: &FinProdMulConsts,
    parent: &EnvDeclBuilder,
    a: Expr,
    b: Expr,
    x: Expr,
    d: Expr,
) -> Expr {
    let ab = c.mul_rat(a.clone(), b.clone());
    let xd = c.mul_rat(x.clone(), d.clone());
    let ax = c.mul_rat(a.clone(), x.clone());
    let bx = c.mul_rat(b.clone(), x.clone());
    let xb = c.mul_rat(x.clone(), b.clone());
    let mid0 = c.mul_rat(ab.clone(), xd.clone());
    let mid1 = c.mul_rat(c.mul_rat(ab.clone(), x.clone()), d.clone());
    let mid2 = c.mul_rat(c.mul_rat(a.clone(), bx.clone()), d.clone());
    let mid3 = c.mul_rat(c.mul_rat(a.clone(), xb.clone()), d.clone());
    let mid4 = c.mul_rat(c.mul_rat(ax.clone(), b.clone()), d.clone());
    let target = c.mul_rat(ax.clone(), c.mul_rat(b.clone(), d.clone()));

    // step1: (A·B)·(x·d) = ((A·B)·x)·d   via Eq.symm (assoc (A·B) x d)
    let assoc_ab_x_d = Expr::apps(c.rat_mul_assoc.clone(), [ab.clone(), x.clone(), d.clone()]);
    let step1 = eq_symm(c, mid1.clone(), mid0.clone(), assoc_ab_x_d);

    // step2: ((A·B)·x)·d = (A·(B·x))·d   via congr (·d) (assoc A B x)
    let assoc_a_b_x = Expr::apps(c.rat_mul_assoc.clone(), [a.clone(), b.clone(), x.clone()]);
    let step2_fn = mul_right_fn(c, parent, d.clone());
    let step2 = congr_rat(
        c,
        c.base.rat.clone(),
        c.mul_rat(ab, x.clone()),
        c.mul_rat(a.clone(), bx),
        step2_fn,
        assoc_a_b_x,
    );

    // step3: (A·(B·x))·d = (A·(x·B))·d   via congr (A·_·d) (comm B x)
    let comm_b_x = Expr::apps(c.rat_mul_comm.clone(), [b.clone(), x.clone()]);
    let step3_fn = mul_left_then_outer_right_fn(c, parent, a.clone(), d.clone());
    let step3 = congr_rat(
        c,
        c.base.rat.clone(),
        c.mul_rat(b.clone(), x.clone()),
        xb.clone(),
        step3_fn,
        comm_b_x,
    );

    // step4: (A·(x·B))·d = ((A·x)·B)·d   via congr (·d) (Eq.symm (assoc A x B))
    let assoc_a_x_b = Expr::apps(c.rat_mul_assoc.clone(), [a.clone(), x.clone(), b.clone()]);
    let assoc_a_x_b_rev = eq_symm(
        c,
        c.mul_rat(ax.clone(), b.clone()),
        c.mul_rat(a.clone(), xb.clone()),
        assoc_a_x_b,
    );
    let step4_fn = mul_right_fn(c, parent, d.clone());
    let step4 = congr_rat(
        c,
        c.base.rat.clone(),
        c.mul_rat(a.clone(), xb),
        c.mul_rat(ax.clone(), b.clone()),
        step4_fn,
        assoc_a_x_b_rev,
    );

    // step5: ((A·x)·B)·d = (A·x)·(B·d)   via assoc (A·x) B d
    let step5 = Expr::apps(c.rat_mul_assoc.clone(), [ax, b, d]);

    let chain12 = eq_trans(c, mid0.clone(), mid1.clone(), mid2.clone(), step1, step2);
    let chain123 = eq_trans(c, mid0.clone(), mid2.clone(), mid3.clone(), chain12, step3);
    let chain1234 = eq_trans(c, mid0.clone(), mid3, mid4.clone(), chain123, step4);
    eq_trans(c, mid0, mid4, target, chain1234, step5)
}

fn build_step(c: &FinProdMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let f_type_k = c.fin_to_rat(k.clone());
    let (ih_f_id, ih_f) = b.fresh_local(f_type_k.clone());
    let (ih_g_id, ih_g) = b.fresh_local(f_type_k.clone());
    let ih_lhs = c.prod(
        k.clone(),
        pointwise_mul(c, &b, k.clone(), ih_f.clone(), ih_g.clone()),
    );
    let ih_rhs = c.mul_rat(c.prod(k.clone(), ih_f), c.prod(k.clone(), ih_g));
    let ih_body = c.eq_rat(ih_lhs, ih_rhs);
    let ih_type = b.mk_pi(ih_g_id, BinderInfo::Default, f_type_k.clone(), ih_body);
    let ih_type = b.mk_pi(ih_f_id, BinderInfo::Default, f_type_k, ih_type);
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let f_type_succ = c.fin_to_rat(succ_k.clone());
    let (f_id, f) = b.fresh_local(f_type_succ.clone());
    let (g_id, g) = b.fresh_local(f_type_succ.clone());
    let f_cast = cast_succ_fn(c, &b, k.clone(), f.clone());
    let g_cast = cast_succ_fn(c, &b, k.clone(), g.clone());
    let fg_cast = pointwise_mul(c, &b, k.clone(), f_cast.clone(), g_cast.clone());
    let prod_fg = c.prod(k.clone(), fg_cast);
    let prod_f = c.prod(k.clone(), f_cast.clone());
    let prod_g = c.prod(k.clone(), g_cast.clone());
    let f_last = Expr::app(f.clone(), Expr::app(c.fin_last.clone(), k.clone()));
    let g_last = Expr::app(g.clone(), Expr::app(c.fin_last.clone(), k));
    let last_mul = c.mul_rat(f_last.clone(), g_last.clone());

    // lhs   = (Fin.prod k (f·g cast)) · (f_last · g_last)
    // mid0  = ((Fin.prod k f) · (Fin.prod k g)) · (f_last · g_last)
    // rhs   = ((Fin.prod k f) · f_last) · ((Fin.prod k g) · g_last)
    let lhs = c.mul_rat(prod_fg.clone(), last_mul.clone());
    let mid0 = c.mul_rat(c.mul_rat(prod_f.clone(), prod_g.clone()), last_mul);
    let rhs = c.mul_rat(
        c.mul_rat(prod_f.clone(), f_last.clone()),
        c.mul_rat(prod_g.clone(), g_last.clone()),
    );

    // step1: lhs = mid0  via congr (·(f_last·g_last)) (ih f_cast g_cast)
    let ih_app = Expr::app(Expr::app(ih, f_cast), g_cast);
    let step1_fn = mul_right_fn(c, &b, c.mul_rat(f_last.clone(), g_last.clone()));
    let step1 = congr_rat(
        c,
        c.base.rat.clone(),
        prod_fg,
        c.mul_rat(prod_f.clone(), prod_g.clone()),
        step1_fn,
        ih_app,
    );
    // step2: mid0 = rhs  via the four-factor rearrange
    let step2 = build_four_mul_rearrange(c, &b, prod_f, prod_g, f_last, g_last);
    let proof = eq_trans(c, lhs, mid0, rhs, step1, step2);

    let val = b.mk_lam(g_id, BinderInfo::Default, f_type_succ.clone(), proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type_succ, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), val);
    b.finish(val)
}

fn build_value(c: &FinProdMulConsts) -> Expr {
    let motive = build_motive(c);
    let base = build_base(c);
    let step = build_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), body);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.prod_mul` as a kernel-checked, constructive theorem.
    ///
    /// `∀ (n : Nat) (a b : Fin n → Rat), Fin.prod n (fun i => a i * b i)`
    /// `  = Fin.prod n a * Fin.prod n b`.
    ///
    /// Depends on the `Fin.prod` foundation (via `init_boolean_analysis_foundations`)
    /// and the constructive `Rat.mul_one` / `Rat.mul_assoc` / `Rat.mul_comm`
    /// theorems (via `init_rat`/the quotient field tower). Idempotent.
    pub(crate) fn register_fin_prod_mul_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.prod_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        // `Fin.prod` + the Rat field tower (Rat.mul/one) live in the foundations
        // overlay; the multiplicative algebra (mul_one/assoc/comm) in the Rat
        // quotient tower pulled in transitively by `init_boolean_analysis_foundations`.
        self.init_boolean_analysis_foundations()?;
        self.init_rat()?;

        let c = FinProdMulConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}
