// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `NNReal.finSum_add` — additivity of `NNReal.finSum`, the NNReal dual of the
//! landed Rat `Fin.sum_add`. `Nat.rec.{0}` induction; base `Eq.symm
//! (NNReal.zero_add NNReal.zero)`; step consumes the IH then reassociates/reorders
//! four `NNReal.add`s with `NNReal.add_assoc`/`NNReal.add_comm`.

use super::FinSumStructConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `NNReal.finSum_add : ∀ n f g,
    ///     finSum n (fun i => f i + g i) = finSum n f + finSum n g`.
    pub(crate) fn register_nnreal_finsum_add(
        &mut self,
        c: &FinSumStructConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.finSum_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_add_type(c);
        let value = build_add_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

fn build_add_type(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let ft = c.fin_to_nn(&n);
    let (f_id, f) = b.fresh_local(ft.clone());
    let (g_id, g) = b.fresh_local(ft.clone());
    let lhs = c.sum(&n, &c.pointwise_add(&b, &n, &f, &g));
    let rhs = c.add(&c.sum(&n, &f), &c.sum(&n, &g));
    let concl = c.eq_nn(&lhs, &rhs);
    let r = b.mk_pi(g_id, BinderInfo::Default, ft.clone(), concl);
    let r = b.mk_pi(f_id, BinderInfo::Default, ft, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), r);
    b.finish(r)
}

fn build_motive(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let inner = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ft = c.fin_to_nn(&k);
        let (f_id, f) = d.fresh_local(ft.clone());
        let (g_id, g) = d.fresh_local(ft.clone());
        let lhs = c.sum(&k, &c.pointwise_add(&d, &k, &f, &g));
        let rhs = c.add(&c.sum(&k, &f), &c.sum(&k, &g));
        let body = c.eq_nn(&lhs, &rhs);
        let pi_g = d.mk_pi(g_id, BinderInfo::Default, ft.clone(), body);
        let pi_f = d.mk_pi(f_id, BinderInfo::Default, ft, pi_g);
        d.finish_child(pi_f)
    };
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), inner))
}

/// Base `motive 0`: both `finSum 0 _ ≡ NNReal.zero`; goal
/// `NNReal.zero = NNReal.add NNReal.zero NNReal.zero` = `Eq.symm (zero_add 0)`.
fn build_base(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let ft = c.fin_to_nn(&c.nat_zero);
    let (f_id, _f) = b.fresh_local(ft.clone());
    let (g_id, _g) = b.fresh_local(ft.clone());
    // NNReal.zero_add NNReal.zero : add zero zero = zero.
    let h = Expr::app(c.nnreal_zero_add.clone(), c.base.nnreal_zero.clone());
    let add_zz = c.add(&c.base.nnreal_zero, &c.base.nnreal_zero);
    // Eq.symm : zero = add zero zero.
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        ),
        [c.nn(), add_zz, c.base.nnreal_zero.clone(), h],
    );
    let r = b.mk_lam(g_id, BinderInfo::Default, ft.clone(), proof);
    let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
    b.finish(r)
}

/// `(a+b) + (x+d) = (a+x) + (b+d)` over NNReal, pure assoc/comm.
fn four_add_rearrange(
    c: &FinSumStructConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bb: &Expr,
    x: &Expr,
    d: &Expr,
) -> Expr {
    let ab = c.add(a, bb);
    let xd = c.add(x, d);
    let ax = c.add(a, x);
    let bx = c.add(bb, x);
    let xb = c.add(x, bb);
    let mid0 = c.add(&ab, &xd);
    let mid1 = c.add(&c.add(&ab, x), d);
    let mid2 = c.add(&c.add(a, &bx), d);
    let mid3 = c.add(&c.add(a, &xb), d);
    let mid4 = c.add(&c.add(&ax, bb), d);
    let target = c.add(&ax, &c.add(bb, d));

    // step1 : (ab + xd) = ((ab + x) + d)  = symm add_assoc ab x d.
    let step1 = c.symm_assoc(&ab, x, d);
    // step2 : ((ab+x)+d) = ((a+bx)+d)  = congr (·+d) (add_assoc a b x).
    let step2 = c.cong_add_left(
        parent,
        d,
        &c.add(&ab, x),
        &c.add(a, &bx),
        c.add_assoc(a, bb, x),
    );
    // step3 : ((a+bx)+d) = ((a+xb)+d)  = congr ((a+·)+d) (add_comm b x).
    let step3 = {
        let inner = c.cong_add_right(parent, a, &bx, &xb, c.add_comm(bb, x));
        c.cong_add_left(parent, d, &c.add(a, &bx), &c.add(a, &xb), inner)
    };
    // step4 : ((a+xb)+d) = ((ax+b)+d)  = congr (·+d) (symm add_assoc a x b).
    let step4 = {
        let sym = {
            // symm (add_assoc a x b) : a+(x+b) = (a+x)+b.
            let lhs = c.add(&c.add(a, x), bb);
            let rhs = c.add(a, &xb);
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![crate::level::Level::succ(crate::level::Level::zero())],
                ),
                [c.nn(), lhs, rhs, c.add_assoc(a, x, bb)],
            )
        };
        c.cong_add_left(parent, d, &c.add(a, &xb), &c.add(&ax, bb), sym)
    };
    // step5 : ((ax+b)+d) = (ax+(b+d))  = add_assoc ax b d.
    let step5 = c.add_assoc(&ax, bb, d);

    let chain12 = c.trans(&mid0, &mid1, &mid2, step1, step2);
    let chain123 = c.trans(&mid0, &mid2, &mid3, chain12, step3);
    let chain1234 = c.trans(&mid0, &mid3, &mid4, chain123, step4);
    c.trans(&mid0, &mid4, &target, chain1234, step5)
}

fn build_step(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());

    let ft_k = c.fin_to_nn(&k);
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = d.fresh_local(ft_k.clone());
        let (g_id, g) = d.fresh_local(ft_k.clone());
        let lhs = c.sum(&k, &c.pointwise_add(&d, &k, &f, &g));
        let rhs = c.add(&c.sum(&k, &f), &c.sum(&k, &g));
        let body = c.eq_nn(&lhs, &rhs);
        let r = d.mk_pi(g_id, BinderInfo::Default, ft_k.clone(), body);
        let r = d.mk_pi(f_id, BinderInfo::Default, ft_k.clone(), r);
        d.finish_child(r)
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let ft_sk = c.fin_to_nn(&succ_k);
    let (f_id, f) = b.fresh_local(ft_sk.clone());
    let (g_id, g) = b.fresh_local(ft_sk.clone());
    let f_cast = c.cast_fn(&b, &k, &f);
    let g_cast = c.cast_fn(&b, &k, &g);
    let fg_cast = c.pointwise_add(&b, &k, &f_cast, &g_cast);
    let sum_fg = c.sum(&k, &fg_cast);
    let sum_f = c.sum(&k, &f_cast);
    let sum_g = c.sum(&k, &g_cast);
    let f_last = Expr::app(f.clone(), Expr::app(c.fin_last.clone(), k.clone()));
    let g_last = Expr::app(g.clone(), Expr::app(c.fin_last.clone(), k.clone()));
    let last_sum = c.add(&f_last, &g_last);

    let lhs = c.add(&sum_fg, &last_sum);
    let mid0 = c.add(&c.add(&sum_f, &sum_g), &last_sum);
    let rhs = c.add(&c.add(&sum_f, &f_last), &c.add(&sum_g, &g_last));

    // step1 : lhs = mid0  via congr (·+last_sum) (IH f_cast g_cast).
    let ih_app = Expr::apps(ih.clone(), [f_cast.clone(), g_cast.clone()]);
    let step1 = c.cong_add_left(&b, &last_sum, &sum_fg, &c.add(&sum_f, &sum_g), ih_app);
    // step2 : mid0 = rhs  via four_add_rearrange sum_f sum_g f_last g_last.
    let step2 = four_add_rearrange(c, &b, &sum_f, &sum_g, &f_last, &g_last);
    let proof = c.trans(&lhs, &mid0, &rhs, step1, step2);

    let r = b.mk_lam(g_id, BinderInfo::Default, ft_sk.clone(), proof);
    let r = b.mk_lam(f_id, BinderInfo::Default, ft_sk, r);
    let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
    let r = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), r);
    b.finish(r)
}

fn build_add_value(c: &FinSumStructConsts) -> Expr {
    let motive = build_motive(c);
    let base = build_base(c);
    let step = build_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let body = Expr::apps(c.nat_rec0.clone(), [motive, base, step, n]);
    let r = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), body);
    b.finish(r)
}
