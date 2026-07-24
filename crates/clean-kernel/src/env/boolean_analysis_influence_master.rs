// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_influence_chain.rs — the master x-side identity
// (Leg 4) and the disagree-bridge / normalization legs for the
// `influence_fourier` assembly.

// ════════════ Leg 4: subsetSum_influence_master ════════════
//
//   subsetSum n (fun x => (2^n·(b x − b(hcFlip n x i)))²)
//     = 2^n · subsetSum n (fun S => a_fn(S)·a_fn(S)),
// where a_fn(S) = (2·ind(S i))·A_S.
//
// Proof: subsetSum_xside_core n a_fn gives the LHS in xside form
// `subsetSum n (fun x => (Σ_S a_fn S·χ_S x)²)`; Fin.sum_congr over the decoded
// cube index rewrites each squared inner sum to `(2^n·diff)²` via
// subsetSum_flip_diff_decoded (Leg 3) squared.

impl InflConsts {
    /// `fun S => a_fn(S)·χ_S(x)` — the xside inner integrand (def-eq to
    /// `split_lhs_fn`, but phrased through the `a_fn` lambda application).
    fn xside_inner_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        b: &Expr,
        x: &Expr,
        i: &Expr,
    ) -> Expr {
        let a = self.a_fn(parent, n, b, i);
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(a.clone(), s.clone()), self.chi_(n, &s, x));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `2^n·(b x − b(hcFlip n x i))` — the scaled flip difference at `x`.
    fn cube_diff(&self, n: &Expr, b: &Expr, x: &Expr, i: &Expr) -> Expr {
        let diff = self.sub(
            Expr::app(b.clone(), x.clone()),
            Expr::app(b.clone(), self.hc_flip_(n, x, i)),
        );
        self.mul(self.cube(n), diff)
    }
    /// xside LHS integrand `fun x => (Σ_S a_fn S·χ_S x)²` over the sign point.
    fn xside_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let inner = self.ssum(n, self.xside_inner_fn(&xb, n, b, &x, i));
        let body = self.sq(inner);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => (2^n·diff(x))²` over the sign point.
    fn diff_sq_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.sq(self.cube_diff(n, b, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// RHS `S`-integrand `fun S => a_fn(S)·a_fn(S)`.
    fn a_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let a = self.a_fn(parent, n, b, i);
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let as_ = Expr::app(a.clone(), s.clone());
        let body = self.mul(as_.clone(), as_);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// decoded integrand `fun (jx : Fin (2^n)) => g (hcDecode n jx)`.
    fn dec_x(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut jb = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_of(&self.pow2(n));
        let (j_id, j) = jb.fresh_local(fin_p.clone());
        let body = Expr::app(g.clone(), self.hc_decode_(n, &j));
        jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p, body))
    }
}

fn influence_master_type(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.ssum(&n, c.diff_sq_x_fn(&b, &n, &bf, &i));
    let rhs = c.mul(c.cube(&n), c.ssum(&n, c.a_sq_fn(&b, &n, &bf, &i)));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn influence_master_value(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    // xside_core n a_fn : subsetSum n xside_x_fn = 2^n · subsetSum n a_sq_fn.
    let a = c.a_fn(&b, &n, &bf, &i);
    let xcore = Expr::apps(c.xside_core.clone(), [n.clone(), a]);

    // rewrite : subsetSum n xside_x_fn = subsetSum n diff_sq_x_fn   (Fin.sum_congr over jx).
    let before = c.dec_x(&b, &n, &c.xside_x_fn(&b, &n, &bf, &i));
    let after = c.dec_x(&b, &n, &c.diff_sq_x_fn(&b, &n, &bf, &i));
    let h = {
        let mut jb = EnvDeclBuilder::child_of(&b);
        let fin_p = c.fin_of(&c.pow2(&n));
        let (jx_id, jx) = jb.fresh_local(fin_p.clone());
        let x = c.hc_decode_(&n, &jx);
        // Leg 3 at jx: subsetSum n (split_lhs_fn x) = 2^n·diff(x)  (def-eq inner = xside inner).
        let leg3 = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_flip_diff_decoded"),
                vec![],
            ),
            [n.clone(), bf.clone(), i.clone(), jx.clone()],
        );
        let inner = c.ssum(&n, c.xside_inner_fn(&jb, &n, &bf, &x, &i));
        let cd = c.cube_diff(&n, &bf, &x, &i);
        let pf = c.sq_congr(&jb, inner, cd, leg3);
        jb.finish_child(jb.mk_lam(jx_id, BinderInfo::Default, fin_p, pf))
    };
    let rewrite = c.fin_sum_congr_apply(&c.pow2(&n), before, after, h);

    // proof : subsetSum n diff_sq_x_fn = 2^n · subsetSum n a_sq_fn.
    //   symm rewrite : subsetSum n diff_sq_x_fn = subsetSum n xside_x_fn ;
    //   Eq.trans with xcore.
    let lhs = c.ssum(&n, c.diff_sq_x_fn(&b, &n, &bf, &i));
    let mid = c.ssum(&n, c.xside_x_fn(&b, &n, &bf, &i));
    let rhs = c.mul(c.cube(&n), c.ssum(&n, c.a_sq_fn(&b, &n, &bf, &i)));
    let rewrite_sym = c.symm(mid.clone(), lhs.clone(), rewrite);
    let proof = c.trans(lhs, mid, rhs, rewrite_sym, xcore);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

// ════════════ tiny lemma: ind_mul_self (ind² = ind) ════════════

fn ind_mul_self_type(c: &InflConsts) -> Expr {
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(bool_c.clone());
    let ib = c.ind_(bv.clone());
    let concl = c.eq_rat(c.mul(ib.clone(), ib.clone()), ib);
    b.finish(b.mk_pi(bv_id, BinderInfo::Default, bool_c, concl))
}

fn ind_mul_self_value(c: &InflConsts) -> Expr {
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

    let leaf = |bv: Expr| {
        let ib = c.ind_(bv);
        Expr::apps(eq_refl.clone(), [c.rat.clone(), c.mul(ib.clone(), ib)])
    };
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(bool_c.clone());
    // motive : fun (b' : Bool) => ind b' · ind b' = ind b'
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (bp_id, bp) = m.fresh_local(bool_c.clone());
        let ib = c.ind_(bp.clone());
        let body = c.eq_rat(c.mul(ib.clone(), ib.clone()), ib);
        m.finish_child(m.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
    };
    let rec = Expr::apps(bool_rec0, [motive, leaf(bfalse), leaf(btrue), bv.clone()]);
    b.finish(b.mk_lam(bv_id, BinderInfo::Default, bool_c, rec))
}

impl Environment {
    /// Register `BoolAnalysis.ind_mul_self : ∀ (b : Bool), ind b · ind b = ind b`
    /// (`ind²=ind`, idempotence of the `{0,1}` embedding). `Bool.rec`, two ground
    /// Rat-numeral leaves (`0·0=0`, `1·1=1`). Kernel-checked, axiom-free.
    /// Idempotent.
    pub(crate) fn register_ind_mul_self(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.ind_mul_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ind_mul_self_type(&c),
            value: ind_mul_self_value(&c),
        })
    }

    /// Register `BoolAnalysis.subsetSum_influence_master` — the master x-side
    /// identity:
    ///   subsetSum n (fun x => (2^n·(b x − b(hcFlip n x i)))²)
    ///     = 2^n · subsetSum n (fun S => a_fn(S)²),
    /// where `a_fn(S) = (2·ind(S i))·A_S`, `A_S = subsetSum n (fun y => b(y)·χ_S(y))`.
    /// Combines `subsetSum_xside_core` with `subsetSum_flip_diff_decoded`
    /// (Leg 3, squared, under `Fin.sum_congr` over the decoded cube index).
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_influence_master(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_influence_master");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_flip_diff_decoded()?;
        self.register_subset_sum_xside_core_theorem()?;
        self.init_fin_sum()?; // Fin.sum_congr

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: influence_master_type(&c),
            value: influence_master_value(&c),
        })
    }
}

#[cfg(test)]
mod influence_master_tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_influence_master_constructive() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_influence_master()
            .expect("register influence_master");
        env.register_subset_sum_influence_master()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.subsetSum_influence_master");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .expect("influence_master should type-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "influence_master closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
