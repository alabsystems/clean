// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! The existing constructive high-bit bound, shared by the native arithmetic
//! prelude and the Boolean-analysis client. No domain axiom is introduced.
//! The proof is Nat induction over the actual div2/testBit definitions.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

struct BoundConsts {
    nat: Expr,
    bool_ty: Expr,
    bfalse: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    pow: Expr,
    two: Expr,
    nat_lt: Expr,
    nat_le: Expr,
    testbit: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst: Expr,
    or_c: Expr,
    or_rec: Expr,
}
impl BoundConsts {
    fn new() -> Self {
        let c = |name: &str| Expr::const_(Name::from_string(name), vec![]);
        let one = Level::succ(Level::zero());
        Self {
            nat: c("Nat"),
            bool_ty: c("Bool"),
            bfalse: c("Bool.false"),
            zero: c("Nat.zero"),
            succ: c("Nat.succ"),
            add: c("Nat.add"),
            pow: c("Nat.pow"),
            two: Expr::app(c("Nat.succ"), Expr::app(c("Nat.succ"), c("Nat.zero"))),
            nat_lt: c("Nat.lt"),
            nat_le: c("Nat.le"),
            testbit: c("Nat.testBit"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![one]),
            or_c: c("Or"),
            or_rec: c("Or.rec"),
        }
    }
    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    fn add_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add.clone(), [a, b])
    }
    fn div2_of(&self, x: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Nat.div2"), vec![]), x)
    }
    fn div2par_of(&self, x: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Nat.div2Par"), vec![]), x)
    }
    fn pow2(&self, n: Expr) -> Expr {
        Expr::apps(self.pow.clone(), [self.two.clone(), n])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn testbit(&self, n: Expr, i: Expr) -> Expr {
        Expr::apps(self.testbit.clone(), [n, i])
    }
    fn eq_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), a, b])
    }
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), a, b])
    }
    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nat.clone(), a, b, h])
    }
    fn subst_nat(&self, motive: Expr, a: Expr, b: Expr, h: Expr, pa: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.nat.clone(), motive, a, b, h, pa],
        )
    }
    fn or_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.or_c.clone(), [a, b])
    }
}

fn build_lt_two_pow_of_testbit_ge(c: &BoundConsts) -> (Expr, Expr) {
    // hyp(n,m) := ∀ k, le n k → testBit m k = false
    let hyp_ty = |n: &Expr, m: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut hb = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = hb.fresh_local(c.nat.clone());
        let le_nk = c.le(n.clone(), k.clone());
        let (h_id, _h) = hb.fresh_local(le_nk.clone());
        let bit = c.eq_bool(c.testbit(m.clone(), k.clone()), c.bfalse.clone());
        let imp = hb.mk_pi(h_id, BinderInfo::Default, le_nk, bit);
        hb.finish_child(hb.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), imp))
    };
    // P(n) := ∀ m, hyp(n,m) → lt m (2^n)
    let p_of = |n: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = pb.fresh_local(c.nat.clone());
        let h_ty = hyp_ty(n, &m, &pb);
        let (h_id, _h) = pb.fresh_local(h_ty.clone());
        let concl = c.lt(m.clone(), c.pow2(n.clone()));
        let imp = pb.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        pb.finish_child(pb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), imp))
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = p_of(&n, &b);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (n_id, n) = mb.fresh_local(c.nat.clone());
            let body = p_of(&n, &mb);
            mb.finish_child(mb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // ---- base : P 0 := fun m hyp => ... lt m (2^0 ≡ 1) ----
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&vb);
            let (m_id, m) = bb.fresh_local(c.nat.clone());
            let h_ty = hyp_ty(&c.zero, &m, &bb);
            let (h_id, h) = bb.fresh_local(h_ty.clone());
            let all_false = {
                let mut ab = EnvDeclBuilder::child_of(&bb);
                let (k_id, k) = ab.fresh_local(c.nat.clone());
                let zero_le_k = Expr::app(
                    Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                    k.clone(),
                );
                let body = Expr::apps(h.clone(), [k.clone(), zero_le_k]);
                ab.finish_child(ab.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let m_eq_0 = Expr::apps(
                Expr::const_(
                    Name::from_string("Nat.eq_zero_of_testBit_all_false"),
                    vec![],
                ),
                [m.clone(), all_false],
            );
            let one = c.succ_of(c.zero.clone());
            let lt_0_1 = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                [one.clone()],
            );
            let m_eq_0_symm = c.symm_nat(m.clone(), c.zero.clone(), m_eq_0);
            let mt = {
                let mut lb = EnvDeclBuilder::child_of(&bb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.lt(z.clone(), c.pow2(c.zero.clone()));
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let out = c.subst_nat(mt, c.zero.clone(), m.clone(), m_eq_0_symm, lt_0_1);
            let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            bb.finish_child(bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        // ---- step : (n') → P n' → P (succ n') ----
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&vb);
            let (np_id, np) = sb.fresh_local(c.nat.clone());
            let ih_ty = p_of(&np, &sb);
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            let sn = c.succ_of(np.clone());

            let (m_id, m) = sb.fresh_local(c.nat.clone());
            let h_ty = hyp_ty(&sn, &m, &sb);
            let (h_id, h) = sb.fresh_local(h_ty.clone());

            let r = c.div2_of(m.clone()); // div2 m
            let p = c.div2par_of(m.clone()); // div2Par m
            let pn = c.pow2(np.clone()); // 2^n'
            let rr = c.add_of(r.clone(), r.clone()); // r+r
            let rrp = c.add_of(rr.clone(), p.clone()); // (r+r)+p

            let hyp_r = {
                let mut hb = EnvDeclBuilder::child_of(&sb);
                let (k_id, k) = hb.fresh_local(c.nat.clone());
                let le_npk = c.le(np.clone(), k.clone());
                let (hle_id, hle) = hb.fresh_local(le_npk.clone());
                let sls = Expr::apps(
                    Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
                    [np.clone(), k.clone(), hle],
                );
                let body = Expr::apps(h.clone(), [c.succ_of(k.clone()), sls]);
                let lam = hb.mk_lam(hle_id, BinderInfo::Default, le_npk, body);
                hb.finish_child(hb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let ih_r = Expr::apps(ih.clone(), [r.clone(), hyp_r]);

            let one = c.succ_of(c.zero.clone());
            let hp_le_1 = {
                let disj = Expr::app(
                    Expr::const_(Name::from_string("Nat.div2Par_zero_or_one"), vec![]),
                    m.clone(),
                );
                let p_eq_0 = c.eq_nat(p.clone(), c.zero.clone());
                let p_eq_1 = c.eq_nat(p.clone(), one.clone());
                let or_m = {
                    let mut ob = EnvDeclBuilder::child_of(&sb);
                    let or_ty = c.or_ty(p_eq_0.clone(), p_eq_1.clone());
                    let (d_id, _d) = ob.fresh_local(or_ty.clone());
                    ob.finish_child(ob.mk_lam(
                        d_id,
                        BinderInfo::Default,
                        or_ty,
                        c.le(p.clone(), one.clone()),
                    ))
                };
                let inl = {
                    let mut ib = EnvDeclBuilder::child_of(&sb);
                    let (he_id, he) = ib.fresh_local(p_eq_0.clone());
                    let le_0_1 = Expr::apps(
                        Expr::const_(Name::from_string("Nat.le.step"), vec![]),
                        [
                            c.zero.clone(),
                            c.zero.clone(),
                            Expr::apps(
                                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                                [c.zero.clone()],
                            ),
                        ],
                    ); // le 0 (succ 0) ≡ le 0 1
                    let he_symm = c.symm_nat(p.clone(), c.zero.clone(), he);
                    let mz = {
                        let mut lb = EnvDeclBuilder::child_of(&ib);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        lb.finish_child(lb.mk_lam(
                            z_id,
                            BinderInfo::Default,
                            c.nat.clone(),
                            c.le(z.clone(), one.clone()),
                        ))
                    };
                    let out = c.subst_nat(mz, c.zero.clone(), p.clone(), he_symm, le_0_1);
                    ib.finish_child(ib.mk_lam(he_id, BinderInfo::Default, p_eq_0.clone(), out))
                };
                let inr = {
                    let mut rb = EnvDeclBuilder::child_of(&sb);
                    let (he_id, he) = rb.fresh_local(p_eq_1.clone());
                    let le_1_1 = Expr::apps(
                        Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                        [one.clone()],
                    );
                    let he_symm = c.symm_nat(p.clone(), one.clone(), he);
                    let mz = {
                        let mut lb = EnvDeclBuilder::child_of(&rb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        lb.finish_child(lb.mk_lam(
                            z_id,
                            BinderInfo::Default,
                            c.nat.clone(),
                            c.le(z.clone(), one.clone()),
                        ))
                    };
                    let out = c.subst_nat(mz, one.clone(), p.clone(), he_symm, le_1_1);
                    rb.finish_child(rb.mk_lam(he_id, BinderInfo::Default, p_eq_1.clone(), out))
                };
                Expr::apps(c.or_rec.clone(), [p_eq_0, p_eq_1, or_m, inl, inr, disj])
            };

            let le_refl_rr = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                [rr.clone()],
            );
            let step_a = Expr::apps(
                Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
                [
                    rr.clone(),
                    rr.clone(),
                    p.clone(),
                    one.clone(),
                    le_refl_rr,
                    hp_le_1,
                ],
            ); // : le ((r+r)+p) ((r+r)+1) ≡ le ((r+r)+p) (succ (r+r))
            let succ_rr = c.succ_of(rr.clone());
            let step_b = Expr::apps(
                Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
                [rrp.clone(), succ_rr.clone(), step_a],
            ); // : le (succ ((r+r)+p)) (succ (succ (r+r)))

            let succ_r = c.succ_of(r.clone());
            let step_c0 = Expr::apps(
                Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
                [
                    succ_r.clone(),
                    pn.clone(),
                    succ_r.clone(),
                    pn.clone(),
                    ih_r.clone(),
                    ih_r.clone(),
                ],
            ); // : le ((succ r)+(succ r)) (2^n' + 2^n')
            let succ_add = Expr::apps(
                Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
                [r.clone(), succ_r.clone()],
            ); // : (succ r)+(succ r) = succ (r + succ r) ≡ succ (succ (r+r))
            let pn_pn = c.add_of(pn.clone(), pn.clone());
            let succ_succ_rr = c.succ_of(succ_rr.clone());
            let m_le_z = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                lb.finish_child(lb.mk_lam(
                    z_id,
                    BinderInfo::Default,
                    c.nat.clone(),
                    c.le(z.clone(), pn_pn.clone()),
                ))
            };
            let ss_rr = c.add_of(succ_r.clone(), succ_r.clone());
            let step_c = c.subst_nat(m_le_z, ss_rr, succ_succ_rr.clone(), succ_add, step_c0);

            let chain = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
                [
                    c.succ_of(rrp.clone()),
                    succ_succ_rr.clone(),
                    pn_pn.clone(),
                    step_b,
                    step_c,
                ],
            ); // : le (succ ((r+r)+p)) (2^n'+2^n') ≡ lt ((r+r)+p) (2^n'+2^n')

            let rejoin = Expr::app(
                Expr::const_(Name::from_string("Nat.div2_rejoin"), vec![]),
                m.clone(),
            ); // : m = (r+r)+p
            let rejoin_symm = c.symm_nat(m.clone(), rrp.clone(), rejoin); // : (r+r)+p = m
            let m_lt_z = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                lb.finish_child(lb.mk_lam(
                    z_id,
                    BinderInfo::Default,
                    c.nat.clone(),
                    c.lt(z.clone(), pn_pn.clone()),
                ))
            };
            let lt_m_pnpn = c.subst_nat(m_lt_z, rrp.clone(), m.clone(), rejoin_symm, chain);

            let pts = Expr::app(
                Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
                np.clone(),
            ); // : 2^(succ n') = 2^n'+2^n'
            let pts_symm = c.symm_nat(c.pow2(sn.clone()), pn_pn.clone(), pts); // : (2^n'+2^n') = 2^(succ n')
            let m_lt_z2 = {
                let mut lb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                lb.finish_child(lb.mk_lam(
                    z_id,
                    BinderInfo::Default,
                    c.nat.clone(),
                    c.lt(m.clone(), z.clone()),
                ))
            };
            let out = c.subst_nat(
                m_lt_z2,
                pn_pn.clone(),
                c.pow2(sn.clone()),
                pts_symm,
                lt_m_pnpn,
            );

            let lam = sb.mk_lam(h_id, BinderInfo::Default, h_ty, out);
            let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
            sb.finish_child(sb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        // Nat.rec.{0} motive base step n
        let rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let (n_id, n) = vb.fresh_local(c.nat.clone());
        let rec_app = Expr::apps(rec0, [motive, base, step, n.clone()]);
        vb.finish(vb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app))
    };
    (type_, value)
}

impl Environment {
    /// Install the existing axiom-free theorem independently of the optional
    /// Boolean-analysis bundle. Genuine imported declarations stay authoritative.
    pub(crate) fn register_nat_high_bit_bound_proof(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Nat.lt_two_pow_of_testBit_ge");
        self.init_or()?;
        self.register_nat_eq_of_testbit_proof()?;
        self.register_nat_pow_two_succ_proof()?;
        self.register_nat_arith_order_proofs()?;
        self.register_nat_succ_add_proof()?;
        self.register_nat_ble_le_lemmas()?;
        let (type_, value) = build_lt_two_pow_of_testbit_ge(&BoundConsts::new());
        self.ensure_exact_checked_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })?;
        Ok(())
    }
}
