// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **pointwise ring keystone** of the `noiseFn`
//! coordinate-peel.
//!
//! After the density point-peel turns each cube-half summand into
//! `p·(d·(1+ρ))` / `q·(d·(1−ρ))` (LOW bit; `p := F(extendF…)`, `q :=
//! F(extendT…)`, `d := noiseDensityW ρ n …`), the two halves must be regrouped
//! into the `gPart`/`hPart` integrands. The pure-`Rat` identity that does it is:
//!
//! ```text
//! BoolAnalysis.peel_pointwise_keystone :
//!   ∀ (p q d ρ : Rat),
//!     Rat.add (Rat.mul p (Rat.mul d (Rat.add 1 ρ)))
//!             (Rat.mul q (Rat.mul d (Rat.sub 1 ρ)))
//!       = Rat.add (Rat.mul (Rat.add p q) d)
//!                 (Rat.mul ρ (Rat.mul (Rat.sub p q) d))
//! ```
//!
//! i.e. `p·(d·(1+ρ)) + q·(d·(1−ρ)) = (p+q)·d + ρ·((p−q)·d)`. The `gPart` leg
//! `(p+q)·d` collects the unweighted half-sum into `noiseFn ρ n (gPart n F)`, and
//! the `ρ·((p−q)·d)` leg collects the ρ-weighted half-sum into
//! `ρ·noiseFn ρ n (hPart n F)` (HIGH mirror flips ρ→−ρ, giving the `−ρ·…` sign).
//!
//! ## Proof route (pure Rat ring chain)
//!
//! Expand both legs, cancel the ρ-cross terms, and refactor:
//! `p·(d·(1+ρ)) = p·d + ρ·(p·d)` and `q·(d·(1−ρ)) = q·d − ρ·(q·d)`, so the sum is
//! `(p·d + q·d) + (ρ·(p·d) − ρ·(q·d)) = (p+q)·d + ρ·((p−q)·d)`. Every step is a
//! `Rat.left_distrib`/`right_distrib`/`mul_assoc`/`mul_comm`/`add_assoc`/
//! `add_comm` congruence, so the closure is empty and the theorem is
//! `ProofQuality::Constructive`.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Initialize the pointwise ring keystone layer.
    ///
    /// Registers `BoolAnalysis.peel_pointwise_keystone` as a kernel-checked
    /// `Declaration::Theorem`. Idempotent. No axiom is added or removed.
    pub fn init_boolean_analysis_pointwise_keystone(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis_ring_identities()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }

        let name = Name::from_string("BoolAnalysis.peel_pointwise_keystone");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = KeystoneConsts::new();
        let ty = build_keystone_type(&c);
        let value = build_keystone_proof(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })?;

        let high = Name::from_string("BoolAnalysis.peel_pointwise_keystone_high");
        if self.get_const(&high).is_none() {
            let ty = build_keystone_high_type(&c);
            let value = build_keystone_high_proof(&c);
            self.add_decl(Declaration::Theorem {
                name: high,
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }
        Ok(())
    }
}

/// `∀ p q d ρ, p·(d·(1−ρ)) + q·(d·(1+ρ)) = (p+q)·d + (−ρ)·((p−q)·d)`.
///
/// The HIGH-half mirror of `peel_pointwise_keystone`: the cube's top bit is true,
/// so the inner `extendF` leg carries the `(1−ρ)` factor (peel `_tf`, `pm true ·
/// pm false ≡ −1`) and the `extendT` leg the `(1+ρ)` factor (peel `_tt`, `pm true
/// · pm true ≡ 1`) — the swap of the LOW factors. The cross term flips to `(−ρ)`,
/// so the operator-peel `noiseFn_succ_high` reads `noiseFn(gPart) − ρ·noiseFn(liftH)`.
fn build_keystone_high_type(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());
    let (d_id, d) = b.fresh_local(c.rat());
    let (rho_id, rho) = b.fresh_local(c.rat());
    let lhs = keystone_high_lhs(c, &p, &q, &d, &rho);
    let rhs = keystone_high_rhs(c, &p, &q, &d, &rho);
    let concl = c.eq(lhs, rhs);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), concl);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(q_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(p_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// `p·(d·(1−ρ)) + q·(d·(1+ρ))`.
fn keystone_high_lhs(c: &KeystoneConsts, p: &Expr, q: &Expr, d: &Expr, rho: &Expr) -> Expr {
    let one_minus = c.sub(c.one(), rho.clone()); // 1−ρ
    let one_plus = c.add(c.one(), rho.clone()); // 1+ρ
    let leg_p = c.mul(p.clone(), c.mul(d.clone(), one_minus));
    let leg_q = c.mul(q.clone(), c.mul(d.clone(), one_plus));
    c.add(leg_p, leg_q)
}

/// `(p+q)·d + (−ρ)·((p−q)·d)`.
fn keystone_high_rhs(c: &KeystoneConsts, p: &Expr, q: &Expr, d: &Expr, rho: &Expr) -> Expr {
    let pq = c.add(p.clone(), q.clone()); // p+q
    let p_minus_q = c.sub(p.clone(), q.clone()); // p−q
    let g_leg = c.mul(pq, d.clone()); // (p+q)·d
    let neg_rho = c.r.neg(rho.clone()); // −ρ
    let h_leg = c.mul(neg_rho, c.mul(p_minus_q, d.clone())); // (−ρ)·((p−q)·d)
    c.add(g_leg, h_leg)
}

/// Proof of `peel_pointwise_keystone_high`.
///
/// Derive from the LOW keystone at `ρ := −ρ`. `K1 := keystone p q d (−ρ)` has RHS
/// `(p+q)·d + (−ρ)·((p−q)·d)` — exactly the HIGH RHS. Its LHS is
/// `p·(d·(1+(−ρ))) + q·(d·(1−(−ρ)))`; the first leg is **defeq** to the HIGH first
/// leg (`1−ρ ≡ 1+(−ρ)`), and the second leg differs only by `ρ ↦ −(−ρ)`. A single
/// congruence (lift `Eq.symm (neg_neg ρ)` through `q·(d·(1+·))`) bridges the HIGH
/// second leg `q·(d·(1+ρ))` to `q·(d·(1−(−ρ)))`, then `Eq.trans` chains onto `K1`.
fn build_keystone_high_proof(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());
    let (d_id, d) = b.fresh_local(c.rat());
    let (rho_id, rho) = b.fresh_local(c.rat());

    let neg_rho = c.r.neg(rho.clone()); // −ρ
    let dd_neg_neg = c.r.dneg(rho.clone()); // neg_neg ρ : −(−ρ) = ρ
    let neg_neg_rho = c.r.neg(neg_rho.clone()); // −(−ρ)
                                                // symm : ρ = −(−ρ)
    let symm_dneg = c.symm(neg_neg_rho.clone(), rho.clone(), dd_neg_neg);

    // bridge the HIGH second leg's factor: (1+ρ) = (1+(−(−ρ)))
    let one_plus = c.add(c.one(), rho.clone()); // 1+ρ
    let one_plus_nn = c.add(c.one(), neg_neg_rho.clone()); // 1+(−(−ρ))
    let cong_factor = c.r.cong_right(
        &b,
        &c.add_c(),
        rho.clone(),
        neg_neg_rho.clone(),
        c.one(),
        symm_dneg,
    );
    // lift through `q·(d·(·))`:  q·(d·(1+ρ)) = q·(d·(1+(−(−ρ))))
    let d_one_plus = c.mul(d.clone(), one_plus.clone());
    let d_one_plus_nn = c.mul(d.clone(), one_plus_nn.clone());
    let cong_d = c.r.cong_right(
        &b,
        &c.mul_c(),
        one_plus.clone(),
        one_plus_nn.clone(),
        d.clone(),
        cong_factor,
    );
    let q_leg = c.mul(q.clone(), d_one_plus.clone()); // q·(d·(1+ρ))
    let q_leg_nn = c.mul(q.clone(), d_one_plus_nn.clone()); // q·(d·(1+(−(−ρ))))
    let cong_q = c.r.cong_right(
        &b,
        &c.mul_c(),
        d_one_plus.clone(),
        d_one_plus_nn.clone(),
        q.clone(),
        cong_d,
    );

    // HIGH LHS = p·(d·(1−ρ)) + q·(d·(1+ρ)).
    let high_lhs = keystone_high_lhs(c, &p, &q, &d, &rho);
    // first leg p·(d·(1−ρ)) (defeq to K1's p·(d·(1+(−ρ))) — kept fixed).
    let one_minus = c.sub(c.one(), rho.clone());
    let p_leg = c.mul(p.clone(), c.mul(d.clone(), one_minus));
    // cong: high_lhs = p_leg + q_leg_nn   (rewrite second slot via cong_q).
    let mid = c.add(p_leg.clone(), q_leg_nn.clone());
    let cong_sum = c.r.cong_right(
        &b,
        &c.add_c(),
        q_leg.clone(),
        q_leg_nn.clone(),
        p_leg.clone(),
        cong_q,
    );

    // K1 := keystone p q d (−ρ) : K1_lhs = (p+q)·d + (−ρ)·((p−q)·d).
    let k1 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.peel_pointwise_keystone"),
            vec![],
        ),
        [p.clone(), q.clone(), d.clone(), neg_rho.clone()],
    );
    let rhs = keystone_high_rhs(c, &p, &q, &d, &rho);
    // `mid` is defeq to K1's LHS (first leg: 1−ρ ≡ 1+(−ρ); second leg: 1+(−(−ρ)) ≡
    // 1−(−ρ)), so `Eq.trans cong_sum k1 : high_lhs = rhs`.
    let proof = c.trans(high_lhs, mid, rhs, cong_sum, k1);

    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), proof);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(q_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(p_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Constants + smart-constructors for the pointwise keystone. Wraps `RingConsts`
/// and adds the `Rat.mul_one` accessor the keystone needs.
struct KeystoneConsts {
    r: RingConsts,
    mul_one: Expr,
}

impl KeystoneConsts {
    fn new() -> Self {
        Self {
            r: RingConsts::new(),
            mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.r.rat()
    }
    fn one(&self) -> Expr {
        self.r.one()
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.r.add(a, b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.r.mul(a, b)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.r.sub(a, b)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.r.eq(a, b)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.r.trans(a, b, cc, h1, h2)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.r.symm(a, b, h)
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    fn add_c(&self) -> Expr {
        self.r.add_const()
    }
    fn mul_c(&self) -> Expr {
        self.r.mul_const()
    }
}

/// `∀ p q d ρ, p·(d·(1+ρ)) + q·(d·(1−ρ)) = (p+q)·d + ρ·((p−q)·d)`.
fn build_keystone_type(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());
    let (d_id, d) = b.fresh_local(c.rat());
    let (rho_id, rho) = b.fresh_local(c.rat());
    let lhs = keystone_lhs(c, &p, &q, &d, &rho);
    let rhs = keystone_rhs(c, &p, &q, &d, &rho);
    let concl = c.eq(lhs, rhs);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), concl);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(q_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(p_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// `p·(d·(1+ρ)) + q·(d·(1−ρ))`.
fn keystone_lhs(c: &KeystoneConsts, p: &Expr, q: &Expr, d: &Expr, rho: &Expr) -> Expr {
    let one_plus = c.add(c.one(), rho.clone()); // 1+ρ
    let one_minus = c.sub(c.one(), rho.clone()); // 1−ρ
    let leg_p = c.mul(p.clone(), c.mul(d.clone(), one_plus));
    let leg_q = c.mul(q.clone(), c.mul(d.clone(), one_minus));
    c.add(leg_p, leg_q)
}

/// `(p+q)·d + ρ·((p−q)·d)`.
fn keystone_rhs(c: &KeystoneConsts, p: &Expr, q: &Expr, d: &Expr, rho: &Expr) -> Expr {
    let pq = c.add(p.clone(), q.clone()); // p+q
    let p_minus_q = c.sub(p.clone(), q.clone()); // p−q
    let g_leg = c.mul(pq, d.clone()); // (p+q)·d
    let h_leg = c.mul(rho.clone(), c.mul(p_minus_q, d.clone())); // ρ·((p−q)·d)
    c.add(g_leg, h_leg)
}

/// Build the proof term for `BoolAnalysis.peel_pointwise_keystone`.
fn build_keystone_proof(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.rat());
    let (q_id, q) = b.fresh_local(c.rat());
    let (d_id, d) = b.fresh_local(c.rat());
    let (rho_id, rho) = b.fresh_local(c.rat());

    let proof = keystone_chain(c, &b, &p, &q, &d, &rho);

    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), proof);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(q_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(p_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// `p·(d·(1+ρ)) = p·d + ρ·(p·d)`.
///
/// `d·(1+ρ) = d·1 + d·ρ` [ldist] = `d + d·ρ` [mul_one on d·1]; then
/// `p·(d + d·ρ) = p·d + p·(d·ρ)` [ldist]; `p·(d·ρ) = (p·d)·ρ` [symm mul_assoc]
/// `= ρ·(p·d)` [mul_comm], lifted under `p·d + ·`.
fn expand_plus_leg(
    c: &KeystoneConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    d: &Expr,
    rho: &Expr,
) -> Expr {
    let one = c.one();
    let one_plus = c.add(one.clone(), rho.clone()); // 1+ρ
    let lhs = c.mul(p.clone(), c.mul(d.clone(), one_plus.clone())); // p·(d·(1+ρ))

    // inner : d·(1+ρ) = d + d·ρ
    let d_one = c.mul(d.clone(), one.clone()); // d·1
    let d_rho = c.mul(d.clone(), rho.clone()); // d·ρ
    let d1_drho = c.add(d_one.clone(), d_rho.clone()); // d·1 + d·ρ
    let ldist_inner = c.r.ldist(d.clone(), one.clone(), rho.clone()); // d·(1+ρ) = d·1 + d·ρ
    let d_drho = c.add(d.clone(), d_rho.clone()); // d + d·ρ
    let h_mul_one = c.mul_one(d.clone()); // d·1 = d
    let cong_d1 = c.r.cong_left(
        parent,
        &c.add_c(),
        d_one.clone(),
        d.clone(),
        d_rho.clone(),
        h_mul_one,
    );
    let inner = c.trans(
        c.mul(d.clone(), one_plus.clone()),
        d1_drho,
        d_drho.clone(),
        ldist_inner,
        cong_d1,
    );

    // lift inner under p·· : p·(d·(1+ρ)) = p·(d + d·ρ)
    let p_ddrho = c.mul(p.clone(), d_drho.clone());
    let cong_lhs = c.r.cong_right(
        parent,
        &c.mul_c(),
        c.mul(d.clone(), one_plus.clone()),
        d_drho.clone(),
        p.clone(),
        inner,
    );

    // ldist : p·(d + d·ρ) = p·d + p·(d·ρ)
    let p_d = c.mul(p.clone(), d.clone()); // p·d
    let p_drho = c.mul(p.clone(), d_rho.clone()); // p·(d·ρ)
    let pd_pdrho = c.add(p_d.clone(), p_drho.clone());
    let ldist_outer = c.r.ldist(p.clone(), d.clone(), d_rho.clone());

    // p·(d·ρ) = (p·d)·ρ [symm mul_assoc] then = ρ·(p·d) [mul_comm]
    let pd_rho = c.mul(p_d.clone(), rho.clone()); // (p·d)·ρ
    let massoc = c.r.massoc(p.clone(), d.clone(), rho.clone()); // (p·d)·ρ = p·(d·ρ)
    let symm_massoc = c.symm(pd_rho.clone(), p_drho.clone(), massoc); // p·(d·ρ) = (p·d)·ρ
    let rho_pd = c.mul(rho.clone(), p_d.clone()); // ρ·(p·d)
    let mcomm = c.r.mcomm(p_d.clone(), rho.clone()); // (p·d)·ρ = ρ·(p·d)
    let pdrho_to_rhopd = c.trans(p_drho.clone(), pd_rho, rho_pd.clone(), symm_massoc, mcomm);
    // lift under p·d + · : (p·d + p·(d·ρ)) = (p·d + ρ·(p·d))
    let pd_rhopd = c.add(p_d.clone(), rho_pd.clone());
    let cong_cross = c.r.cong_right(
        parent,
        &c.add_c(),
        p_drho.clone(),
        rho_pd.clone(),
        p_d.clone(),
        pdrho_to_rhopd,
    );

    // chain: lhs = p·(d+d·ρ) = (p·d + p·(d·ρ)) = (p·d + ρ·(p·d))
    let s = c.trans(
        lhs.clone(),
        p_ddrho.clone(),
        pd_pdrho.clone(),
        cong_lhs,
        ldist_outer,
    );
    c.trans(lhs, pd_pdrho, pd_rhopd, s, cong_cross)
}

/// `q·(d·(1−ρ)) = q·d + (−(ρ·(q·d)))`.
///
/// `1−ρ ≡ 1+(−ρ)` (reducible `Rat.sub`), so the leg is `q·(d·(1+(−ρ)))`.
/// Same expansion as `expand_plus_leg` with ρ ↦ −ρ gives
/// `q·d + (−ρ)·... → q·d + ρ·((q·d)·(−1))`; we instead land
/// `q·d + (−(ρ·(q·d)))` so the two cross terms combine to `ρ·((p−q)·d)`.
fn expand_minus_leg(
    c: &KeystoneConsts,
    parent: &EnvDeclBuilder,
    q: &Expr,
    d: &Expr,
    rho: &Expr,
) -> Expr {
    let one = c.one();
    let neg_rho = c.r.neg(rho.clone()); // −ρ
    let one_minus = c.sub(one.clone(), rho.clone()); // 1−ρ ≡ 1+(−ρ)
    let lhs = c.mul(q.clone(), c.mul(d.clone(), one_minus.clone())); // q·(d·(1−ρ))

    // inner : d·(1−ρ) = d + d·(−ρ)
    let d_one = c.mul(d.clone(), one.clone()); // d·1
    let d_nrho = c.mul(d.clone(), neg_rho.clone()); // d·(−ρ)
    let d1_dnrho = c.add(d_one.clone(), d_nrho.clone()); // d·1 + d·(−ρ)
                                                         // ldist d 1 (−ρ) : d·(1+(−ρ)) = d·1 + d·(−ρ); LHS defeq d·(1−ρ).
    let ldist_inner = c.r.ldist(d.clone(), one.clone(), neg_rho.clone());
    let d_dnrho = c.add(d.clone(), d_nrho.clone()); // d + d·(−ρ)
    let h_mul_one = c.mul_one(d.clone()); // d·1 = d
    let cong_d1 = c.r.cong_left(
        parent,
        &c.add_c(),
        d_one.clone(),
        d.clone(),
        d_nrho.clone(),
        h_mul_one,
    );
    let inner = c.trans(
        c.mul(d.clone(), one_minus.clone()),
        d1_dnrho,
        d_dnrho.clone(),
        ldist_inner,
        cong_d1,
    );

    // lift under q·· : q·(d·(1−ρ)) = q·(d + d·(−ρ))
    let q_ddnrho = c.mul(q.clone(), d_dnrho.clone());
    let cong_lhs = c.r.cong_right(
        parent,
        &c.mul_c(),
        c.mul(d.clone(), one_minus.clone()),
        d_dnrho.clone(),
        q.clone(),
        inner,
    );

    // ldist : q·(d + d·(−ρ)) = q·d + q·(d·(−ρ))
    let q_d = c.mul(q.clone(), d.clone()); // q·d
    let q_dnrho = c.mul(q.clone(), d_nrho.clone()); // q·(d·(−ρ))
    let qd_qdnrho = c.add(q_d.clone(), q_dnrho.clone());
    let ldist_outer = c.r.ldist(q.clone(), d.clone(), d_nrho.clone());

    // q·(d·(−ρ)) = (q·d)·(−ρ) [symm massoc] = (q·d)·(−ρ)
    let qd_nrho = c.mul(q_d.clone(), neg_rho.clone()); // (q·d)·(−ρ)
    let massoc = c.r.massoc(q.clone(), d.clone(), neg_rho.clone()); // (q·d)·(−ρ) = q·(d·(−ρ))
    let symm_massoc = c.symm(qd_nrho.clone(), q_dnrho.clone(), massoc); // q·(d·(−ρ)) = (q·d)·(−ρ)
                                                                        // (q·d)·(−ρ) = −((q·d)·ρ) [mul_neg], and (q·d)·ρ = ρ·(q·d) [mul_comm], so
                                                                        //   (q·d)·(−ρ) = −(ρ·(q·d)).
    let qd_rho = c.mul(q_d.clone(), rho.clone()); // (q·d)·ρ
    let neg_qd_rho = c.r.neg(qd_rho.clone()); // −((q·d)·ρ)
    let mneg = c.r.mneg(q_d.clone(), rho.clone()); // (q·d)·(−ρ) = −((q·d)·ρ)
    let rho_qd = c.mul(rho.clone(), q_d.clone()); // ρ·(q·d)
    let neg_rho_qd = c.r.neg(rho_qd.clone()); // −(ρ·(q·d))
    let mcomm = c.r.mcomm(q_d.clone(), rho.clone()); // (q·d)·ρ = ρ·(q·d)
                                                     // cong_neg : −((q·d)·ρ) = −(ρ·(q·d))
    let cong_neg = cong_neg_unary(c, qd_rho.clone(), rho_qd.clone(), mcomm);
    // (q·d)·(−ρ) = −((q·d)·ρ) = −(ρ·(q·d))
    let qdnrho_chain = c.trans(
        qd_nrho.clone(),
        neg_qd_rho.clone(),
        neg_rho_qd.clone(),
        mneg,
        cong_neg,
    );
    // q·(d·(−ρ)) = −(ρ·(q·d))
    let q_dnrho_eq = c.trans(
        q_dnrho.clone(),
        qd_nrho,
        neg_rho_qd.clone(),
        symm_massoc,
        qdnrho_chain,
    );
    // lift under q·d + · : (q·d + q·(d·(−ρ))) = (q·d + (−(ρ·(q·d))))
    let qd_negrhoqd = c.add(q_d.clone(), neg_rho_qd.clone());
    let cong_cross = c.r.cong_right(
        parent,
        &c.add_c(),
        q_dnrho.clone(),
        neg_rho_qd.clone(),
        q_d.clone(),
        q_dnrho_eq,
    );

    // chain: lhs = q·(d+d·(−ρ)) = (q·d + q·(d·(−ρ))) = (q·d + (−(ρ·(q·d))))
    let s = c.trans(
        lhs.clone(),
        q_ddnrho.clone(),
        qd_qdnrho.clone(),
        cong_lhs,
        ldist_outer,
    );
    c.trans(lhs, qd_qdnrho, qd_negrhoqd, s, cong_cross)
}

/// `congrArg.{1,1} Rat Rat a b Rat.neg h : −a = −b`.
fn cong_neg_unary(c: &KeystoneConsts, a: Expr, b: Expr, h: Expr) -> Expr {
    let u1 = crate::level::Level::succ(crate::level::Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]);
    let neg_c = Expr::const_(Name::from_string("Rat.neg"), vec![]);
    Expr::apps(congr_arg, [c.rat(), c.rat(), a, b, neg_c, h])
}

/// `(−q)·d = −(q·d)`.
///
/// `(−q)·d = d·(−q)` [mul_comm] = `−(d·q)` [mul_neg] = `−(q·d)` [cong_neg mul_comm].
/// Avoids the unregistered `Rat.neg_mul`, using only `mul_comm` + `mul_neg`.
fn neg_mul_eq(c: &KeystoneConsts, q: &Expr, d: &Expr) -> Expr {
    let neg_q = c.r.neg(q.clone());
    let neg_q_d = c.mul(neg_q.clone(), d.clone()); // (−q)·d
    let d_neg_q = c.mul(d.clone(), neg_q.clone()); // d·(−q)
    let comm1 = c.r.mcomm(neg_q.clone(), d.clone()); // (−q)·d = d·(−q)
    let d_q = c.mul(d.clone(), q.clone()); // d·q
    let neg_dq = c.r.neg(d_q.clone()); // −(d·q)
    let mneg = c.r.mneg(d.clone(), q.clone()); // d·(−q) = −(d·q)
    let q_d = c.mul(q.clone(), d.clone()); // q·d
    let neg_qd = c.r.neg(q_d.clone()); // −(q·d)
    let comm2 = c.r.mcomm(d.clone(), q.clone()); // d·q = q·d
    let cong = cong_neg_unary(c, d_q.clone(), q_d.clone(), comm2); // −(d·q) = −(q·d)
    let s = c.trans(neg_q_d.clone(), d_neg_q, neg_dq.clone(), comm1, mneg);
    c.trans(neg_q_d, neg_dq, neg_qd, s, cong)
}

/// The full LHS→RHS chain.
///
/// LHS = `p·(d·(1+ρ)) + q·(d·(1−ρ))`
///     = `(p·d + ρ·(p·d)) + (q·d + (−(ρ·(q·d))))`   [expand both legs]
///     = `(p·d + q·d) + (ρ·(p·d) + (−(ρ·(q·d))))`   [comm/assoc regroup]
///     = `(p+q)·d + ρ·((p−q)·d)`                     [right_distrib fold + ρ-factor]
fn keystone_chain(
    c: &KeystoneConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    d: &Expr,
    rho: &Expr,
) -> Expr {
    let lhs = keystone_lhs(c, p, q, d, rho);

    // expanded legs
    let p_d = c.mul(p.clone(), d.clone());
    let q_d = c.mul(q.clone(), d.clone());
    let rho_pd = c.mul(rho.clone(), p_d.clone());
    let rho_qd = c.mul(rho.clone(), q_d.clone());
    let neg_rho_qd = c.r.neg(rho_qd.clone());

    let leg_p_exp = c.add(p_d.clone(), rho_pd.clone()); // p·d + ρ·(p·d)
    let leg_q_exp = c.add(q_d.clone(), neg_rho_qd.clone()); // q·d + (−(ρ·(q·d)))

    let h_leg_p = expand_plus_leg(c, parent, p, d, rho);
    let h_leg_q = expand_minus_leg(c, parent, q, d, rho);

    // Lift both leg-rewrites into the outer sum.
    //   lhs = (leg_p_exp) + q·(d·(1−ρ))   [cong_left along h_leg_p]
    let leg_p_raw = {
        let one_plus = c.add(c.one(), rho.clone());
        c.mul(p.clone(), c.mul(d.clone(), one_plus))
    };
    let leg_q_raw = {
        let one_minus = c.sub(c.one(), rho.clone());
        c.mul(q.clone(), c.mul(d.clone(), one_minus))
    };
    let mid1 = c.add(leg_p_exp.clone(), leg_q_raw.clone());
    let cong_left = c.r.cong_left(
        parent,
        &c.add_c(),
        leg_p_raw.clone(),
        leg_p_exp.clone(),
        leg_q_raw.clone(),
        h_leg_p,
    );
    //   = (leg_p_exp) + (leg_q_exp)       [cong_right along h_leg_q]
    let expanded_sum = c.add(leg_p_exp.clone(), leg_q_exp.clone());
    let cong_right = c.r.cong_right(
        parent,
        &c.add_c(),
        leg_q_raw.clone(),
        leg_q_exp.clone(),
        leg_p_exp.clone(),
        h_leg_q,
    );

    // Now regroup: ((p·d + ρ·(p·d)) + (q·d + (−(ρ·(q·d)))))
    //            = ((p·d + q·d) + (ρ·(p·d) + (−(ρ·(q·d)))))
    let regroup = regroup_four(c, parent, &p_d, &rho_pd, &q_d, &neg_rho_qd);
    let pd_qd = c.add(p_d.clone(), q_d.clone()); // p·d + q·d
    let cross = c.add(rho_pd.clone(), neg_rho_qd.clone()); // ρ·(p·d) + (−(ρ·(q·d)))
    let regrouped = c.add(pd_qd.clone(), cross.clone());

    // Fold p·d + q·d = (p+q)·d  [symm right_distrib]
    let pq = c.add(p.clone(), q.clone());
    let pq_d = c.mul(pq.clone(), d.clone());
    let rdist = c.r.rdist(p.clone(), q.clone(), d.clone()); // (p+q)·d = p·d + q·d
    let symm_rdist = c.symm(pq_d.clone(), pd_qd.clone(), rdist); // p·d + q·d = (p+q)·d
    let g_folded = c.add(pq_d.clone(), cross.clone());
    let cong_g = c.r.cong_left(
        parent,
        &c.add_c(),
        pd_qd.clone(),
        pq_d.clone(),
        cross.clone(),
        symm_rdist,
    );

    // Fold the cross term: ρ·(p·d) + (−(ρ·(q·d))) = ρ·((p−q)·d)
    let cross_fold = fold_cross(c, parent, p, q, d, rho);
    let p_minus_q = c.sub(p.clone(), q.clone());
    let h_leg = c.mul(rho.clone(), c.mul(p_minus_q.clone(), d.clone())); // ρ·((p−q)·d)
    let rhs = c.add(pq_d.clone(), h_leg.clone());
    let cong_h = c.r.cong_right(
        parent,
        &c.add_c(),
        cross.clone(),
        h_leg.clone(),
        pq_d.clone(),
        cross_fold,
    );

    // chain everything
    let s = c.trans(
        lhs.clone(),
        mid1.clone(),
        expanded_sum.clone(),
        cong_left,
        cong_right,
    );
    let s = c.trans(lhs.clone(), expanded_sum, regrouped.clone(), s, regroup);
    let s = c.trans(lhs.clone(), regrouped, g_folded.clone(), s, cong_g);
    c.trans(lhs, g_folded, rhs, s, cong_h)
}

/// `(a + b) + (cc + dd) = (a + cc) + (b + dd)`  — the four-term commutative
/// regroup, via `Rat.add_assoc` / `Rat.add_comm` only.
fn regroup_four(
    c: &KeystoneConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bb: &Expr,
    cc: &Expr,
    dd: &Expr,
) -> Expr {
    // (a+b)+(c+d)
    let a_b = c.add(a.clone(), bb.clone());
    let c_d = c.add(cc.clone(), dd.clone());
    let lhs = c.add(a_b.clone(), c_d.clone());

    // step1: (a+b)+(c+d) = a + (b + (c+d))   [add_assoc a b (c+d)]
    let assoc1 = c.r.aassoc(a.clone(), bb.clone(), c_d.clone());
    let b_cd = c.add(bb.clone(), c_d.clone()); // b+(c+d)
    let a_bcd = c.add(a.clone(), b_cd.clone());

    // inner: b + (c+d) = c + (b+d)
    //   b+(c+d) = (b+c)+d  [symm assoc] = (c+b)+d [comm] = c+(b+d) [assoc]
    let b_c = c.add(bb.clone(), cc.clone());
    let bc_d = c.add(b_c.clone(), dd.clone());
    let assoc_in1 = c.r.aassoc(bb.clone(), cc.clone(), dd.clone()); // (b+c)+d = b+(c+d)
    let symm_in1 = c.symm(bc_d.clone(), b_cd.clone(), assoc_in1); // b+(c+d) = (b+c)+d
    let c_b = c.add(cc.clone(), bb.clone());
    let cb_d = c.add(c_b.clone(), dd.clone());
    let comm_in = c.r.acomm(bb.clone(), cc.clone()); // b+c = c+b
    let cong_comm = c.r.cong_left(
        parent,
        &c.add_c(),
        b_c.clone(),
        c_b.clone(),
        dd.clone(),
        comm_in,
    );
    let assoc_in2 = c.r.aassoc(cc.clone(), bb.clone(), dd.clone()); // (c+b)+d = c+(b+d)
    let b_d = c.add(bb.clone(), dd.clone());
    let c_bd = c.add(cc.clone(), b_d.clone());
    let inner = c.trans(
        b_cd.clone(),
        bc_d.clone(),
        cb_d.clone(),
        symm_in1,
        cong_comm,
    );
    let inner = c.trans(b_cd.clone(), cb_d, c_bd.clone(), inner, assoc_in2);

    // lift inner under a + · : a+(b+(c+d)) = a+(c+(b+d))
    let a_cbd = c.add(a.clone(), c_bd.clone());
    let cong_a = c.r.cong_right(
        parent,
        &c.add_c(),
        b_cd.clone(),
        c_bd.clone(),
        a.clone(),
        inner,
    );

    // a+(c+(b+d)) = (a+c)+(b+d)  [symm assoc a c (b+d)]
    let a_c = c.add(a.clone(), cc.clone());
    let ac_bd = c.add(a_c.clone(), b_d.clone());
    let assoc_out = c.r.aassoc(a.clone(), cc.clone(), b_d.clone()); // (a+c)+(b+d) = a+(c+(b+d))
    let symm_out = c.symm(ac_bd.clone(), a_cbd.clone(), assoc_out);

    // chain: lhs = a_bcd [assoc1] = a_cbd [cong_a] = ac_bd [symm_out]
    let s = c.trans(lhs.clone(), a_bcd.clone(), a_cbd.clone(), assoc1, cong_a);
    c.trans(lhs, a_cbd, ac_bd, s, symm_out)
}

/// `ρ·(p·d) + (−(ρ·(q·d))) = ρ·((p−q)·d)`.
///
/// `ρ·((p−q)·d)` with `p−q ≡ p+(−q)`:
///   `(p−q)·d = p·d + (−q)·d`  [right_distrib]; `(−q)·d = −(q·d)` [neg_mul];
///   so `(p−q)·d = p·d + (−(q·d))`, and `ρ·((p−q)·d) = ρ·(p·d) + ρ·(−(q·d))`
///   [left_distrib]; `ρ·(−(q·d)) = −(ρ·(q·d))` [mul_neg]. We prove the symmetric
///   direction and `Eq.symm` it.
fn fold_cross(
    c: &KeystoneConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    d: &Expr,
    rho: &Expr,
) -> Expr {
    let neg_q = c.r.neg(q.clone());
    let p_minus_q = c.sub(p.clone(), q.clone()); // p−q ≡ p+(−q)
    let target = c.mul(rho.clone(), c.mul(p_minus_q.clone(), d.clone())); // ρ·((p−q)·d)

    let p_d = c.mul(p.clone(), d.clone());
    let q_d = c.mul(q.clone(), d.clone());
    let rho_pd = c.mul(rho.clone(), p_d.clone());
    let rho_qd = c.mul(rho.clone(), q_d.clone());
    let neg_rho_qd = c.r.neg(rho_qd.clone());
    let cross = c.add(rho_pd.clone(), neg_rho_qd.clone()); // ρ·(p·d) + (−(ρ·(q·d)))

    // Build target → cross, then symm.
    // (p−q)·d ≡ (p+(−q))·d. rdist p (−q) d : (p+(−q))·d = p·d + (−q)·d.
    let neg_q_d = c.mul(neg_q.clone(), d.clone()); // (−q)·d
    let pd_negqd = c.add(p_d.clone(), neg_q_d.clone());
    let rdist = c.r.rdist(p.clone(), neg_q.clone(), d.clone()); // (p−q)·d = p·d + (−q)·d
                                                                // (−q)·d = −(q·d):  (−q)·d = d·(−q) [mul_comm] = −(d·q) [mul_neg] = −(q·d) [cong_neg mul_comm]
    let neg_qd = c.r.neg(q_d.clone());
    let h_neg_mul = neg_mul_eq(c, q, d); // (−q)·d = −(q·d)
    let pd_neg_qd = c.add(p_d.clone(), neg_qd.clone()); // p·d + (−(q·d))
    let cong_negmul = c.r.cong_right(
        parent,
        &c.add_c(),
        neg_q_d.clone(),
        neg_qd.clone(),
        p_d.clone(),
        h_neg_mul,
    );
    // (p−q)·d = p·d + (−(q·d))
    let pmq_d = c.mul(p_minus_q.clone(), d.clone());
    let pmq_d_eq = c.trans(
        pmq_d.clone(),
        pd_negqd.clone(),
        pd_neg_qd.clone(),
        rdist,
        cong_negmul,
    );

    // lift under ρ·· : ρ·((p−q)·d) = ρ·(p·d + (−(q·d)))
    let rho_pdnegqd = c.mul(rho.clone(), pd_neg_qd.clone());
    let cong_rho = c.r.cong_right(
        parent,
        &c.mul_c(),
        pmq_d.clone(),
        pd_neg_qd.clone(),
        rho.clone(),
        pmq_d_eq,
    );
    // ldist ρ (p·d) (−(q·d)) : ρ·(p·d + (−(q·d))) = ρ·(p·d) + ρ·(−(q·d))
    let rho_neg_qd = c.mul(rho.clone(), neg_qd.clone()); // ρ·(−(q·d))
    let rhopd_plus = c.add(rho_pd.clone(), rho_neg_qd.clone());
    let ldist = c.r.ldist(rho.clone(), p_d.clone(), neg_qd.clone());
    // ρ·(−(q·d)) = −(ρ·(q·d))  [mul_neg]
    let mneg = c.r.mneg(rho.clone(), q_d.clone()); // ρ·(−(q·d)) = −(ρ·(q·d))
    let cong_mneg = c.r.cong_right(
        parent,
        &c.add_c(),
        rho_neg_qd.clone(),
        neg_rho_qd.clone(),
        rho_pd.clone(),
        mneg,
    );

    // chain target → cross
    let s = c.trans(
        target.clone(),
        rho_pdnegqd.clone(),
        rhopd_plus.clone(),
        cong_rho,
        ldist,
    );
    let target_to_cross = c.trans(target.clone(), rhopd_plus, cross.clone(), s, cong_mneg);
    // symm : cross = target
    c.symm(target, cross, target_to_cross)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_peel_pointwise_keystone_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_pointwise_keystone()
            .expect("init_boolean_analysis_pointwise_keystone");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name_str in [
            "BoolAnalysis.peel_pointwise_keystone",
            "BoolAnalysis.peel_pointwise_keystone_high",
        ] {
            let name = Name::from_string(name_str);
            let info = env
                .get_const(&name)
                .unwrap_or_else(|| panic!("{name_str} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem);
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name_str} proof must check: {e:?}"));
            let deps = env.axiom_deps(&name).expect("deps");
            let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            assert!(
                names.is_empty(),
                "{name_str} must be axiom-free, got {names:?}"
            );
            assert_eq!(
                env.proof_quality(&name),
                Some(ProofQuality::Constructive),
                "{name_str} must be Constructive"
            );
        }
    }
}
