// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-bound Stage C-3 — the ASSEMBLED `(4,4/3)` Hölder inequality over
//! `subsetSum`, in its 4th-power rational shadow (component B3c, the genuine
//! analytic core).
//!
//! # The theorem
//!
//! ```text
//! BoolAnalysis.subsetSum_holder_fourth :
//!   ∀ (n : Nat) (a b : HCPoint n → Rat),
//!     Rat.le Rat.zero (subsetSum n (fun x => a x · a x)) →   -- 0 ≤ ⟨a,a⟩
//!     Rat.le Rat.zero (subsetSum n (fun x => b x · b x)) →   -- 0 ≤ ⟨b,b⟩
//!     Rat.le
//!       (P · P) · (P · P)                                    -- ⟨a,b⟩⁴
//!       ( (⟨a²,a²⟩ · ⟨1,1⟩) · (⟨b,b⟩ · ⟨b,b⟩) )              -- ‖a‖₄⁴·|cube|·⟨b,b⟩²
//! ```
//!
//! with `P := ⟨a,b⟩ = subsetSum n (fun x => a x · b x)`,
//! `⟨a²,a²⟩ := subsetSum n (fun x => (a²·1)·(a²·1))`,
//! `⟨1,1⟩ := subsetSum n (fun x => 1·1)`. This is the `(4,4/3)` Hölder step
//! `⟨a,b⟩ ≤ ‖a‖₄·‖b‖_{4/3}` raised to the 4th power so that BOTH endpoint norms
//! become RATIONAL (`‖a‖₄⁴ = Σa⁴`, `‖b‖_{4/3}⁴ = …·⟨b,b⟩²` after the b-support
//! sharpening), with NO `^{4/3}` carrier anywhere — the dyadic double-CS route
//! the obstruction note (§5) called for.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! Let `Q := ⟨a,a⟩`, `R := ⟨b,b⟩`, `S·T := ⟨a²,a²⟩·⟨1,1⟩`. From the two landed
//! CS halves:
//! - `h_cs   : P·P ≤ Q·R`         (`subsetSum_cauchy_schwarz n a b`);
//! - `h_interp : Q·Q ≤ S·T`       (`subsetSum_sq_le_fourth_card n a`).
//!
//! and the nonnegativity facts `0 ≤ Q`, `0 ≤ R` (hypotheses; the consumer has
//! them as sums of squares) plus `0 ≤ P·P` (`sq_nonneg`) and `0 ≤ Q·R`
//! (`mul_nonneg`), the chain is:
//!
//! 1. `(P·P)·(P·P) ≤ (P·P)·(Q·R)`   (`mul_le_mul_of_nonneg_left`, `0≤P·P`);
//! 2. `(P·P)·(Q·R) ≤ (Q·R)·(Q·R)`   (`mul_le_mul_of_nonneg_right`, `0≤Q·R`);
//! 3. `le_trans` (1)(2) ⇒ `(P·P)·(P·P) ≤ (Q·R)·(Q·R)`;
//! 4. `(Q·R)·(Q·R) = (Q·Q)·(R·R)`   (`mul_mul_mul_comm Q R Q R`), transported by
//!    `Eq.subst` into (3)'s RHS ⇒ `(P·P)·(P·P) ≤ (Q·Q)·(R·R)`;
//! 5. `(Q·Q)·(R·R) ≤ (S·T)·(R·R)`   (`mul_le_mul_of_nonneg_right (R·R)(Q·Q)(S·T)
//!    h_interp (0≤R·R)`, with `0≤R·R` = `mul_nonneg`);
//! 6. `le_trans` (4)(5) ⇒ the goal `(P·P)·(P·P) ≤ (S·T)·(R·R)`.
//!
//! Every atom (`subsetSum_cauchy_schwarz`, `subsetSum_sq_le_fourth_card`,
//! `Rat.sq_nonneg`, `Rat.mul_nonneg`, `Rat.mul_le_mul_of_nonneg_left/right`,
//! `Rat.mul_mul_mul_comm`, `Rat.le_trans`, `Eq.subst`) is `Constructive` with
//! empty closure, so the assembled theorem is too.
//!
//! # The residual (the `2^n` → support-count sharpening)
//!
//! `⟨1,1⟩ = Σ 1·1 = 2^n` in this ABSTRACT form. The consumer's exact target
//! `(‖T_{1/3}g‖₂²)² ≤ 16·count³` requires `2^n` replaced by the disagreement
//! count `count = subsetSum n (ind∘disagree)`; that sharpening is the b-support
//! restriction `⟨a,b⟩ = ⟨a·χ_E, b⟩` (b = D_i f vanishes off E), the remaining
//! glue (NOT another carrier). See the dual-B obstruction note for the full
//! residual map.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached atoms for the assembled Hölder build.
struct HolderConsts {
    o: OrderConsts,
    nat: Expr,
    rat_one: Expr,
    hcpoint: Expr,
    subset_sum: Expr,
    cs: Expr,
    interp: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    mul_le_left: Expr,
    mul_le_right: Expr,
    mmmc: Expr,
    le_trans: Expr,
}

impl HolderConsts {
    fn new() -> Self {
        Self {
            o: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            cs: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_cauchy_schwarz"),
                vec![],
            ),
            interp: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_sq_le_fourth_card"),
                vec![],
            ),
            sq_nonneg: Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
            mul_nonneg: Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            mul_le_left: Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            mul_le_right: Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
            mmmc: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            le_trans: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `fun (x : HCPoint n) => Rat.mul (p x) (q x)`.
    fn prod_fn(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr, q: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = self.mul(
            Expr::app(p.clone(), x.clone()),
            Expr::app(q.clone(), x.clone()),
        );
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => Rat.mul (a x) (a x)` — the squared function `a²`.
    fn sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        self.prod_fn(parent, n, a, a)
    }
    /// `fun (_ : HCPoint n) => Rat.one`.
    fn one_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, _x) = d.fresh_local(hcp.clone());
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, self.rat_one.clone()))
    }
    /// `Rat.sq_nonneg t : 0 ≤ t·t`.
    fn sq_nonneg(&self, t: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), t)
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h:b≤c)(h0:0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h:b≤c)(h0:0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mmmc.clone(), [a, b, cc, d])
    }
    /// `Rat.le_trans a b c (h1:a≤b)(h2:b≤c) : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h1, h2])
    }
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_holder_fourth` — the assembled `(4,4/3)`
    /// Hölder inequality over `subsetSum` in 4th-power rational shadow form.
    /// Kernel-checked, `ProofQuality::Constructive`, empty closure. Idempotent.
    pub fn register_subset_sum_holder_fourth(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_holder_fourth");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_cauchy_schwarz()?;
        self.register_subset_sum_sq_le_fourth_card()?;
        self.init_boolean_analysis_order_toolkit()?; // sq_nonneg, mul_le_mul_*
        self.register_rat_order_proofs()?; // le_trans, mul_nonneg
        self.register_rat_mul_mul_mul_comm_theorem()?; // mul_mul_mul_comm

        let c = HolderConsts::new();
        let (ty, value) = build_holder(&c);
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

/// Build the type + proof of `BoolAnalysis.subsetSum_holder_fourth`.
fn build_holder(c: &HolderConsts) -> (Expr, Expr) {
    // Shared term-builder for the four inner products at fixed (builder, n, a, b).
    // Returns (P, Q, R, ST) where ST = ⟨a²,a²⟩·⟨1,1⟩.
    let pieces = |b: &EnvDeclBuilder, n: &Expr, a: &Expr, bv: &Expr| -> (Expr, Expr, Expr, Expr) {
        let p = c.ssum(n, c.prod_fn(b, n, a, bv)); // ⟨a,b⟩
        let q = c.ssum(n, c.prod_fn(b, n, a, a)); // ⟨a,a⟩
        let r = c.ssum(n, c.prod_fn(b, n, bv, bv)); // ⟨b,b⟩
                                                    // ⟨a²,a²⟩ and ⟨1,1⟩ exactly as the interp lemma states them.
        let a2 = c.sq_fn(b, n, a);
        let one = c.one_fn(b, n);
        let s = c.ssum(n, c.prod_fn(b, n, &a2, &a2)); // ⟨a²,a²⟩
        let t = c.ssum(n, c.prod_fn(b, n, &one, &one)); // ⟨1,1⟩
        let st = c.mul(s, t);
        (p, q, r, st)
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));
        let (bb_id, bv) = b.fresh_local(c.hcpoint_to_rat(&n));

        let (p, q, r, st) = pieces(&b, &n, &a, &bv);
        let hyp_q = c.le(c.zero(), q.clone());
        let hyp_r = c.le(c.zero(), r.clone());

        let pp = c.mul(p.clone(), p.clone());
        let lhs = c.mul(pp.clone(), pp); // ⟨a,b⟩⁴
        let rr = c.mul(r.clone(), r.clone());
        let rhs = c.mul(st, rr); // (⟨a²,a²⟩·⟨1,1⟩)·⟨b,b⟩²
        let concl = c.le(lhs, rhs);

        let (hr_id, _) = b.fresh_local(hyp_r.clone());
        let e = b.mk_pi(hr_id, BinderInfo::Default, hyp_r, concl);
        let (hq_id, _) = b.fresh_local(hyp_q.clone());
        let e = b.mk_pi(hq_id, BinderInfo::Default, hyp_q, e);
        let e = b.mk_pi(bb_id, BinderInfo::Default, c.hcpoint_to_rat(&n), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.hcpoint_to_rat(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));
        let (bb_id, bv) = b.fresh_local(c.hcpoint_to_rat(&n));

        let (p, q, r, st) = pieces(&b, &n, &a, &bv);
        let hyp_q = c.le(c.zero(), q.clone());
        let hyp_r = c.le(c.zero(), r.clone());
        let (hq_id, h_q) = b.fresh_local(hyp_q.clone());
        let (hr_id, h_r) = b.fresh_local(hyp_r.clone());

        let pp = c.mul(p.clone(), p.clone()); // P·P
        let qr = c.mul(q.clone(), r.clone()); // Q·R
        let qq = c.mul(q.clone(), q.clone()); // Q·Q
        let rr = c.mul(r.clone(), r.clone()); // R·R

        // h_cs : P·P ≤ Q·R.
        let h_cs = Expr::apps(c.cs.clone(), [n.clone(), a.clone(), bv.clone()]);
        // h_interp : Q·Q ≤ S·T.
        let h_interp = Expr::apps(c.interp.clone(), [n.clone(), a.clone()]);

        // 0 ≤ P·P (sq_nonneg P), 0 ≤ Q·R (mul_nonneg Q R h_q h_r), 0 ≤ R·R.
        let h_pp_nn = c.sq_nonneg(p.clone());
        let h_qr_nn = c.mul_nonneg(q.clone(), r.clone(), h_q.clone(), h_r.clone());
        let h_rr_nn = c.sq_nonneg(r.clone());

        // 1. (P·P)·(P·P) ≤ (P·P)·(Q·R)  [left-mono, 0≤P·P, P·P≤Q·R]
        let step1 = c.mul_le_left(pp.clone(), pp.clone(), qr.clone(), h_cs.clone(), h_pp_nn);
        // 2. (P·P)·(Q·R) ≤ (Q·R)·(Q·R)  [right-mono, 0≤Q·R, P·P≤Q·R]
        let step2 = c.mul_le_right(qr.clone(), pp.clone(), qr.clone(), h_cs, h_qr_nn);
        // 3. le_trans : (P·P)·(P·P) ≤ (Q·R)·(Q·R)
        let lhs4 = c.mul(pp.clone(), pp.clone());
        let pp_qr = c.mul(pp.clone(), qr.clone());
        let qr_qr = c.mul(qr.clone(), qr.clone());
        let step3 = c.le_trans(lhs4.clone(), pp_qr, qr_qr.clone(), step1, step2);

        // 4. (Q·R)·(Q·R) = (Q·Q)·(R·R)  [mul_mul_mul_comm Q R Q R]
        let h_eq = c.mmmc(q.clone(), r.clone(), q.clone(), r.clone());
        let qq_rr = c.mul(qq.clone(), rr.clone());
        // transport step3's RHS (Q·R)·(Q·R) → (Q·Q)·(R·R):
        //   Eq.subst (motive := fun z => lhs4 ≤ z) h_eq step3.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat());
            let body = c.le(lhs4.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
        };
        let step4 = c.o.subst(motive, qr_qr, qq_rr.clone(), h_eq, step3);

        // 5. (Q·Q)·(R·R) ≤ (S·T)·(R·R)  [right-mono: a=R·R, b=Q·Q, c=S·T]
        let step5 = c.mul_le_right(rr.clone(), qq.clone(), st.clone(), h_interp, h_rr_nn);

        // 6. le_trans : (P·P)·(P·P) ≤ (S·T)·(R·R)
        let st_rr = c.mul(st.clone(), rr.clone());
        let proof = c.le_trans(lhs4, qq_rr, st_rr, step4, step5);

        let e = b.mk_lam(hr_id, BinderInfo::Default, hyp_r, proof);
        let e = b.mk_lam(hq_id, BinderInfo::Default, hyp_q, e);
        let e = b.mk_lam(bb_id, BinderInfo::Default, c.hcpoint_to_rat(&n), e);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.hcpoint_to_rat(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_holder_fourth()
            .expect("register_subset_sum_holder_fourth should succeed");
        env
    }

    #[test]
    fn test_holder_registered_as_theorem() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.subsetSum_holder_fourth"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_holder_type_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_holder_fourth"),
                vec![],
            ))
            .expect("BoolAnalysis.subsetSum_holder_fourth should type-check");
    }

    #[test]
    fn test_holder_constructive_axiom_free() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.subsetSum_holder_fourth");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). The assembled Hölder shadow
    /// is TRUE; `refute_conjecture` must NOT find a counterexample.
    #[test]
    fn test_holder_refute_returns_none() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.subsetSum_holder_fourth"))
            .expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "assembled Hölder shadow is TRUE; refute_conjecture must return None"
        );
    }
}
