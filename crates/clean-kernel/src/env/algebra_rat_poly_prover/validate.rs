// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validation: register polynomial identities PROVED by `RatPolyProver` as
//! kernel-checked `Declaration::Theorem`s.
//!
//! `RatPoly.test_add_sq`   `(a+b)² = a² + (1+1)·(a·b) + b²`
//! `RatPoly.test_add_cube` `(a+b)³ = a³ + (1+1+1)·(a²b) + (1+1+1)·(ab²) + b³`
//! `RatPoly.test_ch3_sos`  `(2P+Q)³ = 27·P²Q + (P−Q)²·(8P+Q)`   (CH3 SOS)
//!
//! Each theorem's TYPE is a hand-written `lhs = rhs`; the VALUE is the proof the
//! prover emits by normalizing both sides. All Constructive / empty axiom
//! closure (the prover only ever cites the constructive `Rat` ring/group
//! surface + the `Eq` built-ins).

use super::RatPolyProver;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register the polynomial-prover validation theorems. Idempotent.
    pub fn init_algebra_rat_poly_prover(&mut self) -> Result<(), EnvError> {
        // Pull in the full constructive Rat ring + additive-group + order surface
        // the prover cites: distrib/comm/assoc/one_mul/mul_one/zero_*, the
        // neg-algebra (mul_neg/neg_mul_neg/neg_neg/add_neg_self/add_left_neg/
        // add_right_cancel), and the `mul_mul_mul_comm` interchange.
        self.init_algebra_rat_cube_identity()?; // distrib, comm, assoc, one_mul, add_sq, neg_mul_neg
        self.init_boolean_analysis_amgm()?; // mul_mul_mul_comm + order surface
        self.register_rat_abs_mul_proof()?; // pulls add_neg_self/add_left_neg/add_right_cancel/neg_neg

        self.register_test_add_sq()?;
        self.register_test_add_cube()?;
        self.register_test_ch3_sos()?;
        Ok(())
    }

    fn register_test_add_sq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("RatPoly.test_add_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        // Build type ∀ a b, (a+b)·(a+b) = (a·a + (1+1)·(a·b)) + b·b  and value.
        let mut tb = EnvDeclBuilder::new();
        let (a_id, a) = tb.fresh_local(rat.clone());
        let (b_id, b) = tb.fresh_local(rat.clone());
        let p = RatPolyProver::new(vec![a.clone(), b.clone()]);
        let s = p.add(a.clone(), b.clone());
        let lhs = p.mul(s.clone(), s);
        let aa = p.mul(a.clone(), a.clone());
        let bb = p.mul(b.clone(), b.clone());
        let ab = p.mul(a.clone(), b.clone());
        let two = p.add(p.one(), p.one());
        let two_ab = p.mul(two, ab);
        let rhs = p.add(p.add(aa, two_ab), bb);
        let concl = p.eq(lhs.clone(), rhs.clone());
        let proof = p
            .prove_poly_eq(&tb, &lhs, &rhs)
            .expect("add_sq is a polynomial identity");
        let ty = {
            let e = tb.mk_pi(b_id, BinderInfo::Default, rat.clone(), concl);
            tb.finish(tb.mk_pi(a_id, BinderInfo::Default, rat.clone(), e))
        };
        let value = {
            let e = tb.mk_lam(b_id, BinderInfo::Default, rat.clone(), proof);
            tb.finish(tb.mk_lam(a_id, BinderInfo::Default, rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_test_add_cube(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("RatPoly.test_add_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let mut tb = EnvDeclBuilder::new();
        let (a_id, a) = tb.fresh_local(rat.clone());
        let (b_id, b) = tb.fresh_local(rat.clone());
        let p = RatPolyProver::new(vec![a.clone(), b.clone()]);
        let s = p.add(a.clone(), b.clone());
        let lhs = p.mul(p.mul(s.clone(), s.clone()), s); // (a+b)³
                                                         // RHS: a³ + (3·a²b + (3·ab² + b³))
        let three = p.add(p.add(p.one(), p.one()), p.one());
        let a3 = p.mul(p.mul(a.clone(), a.clone()), a.clone());
        let b3 = p.mul(p.mul(b.clone(), b.clone()), b.clone());
        let a2b = p.mul(p.mul(a.clone(), a.clone()), b.clone());
        let ab2 = p.mul(p.mul(a.clone(), b.clone()), b.clone());
        let three_a2b = p.mul(three.clone(), a2b);
        let three_ab2 = p.mul(three, ab2);
        let rhs = p.add(a3, p.add(three_a2b, p.add(three_ab2, b3)));
        let concl = p.eq(lhs.clone(), rhs.clone());
        let proof = p
            .prove_poly_eq(&tb, &lhs, &rhs)
            .expect("add_cube is a polynomial identity");
        let ty = {
            let e = tb.mk_pi(b_id, BinderInfo::Default, rat.clone(), concl);
            tb.finish(tb.mk_pi(a_id, BinderInfo::Default, rat.clone(), e))
        };
        let value = {
            let e = tb.mk_lam(b_id, BinderInfo::Default, rat.clone(), proof);
            tb.finish(tb.mk_lam(a_id, BinderInfo::Default, rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_test_ch3_sos(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("RatPoly.test_ch3_sos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let mut tb = EnvDeclBuilder::new();
        let (p_id, pp) = tb.fresh_local(rat.clone());
        let (q_id, qq) = tb.fresh_local(rat.clone());
        let pr = RatPolyProver::new(vec![pp.clone(), qq.clone()]);
        // numerals
        let two = pr.add(pr.one(), pr.one());
        let eight = {
            let mut acc = pr.one();
            for _ in 1..8 {
                acc = pr.add(acc, pr.one());
            }
            acc
        };
        let twenty_seven = {
            let mut acc = pr.one();
            for _ in 1..27 {
                acc = pr.add(acc, pr.one());
            }
            acc
        };
        // LHS = (2P+Q)³
        let two_p = pr.mul(two.clone(), pp.clone());
        let two_p_q = pr.add(two_p, qq.clone());
        let lhs = pr.mul(pr.mul(two_p_q.clone(), two_p_q.clone()), two_p_q);
        // RHS = 27·(P·P·Q) + (P−Q)²·(8P+Q)
        let p2q = pr.mul(pr.mul(pp.clone(), pp.clone()), qq.clone());
        let term1 = pr.mul(twenty_seven, p2q);
        let p_minus_q = pr.sub(pp.clone(), qq.clone());
        let pmq_sq = pr.mul(p_minus_q.clone(), p_minus_q);
        let eight_p = pr.mul(eight, pp.clone());
        let eight_p_q = pr.add(eight_p, qq.clone());
        let term2 = pr.mul(pmq_sq, eight_p_q);
        let rhs = pr.add(term1, term2);
        let concl = pr.eq(lhs.clone(), rhs.clone());
        let proof = pr
            .prove_poly_eq(&tb, &lhs, &rhs)
            .expect("CH3 SOS is a polynomial identity");
        let ty = {
            let e = tb.mk_pi(q_id, BinderInfo::Default, rat.clone(), concl);
            tb.finish(tb.mk_pi(p_id, BinderInfo::Default, rat.clone(), e))
        };
        let value = {
            let e = tb.mk_lam(q_id, BinderInfo::Default, rat.clone(), proof);
            tb.finish(tb.mk_lam(p_id, BinderInfo::Default, rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::{PolyProveError, RatPolyProver};
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "RatPoly.test_add_sq",
        "RatPoly.test_add_cube",
        "RatPoly.test_ch3_sos",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_poly_prover()
            .expect("init_algebra_rat_poly_prover");
        env.init_algebra_rat_poly_prover().expect("idempotent");
        env
    }

    /// Build a fresh env with the ring surface; normalize `e` over `vars` and
    /// kernel-check the emitted `e = canon` proof under two binders.
    fn check_normalize(e_builder: impl Fn(&RatPolyProver, &Expr, &Expr) -> Expr, label: &str) {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_cube_identity().expect("cube init");
        env.init_boolean_analysis_amgm().expect("amgm init");
        env.register_rat_abs_mul_proof().expect("abs_mul init");
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let mut tb = EnvDeclBuilder::new();
        let (a_id, a) = tb.fresh_local(rat.clone());
        let (b_id, b) = tb.fresh_local(rat.clone());
        let p = RatPolyProver::new(vec![a.clone(), b.clone()]);
        let e = e_builder(&p, &a, &b);
        let nr = p.normalize(&tb, &e).expect("normalize");
        let concl = p.eq(e.clone(), nr.canon.clone());
        let ty = {
            let inner = tb.mk_pi(b_id, crate::expr::BinderInfo::Default, rat.clone(), concl);
            tb.finish(tb.mk_pi(a_id, crate::expr::BinderInfo::Default, rat.clone(), inner))
        };
        let value = {
            let inner = tb.mk_lam(
                b_id,
                crate::expr::BinderInfo::Default,
                rat.clone(),
                nr.proof,
            );
            tb.finish(tb.mk_lam(a_id, crate::expr::BinderInfo::Default, rat.clone(), inner))
        };
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &ty)
            .unwrap_or_else(|err| panic!("normalize {label} must kernel-check: {err:?}"));
    }

    #[test]
    fn test_normalize_mul_swap_kernel_checks() {
        check_normalize(|p, a, b| p.mul(b.clone(), a.clone()), "b*a");
    }

    #[test]
    fn test_normalize_bb_kernel_checks() {
        check_normalize(|p, _a, b| p.mul(b.clone(), b.clone()), "b*b");
    }

    #[test]
    fn test_normalize_sub_kernel_checks() {
        check_normalize(|p, a, b| p.sub(a.clone(), b.clone()), "a-b");
    }

    #[test]
    fn test_normalize_neg_plus_neg_kernel_checks() {
        // (−a) + (−a) → −2a  : exercises fold_same_sign(negative) + neg_add_distrib.
        check_normalize(
            |p, a, _b| p.add(p.neg(a.clone()), p.neg(a.clone())),
            "(-a)+(-a)",
        );
    }

    #[test]
    fn test_normalize_neg_ab_plus_neg_ab_kernel_checks() {
        // a·(−b) + (−b)·a → −2ab  : the (a−b)² cross-term merge.
        check_normalize(
            |p, a, b| {
                let anb = p.mul(a.clone(), p.neg(b.clone()));
                let nba = p.mul(p.neg(b.clone()), a.clone());
                p.add(anb, nba)
            },
            "a(-b)+(-b)a",
        );
    }

    #[test]
    fn test_normalize_sub_sq_kernel_checks() {
        check_normalize(
            |p, a, b| {
                let d = p.sub(a.clone(), b.clone());
                p.mul(d.clone(), d)
            },
            "(a-b)^2",
        );
    }

    #[test]
    fn test_normalize_sub_sq_times_sum_kernel_checks() {
        // (a−b)²·(a+b) — exercises opposite-sign folding under a product.
        check_normalize(
            |p, a, b| {
                let d = p.sub(a.clone(), b.clone());
                let sq = p.mul(d.clone(), d);
                let s = p.add(a.clone(), b.clone());
                p.mul(sq, s)
            },
            "(a-b)^2*(a+b)",
        );
    }

    #[test]
    fn test_poly_prover_theorems_kernel_check() {
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
    fn test_poly_prover_theorems_constructive_empty_closure() {
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

    /// Build the σ-route degree-9 polynomials over `(s, r)` (σ := s+r):
    ///   LHS = 27·σ³·(9(s⁴+r⁴)+4s³r³)   (the `27·σ³·LHS'` side, degree 9)
    /// Returns `(prover, s, r, builder, lhs_expr)`.
    fn deg9_lhs(p: &RatPolyProver, s: &Expr, r: &Expr) -> Expr {
        let pow = |x: &Expr, k: u32| {
            let mut acc = x.clone();
            for _ in 1..k {
                acc = p.mul(acc, x.clone());
            }
            acc
        };
        let num = |n: u32| {
            let mut acc = p.one();
            for _ in 1..n {
                acc = p.add(acc, p.one());
            }
            acc
        };
        let sigma = p.add(s.clone(), r.clone());
        let sigma3 = p.mul(p.mul(sigma.clone(), sigma.clone()), sigma.clone());
        // LHS' = 9(s⁴+r⁴) + 4·(s³r³)
        let s4 = pow(s, 4);
        let r4 = pow(r, 4);
        let nine_s4r4 = p.mul(num(9), p.add(s4, r4));
        let s3r3 = p.mul(pow(s, 3), pow(r, 3));
        let four_s3r3 = p.mul(num(4), s3r3);
        let lhsp = p.add(nine_s4r4, four_s3r3);
        // 27·σ³·LHS'
        p.mul(p.mul(num(27), sigma3), lhsp)
    }

    /// Report proof-term node count + build time for a normalize, WITHOUT
    /// kernel-checking (isolates proof-construction scaling from kernel scaling).
    fn report_build_only(label: &str, build: impl Fn(&RatPolyProver, &Expr, &Expr) -> Expr) {
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let mut tb = EnvDeclBuilder::new();
        let (_s_id, s) = tb.fresh_local(rat.clone());
        let (_r_id, r) = tb.fresh_local(rat.clone());
        let p = RatPolyProver::new(vec![s.clone(), r.clone()]);
        let e = build(&p, &s, &r);
        let poly = p.parse(&e).expect("parse");
        let t0 = std::time::Instant::now();
        let nr = p.normalize(&tb, &e).expect("normalize");
        let ms = t0.elapsed().as_millis();
        eprintln!(
            "[{label}] monomials={} build={ms}ms proof_nodes={}",
            poly.sorted_terms_dbg().len(),
            super::super::expr_node_count(&nr.proof),
        );
    }

    #[test]
    fn test_deg_scaling_sweep_build_only() {
        let num = |p: &RatPolyProver, n: u32| {
            let mut acc = p.one();
            for _ in 1..n {
                acc = p.add(acc, p.one());
            }
            acc
        };
        let pow = |p: &RatPolyProver, x: &Expr, k: u32| {
            let mut acc = x.clone();
            for _ in 1..k {
                acc = p.mul(acc, x.clone());
            }
            acc
        };
        // deg-6: σ³·(s³+r³)
        report_build_only("deg6_sigma3_s3r3", |p, s, r| {
            let sig = p.add(s.clone(), r.clone());
            let sig3 = p.mul(p.mul(sig.clone(), sig.clone()), sig.clone());
            p.mul(sig3, p.add(pow(p, s, 3), pow(p, r, 3)))
        });
        // deg-7: σ³·LHS'  (no 27)
        report_build_only("deg7_sigma3_lhsp", |p, s, r| {
            let sig = p.add(s.clone(), r.clone());
            let sig3 = p.mul(p.mul(sig.clone(), sig.clone()), sig.clone());
            let lhsp = p.add(
                p.mul(num(p, 9), p.add(pow(p, s, 4), pow(p, r, 4))),
                p.mul(num(p, 4), p.mul(pow(p, s, 3), pow(p, r, 3))),
            );
            p.mul(sig3, lhsp)
        });
        // isolate the large-coefficient (27·) cost on the small deg-6 base:
        report_build_only("deg6_times27", |p, s, r| {
            let sig = p.add(s.clone(), r.clone());
            let sig3 = p.mul(p.mul(sig.clone(), sig.clone()), sig.clone());
            let base = p.mul(sig3, p.add(pow(p, s, 3), pow(p, r, 3)));
            p.mul(num(p, 27), base)
        });
        // NOTE: the full deg-9 σ-route term `27·σ³·LHS'` builds ~48.7M proof
        // nodes (see `test_deg9_build_only_blowup`) — built separately so this
        // sweep stays light.
    }

    #[test]
    fn test_deg9_construction_succeeds() {
        // The σ-route degree-9 LHS `27·σ³·(9(s⁴+r⁴)+4s³r³)`: proof-term
        // CONSTRUCTION (parse → normalize → emit) succeeds. The emitted term is
        // ~48.7M nodes (see `report_build_only` output), which OOM-defeats the
        // KERNEL CHECK — the documented scaling wall. We assert only that the
        // sound canonical poly + a well-formed proof term are produced; we do
        // NOT kernel-check it here (that needs >available RAM).
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let mut tb = EnvDeclBuilder::new();
        let (_s_id, s) = tb.fresh_local(rat.clone());
        let (_r_id, r) = tb.fresh_local(rat.clone());
        let p = RatPolyProver::new(vec![s.clone(), r.clone()]);
        let lhs = deg9_lhs(&p, &s, &r);
        let poly = p.parse(&lhs).expect("parse deg9");
        // Canonical poly: the 8 degree-7 σ-monomials × LHS' folded = 12 distinct
        // monomials (s⁷..r⁷ shapes), all with the correct integer coefficients.
        assert_eq!(
            poly.sorted_terms_dbg().len(),
            12,
            "deg9 canonical monomials"
        );
        let nr = p
            .normalize(&tb, &lhs)
            .expect("normalize deg9 (construction)");
        assert_eq!(nr.poly, poly, "normalize poly matches parse poly");
        assert!(
            super::super::expr_node_count(&nr.proof) > 1_000_000,
            "deg9 proof term is large (documents the wall)"
        );
    }

    /// Build + KERNEL-CHECK a normalize; report whether the kernel accepts it
    /// within memory, with timing. Returns true on success.
    fn build_and_check(label: &str, build: impl Fn(&RatPolyProver, &Expr, &Expr) -> Expr) {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_cube_identity().expect("cube init");
        env.init_boolean_analysis_amgm().expect("amgm init");
        env.register_rat_abs_mul_proof().expect("abs_mul init");
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let mut tb = EnvDeclBuilder::new();
        let (s_id, s) = tb.fresh_local(rat.clone());
        let (r_id, r) = tb.fresh_local(rat.clone());
        let p = RatPolyProver::new(vec![s.clone(), r.clone()]);
        let e = build(&p, &s, &r);
        let nr = p.normalize(&tb, &e).expect("normalize");
        let concl = p.eq(e.clone(), nr.canon.clone());
        let ty = {
            let inner = tb.mk_pi(r_id, crate::expr::BinderInfo::Default, rat.clone(), concl);
            tb.finish(tb.mk_pi(s_id, crate::expr::BinderInfo::Default, rat.clone(), inner))
        };
        let value = {
            let inner = tb.mk_lam(
                r_id,
                crate::expr::BinderInfo::Default,
                rat.clone(),
                nr.proof,
            );
            tb.finish(tb.mk_lam(s_id, crate::expr::BinderInfo::Default, rat.clone(), inner))
        };
        let tc = TypeChecker::with_mode(&env, env.mode());
        let t0 = std::time::Instant::now();
        tc.check_type(&value, &ty)
            .unwrap_or_else(|err| panic!("{label} kernel-check FAILED: {err:?}"));
        eprintln!(
            "[{label}] kernel-check OK in {} ms",
            t0.elapsed().as_millis()
        );
    }

    #[test]
    fn test_deg7_kernel_checks() {
        let num = |p: &RatPolyProver, n: u32| {
            let mut acc = p.one();
            for _ in 1..n {
                acc = p.add(acc, p.one());
            }
            acc
        };
        let pow = |p: &RatPolyProver, x: &Expr, k: u32| {
            let mut acc = x.clone();
            for _ in 1..k {
                acc = p.mul(acc, x.clone());
            }
            acc
        };
        build_and_check("deg7_sigma3_lhsp", |p, s, r| {
            let sig = p.add(s.clone(), r.clone());
            let sig3 = p.mul(p.mul(sig.clone(), sig.clone()), sig.clone());
            let lhsp = p.add(
                p.mul(num(p, 9), p.add(pow(p, s, 4), pow(p, r, 4))),
                p.mul(num(p, 4), p.mul(pow(p, s, 3), pow(p, r, 3))),
            );
            p.mul(sig3, lhsp)
        });
    }

    #[test]
    fn test_poly_prover_rejects_non_identity() {
        // (a+b)² ≠ a² + b²  → prover must report NotAnIdentity.
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let mut tb = EnvDeclBuilder::new();
        let (_a_id, a) = tb.fresh_local(rat.clone());
        let (_b_id, b) = tb.fresh_local(rat.clone());
        let p = RatPolyProver::new(vec![a.clone(), b.clone()]);
        let s = p.add(a.clone(), b.clone());
        let lhs = p.mul(s.clone(), s);
        let rhs = p.add(p.mul(a.clone(), a.clone()), p.mul(b.clone(), b.clone()));
        match p.prove_poly_eq(&tb, &lhs, &rhs) {
            Err(PolyProveError::NotAnIdentity { .. }) => {}
            other => panic!("expected NotAnIdentity, got {other:?}"),
        }
    }
}
