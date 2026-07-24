// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.Expect_congr` — the uniform cube
//! expectation respects pointwise equality of its integrand:
//!
//! `Expect_congr : ∀ (n : Nat) (g h : HCPoint n → Rat),`
//! `  (∀ (x : HCPoint n), g x = h x) → Expect n g = Expect n h`
//!
//! `Expect n g` δ-unfolds to
//! `Rat.div (Fin.sum (2^n) (fun k => g (hcDecode n k))) D` with the fixed
//! denominator `D = Rat.mk (Int.ofNat (2^n)) 1`. The two summand functions
//! `k ↦ g (hcDecode n k)` and `k ↦ h (hcDecode n k)` are pointwise equal (apply
//! the hypothesis at `hcDecode n k`), so `Fin.sum_congr` equates the numerators;
//! `congrArg (fun s => Rat.div s D)` then lifts that to the quotient. Kernel-
//! checked, `ProofQuality::Constructive` (closure ⊆ {`Fin.sum_congr`} ∪ Eq
//! built-ins — axiom-free).
//!
//! This is the integrand-substitution lemma the orthonormality / Parseval
//! arguments use to replace `χ_S(x)·χ_S(x)` by its proven constant value `1`
//! under the expectation, reducing the diagonal inner product to the single
//! normalization fact `Expect n (fun _ => 1) = 1`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct ExpectCongrConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    expect: Expr,
    hc_decode: Expr,
    fin_sum: Expr,
    rat_div: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    nat_pow: Expr,
    two: Expr,
    nat_one: Expr,
    fin_sum_congr: Expr,
    eq1: Expr,
    congr_arg: Expr,
}

impl ExpectCongrConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ, nat_one.clone());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            expect: Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two,
            nat_one,
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    /// `BoolAnalysis.Expect n g`.
    fn expect(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.expect.clone(), [n, g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }

    /// `fun (k : Fin (2^n)) => g (hcDecode n k)` — the cube-enumerated summand.
    fn decoded_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_pow = self.fin_of(&self.pow2(n));
        let (k_id, k) = b.fresh_local(fin_pow.clone());
        let decoded = Expr::apps(self.hc_decode.clone(), [n.clone(), k]);
        let body = Expr::app(g.clone(), decoded);
        let lam = b.mk_lam(k_id, BinderInfo::Default, fin_pow, body);
        b.finish_child(lam)
    }

    /// `Fin.sum (2^n) (decoded_fn n g)`.
    fn numerator(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.fin_sum.clone(),
            [self.pow2(n), self.decoded_fn(parent, n, g)],
        )
    }

    /// The fixed denominator `Rat.mk (Int.ofNat (2^n)) 1`.
    fn denom(&self, n: &Expr) -> Expr {
        let denom_int = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [denom_int, self.nat_one.clone()])
    }

    /// `fun (s : Rat) => Rat.div s D` — the quotient-by-`D` map, for `congrArg`.
    fn div_by_denom_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = b.fresh_local(self.rat.clone());
        let body = Expr::apps(self.rat_div.clone(), [s, self.denom(n)]);
        let lam = b.mk_lam(s_id, BinderInfo::Default, self.rat.clone(), body);
        b.finish_child(lam)
    }
}

/// Pointwise hypothesis type `∀ x : HCPoint n, g x = h x`.
fn hyp_ty(c: &ExpectCongrConsts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, h: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let body = c.eq_rat(Expr::app(g.clone(), x.clone()), Expr::app(h.clone(), x));
    b.finish_child(b.mk_pi(x_id, BinderInfo::Default, hcp, body))
}

fn build_type(c: &ExpectCongrConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let gt = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(gt.clone());
    let (h_id, h) = b.fresh_local(gt.clone());
    let hyp = hyp_ty(c, &b, &n, &g, &h);
    let (hh_id, _hh) = b.fresh_local(hyp.clone());
    let concl = c.eq_rat(
        c.expect(n.clone(), g.clone()),
        c.expect(n.clone(), h.clone()),
    );
    let ty = b.mk_pi(hh_id, BinderInfo::Default, hyp, concl);
    let ty = b.mk_pi(h_id, BinderInfo::Default, gt.clone(), ty);
    let ty = b.mk_pi(g_id, BinderInfo::Default, gt, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &ExpectCongrConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let gt = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(gt.clone());
    let (h_id, h) = b.fresh_local(gt.clone());
    let hyp = hyp_ty(c, &b, &n, &g, &h);
    let (hh_id, hh) = b.fresh_local(hyp.clone());

    let dec_g = c.decoded_fn(&b, &n, &g);
    let dec_h = c.decoded_fn(&b, &n, &h);

    // pointwise hyp for Fin.sum_congr: fun (k : Fin (2^n)) => hh (hcDecode n k)
    //   : (dec_g k) = (dec_h k)   (both β-reduce to g/h (hcDecode n k))
    let hyp_dec = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_pow = c.fin_of(&c.pow2(&n));
        let (k_id, k) = d.fresh_local(fin_pow.clone());
        let decoded = Expr::apps(c.hc_decode.clone(), [n.clone(), k]);
        let body = Expr::app(hh.clone(), decoded);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, fin_pow, body))
    };

    // Fin.sum_congr (2^n) dec_g dec_h hyp_dec
    //   : Fin.sum (2^n) dec_g = Fin.sum (2^n) dec_h
    let sum_eq = Expr::apps(
        c.fin_sum_congr.clone(),
        [c.pow2(&n), dec_g.clone(), dec_h.clone(), hyp_dec],
    );

    let num_g = c.numerator(&b, &n, &g);
    let num_h = c.numerator(&b, &n, &h);
    // congrArg (fun s => Rat.div s D) sum_eq
    //   : Rat.div num_g D = Rat.div num_h D
    // which is def-eq to `Expect n g = Expect n h`.
    let proof = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            num_g,
            num_h,
            c.div_by_denom_fn(&b, &n),
            sum_eq,
        ],
    );

    let val = b.mk_lam(hh_id, BinderInfo::Default, hyp, proof);
    let val = b.mk_lam(h_id, BinderInfo::Default, gt.clone(), val);
    let val = b.mk_lam(g_id, BinderInfo::Default, gt, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.Expect_congr` as a kernel-checked, constructive
    /// theorem. Idempotent.
    pub(crate) fn register_expect_congr_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.Expect_congr");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        // `Fin.sum_congr` lives in the Fin.sum overlay.
        self.init_fin_sum()?;

        let c = ExpectCongrConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env
    }

    /// `Expect_congr` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof term
    /// re-checks under C1.
    #[test]
    fn test_expect_congr_is_constructive_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.Expect_congr"))
            .expect("Expect_congr should be registered by init_boolean_analysis");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Expect_congr must be a kernel-checked Theorem, not an Axiom"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("Expect_congr proof must check against its declared type");

        assert_eq!(
            env.proof_quality(&Name::from_string("BoolAnalysis.Expect_congr")),
            Some(ProofQuality::Constructive),
            "Expect_congr must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string("BoolAnalysis.Expect_congr"))
                .expect("deps")
                .is_empty(),
            "Expect_congr's transitive axiom closure must be empty"
        );
    }
}
