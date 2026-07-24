// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `BoolAnalysis.chi_inner_eq_expect_symmDiff` — the
//! inner-product-to-single-character reduction:
//!
//! ```text
//! chi_inner_eq_expect_symmDiff : ∀ (n : Nat) (S T : HCPoint n),
//!   @Eq Rat (Expect n (fun x => Rat.mul (chi n S x) (chi n T x)))
//!           (Expect n (fun x => chi n (fun i => Bool.xor (S i) (T i)) x))
//! ```
//!
//! i.e. `⟨χ_S, χ_T⟩ = E_x[χ_S(x)·χ_T(x)] = E_x[χ_{S Δ T}(x)]` (O'Donnell,
//! *Analysis of Boolean Functions*, §1.4). This collapses EVERY character inner
//! product to a *single*-character average, the form the off-diagonal
//! cancellation `E[χ_U] = 0` (for `U ≠ ∅`) and the diagonal normalization
//! `E[χ_∅] = E[1] = 1` then dispatch.
//!
//! Proof: `Expect_congr` over the landed pointwise group law
//! `chi_mul_chi_symmDiff n S T x : χ_S(x)·χ_T(x) = χ_{S Δ T}(x)`. The two
//! integrands are exactly `fun x => χ_S(x)·χ_T(x)` and
//! `fun x => χ_{S Δ T}(x)`, so the pointwise hypothesis
//! `fun x => chi_mul_chi_symmDiff n S T x` discharges the `Expect_congr`
//! premise verbatim.
//!
//! When `S = T` this specializes (via `S Δ S = ∅` and the closed diagonal
//! `chi_self_inner_eq_one`) to `1`; when `S ≠ T` the symmetric difference is a
//! nonempty subset and the cube-split induction drives the average to `0`.
//! Together these are character orthonormality.
//!
//! Kernel-checked, `ProofQuality::Constructive` (closure ⊆
//! {`Expect_congr`, `chi_mul_chi_symmDiff`} ∪ Eq built-ins — all axiom-free).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct ChiInnerConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_xor: Expr,
    rat_mul: Expr,
    chi: Expr,
    expect: Expr,
    expect_congr: Expr,
    chi_mul_chi_symm_diff: Expr,
    eq1: Expr,
}

impl ChiInnerConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            expect: Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
            expect_congr: Expr::const_(Name::from_string("BoolAnalysis.Expect_congr"), vec![]),
            chi_mul_chi_symm_diff: Expr::const_(
                Name::from_string("BoolAnalysis.chi_mul_chi_symmDiff"),
                vec![],
            ),
            eq1: Expr::const_(Name::from_string("Eq"), vec![type1]),
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
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n, s, x])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn xor(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_xor.clone(), [a, b])
    }
    fn expect_of(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.expect.clone(), [n, g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }

    /// `fun (i : Fin n) => Bool.xor (S i) (T i)` — the symmetric-difference
    /// indicator `S Δ T`.
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.xor(Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (x : HCPoint n) => Rat.mul (chi n S x) (chi n T x)` — the inner
    /// product integrand `χ_S(x)·χ_T(x)`.
    fn product_integrand(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(
            self.chi(n.clone(), s.clone(), x.clone()),
            self.chi(n.clone(), t.clone(), x),
        );
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (x : HCPoint n) => chi n (S Δ T) x` — the single-character
    /// integrand `χ_{S Δ T}(x)`.
    fn symm_diff_integrand(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.chi(n.clone(), self.symm_diff_fn(&b, n, s, t), x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

fn build_type(c: &ChiInnerConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());

    let lhs = c.expect_of(n.clone(), c.product_integrand(&b, &n, &s, &t));
    let rhs = c.expect_of(n.clone(), c.symm_diff_integrand(&b, &n, &s, &t));
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &ChiInnerConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());

    let g = c.product_integrand(&b, &n, &s, &t);
    let h = c.symm_diff_integrand(&b, &n, &s, &t);

    // pointwise : fun (x : HCPoint n) => chi_mul_chi_symmDiff n S T x
    //   : χ_S(x)·χ_T(x) = χ_{S Δ T}(x)
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::apps(
            c.chi_mul_chi_symm_diff.clone(),
            [n.clone(), s.clone(), t.clone(), x],
        );
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };

    // Expect_congr n g h pointwise : Expect n g = Expect n h
    let proof = Expr::apps(c.expect_congr.clone(), [n.clone(), g, h, pointwise]);

    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_inner_eq_expect_symmDiff` as a kernel-checked,
    /// constructive theorem:
    ///
    /// `∀ n S T, Expect n (fun x => chi n S x * chi n T x)`
    /// `       = Expect n (fun x => chi n (S Δ T) x)`.
    ///
    /// The character inner product `⟨χ_S, χ_T⟩` averages identically to the
    /// single-character average `E[χ_{S Δ T}]`, by `Expect_congr` over the proven
    /// per-point group law `chi_mul_chi_symmDiff`. Idempotent.
    pub(crate) fn register_chi_inner_symm_diff_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_inner_eq_expect_symmDiff");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?; // chi / Expect / Bool.xor
        self.register_expect_congr_theorem()?;
        self.register_chi_symm_diff_theorem()?;

        let c = ChiInnerConsts::new();
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
        env.register_chi_inner_symm_diff_theorem()
            .expect("register_chi_inner_symm_diff_theorem");
        env
    }

    /// `chi_inner_eq_expect_symmDiff` is a genuine kernel-checked, `Constructive`
    /// `Declaration::Theorem` (empty admitted-axiom closure), and its proof term
    /// re-checks under C1.
    #[test]
    fn test_chi_inner_symm_diff_is_constructive_theorem() {
        let env = make_env();
        let name = Name::from_string("BoolAnalysis.chi_inner_eq_expect_symmDiff");
        let info = env
            .get_const(&name)
            .expect("chi_inner_eq_expect_symmDiff should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "chi_inner_eq_expect_symmDiff must be a kernel-checked Theorem"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("chi_inner_eq_expect_symmDiff proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "chi_inner_eq_expect_symmDiff must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_inner_eq_expect_symmDiff's transitive axiom closure must be empty"
        );
    }
}
