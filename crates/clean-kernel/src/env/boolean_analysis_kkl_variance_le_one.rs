// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL unconditional strengthening — the variance upper bound `Var[f] ≤ 1`.
//!
//! ```text
//! BoolAnalysis.variance_le_one :
//!   ∀ (n : Nat) (f : BoolFn n), Rat.le (Variance n f) Rat.one
//! ```
//!
//! `Variance n f` δ-unfolds to `E[f̃²] − (E[f̃])²` with `f̃ = pm∘f`. The textbook
//! one-line bound:
//!   - `E[f̃²] = E[const 1] = 1` (`Expect_congr` over the per-point `pm_mul_self`
//!     `f̃(x)² = 1`, then `Expect_const_one`),
//!   - `0 ≤ (E[f̃])²` (`Rat.sq_nonneg`),
//!   - so `Var = E[f̃²] − (E[f̃])² ≤ 1 − 0 = 1` (`Rat.sub_le_sub` + `Rat.sub_zero`).
//!
//! This is the `Var ≤ 1` half O'Donnell uses to turn the conditional sharp-KKL
//! bound `(k+1)·Var ≤ 2·n·Inf_i` into the UNCONDITIONAL max-influence inequality
//! (combined with the large-influence dichotomy and the `(k+1)³·81^k ≤ n`
//! threshold). Kernel-checked, `Constructive`, empty admitted-axiom closure. No
//! axiom added/removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the `Var ≤ 1` proof. `Expect`/`pm`/`Variance` spellings
/// BYTE-MATCH `register_variance` so the unfolded `Variance n f` body is
/// definitionally the `E[sq] − sqE` term this proof reasons about.
struct VarOneConsts {
    nat: Expr,
    rat: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    expect: Expr,
    pm: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    variance: Expr,
    u1: Level,
}

impl VarOneConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_one: k("Rat.one"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            expect: k("BoolAnalysis.Expect"),
            pm: k("BoolAnalysis.pm"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            variance: k("BoolAnalysis.Variance"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn rat_le(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [l, r])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    #[cfg(test)]
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }

    /// `fun (x : HCPoint n) => pm (f x)` — the `±1` embedding `f̃`. BYTE-MATCHES
    /// the `pm_f` integrand in `register_variance`.
    fn pm_f(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = Expr::app(self.pm.clone(), Expr::app(f.clone(), x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => Rat.mul (pm (f x)) (pm (f x))` — the `f̃²`
    /// integrand. BYTE-MATCHES `pm_f_sq` in `register_variance`.
    fn pm_f_sq(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let pmfx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x));
        let body = self.mul(pmfx.clone(), pmfx);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (_ : HCPoint n) => Rat.one` — the const-1 integrand. BYTE-MATCHES
    /// `const_one_integrand` in `register_expect_one_theorems` (the LHS of
    /// `Expect_const_one`).
    fn const_one(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, _x) = b.fresh_local(hcp.clone());
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, self.rat_one.clone()))
    }
    /// `Expect n g`.
    fn expect_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.expect.clone(), [n.clone(), g])
    }
    /// `fun (x : HCPoint n) => pm_mul_self (f x) : (pm (f x))·(pm (f x)) = 1`
    /// — the pointwise-equality witness `(pm_f_sq) x = (const_one) x` that
    /// `Expect_congr` consumes. The body type at `x` is `pm(f x)·pm(f x) = 1`,
    /// which is exactly `(pm_f_sq) x = (const_one) x` after β.
    fn pointwise(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.pm_mul_self"), vec![]),
            Expr::app(f.clone(), x),
        );
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

/// Build the proof term `fun (n)(f) => (proof of Var n f ≤ 1)`.
fn build_variance_le_one(c: &VarOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let sq = c.pm_f_sq(&b, &n, &f); // f̃² integrand
    let pmf = c.pm_f(&b, &n, &f); // f̃ integrand
    let c1 = c.const_one(&b, &n); // const-1 integrand
    let e_sq = c.expect_of(&n, sq.clone()); // E[f̃²]
    let e_pm = c.expect_of(&n, pmf.clone()); // E[f̃]
    let sq_e = c.mul(e_pm.clone(), e_pm.clone()); // (E[f̃])²
    let e_c1 = c.expect_of(&n, c1.clone()); // E[const 1]

    // hcongr : E[f̃²] = E[const 1]
    //   Expect_congr n (f̃²) (const 1) pointwise.
    let hcongr = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.Expect_congr"), vec![]),
        [n.clone(), sq.clone(), c1.clone(), c.pointwise(&b, &n, &f)],
    );
    // hconst : E[const 1] = 1   (Expect_const_one n).
    let hconst = Expr::app(
        Expr::const_(Name::from_string("BoolAnalysis.Expect_const_one"), vec![]),
        n.clone(),
    );
    // hEsq : E[f̃²] = 1   (Eq.trans hcongr hconst).
    let hesq = c.trans(
        e_sq.clone(),
        e_c1.clone(),
        c.rat_one.clone(),
        hcongr,
        hconst,
    );

    // hle1 : E[f̃²] ≤ 1.
    //   Rat.le_refl 1 : 1 ≤ 1; subst (symm hEsq : 1 = E[f̃²]) into motive (t ↦ t ≤ 1).
    let h_refl1 = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        [c.rat_one.clone()],
    );
    let motive_le1 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.rat_le(t, c.rat_one.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let hle1 = c.subst(
        motive_le1,
        c.rat_one.clone(),
        e_sq.clone(),
        c.symm(e_sq.clone(), c.rat_one.clone(), hesq),
        h_refl1,
    );

    // h0_sqe : 0 ≤ (E[f̃])²   (Rat.sq_nonneg (E[f̃])).
    let h0_sqe = Expr::apps(
        Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
        [e_pm.clone()],
    );

    // h_sub_le : (E[f̃²] − (E[f̃])²) ≤ (1 − 0)
    //   Rat.sub_le_sub a b c d (a≤b)(d≤c) : a−c ≤ b−d
    //   with a := E[f̃²], b := 1, c := (E[f̃])², d := 0.
    let h_sub_le = Expr::apps(
        Expr::const_(Name::from_string("Rat.sub_le_sub"), vec![]),
        [
            e_sq.clone(),
            c.rat_one.clone(),
            sq_e.clone(),
            c.rat_zero.clone(),
            hle1,
            h0_sqe,
        ],
    );

    // e_sub_zero : (1 − 0) = 1   (Rat.sub_zero 1).
    let e_sub_zero = Expr::apps(
        Expr::const_(Name::from_string("Rat.sub_zero"), vec![]),
        [c.rat_one.clone()],
    );
    // Goal: Var ≤ 1, where Var ≡ (E[f̃²] − (E[f̃])²) by δ. Transport the RHS of
    // h_sub_le (which is `1 − 0`) to `1` via e_sub_zero; motive (t ↦ Var ≤ t).
    let var = c.variance_of(&n, &f);
    let one_minus_zero = c.sub(c.rat_one.clone(), c.rat_zero.clone());
    let motive_var_le = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.rat_le(var.clone(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // h_sub_le : Var ≤ (1 − 0)  (def-eq: LHS E[f̃²]−(E[f̃])² ≡ Var; Rat.le ≡ LE.le).
    let proof = c.subst(
        motive_var_le,
        one_minus_zero,
        c.rat_one.clone(),
        e_sub_zero,
        h_sub_le,
    );

    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, proof);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.variance_le_one : ∀ n f, Variance n f ≤ 1`.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent;
    /// no axiom added/removed.
    pub fn register_variance_le_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.variance_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Variance, Expect, pm, Expect_congr, Expect_const_one
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_pm_mul_self_theorem()?; // pm b · pm b = 1
        self.register_expect_one_theorems()?; // Expect_const_one
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg, Rat.le_refl-adjacent
        self.register_rat_sub_le_sub()?; // Rat.sub_le_sub
        self.register_rat_sub_zero()?; // Rat.sub_zero
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = VarOneConsts::new();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let concl = c.rat_le(c.variance_of(&n, &f), c.rat_one.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, concl);
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
        };
        let value = build_variance_le_one(&c);
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
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_variance_le_one_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_variance_le_one()
            .expect("register_variance_le_one");
        let nm = Name::from_string("BoolAnalysis.variance_le_one");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("variance_le_one proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_variance_le_one_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_variance_le_one().expect("first");
        env.register_variance_le_one().expect("idempotent");
    }
}
