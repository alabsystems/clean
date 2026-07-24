// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **STEP 4 (glue piece)**: the half-factor self-adjoint identity
//! that turns STEP 2's inner product `Σ_x (D_i f · half)·(T²g)` into `half·W`,
//! where `W := Σ_y (T_{1/3} g)(y)²` is STEP 3's squared spectral quantity.
//!
//! ## What this proves
//!
//! Writing `T := noiseOp (1/3) n`, `Tg := T g`, `T²g := T (T g)`, `half :=
//! Rat.inv Rat.two`:
//!
//! ```text
//! BoolAnalysis.dualhc_step4_half_inner_eq :
//!   ∀ (n : Nat) (g : HCPoint n → Rat),
//!     subsetSum n (fun x => Rat.mul (Rat.mul (g x) half) (noiseOp (1/3) n (noiseOp (1/3) n g) x))
//!   = Rat.mul half (subsetSum n (fun y => Rat.mul (noiseOp (1/3) n g y) (noiseOp (1/3) n g y)))
//! ```
//!
//! i.e. `Σ_x (g x · half)·(T²g x) = half · W`, `W := Σ_y (Tg y)²`. This is the
//! exact identity STEP 4 needs to cancel: STEP 2's LHS integrand is `(D_i f x ·
//! half)·(w x)` with `w := T²g` (STEP 3's weight, the twice-applied operator as a
//! function), so `Σ_x (D_i f · half)·(T²g) = half·W`, and its 4th power is
//! `(half·W)⁴ = half⁴·W⁴ = W⁴/16` — the source of the constant `16`.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Three rungs, chained by `Eq.trans`:
//!
//! 1. **pointwise regroup** `(g x · half)·u = half·(g x · u)` for `u := T²g x`:
//!    `congrArg (·u) (Rat.mul_comm (g x) half)` lands `(half·g x)·u`, then
//!    `Rat.mul_assoc half (g x) u` lands `half·(g x · u)`. Lifted over the cube by
//!    `subsetSum_congr`, giving `Σ_x (g x·half)·u = Σ_x half·(g x · u)`.
//! 2. **scalar pull-out** `subsetSum_smul n half (fun x => g x · (T²g x))`:
//!    `Σ_x half·(g x·(T²g x)) = half·Σ_x g x·(T²g x)`.
//! 3. **self-adjoint pivot** `noise_self_adjoint_sq (1/3) n g` (GLUE-2):
//!    `Σ_y (Tg y)² = Σ_x g x·(T²g x)`, so `Eq.symm` gives `Σ_x g x·(T²g x) = W`;
//!    `congrArg (half·_)` lifts it to `half·Σ_x g x·(T²g x) = half·W`.
//!
//! Chain `(1)·(2)·(3)` : `Σ_x (g x·half)·(T²g x) = half·W`. Every leaf
//! (`Rat.mul_comm`, `Rat.mul_assoc`, `subsetSum_congr`, `subsetSum_smul`,
//! `noise_self_adjoint_sq`, `congrArg`, `Eq.symm/trans`) is `Constructive` with
//! empty closure, so this glue is too. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the STEP-4 half-factor glue. `noiseOp` / `subsetSum` / `half`
/// spellings are byte-identical to the glue + step2 modules so every leaf is
/// def-eq.
struct Step4Consts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    rat_two: Expr,
    rat_inv: Expr,
    hcpoint: Expr,
    noise_op: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_smul: Expr,
    self_adjoint_sq: Expr,
    mul_comm: Expr,
    mul_assoc: Expr,
    congr_arg: Expr,
}

impl Step4Consts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            rat_two: k("Rat.two"),
            rat_inv: k("Rat.inv"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            noise_op: k("BoolAnalysis.noiseOp"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            self_adjoint_sq: k("BoolAnalysis.noise_self_adjoint_sq"),
            mul_comm: k("Rat.mul_comm"),
            mul_assoc: k("Rat.mul_assoc"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, cc, h1, h2)
    }
    /// `half := Rat.inv Rat.two`. Byte-matches step2's `half`.
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
    }
    /// `ρ_hc := Rat.mk (Int.ofNat 1) 3` (= 1/3). Byte-matches `hc24_at_third`.
    fn rho_third(&self) -> Expr {
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
        let mut three_nat = nat_zero;
        for _ in 0..3 {
            three_nat = Expr::app(nat_succ.clone(), three_nat);
        }
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(int_of_nat, one_nat), three_nat],
        )
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    /// `noiseOp (1/3) n g`.
    fn op(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.noise_op.clone(),
            [self.rho_third(), n.clone(), g.clone()],
        )
    }
    /// `subsetSum n G`.
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `subsetSum_congr n G H pw : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, pw: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, pw])
    }
    /// `subsetSum_smul n c f : subsetSum n (fun p => c·f p) = c·subsetSum n f`.
    fn ssum_smul(&self, n: &Expr, c: Expr, f: Expr) -> Expr {
        Expr::apps(self.subset_sum_smul.clone(), [n.clone(), c, f])
    }
    /// `noise_self_adjoint_sq (1/3) n g : Σ_y (Tg y)² = Σ_x g x·(T²g x)`.
    fn self_adjoint_sq(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.self_adjoint_sq.clone(),
            [self.rho_third(), n.clone(), g.clone()],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `congrArg.{1,1} Rat Rat a b f (h:a=b) : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, f, h])
    }
    /// Build `fun (t : Rat) => f(t)` for `congrArg`.
    fn lam_rat<F: Fn(Expr) -> Expr>(&self, parent: &EnvDeclBuilder, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(self.rat());
        let body = f(t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat(), body))
    }
}

impl Environment {
    /// Register STEP 4's half-factor glue (`dualhc_step4_half_inner_eq`).
    /// Idempotent; kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_step4(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_step4_half_inner_eq()?;
        Ok(())
    }

    /// `BoolAnalysis.dualhc_step4_half_inner_eq` — see the module docs.
    /// `Σ_x (g x·half)·(T²g x) = half·W`. Kernel-checked, `Constructive`, empty
    /// admitted-axiom closure. Idempotent.
    pub fn register_dualhc_step4_half_inner_eq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_step4_half_inner_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_op()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_noise_self_adjoint_sq()?; // GLUE-2
        self.init_algebra_rat_halves()?; // Rat.two, Rat.inv (half spelling)
        self.init_rat_field_inst()?; // mul_comm, mul_assoc
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = Step4Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_half_inner_eq(&c, false),
            value: build_half_inner_eq(&c, true),
        })
    }
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_step4_half_inner_eq`.
fn build_half_inner_eq(c: &Step4Consts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let half = c.half();

    // tg := noiseOp 1/3 n g ; ttg := noiseOp 1/3 n (noiseOp 1/3 n g).
    let tg = c.op(&n, &g);
    let ttg = c.op(&n, &tg);

    // LHS integrand `fun x => (g x · half)·(ttg x)`.
    let lhs_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let gx = Expr::app(g.clone(), x.clone());
        let ttgx = Expr::app(ttg.clone(), x.clone());
        let body = c.mul(c.mul(gx, half.clone()), ttgx);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs = c.ssum(&n, lhs_fn.clone());

    // `prod_fn := fun x => g x · (ttg x)`  (the GLUE-2 RHS integrand).
    let prod_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let gx = Expr::app(g.clone(), x.clone());
        let ttgx = Expr::app(ttg.clone(), x.clone());
        let body = c.mul(gx, ttgx);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    // `mid_fn := fun x => half·(g x · (ttg x))`  (subsetSum_smul's scaled form).
    let mid_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let gx = Expr::app(g.clone(), x.clone());
        let ttgx = Expr::app(ttg.clone(), x.clone());
        let body = c.mul(half.clone(), c.mul(gx, ttgx));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };

    let sum_prod = c.ssum(&n, prod_fn.clone()); // Σ_x g·(ttg)
    let sum_mid = c.ssum(&n, mid_fn.clone()); // Σ_x half·(g·ttg)
                                              // W := Σ_y (tg y)·(tg y)  (GLUE-2 LHS).
    let w = {
        let w_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = d.fresh_local(hcp.clone());
            let tgy = Expr::app(tg.clone(), y.clone());
            let body = c.mul(tgy.clone(), tgy);
            d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum(&n, w_fn)
    };
    let half_w = c.mul(half.clone(), w.clone());
    let half_sum_prod = c.mul(half.clone(), sum_prod.clone());

    let concl = c.eq(lhs.clone(), half_w.clone());

    let tail = if for_value {
        // RUNG 1: pointwise (g x·half)·u = half·(g x·u), lifted by subsetSum_congr.
        let pw = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = d.fresh_local(hcp.clone());
            let gx = Expr::app(g.clone(), x.clone());
            let ttgx = Expr::app(ttg.clone(), x.clone());
            // s1 : (g·half)·u = (half·g)·u   [congrArg (·u) (mul_comm g half)]
            let g_half = c.mul(gx.clone(), half.clone());
            let half_g = c.mul(half.clone(), gx.clone());
            let f1 = c.lam_rat(&d, |t| c.mul(t, ttgx.clone()));
            let s1 = c.congr_arg(
                g_half.clone(),
                half_g.clone(),
                f1,
                c.mul_comm(gx.clone(), half.clone()),
            );
            // s2 : (half·g)·u = half·(g·u)   [mul_assoc half g u]
            let s2 = c.mul_assoc(half.clone(), gx.clone(), ttgx.clone());
            // chain
            let lhs_pt = c.mul(g_half, ttgx.clone());
            let mid_pt = c.mul(half_g, ttgx.clone());
            let rhs_pt = c.mul(half.clone(), c.mul(gx.clone(), ttgx.clone()));
            let pf = c.trans(lhs_pt, mid_pt, rhs_pt, s1, s2);
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), pf))
        };
        let step1 = c.ssum_congr(&n, lhs_fn.clone(), mid_fn.clone(), pw); // lhs = sum_mid

        // RUNG 2: subsetSum_smul n half prod_fn : sum_mid = half·sum_prod.
        let step2 = c.ssum_smul(&n, half.clone(), prod_fn.clone());

        // RUNG 3: noise_self_adjoint_sq 1/3 n g : W = sum_prod ; symm → sum_prod = W ;
        //         congrArg (half·_) → half·sum_prod = half·W.
        let glue = c.self_adjoint_sq(&n, &g); // W = sum_prod
        let sum_prod_eq_w = c.symm(w.clone(), sum_prod.clone(), glue); // sum_prod = W
        let f3 = c.lam_rat(&b, |t| c.mul(half.clone(), t));
        let step3 = c.congr_arg(sum_prod.clone(), w.clone(), f3, sum_prod_eq_w); // half·sum_prod = half·W

        // Chain: lhs = sum_mid = half·sum_prod = half·W.
        let t12 = c.trans(
            lhs.clone(),
            sum_mid.clone(),
            half_sum_prod.clone(),
            step1,
            step2,
        );
        c.trans(lhs, half_sum_prod, half_w, t12, step3)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, g_id, fn_ty, tail);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_step4()
            .expect("init_boolean_analysis_kkl_dualhc_step4");
        env.init_boolean_analysis_kkl_dualhc_step4()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dualhc_step4_half_inner_eq_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.dualhc_step4_half_inner_eq");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
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
}
