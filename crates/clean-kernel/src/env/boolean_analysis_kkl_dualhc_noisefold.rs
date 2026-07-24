// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — the **`noiseFn` ↔ `noiseOp` fold bridge**: the two un-normalized
//! noise-operator carriers agree pointwise (up to summand commutativity).
//!
//! `noiseFn` (the `Fin (2^n)`-indexed carrier `hc24_at_third` / STEP 3 speak) and
//! `noiseOp` (the `HCPoint n → Rat` function carrier the self-adjoint glue / STEP
//! 2's weight speak) are the SAME un-normalized `T_ρ`, written with the two
//! factors of the summand in opposite order:
//!
//! ```text
//! noiseFn ρ n F jx = Fin.sum (2^n) (fun jy => F(decode jy) · dens ρ n (decode jx)(decode jy))
//! noiseOp ρ n F (decode jx)
//!   = subsetSum n (fun x => dens ρ n (decode jx) x · F x)
//!   = Fin.sum (2^n) (fun jy => dens ρ n (decode jx)(decode jy) · F(decode jy))
//! ```
//!
//! (the second line uses `subsetSum n G ≡ Fin.sum (2^n) (fun j => G (decode j))`,
//! the reducible def of `subsetSum`). So:
//!
//! ```text
//! BoolAnalysis.noiseFn_eq_noiseOp :
//!   ∀ (ρ : Rat) (n : Nat) (F : HCPoint n → Rat) (jx : Fin (2^n)),
//!     noiseFn ρ n F jx = noiseOp ρ n F (hcDecode n jx)
//! ```
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! `Fin.sum_congr (2^n) lhsFn rhsFn (fun jy => Rat.mul_comm (F(decode jy)) (dens
//! ρ n (decode jx)(decode jy)))`: both sides δ-reduce to a `Fin.sum (2^n)` whose
//! summands are `F·dens` (LHS) and `dens·F` (RHS), related pointwise by
//! `Rat.mul_comm`. `Fin.sum_congr` lifts the pointwise commutation to the sums.
//! Leaves `Fin.sum_congr`, `Rat.mul_comm` are `Constructive` with empty closure,
//! so this bridge is too. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms. `noiseFn` / `noiseOp` / `noiseDensityW` / `hcDecode` spellings
/// are byte-identical to the carrier modules so the def-unfolds are def-eq.
struct FoldConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_congr: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    noise_density: Expr,
    noise_fn: Expr,
    noise_op: Expr,
    mul_comm: Expr,
}

impl FoldConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_congr: k("Fin.sum_congr"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            noise_fn: k("BoolAnalysis.noiseFn"),
            noise_op: k("BoolAnalysis.noiseOp"),
            mul_comm: k("Rat.mul_comm"),
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
    /// `2^n := Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_pow(&self, n: &Expr) -> Expr {
        self.fin_of(&self.pow2(n))
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    /// `hcDecode n k`.
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()])
    }
    /// `noiseDensityW ρ n a b`.
    fn dens(&self, rho: &Expr, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), a.clone(), b.clone()],
        )
    }
    /// `noiseFn ρ n F jx`.
    fn noise_fn(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), n.clone(), f.clone(), jx.clone()],
        )
    }
    /// `noiseOp ρ n F y`.
    fn noise_op_at(&self, rho: &Expr, n: &Expr, f: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_op.clone(),
            [rho.clone(), n.clone(), f.clone(), y.clone()],
        )
    }
    /// `Fin.sum N h`.
    fn fin_sum(&self, n_pow: &Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n_pow.clone(), h])
    }
    /// `Fin.sum_congr N f g pw : Fin.sum N f = Fin.sum N g`.
    fn fin_sum_congr(&self, n_pow: &Expr, f: Expr, g: Expr, pw: Expr) -> Expr {
        Expr::apps(self.fin_sum_congr.clone(), [n_pow.clone(), f, g, pw])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
}

impl Environment {
    /// Register the `noiseFn ↔ noiseOp` fold bridge. Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_noisefold(&mut self) -> Result<(), EnvError> {
        self.register_noise_fn_eq_noise_op()?;
        Ok(())
    }

    /// `BoolAnalysis.noiseFn_eq_noiseOp` — see the module docs.
    /// `noiseFn ρ n F jx = noiseOp ρ n F (hcDecode n jx)`. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_noise_fn_eq_noise_op(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseFn_eq_noiseOp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_fn()?;
        self.register_noise_op()?;
        self.register_subset_sum()?;
        self.init_fin_sum()?; // Fin.sum_congr
        self.register_rat_mul_comm_proof()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = FoldConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_fold(&c, false),
            value: build_fold(&c, true),
        })
    }
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `noiseFn_eq_noiseOp`.
fn build_fold(c: &FoldConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.hcpoint_to_rat(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (jx_id, jx) = b.fresh_local(c.fin_pow(&n));

    let n_pow = c.pow2(&n);
    let x = c.decode(&n, &jx); // hcDecode n jx, the `noiseOp` argument.

    let lhs = c.noise_fn(&rho, &n, &f, &jx);
    let rhs = c.noise_op_at(&rho, &n, &f, &x);
    let concl = c.eq(lhs.clone(), rhs.clone());

    let tail = if for_value {
        // lhsFn := fun jy => F(decode jy)·dens ρ n (decode jx)(decode jy)  (noiseFn summand)
        let lhs_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (jy_id, jy) = d.fresh_local(c.fin_pow(&n));
            let y = c.decode(&n, &jy);
            let f_y = Expr::app(f.clone(), y.clone());
            let dens = c.dens(&rho, &n, &x, &y);
            let body = c.mul(f_y, dens);
            d.finish_child(d.mk_lam(jy_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        // rhsFn := fun jy => dens ρ n (decode jx)(decode jy)·F(decode jy)  (noiseOp∘subsetSum summand)
        let rhs_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (jy_id, jy) = d.fresh_local(c.fin_pow(&n));
            let y = c.decode(&n, &jy);
            let f_y = Expr::app(f.clone(), y.clone());
            let dens = c.dens(&rho, &n, &x, &y);
            let body = c.mul(dens, f_y);
            d.finish_child(d.mk_lam(jy_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        // pointwise hyp : fun jy => mul_comm (F(decode jy)) (dens ρ n (decode jx)(decode jy))
        let pw = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (jy_id, jy) = d.fresh_local(c.fin_pow(&n));
            let y = c.decode(&n, &jy);
            let f_y = Expr::app(f.clone(), y.clone());
            let dens = c.dens(&rho, &n, &x, &y);
            let body = c.mul_comm(f_y, dens);
            d.finish_child(d.mk_lam(jy_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        // Fin.sum_congr (2^n) lhsFn rhsFn pw : Fin.sum lhsFn = Fin.sum rhsFn.
        // LHS def-eq `noiseFn ρ n F jx`; RHS def-eq `noiseOp ρ n F (decode jx)`.
        let _ = (
            c.fin_sum(&n_pow, lhs_fn.clone()),
            c.fin_sum(&n_pow, rhs_fn.clone()),
        );
        c.fin_sum_congr(&n_pow, lhs_fn, rhs_fn, pw)
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
    let e = bind(&b, jx_id, c.fin_pow(&n), tail);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    let e = bind(&b, rho_id, c.rat.clone(), e);
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
        env.init_boolean_analysis_kkl_dualhc_noisefold()
            .expect("init_boolean_analysis_kkl_dualhc_noisefold");
        env.init_boolean_analysis_kkl_dualhc_noisefold()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_noise_fn_eq_noise_op_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.noiseFn_eq_noiseOp");
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
