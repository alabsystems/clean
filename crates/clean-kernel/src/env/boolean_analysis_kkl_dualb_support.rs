// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-bound Stage C-3 — the support-count collapse for the Hölder b-side
//! (component B3c, the `⟨1,1⟩ → count` glue).
//!
//! # Why this module exists
//!
//! The assembled `(4,4/3)` Hölder shadow `subsetSum_holder_fourth` carries the
//! a-side `⟨1,1⟩ = subsetSum n (fun x => 1·1) = 2^n` factor. For the consumer's
//! exact target `(‖T_{1/3}g‖₂²)² ≤ 16·count³` (with `b = D_i f ∈ {0,±2}`
//! supported on the disagreement set `E`), that abstract `2^n` must be sharpened
//! to the support count `count = subsetSum n (ind∘disagree)`. The sharpening
//! routes the a-side through the indicator `χ_E = ind∘p` (so the constant `1`
//! becomes `χ_E`); the resulting a-side cardinal factor is `⟨χ_E, χ_E⟩ =
//! Σ χ_E·χ_E`, which collapses to `Σ χ_E = count` by indicator idempotence.
//! THIS module lands that collapse at the `subsetSum` level:
//!
//! ```text
//! BoolAnalysis.subsetSum_ind_sq_eq_ind :
//!   ∀ (n : Nat) (p : HCPoint n → Bool),
//!     subsetSum n (fun x => Rat.mul (ind (p x)) (ind (p x)))
//!       = subsetSum n (fun x => ind (p x))
//! ```
//!
//! i.e. `Σ_x χ(x)² = Σ_x χ(x)` for any Boolean predicate `p` and its `{0,1}`
//! indicator `χ = ind∘p`. At `p := disagree_i`, the RHS is exactly the
//! un-normalized influence count `count` that `2^n` must become.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! `subsetSum_congr n (fun x => ind(p x)·ind(p x)) (fun x => ind(p x))
//! (fun x => ind_mul_self (p x))`, where `BoolAnalysis.ind_mul_self b :
//! ind b · ind b = ind b` (landed, constructive) discharges each per-point goal.
//! Both atoms (`subsetSum_congr`, `ind_mul_self`) are `Constructive` with empty
//! closure, so the result is too.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the indicator support-count collapse.
struct SupportConsts {
    nat: Expr,
    rat: Expr,
    bool_t: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    ind: Expr,
    ind_mul_self: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    eq: Expr,
}

impl SupportConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_t: Expr::const_(Name::from_string("Bool"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            ind_mul_self: Expr::const_(Name::from_string("BoolAnalysis.ind_mul_self"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Bool`.
    fn hcpoint_to_bool(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.bool_t.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `ind (p x)`.
    fn ind_at(&self, p: &Expr, x: &Expr) -> Expr {
        Expr::app(self.ind.clone(), Expr::app(p.clone(), x.clone()))
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), l, r])
    }
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, hyp: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, hyp])
    }
    /// `fun (x : HCPoint n) => Rat.mul (ind (p x)) (ind (p x))`.
    fn ind_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = self.mul(self.ind_at(p, &x), self.ind_at(p, &x));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => ind (p x)`.
    fn ind_fn(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = self.ind_at(p, &x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_ind_sq_eq_ind` — the indicator
    /// support-count collapse `Σ χ² = Σ χ` (`χ = ind∘p`), the `⟨1,1⟩ → count`
    /// glue for the Hölder b-side. Kernel-checked, `ProofQuality::Constructive`,
    /// empty closure. Idempotent.
    pub fn register_subset_sum_ind_sq_eq_ind(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_ind_sq_eq_ind");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_ind_mul_self()?;

        let c = SupportConsts::new();
        let (ty, value) = build_support(&c);
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

/// Build the type + proof of `BoolAnalysis.subsetSum_ind_sq_eq_ind`.
fn build_support(c: &SupportConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (p_id, p) = b.fresh_local(c.hcpoint_to_bool(&n));
        let lhs = c.ssum(&n, c.ind_sq_fn(&b, &n, &p));
        let rhs = c.ssum(&n, c.ind_fn(&b, &n, &p));
        let concl = c.eq_rat(lhs, rhs);
        let e = b.mk_pi(p_id, BinderInfo::Default, c.hcpoint_to_bool(&n), concl);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (p_id, p) = b.fresh_local(c.hcpoint_to_bool(&n));

        let g = c.ind_sq_fn(&b, &n, &p); // fun x => ind(p x)·ind(p x)
        let h = c.ind_fn(&b, &n, &p); // fun x => ind(p x)

        // pointwise hyp : ∀ x, ind(p x)·ind(p x) = ind(p x)  (ind_mul_self (p x)).
        let hyp = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = d.fresh_local(hcp.clone());
            let body = Expr::app(c.ind_mul_self.clone(), Expr::app(p.clone(), x.clone()));
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
        };
        let proof = c.ssum_congr(&n, g, h, hyp);

        let e = b.mk_lam(p_id, BinderInfo::Default, c.hcpoint_to_bool(&n), proof);
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
        env.register_subset_sum_ind_sq_eq_ind()
            .expect("register_subset_sum_ind_sq_eq_ind should succeed");
        env
    }

    #[test]
    fn test_support_registered_as_theorem() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.subsetSum_ind_sq_eq_ind"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_support_type_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_ind_sq_eq_ind"),
                vec![],
            ))
            .expect("BoolAnalysis.subsetSum_ind_sq_eq_ind should type-check");
    }

    #[test]
    fn test_support_constructive_axiom_free() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.subsetSum_ind_sq_eq_ind");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
