// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-bound Stage C-3 — the `subsetSum`-level Cauchy–Schwarz inequality
//! (component B3c, the `p = q = 2` case of the Hölder step).
//!
//! The §9.6 dual `(4/3→2)` hypercontractive bound factors through the inner
//! product `⟨a,b⟩ := subsetSum n (fun x => a x · b x)` and the Hölder step
//! `⟨a,b⟩ ≤ ‖a‖₄·‖b‖_{4/3}`. The genuine `(4,4/3)` Hölder needs a `^{4/3}`
//! carrier the `Rat`-only overlay does not have (see the module-level
//! obstruction note in `boolean_analysis_kkl_dualb_holder_obstruction.rs`); the
//! `p = q = 2` ENDPOINT of the Hölder family is the finite Cauchy–Schwarz
//! inequality, which IS axiom-free in the overlay. This module lands it at the
//! `subsetSum` level:
//!
//! ```text
//! BoolAnalysis.subsetSum_cauchy_schwarz :
//!   ∀ (n : Nat) (a b : HCPoint n → Rat),
//!     Rat.le (Rat.mul (subsetSum n (fun x => a x · b x))
//!                     (subsetSum n (fun x => a x · b x)))
//!            (Rat.mul (subsetSum n (fun x => a x · a x))
//!                     (subsetSum n (fun x => b x · b x)))
//! ```
//!
//! i.e. `⟨a,b⟩² ≤ ⟨a,a⟩·⟨b,b⟩`. This is the inner-product Cauchy–Schwarz the
//! Hölder assembly degenerates to at conjugate exponents `(2,2)`, and a
//! genuinely reusable on-branch brick (every quadratic-form bound over the cube
//! is an instance).
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! The landed `Fin.sum_cauchy_schwarz : ∀ (m : Nat) (a' b' : Fin m → Rat),
//! (Σⱼ a'ⱼb'ⱼ)² ≤ (Σⱼ a'ⱼ²)·(Σⱼ b'ⱼ²)` (the Lagrange-identity finite
//! Cauchy–Schwarz, axiom-free) is instantiated at
//! `m := Nat.pow 2 n`, `a' := fun j => a (hcDecode n j)`,
//! `b' := fun j => b (hcDecode n j)`. Because `BoolAnalysis.subsetSum` is a
//! `is_reducible` definition that δ-reduces to
//! `Fin.sum (2^n) (fun j => G (hcDecode n j))`, each `subsetSum n (fun x => p x·q x)`
//! is DEFINITIONALLY EQUAL (reducible δ + β) to `Fin.sum (2^n) (fun j =>
//! (p (hcDecode n j))·(q (hcDecode n j)))`, which is exactly the corresponding
//! `Fin.sum_cauchy_schwarz` operand. So the instantiated proof term type-checks
//! directly against the `subsetSum`-level statement — no rewriting, no new
//! lemmas. Its axiom closure is `Fin.sum_cauchy_schwarz`'s, which is empty, so
//! the result is `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the `subsetSum`-level Cauchy–Schwarz build.
struct DualbCsConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    subset_sum: Expr,
    fin_cs: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
}

impl DualbCsConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            fin_cs: Expr::const_(Name::from_string("Fin.sum_cauchy_schwarz"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Rat`.
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    /// `subsetSum n g`.
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
    /// `fun (j : Fin (2^n)) => g (hcDecode n j)` — the `Fin.sum` summand the
    /// reducible `subsetSum` δ-unfolds to.
    fn decoded_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_pow = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), self.pow2(n));
        let (j_id, j) = d.fresh_local(fin_pow.clone());
        let decoded = Expr::apps(self.hc_decode.clone(), [n.clone(), j]);
        let body = Expr::app(g.clone(), decoded);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
    }
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_cauchy_schwarz` — the inner-product
    /// Cauchy–Schwarz inequality over the cube (the `(2,2)` endpoint of the
    /// Hölder family used by the dual `(4/3→2)` bound). Kernel-checked,
    /// `ProofQuality::Constructive` with empty admitted-axiom closure.
    /// Idempotent.
    pub fn register_subset_sum_cauchy_schwarz(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_cauchy_schwarz");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_fin_sum_cauchy_schwarz_theorem()?;

        let c = DualbCsConsts::new();
        let (ty, value) = build_subset_sum_cs(&c);
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

/// Build the type + proof of `BoolAnalysis.subsetSum_cauchy_schwarz`.
fn build_subset_sum_cs(c: &DualbCsConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));
        let (bb_id, bv) = b.fresh_local(c.hcpoint_to_rat(&n));

        let sab = c.ssum(&n, c.prod_fn(&b, &n, &a, &bv));
        let saa = c.ssum(&n, c.prod_fn(&b, &n, &a, &a));
        let sbb = c.ssum(&n, c.prod_fn(&b, &n, &bv, &bv));

        let lhs = c.mul(sab.clone(), sab);
        let rhs = c.mul(saa, sbb);
        let concl = c.le(lhs, rhs);

        let e = b.mk_pi(bb_id, BinderInfo::Default, c.hcpoint_to_rat(&n), concl);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.hcpoint_to_rat(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));
        let (bb_id, bv) = b.fresh_local(c.hcpoint_to_rat(&n));

        // a' := fun j => a (hcDecode n j); b' := fun j => b (hcDecode n j).
        let a_prime = c.decoded_fn(&b, &n, &a);
        let b_prime = c.decoded_fn(&b, &n, &bv);

        // Fin.sum_cauchy_schwarz (2^n) a' b'
        //   : (Σⱼ a'ⱼb'ⱼ)² ≤ (Σⱼ a'ⱼ²)·(Σⱼ b'ⱼ²)
        // which is reducible-δ + β equal to the subsetSum-level statement.
        let proof = Expr::apps(c.fin_cs.clone(), [c.pow2(&n), a_prime, b_prime]);

        let e = b.mk_lam(bb_id, BinderInfo::Default, c.hcpoint_to_rat(&n), proof);
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
        env.register_subset_sum_cauchy_schwarz()
            .expect("register_subset_sum_cauchy_schwarz should succeed");
        env
    }

    #[test]
    fn test_subset_sum_cs_registered_as_theorem() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.subsetSum_cauchy_schwarz"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_subset_sum_cs_type_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_cauchy_schwarz"),
                vec![],
            ))
            .expect("BoolAnalysis.subsetSum_cauchy_schwarz should type-check");
    }

    #[test]
    fn test_subset_sum_cs_constructive_axiom_free() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.subsetSum_cauchy_schwarz");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// find a counterexample to the (TRUE) Cauchy–Schwarz target.
    #[test]
    fn test_subset_sum_cs_refute_returns_none() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.subsetSum_cauchy_schwarz"))
            .expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "Cauchy-Schwarz is TRUE; refute_conjecture must return None"
        );
    }
}
