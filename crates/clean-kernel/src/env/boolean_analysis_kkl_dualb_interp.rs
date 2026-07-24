// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-bound Stage C-3 — the a-side INTERPOLATION Cauchy–Schwarz
//! (component B3c, the second of the two CS applications that compose into the
//! `(4,4/3)` Hölder step).
//!
//! # The double-CS route to `(4,4/3)` Hölder
//!
//! The §9.6 dual `(4/3→2)` bound's Hölder step is `⟨a,b⟩ ≤ ‖a‖₄·‖b‖_{4/3}`.
//! Because `4 = 2²` and `4/3` is its conjugate, this Hölder factors into TWO
//! Cauchy–Schwarz applications (the classical dyadic interpolation), so it is
//! reachable axiom-free WITHOUT a `^{4/3}` carrier — exactly the route the
//! sqrt-layer obstruction note (§5) asked for ("re-shape the chain so the √
//! cancels symbolically"). The two halves, in their squared/4th-power RATIONAL
//! shadows:
//!
//! 1. **The endpoint CS** (`subsetSum_cauchy_schwarz`, landed):
//!    `⟨a,b⟩² ≤ ⟨a,a⟩·⟨b,b⟩`.
//! 2. **The a-side interpolation CS** (THIS module):
//!    `⟨a,a⟩² ≤ ⟨a²,a²⟩·⟨1,1⟩`, i.e. `(Σ a²)² ≤ (Σ a⁴)·(Σ 1)`. The LHS is the
//!    CLEAN `(Σ a²)²` (the `·1` of the raw CS instance bridged off by
//!    `subsetSum_congr`∘`Rat.mul_one`) so it composes verbatim with the endpoint
//!    CS, whose `⟨a,a⟩` is the same `Σ a²`.
//!
//! Chaining (1) squared with (2):
//! `⟨a,b⟩⁴ ≤ ⟨a,a⟩²·⟨b,b⟩² ≤ (Σa⁴)·(Σ1)·⟨b,b⟩²`. With `b = D_i f ∈ {0,±2}`
//! supported on the disagreement set, the `Σ1` collapses to the support count
//! (this collapse — the b-support restriction — is the remaining glue, see the
//! module-level note in `boolean_analysis_kkl_dualb_cs.rs`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! ```text
//! BoolAnalysis.subsetSum_sq_le_fourth_card :
//!   ∀ (n : Nat) (a : HCPoint n → Rat),
//!     Rat.le
//!       (Rat.mul (subsetSum n (fun x => Rat.mul (a x) (a x)))
//!                (subsetSum n (fun x => Rat.mul (a x) (a x))))
//!       (Rat.mul (subsetSum n (fun x => Rat.mul (Rat.mul (a x) (a x))
//!                                               (Rat.mul (a x) (a x))))
//!                (subsetSum n (fun x => Rat.mul Rat.one Rat.one)))
//! ```
//!
//! i.e. `(Σ a²)² ≤ (Σ a²·a²)·(Σ 1·1)`, the `‖a‖₂⁴ ≤ ‖a‖₄⁴·|cube|` interpolation.
//! The LHS is the CLEAN `(Σ a²)²` so it composes verbatim with the endpoint CS.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! Instantiate `subsetSum_cauchy_schwarz` at `A := fun x => a x · a x` (the
//! squared function) and `B := fun x => Rat.one`, giving
//! `(Σ a²·1)² ≤ (Σ a²·a²)·(Σ 1·1)`. Then bridge the LHS `Σ(a²·1) → Σ a²` via
//! `subsetSum_congr` over the pointwise `Rat.mul_one (a x·a x)`, and transport it
//! into the squared LHS by `Eq.subst` (motive `fun L => L·L ≤ rhs`). Every atom
//! (`subsetSum_cauchy_schwarz`, `subsetSum_congr`, `Rat.mul_one`, `Eq.subst`) is
//! `Constructive` with empty closure, so the result is too.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the a-side interpolation-CS build.
struct DualbInterpConsts {
    nat: Expr,
    rat: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_mul_one: Expr,
    hcpoint: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    cs: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    eq_subst: Expr,
}

impl DualbInterpConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            cs: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_cauchy_schwarz"),
                vec![],
            ),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![u1]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `Eq.subst (motive) a b (h:a=b)(hm:motive a) : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h: Expr, hm: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h, hm],
        )
    }
    /// `subsetSum_congr n G H (∀x, G x = H x) : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, hyp: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, hyp])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `fun (x : HCPoint n) => Rat.mul (a x) (a x)` — the squared function `A`.
    fn sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(a.clone(), x.clone()), Expr::app(a.clone(), x));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (_ : HCPoint n) => Rat.one` — the constant `B`.
    fn one_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, _x) = d.fresh_local(hcp.clone());
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, self.rat_one.clone()))
    }
    /// `fun (x : HCPoint n) => Rat.mul (P x) (Q x)` — the CS product integrand.
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
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_sq_le_fourth_card` — the a-side
    /// interpolation Cauchy–Schwarz `(Σ a²)² ≤ (Σ a²·a²)·(Σ 1·1)`, the second
    /// of the two CS applications composing into the `(4,4/3)` Hölder step.
    /// Kernel-checked, `ProofQuality::Constructive`, empty closure. Idempotent.
    pub fn register_subset_sum_sq_le_fourth_card(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_sq_le_fourth_card");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_cauchy_schwarz()?;
        self.init_eq()?;
        self.init_rat()?; // Rat.mul_one
        self.register_subset_sum_congr()?; // BoolAnalysis.subsetSum_congr

        let c = DualbInterpConsts::new();
        let (ty, value) = build_interp(&c);
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

/// Build the type + proof of `BoolAnalysis.subsetSum_sq_le_fourth_card`.
///
/// Conclusion (the CLEAN form, LHS bridged off the `·1`):
/// `(Σ a²)² ≤ (Σ a²·a²)·(Σ 1·1)`, i.e. with `M := subsetSum n (fun x => a x·a x)`,
/// `M·M ≤ (Σ a⁴)·(Σ 1²)`. The clean `M` LHS is what makes this directly
/// composable with the endpoint CS (whose `⟨a,a⟩` is the same `M`).
fn build_interp(c: &DualbInterpConsts) -> (Expr, Expr) {
    // Shared pieces at fixed (builder, n, a). `m` = Σ a² (clean), `s_ab` = Σ(a²·1)
    // (the raw CS LHS integrand), `rhs` = (Σ a²·a²)·(Σ 1·1).
    let pieces = |b: &EnvDeclBuilder, n: &Expr, a: &Expr| -> (Expr, Expr, Expr) {
        let big_a = c.sq_fn(b, n, a); // a² as a function
        let big_b = c.one_fn(b, n); // const 1
        let m = c.ssum(n, c.sq_fn(b, n, a)); // Σ (a x·a x)
        let s_ab = c.ssum(n, c.prod_fn(b, n, &big_a, &big_b)); // Σ (a²·1)
        let s_aa = c.ssum(n, c.prod_fn(b, n, &big_a, &big_a)); // Σ (a²·a²)
        let s_bb = c.ssum(n, c.prod_fn(b, n, &big_b, &big_b)); // Σ (1·1)
        let rhs = c.mul(s_aa, s_bb);
        (m, s_ab, rhs)
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));
        let (m, _s_ab, rhs) = pieces(&b, &n, &a);
        let lhs = c.mul(m.clone(), m);
        let concl = c.le(lhs, rhs);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.hcpoint_to_rat(&n), concl);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));

        let big_a = c.sq_fn(&b, &n, &a);
        let big_b = c.one_fn(&b, &n);
        let (m, s_ab, rhs) = pieces(&b, &n, &a);

        // h_cs : (Σ(a²·1))² ≤ rhs   (subsetSum_cauchy_schwarz n a² 1).
        let h_cs = Expr::apps(c.cs.clone(), [n.clone(), big_a.clone(), big_b]);

        // bridge : Σ(a²·1) = Σ a²  via subsetSum_congr over (a² x·1 = a² x).
        //   pointwise hyp : ∀ x, (a x·a x)·1 = (a x·a x)   [Rat.mul_one (a x·a x)].
        let a2_one_fn = c.prod_fn(&b, &n, &big_a, &c.one_fn(&b, &n)); // fun x => (a²·1)
        let a2_fn = c.sq_fn(&b, &n, &a); // fun x => a²
        let hyp = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = d.fresh_local(hcp.clone());
            let a2x = c.mul(
                Expr::app(a.clone(), x.clone()),
                Expr::app(a.clone(), x.clone()),
            );
            let body = c.mul_one(a2x); // : (a x·a x)·1 = (a x·a x)
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
        };
        let bridge = c.ssum_congr(&n, a2_one_fn, a2_fn, hyp); // : Σ(a²·1) = Σ a²

        // Transport h_cs's LHS `(Σ(a²·1))²` → `(Σ a²)²` via Eq.subst:
        //   motive := fun L => Rat.le (L·L) rhs.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (l_id, l) = d.fresh_local(c.rat.clone());
            let body = c.le(c.mul(l.clone(), l), rhs.clone());
            d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let proof = c.subst(motive, s_ab, m, bridge, h_cs);

        let e = b.mk_lam(a_id, BinderInfo::Default, c.hcpoint_to_rat(&n), proof);
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
        env.register_subset_sum_sq_le_fourth_card()
            .expect("register_subset_sum_sq_le_fourth_card should succeed");
        env
    }

    #[test]
    fn test_interp_registered_as_theorem() {
        let env = env();
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.subsetSum_sq_le_fourth_card",
            ))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_interp_type_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_sq_le_fourth_card"),
                vec![],
            ))
            .expect("BoolAnalysis.subsetSum_sq_le_fourth_card should type-check");
    }

    #[test]
    fn test_interp_constructive_axiom_free() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.subsetSum_sq_le_fourth_card");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule).
    #[test]
    fn test_interp_refute_returns_none() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.subsetSum_sq_le_fourth_card",
            ))
            .expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "interpolation CS is TRUE; refute_conjecture must return None"
        );
    }
}
