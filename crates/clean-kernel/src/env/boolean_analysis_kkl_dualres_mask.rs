// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3 residual, component **M-Hölder**, the
//! SUPPORT-MASK pointwise atom.
//!
//! # Where this sits
//!
//! The §9.6 M-Hölder hypothesis the dual-bound assembly
//! (`two_norm_sq_le_of_holder_chain`) consumes is
//! `h_holder4 : (l·l)·(l·l) ≤ f4·(16·cnt³)` with `l = ⟨a, D⟩`, `f4 = Σ a⁴`,
//! `cnt = Σ χ`, where `D = pm p − pm q ∈ {0,±2}` is a discrete derivative and
//! `χ = ind(¬(p == q))` is the `{0,1}` indicator of its support (the
//! disagreement set). The genuine analytic content is the SUPPORT-restricted
//! double Cauchy–Schwarz: because `D` vanishes off `χ`'s support, the inner
//! product `⟨a, D⟩` only sees `a` on the support, and the cardinal factor is the
//! support count `cnt` (NOT the full cube `2^n`). See the consumer module
//! `boolean_analysis_kkl_dualres_holder.rs`.
//!
//! The load-bearing per-point fact making the support restriction VALID is that
//! `D` is unchanged by masking with its own support indicator `χ`:
//!
//! ```text
//! BoolAnalysis.deriv_mul_ind_self :
//!   ∀ (a b : Bool),
//!     Rat.mul (Rat.sub (pm a) (pm b)) (ind (Bool.not (Bool.beq a b)))
//!       = Rat.sub (pm a) (pm b)
//! ```
//!
//! i.e. `D·χ = D` for the `{0,±2}` derivative `D = pm a − pm b` and its support
//! indicator `χ = ind(¬(a == b))`. Where `a = b` the difference `D` is `0`, so
//! masking by the (zero) indicator is a no-op; where `a ≠ b` the indicator is
//! `1`, so `D·1 = D`. This is the SIBLING of the landed
//! `BoolAnalysis.disagree_sq_bridge` (`4·χ = D·D`); together they express the
//! full support algebra of the discrete derivative.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! `Bool.rec` on `a` then `b` (four leaves). Each leaf is a CLOSED `Rat` identity
//! that ground-reduces (`pm`/`ind` reduce on concrete Bools, `Bool.beq`/`Bool.not`
//! reduce natively):
//!   * `(true,true)/(false,false)`: `(pm a − pm a)·ind(¬true) = 0·0 = 0` and
//!     `pm a − pm a = 0`.
//!   * `(true,false)`: `(−1 − 1)·ind(¬false) = (−2)·1 = −2` and `−1 − 1 = −2`.
//!   * `(false,true)`: `(1 − (−1))·ind(¬false) = 2·1 = 2` and `1 − (−1) = 2`.
//!
//! Closed by `@Eq.refl Rat <LHS>` per leaf (both sides reduce to the same
//! `Rat.mk` numeral). Mirrors `register_disagree_sq_bridge` byte-for-byte, so the
//! closure is empty and the quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `BoolAnalysis.deriv_mul_ind_self :
    ///   ∀ (a b : Bool),
    ///     (pm a − pm b)·ind(¬(a == b)) = pm a − pm b`
    /// — the support-mask idempotence of the `{0,±2}` discrete derivative.
    /// Kernel-checked, `ProofQuality::Constructive`, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_deriv_mul_ind_self(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_mul_ind_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_beq()?; // Bool.beq
        self.init_boolean_analysis()?; // ind, pm, Rat foundations
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // `init_boolean_analysis` re-enters the influence_fourier assembly; the
        // mask lemma is NOT part of it, but guard re-declaration defensively.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let one = Level::succ(Level::zero());
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
        let bool_beq = Expr::const_(Name::from_string("Bool.beq"), vec![]);
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let eq_rat = Expr::const_(Name::from_string("Eq"), vec![one]);
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        // diff(a,b) = Rat.sub (pm a) (pm b)
        let diff = |a: Expr, b: Expr| {
            Expr::apps(
                rat_sub.clone(),
                [Expr::app(pm.clone(), a), Expr::app(pm.clone(), b)],
            )
        };
        // lhs(a,b) = Rat.mul (diff a b) (ind (Bool.not (Bool.beq a b)))
        let lhs = |a: Expr, b: Expr| {
            let beq = Expr::apps(bool_beq.clone(), [a.clone(), b.clone()]);
            let not_beq = Expr::app(bool_not.clone(), beq);
            let ind_term = Expr::app(ind.clone(), not_beq);
            Expr::apps(rat_mul.clone(), [diff(a, b), ind_term])
        };
        // rhs(a,b) = diff a b
        let rhs = |a: Expr, b: Expr| diff(a, b);
        let eqn = |l: Expr, r: Expr| Expr::apps(eq_rat.clone(), [rat.clone(), l, r]);

        // Type: ∀ (a b : Bool), lhs a b = rhs a b
        let type_ = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, a) = bld.fresh_local(bool_c.clone());
            let (b_id, b) = bld.fresh_local(bool_c.clone());
            let concl = eqn(lhs(a.clone(), b.clone()), rhs(a.clone(), b.clone()));
            let e = bld.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl);
            let e = bld.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
            bld.finish(e)
        };

        // value: fun (a b : Bool) => Bool.rec (motive_a) <a=false> <a=true> a
        // each inner case splits on b and emits @Eq.refl Rat (lhs a b)
        // (lhs a b ≡ rhs a b by ground Rat reduction).
        let value = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, a) = bld.fresh_local(bool_c.clone());
            let (b_id, b) = bld.fresh_local(bool_c.clone());

            // motive_a : fun (a' : Bool) => lhs a' b = rhs a' b
            let motive_a = {
                let mut d = EnvDeclBuilder::child_of(&bld);
                let (ap_id, ap) = d.fresh_local(bool_c.clone());
                let body = eqn(lhs(ap.clone(), b.clone()), rhs(ap.clone(), b.clone()));
                d.finish_child(d.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), body))
            };

            // For a fixed concrete `av`, split on `b` and emit Eq.refl leaves.
            let inner_rec = |av: Expr, parent: &EnvDeclBuilder| {
                let d = EnvDeclBuilder::child_of(parent);
                // motive_b : fun (b' : Bool) => lhs av b' = rhs av b'
                let motive_b = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (bp_id, bp) = e.fresh_local(bool_c.clone());
                    let body = eqn(lhs(av.clone(), bp.clone()), rhs(av.clone(), bp.clone()));
                    e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let leaf =
                    |bv: Expr| Expr::apps(eq_refl.clone(), [rat.clone(), lhs(av.clone(), bv)]);
                let b_false = leaf(bfalse.clone());
                let b_true = leaf(btrue.clone());
                let e = Expr::apps(bool_rec0.clone(), [motive_b, b_false, b_true, b.clone()]);
                d.finish_child(e)
            };

            let a_false_case = inner_rec(bfalse.clone(), &bld);
            let a_true_case = inner_rec(btrue.clone(), &bld);

            let rec_a = Expr::apps(
                bool_rec0.clone(),
                [motive_a, a_false_case, a_true_case, a.clone()],
            );
            let e = bld.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec_a);
            let e = bld.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e);
            bld.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_deriv_mul_ind_self()
            .expect("register_deriv_mul_ind_self should succeed");
        env
    }

    #[test]
    fn test_deriv_mul_ind_self_is_theorem() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.deriv_mul_ind_self"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_deriv_mul_ind_self_type_checks() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.deriv_mul_ind_self");
        let info = env.get_const(&nm).expect("registered");
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("proof must check against its type: {e:?}"));
    }

    #[test]
    fn test_deriv_mul_ind_self_constructive_axiom_free() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.deriv_mul_ind_self");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_deriv_mul_ind_self().expect("first");
        env.register_deriv_mul_ind_self().expect("idempotent");
    }
}
